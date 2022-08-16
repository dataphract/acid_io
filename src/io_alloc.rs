//! I/O implementations which rely on `alloc`.

#![cfg(all(not(feature = "std"), feature = "alloc"))]

use alloc::{boxed::Box, string::String, vec, vec::Vec};
use core::{cmp, fmt, mem, ptr, str};

use crate::{
    io_core, BufRead, Cursor, Error, ErrorKind, IoSlice, IoSliceMut, Read, Result, Seek, SeekFrom,
    Write, DEFAULT_BUF_SIZE,
};

// This uses an adaptive system to extend the vector when it fills. We want to
// avoid paying to allocate and zero a huge chunk of memory if the reader only
// has 4 bytes while still making large reads if the reader does have a ton
// of data to return. Simply tacking on an extra DEFAULT_BUF_SIZE space every
// time is 4,500 times (!) slower than a default reservation size of 32 if the
// reader has a very small amount of data to return.
//
// Because we're extending the buffer with uninitialized data for trusted
// readers, we need to make sure to truncate that if any of this panics.
pub(crate) fn default_read_to_end<R: Read + ?Sized>(r: &mut R, buf: &mut Vec<u8>) -> Result<usize> {
    let start_len = buf.len();
    let start_cap = buf.capacity();
    let mut g = Guard {
        len: buf.len(),
        buf,
    };
    loop {
        // If we've read all the way up to the capacity, reserve more space.
        if g.len == g.buf.capacity() {
            g.buf.reserve(32);
        }

        // Initialize any excess capacity and adjust the length so we can write
        // to it.
        if g.buf.len() < g.buf.capacity() {
            // TODO(dataphract):
            //
            // The implementation used in Rust 1.58 and earlier is as follows,
            // verbatim:
            //
            // ```
            // unsafe {
            //     // FIXME(danielhenrymantilla): #42788
            //     //
            //     //   - This creates a (mut) reference to a slice of
            //     //     _uninitialized_ integers, which is **undefined behavior**
            //     //
            //     //   - Only the standard library gets to soundly "ignore" this,
            //     //     based on its privileged knowledge of unstable rustc
            //     //     internals;
            //     let capacity = g.buf.capacity();
            //     g.buf.set_len(capacity);
            //     r.initializer().initialize(&mut g.buf[g.len..]);
            // }
            // ```
            //
            // Starting in version 1.59, this is replaced with a truly-sound
            // implementation. However, that implementation is not usable in
            // (stable) downstream crates because it relies on unstable
            // features.
            //
            // To avoid possible UB in the future, we unconditionally zero the
            // newly allocated memory before reading into it. This is expected
            // to have a substantial performance impact. Once the necessary APIs
            // are stabilized, this should be replaced with the 1.59 version.
            //
            // (libs team pls ;-;)
            g.buf.resize(g.buf.capacity(), 0);
        }

        let buf = &mut g.buf[g.len..];
        match r.read(buf) {
            Ok(0) => return Ok(g.len - start_len),
            Ok(n) => {
                // We can't allow bogus values from read. If it is too large, the returned vec could have its length
                // set past its capacity, or if it overflows the vec could be shortened which could create an invalid
                // string if this is called via read_to_string.
                assert!(n <= buf.len());
                g.len += n;
            }
            Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }

        if g.len == g.buf.capacity() && g.buf.capacity() == start_cap {
            // The buffer might be an exact fit. Let's read into a probe buffer
            // and see if it returns `Ok(0)`. If so, we've avoided an
            // unnecessary doubling of the capacity. But if not, append the
            // probe buffer to the primary buffer and let its capacity grow.
            let mut probe = [0u8; 32];

            loop {
                match r.read(&mut probe) {
                    Ok(0) => return Ok(g.len - start_len),
                    Ok(n) => {
                        g.buf.extend_from_slice(&probe[..n]);
                        g.len += n;
                        break;
                    }
                    Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
                    Err(e) => return Err(e),
                }
            }
        }
    }
}

pub(crate) fn default_read_to_string<R: Read + ?Sized>(
    r: &mut R,
    buf: &mut String,
) -> Result<usize> {
    // Note that we do *not* call `r.read_to_end()` here. We are passing
    // `&mut Vec<u8>` (the raw contents of `buf`) into the `read_to_end`
    // method to fill it up. An arbitrary implementation could overwrite the
    // entire contents of the vector, not just append to it (which is what
    // we are expecting).
    //
    // To prevent extraneously checking the UTF-8-ness of the entire buffer
    // we pass it to our hardcoded `default_read_to_end` implementation which
    // we know is guaranteed to only read data into the end of the buffer.
    unsafe { append_to_string(buf, |b| default_read_to_end(r, b)) }
}

pub(crate) fn read_until<R: BufRead + ?Sized>(
    r: &mut R,
    delim: u8,
    buf: &mut Vec<u8>,
) -> Result<usize> {
    let mut read = 0;
    loop {
        let (done, used) = {
            let available = match r.fill_buf() {
                Ok(n) => n,
                Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            };
            match memchr::memchr(delim, available) {
                Some(i) => {
                    buf.extend_from_slice(&available[..=i]);
                    (true, i + 1)
                }
                None => {
                    buf.extend_from_slice(available);
                    (false, available.len())
                }
            }
        };
        r.consume(used);
        read += used;
        if done || used == 0 {
            return Ok(read);
        }
    }
}

struct Guard<'a> {
    buf: &'a mut Vec<u8>,
    len: usize,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        unsafe {
            self.buf.set_len(self.len);
        }
    }
}

// Several `read_to_string` and `read_line` methods in the standard library will
// append data into a `String` buffer, but we need to be pretty careful when
// doing this. The implementation will just call `.as_mut_vec()` and then
// delegate to a byte-oriented reading method, but we must ensure that when
// returning we never leave `buf` in a state such that it contains invalid UTF-8
// in its bounds.
//
// To this end, we use an RAII guard (to protect against panics) which updates
// the length of the string when it is dropped. This guard initially truncates
// the string to the prior length and only after we've validated that the
// new contents are valid UTF-8 do we allow it to set a longer length.
//
// The unsafety in this function is twofold:
//
// 1. We're looking at the raw bytes of `buf`, so we take on the burden of UTF-8
//    checks.
// 2. We're passing a raw buffer to the function `f`, and it is expected that
//    the function only *appends* bytes to the buffer. We'll get undefined
//    behavior if existing bytes are overwritten to have non-UTF-8 data.
pub(crate) unsafe fn append_to_string<F>(buf: &mut String, f: F) -> Result<usize>
where
    F: FnOnce(&mut Vec<u8>) -> Result<usize>,
{
    let mut g = Guard {
        len: buf.len(),
        buf: buf.as_mut_vec(),
    };
    let ret = f(g.buf);
    if str::from_utf8(&g.buf[g.len..]).is_err() {
        ret.and_then(|_| {
            Err(Error::new_const(
                ErrorKind::InvalidData,
                &"stream did not contain valid UTF-8",
            ))
        })
    } else {
        g.len = g.buf.len();
        ret
    }
}

/// An iterator over the contents of an instance of `BufRead` split on a
/// particular byte.
///
/// This struct is generally created by calling [`split`] on a `BufRead`.
/// Please see the documentation of [`split`] for more details.
///
/// [`split`]: BufRead::split
#[derive(Debug)]
pub struct Split<B> {
    pub(crate) buf: B,
    pub(crate) delim: u8,
}

impl<B: BufRead> Iterator for Split<B> {
    type Item = Result<Vec<u8>>;

    fn next(&mut self) -> Option<Result<Vec<u8>>> {
        let mut buf = Vec::new();
        match self.buf.read_until(self.delim, &mut buf) {
            Ok(0) => None,
            Ok(_n) => {
                if buf[buf.len() - 1] == self.delim {
                    buf.pop();
                }
                Some(Ok(buf))
            }
            Err(e) => Some(Err(e)),
        }
    }
}

/// An iterator over the lines of an instance of `BufRead`.
///
/// This struct is generally created by calling [`lines`] on a `BufRead`.
/// Please see the documentation of [`lines`] for more details.
///
/// [`lines`]: BufRead::lines
#[derive(Debug)]
pub struct Lines<B> {
    pub(crate) buf: B,
}

impl<B: BufRead> Iterator for Lines<B> {
    type Item = Result<String>;

    fn next(&mut self) -> Option<Result<String>> {
        let mut buf = String::new();
        match self.buf.read_line(&mut buf) {
            Ok(0) => None,
            Ok(_n) => {
                if buf.ends_with('\n') {
                    buf.pop();
                    if buf.ends_with('\r') {
                        buf.pop();
                    }
                }
                Some(Ok(buf))
            }
            Err(e) => Some(Err(e)),
        }
    }
}

/// The `BufReader<R>` struct adds buffering to any reader.
///
/// It can be excessively inefficient to work directly with a [`Read`] instance.
/// A `BufReader<R>` performs large, infrequent reads on the underlying [`Read`]
/// and maintains an in-memory buffer of the results.
///
/// `BufReader<R>` can improve the speed of programs that make *small* and
/// *repeated* read calls to the same `Read` instance. It does not
/// help when reading very large amounts at once, or reading just one or a few
/// times. It also provides no advantage when reading from a source that is
/// already in memory, like a <code>[Vec]\<u8></code>.
///
/// When the `BufReader<R>` is dropped, the contents of its buffer will be
/// discarded. Creating multiple instances of a `BufReader<R>` on the same
/// stream can cause data loss. Reading from the underlying reader after
/// unwrapping the `BufReader<R>` with [`BufReader::into_inner`] can also cause
/// data loss.
///
/// # Examples
///
/// ```
/// use acid_io::prelude::*;
/// use acid_io::BufReader;
///
/// # fn main() -> acid_io::Result<()> {
/// let text = "Some\nlines\nof\ntext\n";
/// let mut reader = BufReader::new(text.as_bytes());
///
/// let mut line = String::new();
/// reader.read_line(&mut line)?;
/// assert_eq!(line, "Some\n");
/// # Ok(())
/// # }
/// ```
pub struct BufReader<R> {
    inner: R,
    buf: Box<[u8]>,
    pos: usize,
    cap: usize,
}

impl<R: Read> BufReader<R> {
    /// Creates a new `BufReader<R>` with a default buffer capacity. The default is currently 8 KB,
    /// but may change in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufReader;
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let src: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    /// let reader = BufReader::new(src.as_slice());
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(inner: R) -> BufReader<R> {
        BufReader::with_capacity(DEFAULT_BUF_SIZE, inner)
    }

    /// Creates a new `BufReader<R>` with the specified buffer capacity.
    ///
    /// # Examples
    ///
    /// Creating a buffer with ten bytes of capacity:
    ///
    /// ```
    /// use acid_io::BufReader;
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let src = "Some data to be buffered while reading";
    /// let reader = BufReader::with_capacity(10, src.as_bytes());
    /// # Ok(())
    /// # }
    /// ```
    pub fn with_capacity(capacity: usize, inner: R) -> BufReader<R> {
        // TODO(dataphract):
        //
        // The standard library does this:
        //
        // ```
        // let mut buf = Box::new_uninit_slice(capacity).assume_init();
        // inner.initializer().initialize(&mut buf);
        // ```
        //
        // We don't have stable access to the initializer API (and it's unlikely
        // to be stabilized), so instead we create a zeroed Vec and turn that
        // into a boxed slice. When `ReadBuf` becomes available, use that
        // instead.
        BufReader {
            inner,
            buf: vec![0; capacity].into_boxed_slice(),
            pos: 0,
            cap: 0,
        }
    }
}

impl<R> BufReader<R> {
    /// Gets a reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufReader;
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let text = "Hello, world!";
    /// let reader = BufReader::new(text.as_bytes());
    ///
    /// let r2 = reader.get_ref();
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufReader;
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let text = "Hello, world!";
    /// let mut reader = BufReader::new(text.as_bytes());
    ///
    /// let r2 = reader.get_mut();
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Returns a reference to the internally buffered data.
    ///
    /// Unlike [`fill_buf`], this will not attempt to fill the buffer if it is empty.
    ///
    /// [`fill_buf`]: BufRead::fill_buf
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufReader, BufRead};
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let text = "Buffer me, please!";
    /// let mut reader = BufReader::new(text.as_bytes());
    /// assert!(reader.buffer().is_empty());
    ///
    /// if reader.fill_buf()?.len() > 0 {
    ///     assert!(!reader.buffer().is_empty());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn buffer(&self) -> &[u8] {
        &self.buf[self.pos..self.cap]
    }

    /// Returns the number of bytes the internal buffer can hold at once.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufReader, BufRead};
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let data = [0u8; 128];
    /// let reader = BufReader::with_capacity(64, data.as_slice());
    ///
    /// assert_eq!(reader.capacity(), 64);
    /// # Ok(())
    /// # }
    /// ```
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Unwraps this `BufReader<R>`, returning the underlying reader.
    ///
    /// Note that any leftover data in the internal buffer is lost. Therefore,
    /// a following read from the underlying reader may lead to data loss.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufReader, Cursor};
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let curs = Cursor::new(b"Some data being read by a cursor".as_slice());
    /// let reader = BufReader::new(curs);
    ///
    /// let curs: Cursor<_> = reader.into_inner();
    /// Ok(())
    /// # }
    /// ```
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Invalidates all data in the internal buffer.
    #[inline]
    fn discard_buffer(&mut self) {
        self.pos = 0;
        self.cap = 0;
    }
}

impl<R: Seek> BufReader<R> {
    /// Seeks relative to the current position. If the new position lies within the buffer,
    /// the buffer will not be flushed, allowing for more efficient seeks.
    /// This method does not return the location of the underlying reader, so the caller
    /// must track this information themselves if it is required.
    pub fn seek_relative(&mut self, offset: i64) -> Result<()> {
        let pos = self.pos as u64;
        if offset < 0 {
            if let Some(new_pos) = pos.checked_sub((-offset) as u64) {
                self.pos = new_pos as usize;
                return Ok(());
            }
        } else if let Some(new_pos) = pos.checked_add(offset as u64) {
            if new_pos <= self.cap as u64 {
                self.pos = new_pos as usize;
                return Ok(());
            }
        }

        self.seek(SeekFrom::Current(offset)).map(drop)
    }
}

impl<R: Read> Read for BufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if self.pos == self.cap && buf.len() >= self.buf.len() {
            self.discard_buffer();
            return self.inner.read(buf);
        }
        let nread = {
            let mut rem = self.fill_buf()?;
            rem.read(buf)?
        };
        self.consume(nread);
        Ok(nread)
    }

    // Small read_exacts from a BufReader are extremely common when used with a deserializer.
    // The default implementation calls read in a loop, which results in surprisingly poor code
    // generation for the common path where the buffer has enough bytes to fill the passed-in
    // buffer.
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        if self.buffer().len() >= buf.len() {
            buf.copy_from_slice(&self.buffer()[..buf.len()]);
            self.consume(buf.len());
            return Ok(());
        }

        io_core::default_read_exact(self, buf)
    }

    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum::<usize>();
        if self.pos == self.cap && total_len >= self.buf.len() {
            self.discard_buffer();
            return self.inner.read_vectored(bufs);
        }
        let nread = {
            let mut rem = self.fill_buf()?;
            rem.read_vectored(bufs)?
        };
        self.consume(nread);
        Ok(nread)
    }

    fn is_read_vectored(&self) -> bool {
        self.inner.is_read_vectored()
    }

    // The inner reader might have an optimized `read_to_end`. Drain our buffer and then
    // delegate to the inner implementation.
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize> {
        let nread = self.cap - self.pos;
        buf.extend_from_slice(&self.buf[self.pos..self.cap]);
        self.discard_buffer();
        Ok(nread + self.inner.read_to_end(buf)?)
    }

    // The inner reader might have an optimized `read_to_end`. Drain our buffer and then
    // delegate to the inner implementation.
    fn read_to_string(&mut self, buf: &mut String) -> Result<usize> {
        // In the general `else` case below we must read bytes into a side buffer, check
        // that they are valid UTF-8, and then append them to `buf`. This requires a
        // potentially large memcpy.
        //
        // If `buf` is empty--the most common case--we can leverage `append_to_string`
        // to read directly into `buf`'s internal byte buffer, saving an allocation and
        // a memcpy.
        if buf.is_empty() {
            // `append_to_string`'s safety relies on the buffer only being appended to since
            // it only checks the UTF-8 validity of new data. If there were existing content in
            // `buf` then an untrustworthy reader (i.e. `self.inner`) could not only append
            // bytes but also modify existing bytes and render them invalid. On the other hand,
            // if `buf` is empty then by definition any writes must be appends and
            // `append_to_string` will validate all of the new bytes.
            unsafe { append_to_string(buf, |b| self.read_to_end(b)) }
        } else {
            // We cannot append our byte buffer directly onto the `buf` String as there could
            // be an incomplete UTF-8 sequence that has only been partially read. We must read
            // everything into a side buffer first and then call `from_utf8` on the complete
            // buffer.
            let mut bytes = Vec::new();
            self.read_to_end(&mut bytes)?;
            let string = str::from_utf8(&bytes).map_err(|_| {
                Error::new_const(
                    ErrorKind::InvalidData,
                    &"stream did not contain valid UTF-8",
                )
            })?;
            *buf += string;
            Ok(string.len())
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min, max) = self.inner.size_hint();

        (
            min + self.buffer().len(),
            max.and_then(|up| self.buffer().len().checked_add(up)),
        )
    }
}

impl<R: Read> BufRead for BufReader<R> {
    fn fill_buf(&mut self) -> Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.
        if self.pos >= self.cap {
            debug_assert!(self.pos == self.cap);
            self.cap = self.inner.read(&mut self.buf)?;
            self.pos = 0;
        }
        Ok(&self.buf[self.pos..self.cap])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = cmp::min(self.pos + amt, self.cap);
    }
}

impl<R> fmt::Debug for BufReader<R>
where
    R: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("BufReader")
            .field("reader", &self.inner)
            .field(
                "buffer",
                &format_args!("{}/{}", self.cap - self.pos, self.buf.len()),
            )
            .finish()
    }
}

impl<R: Seek> Seek for BufReader<R> {
    /// Seek to an offset, in bytes, in the underlying reader.
    ///
    /// The position used for seeking with <code>[SeekFrom::Current]\(_)</code> is the
    /// position the underlying reader would be at if the `BufReader<R>` had no
    /// internal buffer.
    ///
    /// Seeking always discards the internal buffer, even if the seek position
    /// would otherwise fall within it. This guarantees that calling
    /// [`BufReader::into_inner()`] immediately after a seek yields the underlying reader
    /// at the same position.
    ///
    /// To seek without discarding the internal buffer, use [`BufReader::seek_relative`].
    ///
    /// See [`acid_io::Seek`] for more details.
    ///
    /// Note: In the edge case where you're seeking with <code>[SeekFrom::Current]\(n)</code>
    /// where `n` minus the internal buffer length overflows an `i64`, two
    /// seeks will be performed instead of one. If the second seek returns
    /// [`Err`], the underlying reader will be left at the same position it would
    /// have if you called `seek` with <code>[SeekFrom::Current]\(0)</code>.
    ///
    /// [`acid_io::Seek`]: Seek
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        let result: u64;
        if let SeekFrom::Current(n) = pos {
            let remainder = (self.cap - self.pos) as i64;
            // it should be safe to assume that remainder fits within an i64 as the alternative
            // means we managed to allocate 8 exbibytes and that's absurd.
            // But it's not out of the realm of possibility for some weird underlying reader to
            // support seeking by i64::MIN so we need to handle underflow when subtracting
            // remainder.
            if let Some(offset) = n.checked_sub(remainder) {
                result = self.inner.seek(SeekFrom::Current(offset))?;
            } else {
                // seek backwards by our remainder, and then by the offset
                self.inner.seek(SeekFrom::Current(-remainder))?;
                self.discard_buffer();
                result = self.inner.seek(SeekFrom::Current(n))?;
            }
        } else {
            // Seeking with Start/End doesn't care about our buffer length.
            result = self.inner.seek(pos)?;
        }
        self.discard_buffer();
        Ok(result)
    }

    /// Returns the current seek position from the start of the stream.
    ///
    /// The value returned is equivalent to `self.seek(SeekFrom::Current(0))`
    /// but does not flush the internal buffer. Due to this optimization the
    /// function does not guarantee that calling `.into_inner()` immediately
    /// afterwards will yield the underlying reader at the same position. Use
    /// [`BufReader::seek`] instead if you require that guarantee.
    ///
    /// # Panics
    ///
    /// This function will panic if the position of the inner reader is smaller
    /// than the amount of buffered data. That can happen if the inner reader
    /// has an incorrect implementation of [`Seek::stream_position`], or if the
    /// position has gone out of sync due to calling [`Seek::seek`] directly on
    /// the underlying reader.
    ///
    /// # Example
    ///
    /// ```
    /// use acid_io::{BufRead, BufReader, Cursor, Seek};
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let text = "Lorem ipsum\ndolor sit amet\n";
    /// let mut reader = BufReader::new(Cursor::new(text.as_bytes()));
    ///
    /// let before = reader.stream_position()?;
    /// reader.read_line(&mut String::new())?;
    /// let after = reader.stream_position()?;
    ///
    /// assert_eq!(after - before, "Lorem ipsum\n".len() as u64);
    /// # Ok(())
    /// # }
    /// ```
    fn stream_position(&mut self) -> Result<u64> {
        let remainder = (self.cap - self.pos) as u64;
        self.inner.stream_position().map(|pos| {
            pos.checked_sub(remainder).expect(
                "overflow when subtracting remaining buffer size from inner stream position",
            )
        })
    }
}

/// An error returned by [`BufWriter::into_inner`] which combines an error that
/// happened while writing out the buffer, and the buffered writer object
/// which may be used to recover from the condition.
///
/// # Examples
///
/// ```
/// use acid_io::{BufWriter, Write};
///
/// # fn main() -> acid_io::Result<()> {
/// let mut writer = BufWriter::new(Vec::new());
///
/// // do stuff with the vec
/// writer.write_all("I live in a vector now!".as_bytes())?;
///
/// // we want to get our `Vec` back, so let's try:
///
/// let buf = match writer.into_inner() {
///     Ok(b) => b,
///     Err(e) => {
///         // Here, e is an IntoInnerError
///         panic!("An error occurred");
///     }
/// };
/// # Ok(())
/// # }
///
/// ```
#[derive(Debug)]
pub struct IntoInnerError<W>(W, Error);

impl<W> IntoInnerError<W> {
    /// Construct a new IntoInnerError
    fn new(writer: W, error: Error) -> Self {
        Self(writer, error)
    }

    /// Helper to construct a new IntoInnerError; intended to help with
    /// adapters that wrap other adapters
    fn new_wrapped<W2>(self, f: impl FnOnce(W) -> W2) -> IntoInnerError<W2> {
        let Self(writer, error) = self;
        IntoInnerError::new(f(writer), error)
    }

    /// Returns the error which caused the call to [`BufWriter::into_inner()`]
    /// to fail.
    ///
    /// This error was returned when attempting to write the internal buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufWriter, Write};
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let mut writer = BufWriter::new(Vec::new());
    ///
    /// // do stuff with the vec
    /// writer.write_all("I live in a vector now!".as_bytes())?;
    ///
    /// // we want to get our `Vec` back, so let's try:
    ///
    /// let buf = match writer.into_inner() {
    ///     Ok(b) => b,
    ///     Err(e) => {
    ///         // Here, e is an IntoInnerError
    ///         panic!("An error occurred: {}", e.error());
    ///     }
    /// };
    /// # Ok(())
    /// # }
    /// ```
    pub fn error(&self) -> &Error {
        &self.1
    }

    /// Returns the buffered writer instance which generated the error.
    ///
    /// The returned object can be used for error recovery, such as
    /// re-inspecting the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufWriter, Write};
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let mut writer = BufWriter::new(Vec::new());
    ///
    /// // do stuff with the vec
    /// writer.write_all("I live in a vector now!".as_bytes())?;
    ///
    /// // we want to get our `Vec` back, so let's try:
    ///
    /// let buf = match writer.into_inner() {
    ///     Ok(b) => b,
    ///     Err(e) => {
    ///         // Get the writer back after an error:
    ///         let w: BufWriter<_> = e.into_inner();
    ///         // And unwrap the buffer:
    ///         w.into_inner().unwrap()
    ///     }
    /// };
    /// # Ok(())
    /// # }
    /// ```
    pub fn into_inner(self) -> W {
        self.0
    }

    /// Consumes the [`IntoInnerError`] and returns the error which caused the call to
    /// [`BufWriter::into_inner()`] to fail.  Unlike `error`, this can be used to
    /// obtain ownership of the underlying error.
    ///
    /// # Example
    /// ```
    /// use acid_io::{BufWriter, ErrorKind, Write};
    ///
    /// let mut not_enough_space = [0u8; 10];
    /// let mut stream = BufWriter::new(not_enough_space.as_mut());
    /// write!(stream, "this cannot be actually written").unwrap();
    /// let into_inner_err = stream.into_inner().expect_err("now we discover it's too small");
    /// let err = into_inner_err.into_error();
    /// assert_eq!(err.kind(), ErrorKind::WriteZero);
    /// ```
    pub fn into_error(self) -> Error {
        self.1
    }

    /// Consumes the [`IntoInnerError`] and returns the error which caused the call to
    /// [`BufWriter::into_inner()`] to fail, and the underlying writer.
    ///
    /// This can be used to simply obtain ownership of the underlying error; it can also be used for
    /// advanced error recovery.
    ///
    /// # Example
    /// ```
    /// use acid_io::{BufWriter, ErrorKind, Write};
    ///
    /// let mut not_enough_space = [0u8; 10];
    /// let mut stream = BufWriter::new(not_enough_space.as_mut());
    /// write!(stream, "this cannot be actually written").unwrap();
    /// let into_inner_err = stream.into_inner().expect_err("now we discover it's too small");
    /// let (err, recovered_writer) = into_inner_err.into_parts();
    /// assert_eq!(err.kind(), ErrorKind::WriteZero);
    /// assert_eq!(recovered_writer.buffer(), b"t be actually written");
    /// ```
    pub fn into_parts(self) -> (Error, W) {
        (self.1, self.0)
    }
}

impl<W> From<IntoInnerError<W>> for Error {
    fn from(iie: IntoInnerError<W>) -> Error {
        iie.1
    }
}

impl<W> fmt::Display for IntoInnerError<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error().fmt(f)
    }
}

/// Wraps a writer and buffers its output.
///
/// It can be excessively inefficient to work directly with something that
/// implements [`Write`]. A `BufWriter<W>` keeps an in-memory buffer of data and
/// writes it to an underlying writer in large, infrequent batches.
///
/// `BufWriter<W>` can improve the speed of programs that make *small* and
/// *repeated* write calls to the same `Write` instance. It does not help when
/// writing very large amounts at once, or writing just one or a few times. It
/// also provides no advantage when writing to a destination that is in memory,
/// like a <code>[Vec]\<u8></code>.
///
/// It is critical to call [`flush`] before `BufWriter<W>` is dropped. Though
/// dropping will attempt to flush the contents of the buffer, any errors
/// that happen in the process of dropping will be ignored. Calling [`flush`]
/// ensures that the buffer is empty and thus dropping will not even attempt
/// file operations.
///
/// [`flush`]: BufWriter::flush
pub struct BufWriter<W: Write> {
    inner: W,
    // The buffer. Avoid using this like a normal `Vec` in common code paths.
    // That is, don't use `buf.push`, `buf.extend_from_slice`, or any other
    // methods that require bounds checking or the like. This makes an enormous
    // difference to performance (we may want to stop using a `Vec` entirely).
    buf: Vec<u8>,
    // #30888: If the inner writer panics in a call to write, we don't want to
    // write the buffered data a second time in BufWriter's destructor. This
    // flag tells the Drop impl if it should skip the flush.
    panicked: bool,
}

impl<W: Write> BufWriter<W> {
    /// Creates a new `BufWriter<W>` with a default buffer capacity. The default is currently 8 KB,
    /// but may change in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufWriter, Cursor};
    ///
    /// let buf: Vec<u8> = Vec::new();
    /// let mut writer = BufWriter::new(Cursor::new(buf));
    /// ```
    pub fn new(inner: W) -> BufWriter<W> {
        BufWriter::with_capacity(DEFAULT_BUF_SIZE, inner)
    }

    /// Creates a new `BufWriter<W>` with the specified buffer capacity.
    ///
    /// # Examples
    ///
    /// Creating a writer with a buffer of a hundred bytes.
    ///
    /// ```
    /// use acid_io::{BufWriter, Cursor};
    ///
    /// let buf: Vec<u8> = Vec::new();
    /// let mut writer = BufWriter::with_capacity(100, Cursor::new(buf));
    /// ```
    pub fn with_capacity(capacity: usize, inner: W) -> BufWriter<W> {
        BufWriter {
            inner,
            buf: Vec::with_capacity(capacity),
            panicked: false,
        }
    }

    /// Send data in our local buffer into the inner writer, looping as
    /// necessary until either it's all been sent or an error occurs.
    ///
    /// Because all the data in the buffer has been reported to our owner as
    /// "successfully written" (by returning nonzero success values from
    /// `write`), any 0-length writes from `inner` must be reported as i/o
    /// errors from this method.
    pub(crate) fn flush_buf(&mut self) -> Result<()> {
        /// Helper struct to ensure the buffer is updated after all the writes
        /// are complete. It tracks the number of written bytes and drains them
        /// all from the front of the buffer when dropped.
        struct BufGuard<'a> {
            buffer: &'a mut Vec<u8>,
            written: usize,
        }

        impl<'a> BufGuard<'a> {
            fn new(buffer: &'a mut Vec<u8>) -> Self {
                Self { buffer, written: 0 }
            }

            /// The unwritten part of the buffer
            fn remaining(&self) -> &[u8] {
                &self.buffer[self.written..]
            }

            /// Flag some bytes as removed from the front of the buffer
            fn consume(&mut self, amt: usize) {
                self.written += amt;
            }

            /// true if all of the bytes have been written
            fn done(&self) -> bool {
                self.written >= self.buffer.len()
            }
        }

        impl Drop for BufGuard<'_> {
            fn drop(&mut self) {
                if self.written > 0 {
                    self.buffer.drain(..self.written);
                }
            }
        }

        let mut guard = BufGuard::new(&mut self.buf);
        while !guard.done() {
            self.panicked = true;
            let r = self.inner.write(guard.remaining());
            self.panicked = false;

            match r {
                Ok(0) => {
                    return Err(Error::new_const(
                        ErrorKind::WriteZero,
                        &"failed to write the buffered data",
                    ));
                }
                Ok(n) => guard.consume(n),
                Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Buffer some data without flushing it, regardless of the size of the
    /// data. Writes as much as possible without exceeding capacity. Returns
    /// the number of bytes written.
    pub fn write_to_buf(&mut self, buf: &[u8]) -> usize {
        let available = self.spare_capacity();
        let amt_to_buffer = available.min(buf.len());

        // SAFETY: `amt_to_buffer` is <= buffer's spare capacity by construction.
        unsafe {
            self.write_to_buffer_unchecked(&buf[..amt_to_buffer]);
        }

        amt_to_buffer
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufWriter;
    ///
    /// let mut buffer = BufWriter::new(Vec::new());
    ///
    /// // we can use reference just like buffer
    /// let reference: &Vec<u8> = buffer.get_ref();
    /// ```
    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufWriter;
    ///
    /// let mut buffer = BufWriter::new(Vec::new());
    ///
    /// // we can use reference just like buffer
    /// let reference: &mut Vec<u8> = buffer.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut W {
        &mut self.inner
    }

    /// Returns a reference to the internally buffered data.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufWriter;
    ///
    /// let buf_writer = BufWriter::new(Vec::new());
    ///
    /// // See how many bytes are currently buffered
    /// let bytes_buffered = buf_writer.buffer().len();
    /// ```
    pub fn buffer(&self) -> &[u8] {
        &self.buf
    }

    /// Returns a mutable reference to the internal buffer.
    ///
    /// This can be used to write data directly into the buffer without triggering writers
    /// to the underlying writer.
    ///
    /// That the buffer is a `Vec` is an implementation detail.
    /// Callers should not modify the capacity as there currently is no public API to do so
    /// and thus any capacity changes would be unexpected by the user.
    // TODO(dataphract): this is used in io::copy
    #[allow(dead_code)]
    pub(crate) fn buffer_mut(&mut self) -> &mut Vec<u8> {
        &mut self.buf
    }

    /// Returns the number of bytes the internal buffer can hold without flushing.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufWriter;
    ///
    /// let buf_writer = BufWriter::new(Vec::new());
    ///
    /// // Check the capacity of the inner buffer
    /// let capacity = buf_writer.capacity();
    /// // Calculate how many bytes can be written without flushing
    /// let without_flush = capacity - buf_writer.buffer().len();
    /// ```
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Unwraps this `BufWriter<W>`, returning the underlying writer.
    ///
    /// The buffer is written out before returning the writer.
    ///
    /// # Errors
    ///
    /// An [`Err`] will be returned if an error occurs while flushing the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::BufWriter;
    ///
    /// let mut buffer = BufWriter::new(Vec::new());
    ///
    /// let inner: Vec<u8> = buffer.into_inner().unwrap();
    /// ```
    pub fn into_inner(mut self) -> core::result::Result<W, IntoInnerError<BufWriter<W>>> {
        match self.flush_buf() {
            Err(e) => Err(IntoInnerError::new(self, e)),
            Ok(()) => Ok(self.into_parts().0),
        }
    }

    /// Disassembles this `BufWriter<W>`, returning the underlying writer, and any buffered but
    /// unwritten data.
    ///
    /// If the underlying writer panicked, it is not known what portion of the data was written.
    /// In this case, we return `WriterPanicked` for the buffered data (from which the buffer
    /// contents can still be recovered).
    ///
    /// `into_parts` makes no attempt to flush data and cannot fail.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{BufWriter, Write};
    ///
    /// let mut buffer = [0u8; 10];
    /// let mut stream = BufWriter::new(buffer.as_mut());
    /// write!(stream, "too much data").unwrap();
    /// stream.flush().expect_err("it doesn't fit");
    /// let (recovered_writer, buffered_data) = stream.into_parts();
    /// assert_eq!(recovered_writer.len(), 0);
    /// assert_eq!(&buffered_data.unwrap(), b"ata");
    /// ```
    pub fn into_parts(mut self) -> (W, core::result::Result<Vec<u8>, WriterPanicked>) {
        let buf = mem::take(&mut self.buf);
        let buf = if !self.panicked {
            Ok(buf)
        } else {
            Err(WriterPanicked { buf })
        };

        // SAFETY: forget(self) prevents double dropping inner
        let inner = unsafe { ptr::read(&self.inner) };
        mem::forget(self);

        (inner, buf)
    }

    // Ensure this function does not get inlined into `write`, so that it
    // remains inlineable and its common path remains as short as possible.
    // If this function ends up being called frequently relative to `write`,
    // it's likely a sign that the client is using an improperly sized buffer
    // or their write patterns are somewhat pathological.
    #[cold]
    #[inline(never)]
    fn write_cold(&mut self, buf: &[u8]) -> Result<usize> {
        if buf.len() > self.spare_capacity() {
            self.flush_buf()?;
        }

        // Why not len > capacity? To avoid a needless trip through the buffer when the input
        // exactly fills it. We'd just need to flush it to the underlying writer anyway.
        if buf.len() >= self.buf.capacity() {
            self.panicked = true;
            let r = self.get_mut().write(buf);
            self.panicked = false;
            r
        } else {
            // Write to the buffer. In this case, we write to the buffer even if it fills it
            // exactly. Doing otherwise would mean flushing the buffer, then writing this
            // input to the inner writer, which in many cases would be a worse strategy.

            // SAFETY: There was either enough spare capacity already, or there wasn't and we
            // flushed the buffer to ensure that there is. In the latter case, we know that there
            // is because flushing ensured that our entire buffer is spare capacity, and we entered
            // this block because the input buffer length is less than that capacity. In either
            // case, it's safe to write the input buffer to our buffer.
            unsafe {
                self.write_to_buffer_unchecked(buf);
            }

            Ok(buf.len())
        }
    }

    // Ensure this function does not get inlined into `write_all`, so that it
    // remains inlineable and its common path remains as short as possible.
    // If this function ends up being called frequently relative to `write_all`,
    // it's likely a sign that the client is using an improperly sized buffer
    // or their write patterns are somewhat pathological.
    #[cold]
    #[inline(never)]
    fn write_all_cold(&mut self, buf: &[u8]) -> Result<()> {
        // Normally, `write_all` just calls `write` in a loop. We can do better
        // by calling `self.get_mut().write_all()` directly, which avoids
        // round trips through the buffer in the event of a series of partial
        // writes in some circumstances.

        if buf.len() > self.spare_capacity() {
            self.flush_buf()?;
        }

        // Why not len > capacity? To avoid a needless trip through the buffer when the input
        // exactly fills it. We'd just need to flush it to the underlying writer anyway.
        if buf.len() >= self.buf.capacity() {
            self.panicked = true;
            let r = self.get_mut().write_all(buf);
            self.panicked = false;
            r
        } else {
            // Write to the buffer. In this case, we write to the buffer even if it fills it
            // exactly. Doing otherwise would mean flushing the buffer, then writing this
            // input to the inner writer, which in many cases would be a worse strategy.

            // SAFETY: There was either enough spare capacity already, or there wasn't and we
            // flushed the buffer to ensure that there is. In the latter case, we know that there
            // is because flushing ensured that our entire buffer is spare capacity, and we entered
            // this block because the input buffer length is less than that capacity. In either
            // case, it's safe to write the input buffer to our buffer.
            unsafe {
                self.write_to_buffer_unchecked(buf);
            }

            Ok(())
        }
    }

    // SAFETY: Requires `buf.len() <= self.buf.capacity() - self.buf.len()`,
    // i.e., that input buffer length is less than or equal to spare capacity.
    #[inline]
    unsafe fn write_to_buffer_unchecked(&mut self, buf: &[u8]) {
        debug_assert!(buf.len() <= self.spare_capacity());
        let old_len = self.buf.len();
        let buf_len = buf.len();
        let src = buf.as_ptr();
        let dst = self.buf.as_mut_ptr().add(old_len);
        ptr::copy_nonoverlapping(src, dst, buf_len);
        self.buf.set_len(old_len + buf_len);
    }

    #[inline]
    fn spare_capacity(&self) -> usize {
        self.buf.capacity() - self.buf.len()
    }
}

/// Error returned for the buffered data from `BufWriter::into_parts`, when the underlying
/// writer has previously panicked.  Contains the (possibly partly written) buffered data.
///
/// # Example
///
/// ```
/// use acid_io::{self, BufWriter, Write};
/// use std::panic::{catch_unwind, AssertUnwindSafe};
///
/// struct PanickingWriter;
/// impl Write for PanickingWriter {
///   fn write(&mut self, buf: &[u8]) -> acid_io::Result<usize> { panic!() }
///   fn flush(&mut self) -> acid_io::Result<()> { panic!() }
/// }
///
/// let mut stream = BufWriter::new(PanickingWriter);
/// write!(stream, "some data").unwrap();
/// let result = catch_unwind(AssertUnwindSafe(|| {
///     stream.flush().unwrap()
/// }));
/// assert!(result.is_err());
/// let (recovered_writer, buffered_data) = stream.into_parts();
/// assert!(matches!(recovered_writer, PanickingWriter));
/// assert_eq!(buffered_data.unwrap_err().into_inner(), b"some data");
/// ```
pub struct WriterPanicked {
    buf: Vec<u8>,
}

impl WriterPanicked {
    /// Returns the perhaps-unwritten data.  Some of this data may have been written by the
    /// panicking call(s) to the underlying writer, so simply writing it again is not a good idea.
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_inner(self) -> Vec<u8> {
        self.buf
    }

    const DESCRIPTION: &'static str =
        "BufWriter inner writer panicked, what data remains unwritten is not known";
}

impl fmt::Display for WriterPanicked {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::DESCRIPTION)
    }
}

impl fmt::Debug for WriterPanicked {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WriterPanicked")
            .field(
                "buffer",
                &format_args!("{}/{}", self.buf.len(), self.buf.capacity()),
            )
            .finish()
    }
}

impl<W: Write> Write for BufWriter<W> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        // Use < instead of <= to avoid a needless trip through the buffer in some cases.
        // See `write_cold` for details.
        if buf.len() < self.spare_capacity() {
            // SAFETY: safe by above conditional.
            unsafe {
                self.write_to_buffer_unchecked(buf);
            }

            Ok(buf.len())
        } else {
            self.write_cold(buf)
        }
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        // Use < instead of <= to avoid a needless trip through the buffer in some cases.
        // See `write_all_cold` for details.
        if buf.len() < self.spare_capacity() {
            // SAFETY: safe by above conditional.
            unsafe {
                self.write_to_buffer_unchecked(buf);
            }

            Ok(())
        } else {
            self.write_all_cold(buf)
        }
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        // FIXME: Consider applying `#[inline]` / `#[inline(never)]` optimizations already applied
        // to `write` and `write_all`. The performance benefits can be significant. See #79930.
        if self.get_ref().is_write_vectored() {
            // We have to handle the possibility that the total length of the buffers overflows
            // `usize` (even though this can only happen if multiple `IoSlice`s reference the
            // same underlying buffer, as otherwise the buffers wouldn't fit in memory). If the
            // computation overflows, then surely the input cannot fit in our buffer, so we forward
            // to the inner writer's `write_vectored` method to let it handle it appropriately.
            let saturated_total_len = bufs
                .iter()
                .fold(0usize, |acc, b| acc.saturating_add(b.len()));

            if saturated_total_len > self.spare_capacity() {
                // Flush if the total length of the input exceeds our buffer's spare capacity.
                // If we would have overflowed, this condition also holds, and we need to flush.
                self.flush_buf()?;
            }

            if saturated_total_len >= self.buf.capacity() {
                // Forward to our inner writer if the total length of the input is greater than or
                // equal to our buffer capacity. If we would have overflowed, this condition also
                // holds, and we punt to the inner writer.
                self.panicked = true;
                let r = self.get_mut().write_vectored(bufs);
                self.panicked = false;
                r
            } else {
                // `saturated_total_len < self.buf.capacity()` implies that we did not saturate.

                // SAFETY: We checked whether or not the spare capacity was large enough above. If
                // it was, then we're safe already. If it wasn't, we flushed, making sufficient
                // room for any input <= the buffer size, which includes this input.
                unsafe {
                    bufs.iter().for_each(|b| self.write_to_buffer_unchecked(b));
                };

                Ok(saturated_total_len)
            }
        } else {
            let mut iter = bufs.iter();
            let mut total_written = if let Some(buf) = iter.by_ref().find(|&buf| !buf.is_empty()) {
                // This is the first non-empty slice to write, so if it does
                // not fit in the buffer, we still get to flush and proceed.
                if buf.len() > self.spare_capacity() {
                    self.flush_buf()?;
                }
                if buf.len() >= self.buf.capacity() {
                    // The slice is at least as large as the buffering capacity,
                    // so it's better to write it directly, bypassing the buffer.
                    self.panicked = true;
                    let r = self.get_mut().write(buf);
                    self.panicked = false;
                    return r;
                } else {
                    // SAFETY: We checked whether or not the spare capacity was large enough above.
                    // If it was, then we're safe already. If it wasn't, we flushed, making
                    // sufficient room for any input <= the buffer size, which includes this input.
                    unsafe {
                        self.write_to_buffer_unchecked(buf);
                    }

                    buf.len()
                }
            } else {
                return Ok(0);
            };
            debug_assert!(total_written != 0);
            for buf in iter {
                if buf.len() <= self.spare_capacity() {
                    // SAFETY: safe by above conditional.
                    unsafe {
                        self.write_to_buffer_unchecked(buf);
                    }

                    // This cannot overflow `usize`. If we are here, we've written all of the bytes
                    // so far to our buffer, and we've ensured that we never exceed the buffer's
                    // capacity. Therefore, `total_written` <= `self.buf.capacity()` <= `usize::MAX`.
                    total_written += buf.len();
                } else {
                    break;
                }
            }
            Ok(total_written)
        }
    }

    fn is_write_vectored(&self) -> bool {
        true
    }

    fn flush(&mut self) -> Result<()> {
        self.flush_buf().and_then(|()| self.get_mut().flush())
    }
}

impl<W: Write> fmt::Debug for BufWriter<W>
where
    W: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("BufWriter")
            .field("writer", &self.inner)
            .field(
                "buffer",
                &format_args!("{}/{}", self.buf.len(), self.buf.capacity()),
            )
            .finish()
    }
}

impl<W: Write + Seek> Seek for BufWriter<W> {
    /// Seek to the offset, in bytes, in the underlying writer.
    ///
    /// Seeking always writes out the internal buffer before seeking.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.flush_buf()?;
        self.get_mut().seek(pos)
    }
}

impl<W: Write> Drop for BufWriter<W> {
    fn drop(&mut self) {
        if !self.panicked {
            // dtors should not panic, so we ignore a failed flush
            let _r = self.flush_buf();
        }
    }
}

/// Private helper struct for implementing the line-buffered writing logic.
/// This shim temporarily wraps a BufWriter, and uses its internals to
/// implement a line-buffered writer (specifically by using the internal
/// methods like write_to_buf and flush_buf). In this way, a more
/// efficient abstraction can be created than one that only had access to
/// `write` and `flush`, without needlessly duplicating a lot of the
/// implementation details of BufWriter. This also allows existing
/// `BufWriters` to be temporarily given line-buffering logic; this is what
/// enables Stdout to be alternately in line-buffered or block-buffered mode.
#[derive(Debug)]
pub struct LineWriterShim<'a, W: Write> {
    buffer: &'a mut BufWriter<W>,
}

impl<'a, W: Write> LineWriterShim<'a, W> {
    pub fn new(buffer: &'a mut BufWriter<W>) -> Self {
        Self { buffer }
    }

    /// Get a reference to the inner writer (that is, the writer
    /// wrapped by the BufWriter).
    fn inner(&self) -> &W {
        self.buffer.get_ref()
    }

    /// Get a mutable reference to the inner writer (that is, the writer
    /// wrapped by the BufWriter). Be careful with this writer, as writes to
    /// it will bypass the buffer.
    fn inner_mut(&mut self) -> &mut W {
        self.buffer.get_mut()
    }

    /// Get the content currently buffered in self.buffer
    fn buffered(&self) -> &[u8] {
        self.buffer.buffer()
    }

    /// Flush the buffer iff the last byte is a newline (indicating that an
    /// earlier write only succeeded partially, and we want to retry flushing
    /// the buffered line before continuing with a subsequent write)
    fn flush_if_completed_line(&mut self) -> Result<()> {
        match self.buffered().last().copied() {
            Some(b'\n') => self.buffer.flush_buf(),
            _ => Ok(()),
        }
    }
}

impl<'a, W: Write> Write for LineWriterShim<'a, W> {
    /// Write some data into this BufReader with line buffering. This means
    /// that, if any newlines are present in the data, the data up to the last
    /// newline is sent directly to the underlying writer, and data after it
    /// is buffered. Returns the number of bytes written.
    ///
    /// This function operates on a "best effort basis"; in keeping with the
    /// convention of `Write::write`, it makes at most one attempt to write
    /// new data to the underlying writer. If that write only reports a partial
    /// success, the remaining data will be buffered.
    ///
    /// Because this function attempts to send completed lines to the underlying
    /// writer, it will also flush the existing buffer if it ends with a
    /// newline, even if the incoming data does not contain any newlines.
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let newline_idx = match memchr::memrchr(b'\n', buf) {
            // If there are no new newlines (that is, if this write is less than
            // one line), just do a regular buffered write (which may flush if
            // we exceed the inner buffer's size)
            None => {
                self.flush_if_completed_line()?;
                return self.buffer.write(buf);
            }
            // Otherwise, arrange for the lines to be written directly to the
            // inner writer.
            Some(newline_idx) => newline_idx + 1,
        };

        // Flush existing content to prepare for our write. We have to do this
        // before attempting to write `buf` in order to maintain consistency;
        // if we add `buf` to the buffer then try to flush it all at once,
        // we're obligated to return Ok(), which would mean suppressing any
        // errors that occur during flush.
        self.buffer.flush_buf()?;

        // This is what we're going to try to write directly to the inner
        // writer. The rest will be buffered, if nothing goes wrong.
        let lines = &buf[..newline_idx];

        // Write `lines` directly to the inner writer. In keeping with the
        // `write` convention, make at most one attempt to add new (unbuffered)
        // data. Because this write doesn't touch the BufWriter state directly,
        // and the buffer is known to be empty, we don't need to worry about
        // self.buffer.panicked here.
        let flushed = self.inner_mut().write(lines)?;

        // If buffer returns Ok(0), propagate that to the caller without
        // doing additional buffering; otherwise we're just guaranteeing
        // an "ErrorKind::WriteZero" later.
        if flushed == 0 {
            return Ok(0);
        }

        // Now that the write has succeeded, buffer the rest (or as much of
        // the rest as possible). If there were any unwritten newlines, we
        // only buffer out to the last unwritten newline that fits in the
        // buffer; this helps prevent flushing partial lines on subsequent
        // calls to LineWriterShim::write.

        // Handle the cases in order of most-common to least-common, under
        // the presumption that most writes succeed in totality, and that most
        // writes are smaller than the buffer.
        // - Is this a partial line (ie, no newlines left in the unwritten tail)
        // - If not, does the data out to the last unwritten newline fit in
        //   the buffer?
        // - If not, scan for the last newline that *does* fit in the buffer
        let tail = if flushed >= newline_idx {
            &buf[flushed..]
        } else if newline_idx - flushed <= self.buffer.capacity() {
            &buf[flushed..newline_idx]
        } else {
            let scan_area = &buf[flushed..];
            let scan_area = &scan_area[..self.buffer.capacity()];
            match memchr::memrchr(b'\n', scan_area) {
                Some(newline_idx) => &scan_area[..newline_idx + 1],
                None => scan_area,
            }
        };

        let buffered = self.buffer.write_to_buf(tail);
        Ok(flushed + buffered)
    }

    fn flush(&mut self) -> Result<()> {
        self.buffer.flush()
    }

    /// Write some vectored data into this BufReader with line buffering. This
    /// means that, if any newlines are present in the data, the data up to
    /// and including the buffer containing the last newline is sent directly
    /// to the inner writer, and the data after it is buffered. Returns the
    /// number of bytes written.
    ///
    /// This function operates on a "best effort basis"; in keeping with the
    /// convention of `Write::write`, it makes at most one attempt to write
    /// new data to the underlying writer.
    ///
    /// Because this function attempts to send completed lines to the underlying
    /// writer, it will also flush the existing buffer if it contains any
    /// newlines.
    ///
    /// Because sorting through an array of `IoSlice` can be a bit convoluted,
    /// This method differs from write in the following ways:
    ///
    /// - It attempts to write the full content of all the buffers up to and
    ///   including the one containing the last newline. This means that it
    ///   may attempt to write a partial line, that buffer has data past the
    ///   newline.
    /// - If the write only reports partial success, it does not attempt to
    ///   find the precise location of the written bytes and buffer the rest.
    ///
    /// If the underlying vector doesn't support vectored writing, we instead
    /// simply write the first non-empty buffer with `write`. This way, we
    /// get the benefits of more granular partial-line handling without losing
    /// anything in efficiency
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        // If there's no specialized behavior for write_vectored, just use
        // write. This has the benefit of more granular partial-line handling.
        if !self.is_write_vectored() {
            return match bufs.iter().find(|buf| !buf.is_empty()) {
                Some(buf) => self.write(buf),
                None => Ok(0),
            };
        }

        // Find the buffer containing the last newline
        let last_newline_buf_idx = bufs
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, buf)| memchr::memchr(b'\n', buf).map(|_| i));

        // If there are no new newlines (that is, if this write is less than
        // one line), just do a regular buffered write
        let last_newline_buf_idx = match last_newline_buf_idx {
            // No newlines; just do a normal buffered write
            None => {
                self.flush_if_completed_line()?;
                return self.buffer.write_vectored(bufs);
            }
            Some(i) => i,
        };

        // Flush existing content to prepare for our write
        self.buffer.flush_buf()?;

        // This is what we're going to try to write directly to the inner
        // writer. The rest will be buffered, if nothing goes wrong.
        let (lines, tail) = bufs.split_at(last_newline_buf_idx + 1);

        // Write `lines` directly to the inner writer. In keeping with the
        // `write` convention, make at most one attempt to add new (unbuffered)
        // data. Because this write doesn't touch the BufWriter state directly,
        // and the buffer is known to be empty, we don't need to worry about
        // self.panicked here.
        let flushed = self.inner_mut().write_vectored(lines)?;

        // If inner returns Ok(0), propagate that to the caller without
        // doing additional buffering; otherwise we're just guaranteeing
        // an "ErrorKind::WriteZero" later.
        if flushed == 0 {
            return Ok(0);
        }

        // Don't try to reconstruct the exact amount written; just bail
        // in the event of a partial write
        let lines_len = lines.iter().map(|buf| buf.len()).sum();
        if flushed < lines_len {
            return Ok(flushed);
        }

        // Now that the write has succeeded, buffer the rest (or as much of the
        // rest as possible)
        let buffered: usize = tail
            .iter()
            .filter(|buf| !buf.is_empty())
            .map(|buf| self.buffer.write_to_buf(buf))
            .take_while(|&n| n > 0)
            .sum();

        Ok(flushed + buffered)
    }

    fn is_write_vectored(&self) -> bool {
        self.inner().is_write_vectored()
    }

    /// Write some data into this BufReader with line buffering. This means
    /// that, if any newlines are present in the data, the data up to the last
    /// newline is sent directly to the underlying writer, and data after it
    /// is buffered.
    ///
    /// Because this function attempts to send completed lines to the underlying
    /// writer, it will also flush the existing buffer if it contains any
    /// newlines, even if the incoming data does not contain any newlines.
    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        match memchr::memrchr(b'\n', buf) {
            // If there are no new newlines (that is, if this write is less than
            // one line), just do a regular buffered write (which may flush if
            // we exceed the inner buffer's size)
            None => {
                self.flush_if_completed_line()?;
                self.buffer.write_all(buf)
            }
            Some(newline_idx) => {
                let (lines, tail) = buf.split_at(newline_idx + 1);

                if self.buffered().is_empty() {
                    self.inner_mut().write_all(lines)?;
                } else {
                    // If there is any buffered data, we add the incoming lines
                    // to that buffer before flushing, which saves us at least
                    // one write call. We can't really do this with `write`,
                    // since we can't do this *and* not suppress errors *and*
                    // report a consistent state to the caller in a return
                    // value, but here in write_all it's fine.
                    self.buffer.write_all(lines)?;
                    self.buffer.flush_buf()?;
                }

                self.buffer.write_all(tail)
            }
        }
    }
}

/// Wraps a writer and buffers output to it, flushing whenever a newline
/// (`0x0a`, `'\n'`) is detected.
///
/// The [`BufWriter`] struct wraps a writer and buffers its output.
/// But it only does this batched write when it goes out of scope, or when the
/// internal buffer is full. Sometimes, you'd prefer to write each line as it's
/// completed, rather than the entire buffer at once. Enter `LineWriter`. It
/// does exactly that.
///
/// Like [`BufWriter`], a `LineWriter`’s buffer will also be flushed when the
/// `LineWriter` goes out of scope or when its internal buffer is full.
///
/// If there's still a partial line in the buffer when the `LineWriter` is
/// dropped, it will flush those contents.
///
/// # Examples
///
/// We can use `LineWriter` to write one line at a time, significantly
/// reducing the number of actual writes to the file.
///
/// ```
/// use acid_io::prelude::*;
/// use acid_io::LineWriter;
///
/// fn main() -> acid_io::Result<()> {
///     let road_not_taken = b"I shall be telling this with a sigh
/// Somewhere ages and ages hence:
/// Two roads diverged in a wood, and I -
/// I took the one less traveled by,
/// And that has made all the difference.";
///
///     let mut writer = LineWriter::new(Vec::new());
///
///     writer.write_all(b"I shall be telling this with a sigh")?;
///
///     // No bytes are written until a newline is encountered (or
///     // the internal buffer is filled).
///     assert_eq!(writer.get_ref().as_slice(), &[]);
///     writer.write_all(b"\n")?;
///     assert_eq!(
///         writer.get_ref().as_slice(),
///         &b"I shall be telling this with a sigh\n"[..],
///     );
///
///     // Write the rest of the poem.
///     writer.write_all(b"Somewhere ages and ages hence:
/// Two roads diverged in a wood, and I -
/// I took the one less traveled by,
/// And that has made all the difference.")?;
///
///     // The last line of the poem doesn't end in a newline, so
///     // we have to flush or drop the `LineWriter` to finish
///     // writing.
///     writer.flush()?;
///
///     // Confirm the whole poem was written.
///     let written = writer.into_inner().unwrap();
///     assert_eq!(written, &road_not_taken[..]);
///     Ok(())
/// }
/// ```
pub struct LineWriter<W: Write> {
    inner: BufWriter<W>,
}

impl<W: Write> LineWriter<W> {
    /// Creates a new `LineWriter`.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::LineWriter;
    ///
    /// fn main() -> acid_io::Result<()> {
    ///     let writer = LineWriter::new(Vec::new());
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn new(inner: W) -> LineWriter<W> {
        // Lines typically aren't that long, don't use a giant buffer
        LineWriter::with_capacity(1024, inner)
    }

    /// Creates a new `LineWriter` with a specified capacity for the internal
    /// buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::LineWriter;
    ///
    /// fn main() -> acid_io::Result<()> {
    ///     let writer = LineWriter::with_capacity(100, Vec::new());
    ///     Ok(())
    /// }
    /// ```
    pub fn with_capacity(capacity: usize, inner: W) -> LineWriter<W> {
        LineWriter {
            inner: BufWriter::with_capacity(capacity, inner),
        }
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::LineWriter;
    ///
    /// fn main() -> acid_io::Result<()> {
    ///     let writer = LineWriter::new(Vec::new());
    ///
    ///     let reference: &Vec<u8> = writer.get_ref();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_ref(&self) -> &W {
        self.inner.get_ref()
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// Caution must be taken when calling methods on the mutable reference
    /// returned as extra writes could corrupt the output stream.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::LineWriter;
    ///
    /// fn main() -> acid_io::Result<()> {
    ///     let mut writer = LineWriter::new(Vec::new());
    ///
    ///     // we can use reference just like writer
    ///     let reference = writer.get_mut();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut W {
        self.inner.get_mut()
    }

    /// Unwraps this `LineWriter`, returning the underlying writer.
    ///
    /// The internal buffer is written out before returning the writer.
    ///
    /// # Errors
    ///
    /// An [`Err`] will be returned if an error occurs while flushing the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::LineWriter;
    ///
    /// fn main() -> acid_io::Result<()> {
    ///     let writer: LineWriter<Vec<u8>> = LineWriter::new(Vec::new());
    ///
    ///     let v: Vec<u8> = writer.into_inner()?;
    ///     Ok(())
    /// }
    /// ```
    pub fn into_inner(self) -> core::result::Result<W, IntoInnerError<LineWriter<W>>> {
        self.inner
            .into_inner()
            .map_err(|err| err.new_wrapped(|inner| LineWriter { inner }))
    }
}

impl<W: Write> Write for LineWriter<W> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        LineWriterShim::new(&mut self.inner).write(buf)
    }

    fn flush(&mut self) -> Result<()> {
        self.inner.flush()
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        LineWriterShim::new(&mut self.inner).write_vectored(bufs)
    }

    fn is_write_vectored(&self) -> bool {
        self.inner.is_write_vectored()
    }

    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        LineWriterShim::new(&mut self.inner).write_all(buf)
    }

    fn write_all_vectored(&mut self, bufs: &mut [IoSlice<'_>]) -> Result<()> {
        LineWriterShim::new(&mut self.inner).write_all_vectored(bufs)
    }

    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> Result<()> {
        LineWriterShim::new(&mut self.inner).write_fmt(fmt)
    }
}

impl<W: Write> fmt::Debug for LineWriter<W>
where
    W: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("LineWriter")
            .field("writer", &self.get_ref())
            .field(
                "buffer",
                &format_args!("{}/{}", self.inner.buffer().len(), self.inner.capacity()),
            )
            .finish_non_exhaustive()
    }
}

impl<R: Read + ?Sized> Read for Box<R> {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        R::read(self, dst)
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        R::read_exact(self, buf)
    }
}

impl<T: Seek + ?Sized> Seek for Box<T> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        T::seek(self, pos)
    }
    fn rewind(&mut self) -> Result<()> {
        T::rewind(self)
    }
    fn stream_len(&mut self) -> Result<u64> {
        T::stream_len(self)
    }
    fn stream_position(&mut self) -> Result<u64> {
        T::stream_position(self)
    }
}

impl Write for Vec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        let len = bufs.iter().map(|b| b.len()).sum();
        self.reserve(len);
        for buf in bufs {
            self.extend_from_slice(buf);
        }
        Ok(len)
    }

    #[inline]
    fn is_write_vectored(&self) -> bool {
        true
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        self.extend_from_slice(buf);
        Ok(())
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

// Resizing write implementation
fn vec_write(pos_mut: &mut u64, vec: &mut Vec<u8>, buf: &[u8]) -> Result<usize> {
    let pos: usize = (*pos_mut).try_into().map_err(|_| {
        Error::new_const(
            ErrorKind::InvalidInput,
            &"cursor position exceeds maximum possible vector length",
        )
    })?;
    // Make sure the internal buffer is as least as big as where we
    // currently are
    let len = vec.len();
    if len < pos {
        // use `resize` so that the zero filling is as efficient as possible
        vec.resize(pos, 0);
    }
    // Figure out what bytes will be used to overwrite what's currently
    // there (left), and what will be appended on the end (right)
    {
        let space = vec.len() - pos;
        let (left, right) = buf.split_at(cmp::min(space, buf.len()));
        vec[pos..pos + left.len()].copy_from_slice(left);
        vec.extend_from_slice(right);
    }

    // Bump us forward
    *pos_mut = (pos + buf.len()) as u64;
    Ok(buf.len())
}

fn vec_write_vectored(pos_mut: &mut u64, vec: &mut Vec<u8>, bufs: &[IoSlice<'_>]) -> Result<usize> {
    let mut nwritten = 0;
    for buf in bufs {
        nwritten += vec_write(pos_mut, vec, buf)?;
    }
    Ok(nwritten)
}

impl Write for Cursor<&mut Vec<u8>> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        vec_write(&mut self.pos, self.inner, buf)
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        vec_write_vectored(&mut self.pos, self.inner, bufs)
    }

    #[inline]
    fn is_write_vectored(&self) -> bool {
        true
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

impl Write for Cursor<Vec<u8>> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        vec_write(&mut self.pos, &mut self.inner, buf)
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        vec_write_vectored(&mut self.pos, &mut self.inner, bufs)
    }

    #[inline]
    fn is_write_vectored(&self) -> bool {
        true
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

impl Write for Cursor<Box<[u8]>> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        io_core::slice_write(&mut self.pos, &mut self.inner, buf)
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        io_core::slice_write_vectored(&mut self.pos, &mut self.inner, bufs)
    }

    #[inline]
    fn is_write_vectored(&self) -> bool {
        true
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}
