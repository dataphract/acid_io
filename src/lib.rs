#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! A pared-down version of [`std::io`] usable in `no_std` contexts.
//!
//! [`std::io`]: https://doc.rust-lang.org/std/io/index.html

#[cfg(feature = "byteorder")]
pub mod byteorder;

use core::{cmp, fmt};

#[cfg(not(feature = "std"))]
use core::mem;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc;
#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{boxed::Box, vec::Vec};

/// The error type for I/O operations of the [`Read`], [`Write`], [`Seek`], and
/// associated traits.
#[derive(Clone, Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    /// Returns the corresponding [`ErrorKind`] for this error.
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "I/O error")
    }
}

/// A list specifying general categories of I/O error.
///
/// This list is intended to grow over time and it is not recommended to
/// exhaustively match against it.
///
/// It is used with the [`acid_io::Error`][Error] type.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// This operation was interrupted.
    ///
    /// Interrupted operations can typically be retried.
    Interrupted,
    /// A parameter was incorrect.
    InvalidInput,
    /// An error returned when an operation could not be completed because an
    /// “end of file” was reached prematurely.
    ///
    /// This typically means that an operation could only succeed if it read a
    /// particular number of bytes but only a smaller number of bytes could be
    /// read.
    UnexpectedEof,
    /// An error returned when an operation could not be completed because a
    /// call to [`write`] returned [`Ok(0)`].
    ///
    /// This typically means that an operation could only succeed if it wrote a
    /// particular number of bytes but only a smaller number of bytes could be
    /// written.
    ///
    /// [`write`]: crate::Write::write
    /// [`Ok(0)`]: Ok
    WriteZero,
    /// A custom error that does not fall under any other I/O error kind.
    ///
    /// This can be used to construct your own [`Error`]s that do not match any
    /// [`ErrorKind`].
    ///
    /// This [`ErrorKind`] is not used by `acid_io`.
    ///
    /// Errors from the standard library that do not fall under any of the I/O
    /// error kinds cannot be `match`ed on, and will only match a wildcard (`_`)
    /// pattern.  New [`ErrorKind`]s might be added in the future for some of
    /// those.
    Other,
    /// Any I/O error from `acid_io` that's not part of this list.
    ///
    /// Errors that are `Uncategorized` now may move to a different or a new
    /// [`ErrorKind`] variant in the future. It is not recommended to match
    /// an error against `Uncategorized`; use a wildcard match (`_`) instead.
    #[doc(hidden)]
    Uncategorized,
}

/// A specialized [`Result`] type for I/O operations.
///
/// This type is broadly used across `acid_io` for any operation which may
/// produce an error.
///
/// This typedef is generally used to avoid writing out
/// [`acid_io::Error`][Error] directly and is otherwise a direct mapping to
/// [`Result`].
///
/// While usual Rust style is to import types directly, aliases of [`Result`]
/// often are not, to make it easier to distinguish between them. [`Result`] is
/// generally assumed to be [`core::result::Result`], and so users of this alias
/// will generally use `acid_io::Result` instead of shadowing the [prelude]'s
/// import of [`core::result::Result`].
///
/// [`io::Error`]: Error
/// [prelude]: core::prelude
pub type Result<T> = core::result::Result<T, Error>;

/// The `Read` trait allows for reading bytes from a source.
///
/// Implementors of the `Read` trait are called 'readers'.
///
/// Readers are defined by one required method, [`read()`]. Each call to [`read()`]
/// will attempt to pull bytes from this source into a provided buffer. A
/// number of other methods are implemented in terms of [`read()`], giving
/// implementors a number of ways to read bytes while only needing to implement
/// a single method.
///
/// # Examples
///
/// Read from [`&str`] because [`&[u8]`][prim@slice] implements `Read`:
///
/// ```no_run
/// use acid_io::{self as io, Read as _};
///
/// # fn main() -> io::Result<()> {
/// let mut b = "This string will be read".as_bytes();
/// let mut buffer = [0; 10];
///
/// // read up to 10 bytes
/// b.read(&mut buffer)?;
///
/// # Ok(())
/// # }
/// ```
///
/// [`read()`]: Read::read
/// [`&str`]: prim@str
pub trait Read {
    /// Pull some bytes from this source into the specified buffer, returning
    /// how many bytes were read.
    ///
    /// This function does not provide any guarantees about whether it blocks
    /// waiting for data, but if an object needs to block for a read and cannot,
    /// it will typically signal this via an [`Err`] return value.
    ///
    /// If the return value of this method is [`Ok(n)`], then implementations must
    /// guarantee that `0 <= n <= dst.len()`. A nonzero `n` value indicates
    /// that the buffer `dst` has been filled in with `n` bytes of data from this
    /// source. If `n` is `0`, then it can indicate one of two scenarios:
    ///
    /// 1. This reader has reached its "end of file" and will likely no longer
    ///    be able to produce bytes. Note that this does not mean that the
    ///    reader will *always* no longer be able to produce bytes.
    /// 2. The buffer specified was 0 bytes in length.
    ///
    /// It is not an error if the returned value `n` is smaller than the buffer size,
    /// even when the reader is not at the end of the stream yet.
    /// This may happen for example because fewer bytes are actually available right now
    /// (e. g. being close to end-of-file) or because read() was interrupted by a signal.
    ///
    /// As this trait is safe to implement, callers cannot rely on `n <= dst.len()` for safety.
    /// Extra care needs to be taken when `unsafe` functions are used to access the read bytes.
    /// Callers have to ensure that no unchecked out-of-bounds accesses are possible even if
    /// `n > dst.len()`.
    ///
    /// No guarantees are provided about the contents of `dst` when this
    /// function is called, implementations cannot rely on any property of the
    /// contents of `dst` being true. It is recommended that *implementations*
    /// only write data to `dst` instead of reading its contents.
    ///
    /// Correspondingly, however, *callers* of this method must not assume any guarantees
    /// about how the implementation uses `dst`. The trait is safe to implement,
    /// so it is possible that the code that's supposed to write to the buffer might also read
    /// from it. It is your responsibility to make sure that `dst` is initialized
    /// before calling `read`. Calling `read` with an uninitialized `dst` (of the kind one
    /// obtains via [`MaybeUninit<T>`]) is not safe, and can lead to undefined behavior.
    ///
    /// [`MaybeUninit<T>`]: core::mem::MaybeUninit
    ///
    /// # Errors
    ///
    /// If this function encounters any form of I/O or other error, an error
    /// variant will be returned. If an error is returned then it must be
    /// guaranteed that no bytes were read.
    ///
    /// An error of the [`ErrorKind::Interrupted`] kind is non-fatal and the read
    /// operation should be retried if there is nothing else to do.
    ///
    /// # Examples
    ///
    /// [`Ok(n)`]: Ok
    ///
    /// ```
    /// use acid_io::Read;
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let src = [1u8, 2, 3, 4, 5, 6, 7, 8];
    /// let mut dst = [0u8; 3];
    ///
    /// let mut r = &src[..];
    ///
    /// // read up to 3 bytes
    /// let n = r.read(&mut dst[..])?;
    ///
    /// assert_eq!(dst, [1, 2, 3]);
    /// # Ok(())
    /// # }
    /// ```
    fn read(&mut self, dst: &mut [u8]) -> Result<usize>;

    /// Read the exact number of bytes required to fill `buf`.
    ///
    /// This function reads as many bytes as necessary to completely fill the
    /// specified buffer `buf`.
    ///
    /// No guarantees are provided about the contents of `buf` when this
    /// function is called; implementations cannot rely on any property of the
    /// contents of `buf` being true. It is recommended that implementations
    /// only write data to `buf` instead of reading its contents. The
    /// documentation on [`read`] has a more detailed explanation on this
    /// subject.
    ///
    /// # Errors
    ///
    /// If this function encounters an error of the kind
    /// [`ErrorKind::Interrupted`] then the error is ignored and the operation
    /// will continue.
    ///
    /// If this function encounters an "end of file" before completely filling
    /// the buffer, it returns an error of the kind [`ErrorKind::UnexpectedEof`].
    /// The contents of `buf` are unspecified in this case.
    ///
    /// If any other read error is encountered then this function immediately
    /// returns. The contents of `buf` are unspecified in this case.
    ///
    /// If this function returns an error, it is unspecified how many bytes it
    /// has read, but it will never read more than would be necessary to
    /// completely fill the buffer.
    ///
    /// # Examples
    ///
    /// [`read`]: Read::read
    ///
    /// ```
    /// use acid_io::Read;
    ///
    /// # fn main() -> acid_io::Result<()> {
    /// let src = [1u8, 2, 3, 4, 5, 6, 7, 8];
    /// let mut dst = [0u8; 3];
    ///
    /// let mut r = &src[..];
    ///
    /// // read exactly 3 bytes
    /// let n = r.read_exact(&mut dst[..])?;
    ///
    /// assert_eq!(dst, [1, 2, 3]);
    /// # Ok(())
    /// # }
    /// ```
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        default_read_exact(self, buf)
    }
}

pub(crate) fn default_read_exact<R: Read + ?Sized>(this: &mut R, mut buf: &mut [u8]) -> Result<()> {
    while !buf.is_empty() {
        match this.read(buf) {
            Ok(0) => break,
            Ok(n) => {
                let tmp = buf;
                buf = &mut tmp[n..];
            }
            Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }

    if !buf.is_empty() {
        Err(Error {
            kind: ErrorKind::UnexpectedEof,
        })
    } else {
        Ok(())
    }
}

#[cfg(not(feature = "std"))]
impl<R: Read> Read for &mut R {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        (*self).read(dst)
    }

    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        (*self).read_exact(buf)
    }
}

#[cfg(not(feature = "std"))]
impl Read for &[u8] {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        let copy_len = cmp::min(dst.len(), self.len());
        let (src, rem) = self.split_at(copy_len);

        // Avoid invoking memcpy for very small copies.
        if copy_len == 1 {
            dst[0] = src[0];
        } else {
            dst[..copy_len].copy_from_slice(src);
        }

        *self = rem;

        Ok(copy_len)
    }
}

/// A trait for objects which are byte-oriented sinks.
///
/// Implementors of the `Write` trait are sometimes called 'writers'.
///
/// Writers are defined by two required methods, [`write`] and [`flush`]:
///
/// * The [`write`] method will attempt to write some data into the object,
///   returning how many bytes were successfully written.
///
/// * The [`flush`] method is useful for adapters and explicit buffers
///   themselves for ensuring that all buffered data has been pushed out to the
///   'true sink'.
///
/// Writers are intended to be composable with one another. Many implementors
/// throughout take and provide types which implement the `Write`
/// trait.
///
/// [`write`]: Write::write
/// [`flush`]: Write::flush
///
/// # Examples
///
/// ```no_run
/// use acid_io::{Cursor, Write as _};
/// # fn main() -> acid_io::Result<()> {
/// let data = b"some bytes";
///
/// let mut arr = [0u8; 10];
/// let mut buffer = Cursor::new(&mut arr[..]);
/// buffer.write(data)?;
///
/// assert_eq!(buffer.get_ref(), data);
/// # Ok(())
/// # }
/// ```
///
/// The trait also provides convenience methods like [`write_all`], which calls
/// `write` in a loop until its entire input has been written.
///
/// [`write_all`]: Write::write_all
pub trait Write {
    /// Write a buffer into this writer, returning how many bytes were written.
    ///
    /// This function will attempt to write the entire contents of `buf`, but
    /// the entire write might not succeed, or the write may also generate an
    /// error. A call to `write` represents *at most one* attempt to write to
    /// any wrapped object.
    ///
    /// Calls to `write` are not guaranteed to block waiting for data to be
    /// written, and a write which would otherwise block can be indicated through
    /// an [`Err`] variant.
    ///
    /// If the return value is [`Ok(n)`] then it must be guaranteed that
    /// `n <= buf.len()`. A return value of `0` typically means that the
    /// underlying object is no longer able to accept bytes and will likely not
    /// be able to in the future as well, or that the buffer provided is empty.
    ///
    /// # Errors
    ///
    /// Each call to `write` may generate an I/O error indicating that the
    /// operation could not be completed. If an error is returned then no bytes
    /// in the buffer were written to this writer.
    ///
    /// It is **not** considered an error if the entire buffer could not be
    /// written to this writer.
    ///
    /// An error of the [`ErrorKind::Interrupted`] kind is non-fatal and the
    /// write operation should be retried if there is nothing else to do.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::prelude::*;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let mut buffer = File::create("foo.txt")?;
    ///
    ///     // Writes some prefix of the byte string, not necessarily all of it.
    ///     buffer.write(b"some bytes")?;
    ///     Ok(())
    /// }
    /// ```
    ///
    /// [`Ok(n)`]: Ok
    fn write(&mut self, src: &[u8]) -> Result<usize>;

    /// Flush this output stream, ensuring that all intermediately buffered
    /// contents reach their destination.
    ///
    /// # Errors
    ///
    /// It is considered an error if not all bytes could be written due to
    /// I/O errors or EOF being reached.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::io::prelude::*;
    /// use std::io::BufWriter;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let mut buffer = BufWriter::new(File::create("foo.txt")?);
    ///
    ///     buffer.write_all(b"some bytes")?;
    ///     buffer.flush()?;
    ///     Ok(())
    /// }
    /// ```
    fn flush(&mut self) -> Result<()>;

    /// Attempts to write an entire buffer into this writer.
    ///
    /// This method will continuously call [`write`] until there is no more data
    /// to be written or an error of non-[`ErrorKind::Interrupted`] kind is
    /// returned. This method will not return until the entire buffer has been
    /// successfully written or such an error occurs. The first error that is
    /// not of [`ErrorKind::Interrupted`] kind generated from this method will be
    /// returned.
    ///
    /// If the buffer contains no data, this will never call [`write`].
    ///
    /// # Errors
    ///
    /// This function will return the first error of
    /// non-[`ErrorKind::Interrupted`] kind that [`write`] returns.
    ///
    /// [`write`]: Write::write
    fn write_all(&mut self, mut buf: &[u8]) -> Result<()> {
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => {
                    return Err(Error {
                        kind: ErrorKind::WriteZero,
                    });
                }
                Ok(n) => buf = &buf[n..],
                Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

#[cfg(not(feature = "std"))]
impl Write for &mut [u8] {
    fn write(&mut self, src: &[u8]) -> Result<usize> {
        let copy_len = cmp::min(src.len(), self.len());

        // Move slice out of self before splitting to appease borrowck.
        let (dst, rem) = mem::take(self).split_at_mut(copy_len);
        dst.copy_from_slice(src);

        *self = rem;

        Ok(copy_len)
    }

    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

/// Enumeration of possible methods to seek within an I/O object.
///
/// It is used by the [`Seek`] trait.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeekFrom {
    /// Sets the offset to the provided number of bytes.
    Start(u64),
    /// Sets the offset to the size of this object plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    End(i64),
    /// Sets the offset to the current position plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    Current(i64),
}

/// The `Seek` trait provides a cursor which can be moved within a stream of
/// bytes.
///
/// The stream typically has a fixed size, allowing seeking relative to either
/// end or the current offset.
pub trait Seek {
    /// Seek to an offset, in bytes, in a stream.
    ///
    /// A seek beyond the end of a stream is allowed, but behavior is defined
    /// by the implementation.
    ///
    /// If the seek operation completed successfully,
    /// this method returns the new position from the start of the stream.
    /// That position can be used later with [`SeekFrom::Start`].
    ///
    /// # Errors
    ///
    /// Seeking can fail, for example because it might involve flushing a buffer.
    ///
    /// Seeking to a negative offset is considered an error.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64>;

    /// Rewind to the beginning of a stream.
    ///
    /// This is a convenience method, equivalent to `seek(SeekFrom::Start(0))`.
    ///
    /// # Errors
    ///
    /// Rewinding can fail, for example because it might involve flushing a buffer.
    fn rewind(&mut self) -> Result<()> {
        self.seek(SeekFrom::Start(0))?;
        Ok(())
    }

    /// Returns the length of this stream (in bytes).
    ///
    /// This method is implemented using up to three seek operations. If this
    /// method returns successfully, the seek position is unchanged (i.e. the
    /// position before calling this method is the same as afterwards).
    /// However, if this method returns an error, the seek position is
    /// unspecified.
    ///
    /// If you need to obtain the length of *many* streams and you don't care
    /// about the seek position afterwards, you can reduce the number of seek
    /// operations by simply calling `seek(SeekFrom::End(0))` and using its
    /// return value (it is also the stream length).
    ///
    /// Note that length of a stream can change over time (for example, when
    /// data is appended to a file). So calling this method multiple times does
    /// not necessarily return the same length each time.
    fn stream_len(&mut self) -> Result<u64> {
        let old_pos = self.stream_position()?;
        let len = self.seek(SeekFrom::End(0))?;

        // Avoid seeking a third time when we were already at the end of the
        // stream. The branch is usually way cheaper than a seek operation.
        if old_pos != len {
            self.seek(SeekFrom::Start(old_pos))?;
        }

        Ok(len)
    }

    /// Returns the current seek position from the start of the stream.
    ///
    /// This is equivalent to `self.seek(SeekFrom::Current(0))`.
    fn stream_position(&mut self) -> Result<u64> {
        self.seek(SeekFrom::Current(0))
    }
}

// Cursor ========================================================================================

/// A `Cursor` wraps an in-memory buffer and provides it with a
/// [`Seek`] implementation.
///
/// `Cursor`s are used with in-memory buffers, anything implementing
/// `AsRef<u8>`, to allow them to implement [`Read`] and/or [`Write`], allowing
/// these buffers to be used anywhere you might use a reader or writer that does
/// actual I/O.
///
/// `acid_io` implements some I/O traits on various types which are commonly
/// used as a buffer, like `Cursor<Vec<u8>>` and `Cursor<&[u8]>`.
///
/// # Examples
///
/// [bytes]: crate::slice "slice"
///
/// ```no_run
/// use acid_io::{self, Read, Seek, SeekFrom, Write};
///
/// // a library function we've written
/// fn write_ten_bytes_at_end<W: Write + Seek>(writer: &mut W) -> acid_io::Result<()> {
///     writer.seek(SeekFrom::End(-10))?;
///
///     for i in 0..10 {
///         writer.write(&[i])?;
///     }
///
///     // all went well
///     Ok(())
/// }
///
/// // now let's write a test
/// #[test]
/// fn test_writes_bytes() {
///     use acid_io::Cursor;
///     let mut buf = Cursor::new(vec![0; 15]);
///
///     write_ten_bytes_at_end(&mut buf).unwrap();
///
///     assert_eq!(&buf.get_ref()[5..15], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
/// }
/// ```
pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

impl<T> Cursor<T> {
    /// Creates a new cursor wrapping the provided underlying in-memory buffer.
    ///
    /// The initial position of the cursor is `0` even if the underlying buffer
    /// is not empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::Cursor;
    ///
    /// let buf = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buf);
    /// ```
    pub const fn new(inner: T) -> Cursor<T> {
        Cursor { inner, pos: 0 }
    }

    /// Consumes this cursor, returning the underlying value.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::Cursor;
    ///
    /// let buf = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buf);
    ///
    /// let vec = buf.into_inner();
    /// ```
    pub fn into_inner(self) -> T {
        self.inner
    }

    /// Gets a reference to the underlying value in this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::Cursor;
    ///
    /// let buf = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buf);
    ///
    /// let reference = buf.get_ref();
    /// ```
    pub fn get_ref(&self) -> &T {
        &self.inner
    }

    /// Gets a mutable reference to the underlying value in this cursor.
    ///
    /// Care should be taken to avoid modifying the internal I/O state of the
    /// underlying value as it may corrupt this cursor's position.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::Cursor;
    ///
    /// let mut buf = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buf);
    ///
    /// let reference = buf.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.inner
    }

    /// Returns the current position of this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    /// use std::io::prelude::*;
    /// use std::io::SeekFrom;
    ///
    /// let mut buf = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buf.position(), 0);
    ///
    /// buf.seek(SeekFrom::Current(2)).unwrap();
    /// assert_eq!(buf.position(), 2);
    ///
    /// buf.seek(SeekFrom::Current(-1)).unwrap();
    /// assert_eq!(buf.position(), 1);
    /// ```
    pub const fn position(&self) -> u64 {
        self.pos
    }

    /// Sets the position of this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Cursor;
    ///
    /// let mut buf = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buf.position(), 0);
    ///
    /// buf.set_position(2);
    /// assert_eq!(buf.position(), 2);
    ///
    /// buf.set_position(4);
    /// assert_eq!(buf.position(), 4);
    /// ```
    pub fn set_position(&mut self, pos: u64) {
        self.pos = pos;
    }
}

impl<T> Cursor<T>
where
    T: AsRef<[u8]>,
{
    /// Returns the remaining slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::Cursor;
    ///
    /// let mut buf = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buf.remaining_slice(), &[1, 2, 3, 4, 5]);
    ///
    /// buf.set_position(2);
    /// assert_eq!(buf.remaining_slice(), &[3, 4, 5]);
    ///
    /// buf.set_position(4);
    /// assert_eq!(buf.remaining_slice(), &[5]);
    ///
    /// buf.set_position(6);
    /// assert_eq!(buf.remaining_slice(), &[]);
    /// ```
    pub fn remaining_slice(&self) -> &[u8] {
        let len = self.pos.min(self.inner.as_ref().len() as u64);
        &self.inner.as_ref()[(len as usize)..]
    }

    /// Returns `true` if the remaining slice is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::Cursor;
    ///
    /// let mut buf = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// buf.set_position(2);
    /// assert!(!buf.is_empty());
    ///
    /// buf.set_position(5);
    /// assert!(buf.is_empty());
    ///
    /// buf.set_position(10);
    /// assert!(buf.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.pos >= self.inner.as_ref().len() as u64
    }
}

impl<T> Read for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let n = Read::read(&mut self.remaining_slice(), buf)?;
        self.pos += n as u64;
        Ok(n)
    }

    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        let n = buf.len();
        Read::read_exact(&mut self.remaining_slice(), buf)?;
        self.pos += n as u64;
        Ok(())
    }
}

// Non-resizing write implementation
#[inline]
fn slice_write(pos_mut: &mut u64, slice: &mut [u8], buf: &[u8]) -> Result<usize> {
    let pos = cmp::min(*pos_mut, slice.len() as u64);
    let amt = (&mut slice[(pos as usize)..]).write(buf)?;
    *pos_mut += amt as u64;
    Ok(amt)
}

impl Write for Cursor<&mut [u8]> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        slice_write(&mut self.pos, self.inner, buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

impl<A> Seek for Cursor<A>
where
    A: AsRef<[u8]>,
{
    fn seek(&mut self, style: SeekFrom) -> Result<u64> {
        let (base_pos, offset) = match style {
            SeekFrom::Start(n) => {
                self.pos = n;
                return Ok(n);
            }
            SeekFrom::End(n) => (self.inner.as_ref().len() as u64, n),
            SeekFrom::Current(n) => (self.pos, n),
        };

        // TODO: The standard library does this whole op with a call to
        // `checked_add_signed`, which is unstable behind `mixed_integer_ops`
        // (https://github.com/rust-lang/rust/issues/87840). Once (if) that
        // stabilizes, follow suit here.
        let end_pos = {
            let (p, overflowed) = base_pos.overflowing_add(offset as u64);

            // If offset < 0 and the unsigned addition didn't overflow, then
            // the signed addition would have a negative sum.
            if overflowed ^ (offset < 0) {
                None
            } else {
                Some(p)
            }
        };

        match end_pos {
            Some(n) => {
                self.pos = n;
                Ok(self.pos)
            }
            None => Err(Error {
                kind: ErrorKind::InvalidInput,
            }),
        }
    }

    fn stream_len(&mut self) -> Result<u64> {
        Ok(self.inner.as_ref().len() as u64)
    }

    fn stream_position(&mut self) -> Result<u64> {
        Ok(self.pos)
    }
}

// `alloc`-only implementations ==================================================================

#[cfg(all(feature = "alloc", not(feature = "std")))]
impl<R: Read> Read for Box<R> {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        (**self).read(dst)
    }

    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        (**self).read_exact(buf)
    }
}

#[cfg(all(feature = "alloc", not(feature = "std")))]
impl Write for Vec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<()> {
        Ok(())
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        self.extend_from_slice(buf);
        Ok(())
    }
}

// Resizing write implementation
#[cfg(feature = "alloc")]
fn vec_write(pos_mut: &mut u64, vec: &mut Vec<u8>, buf: &[u8]) -> Result<usize> {
    let pos: usize = (*pos_mut).try_into().map_err(|_| Error {
        kind: ErrorKind::InvalidInput,
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

#[cfg(feature = "alloc")]
impl Write for Cursor<&mut Vec<u8>> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        vec_write(&mut self.pos, self.inner, buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl Write for Cursor<Vec<u8>> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        vec_write(&mut self.pos, &mut self.inner, buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl Write for Cursor<Box<[u8]>> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        slice_write(&mut self.pos, &mut self.inner, buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}

// `std` implementations =========================================================================

#[cfg(feature = "std")]
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error {
            kind: e.kind().into(),
        }
    }
}

#[cfg(feature = "std")]
impl From<std::io::ErrorKind> for ErrorKind {
    fn from(k: std::io::ErrorKind) -> Self {
        match k {
            std::io::ErrorKind::Interrupted => ErrorKind::Interrupted,
            std::io::ErrorKind::InvalidInput => ErrorKind::InvalidInput,
            std::io::ErrorKind::UnexpectedEof => ErrorKind::UnexpectedEof,
            std::io::ErrorKind::WriteZero => ErrorKind::WriteZero,
            _ => ErrorKind::Other,
        }
    }
}

#[cfg(feature = "std")]
impl<R: std::io::Read> Read for R {
    #[inline]
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        let read = <Self as std::io::Read>::read(self, dst)?;
        Ok(read)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        <Self as std::io::Read>::read_exact(self, buf)?;
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<W: std::io::Write> Write for W {
    fn write(&mut self, src: &[u8]) -> Result<usize> {
        let written = <Self as std::io::Write>::write(self, src)?;
        Ok(written)
    }

    fn flush(&mut self) -> Result<()> {
        <Self as std::io::Write>::flush(self)?;
        Ok(())
    }

    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        <Self as std::io::Write>::write_all(self, buf)?;
        Ok(())
    }
}
