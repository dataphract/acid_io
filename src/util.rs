#![cfg(not(feature = "std"))]

use core::fmt;

use crate::{BufRead, ErrorKind, IoSlice, IoSliceMut, Read, Result, Seek, SeekFrom, Write};

/// A reader which is always at EOF.
///
/// This struct is generally created by calling [`empty()`]. Please see
/// the documentation of [`empty()`] for more details.
#[non_exhaustive]
#[derive(Copy, Clone, Default)]
pub struct Empty;

/// Constructs a new handle to an empty reader.
///
/// All reads from the returned reader will return <code>[Ok]\(0)</code>.
///
/// # Examples
///
/// A slightly sad example of not reading anything into a buffer:
///
/// ```
/// use acid_io::Read;
///
/// let mut buffer = String::new();
/// acid_io::empty().read_to_string(&mut buffer).unwrap();
/// assert!(buffer.is_empty());
/// ```
#[must_use]
pub const fn empty() -> Empty {
    Empty
}

impl Read for Empty {
    #[inline]
    fn read(&mut self, _buf: &mut [u8]) -> Result<usize> {
        Ok(0)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl BufRead for Empty {
    #[inline]
    fn fill_buf(&mut self) -> Result<&[u8]> {
        Ok(&[])
    }
    #[inline]
    fn consume(&mut self, _n: usize) {}
}

impl Seek for Empty {
    fn seek(&mut self, _pos: SeekFrom) -> Result<u64> {
        Ok(0)
    }

    fn stream_len(&mut self) -> Result<u64> {
        Ok(0)
    }

    fn stream_position(&mut self) -> Result<u64> {
        Ok(0)
    }
}

impl fmt::Debug for Empty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Empty").finish_non_exhaustive()
    }
}

/// A reader which yields one byte over and over and over and over and over and...
///
/// This struct is generally created by calling [`repeat()`]. Please
/// see the documentation of [`repeat()`] for more details.
pub struct Repeat {
    byte: u8,
}

/// Creates an instance of a reader that infinitely repeats one byte.
///
/// All reads from this reader will succeed by filling the specified buffer with
/// the given byte.
///
/// # Examples
///
/// ```
/// use acid_io::Read;
///
/// let mut buffer = [0; 3];
/// acid_io::repeat(0b101).read_exact(&mut buffer).unwrap();
/// assert_eq!(buffer, [0b101, 0b101, 0b101]);
/// ```
#[must_use]
pub const fn repeat(byte: u8) -> Repeat {
    Repeat { byte }
}

impl Read for Repeat {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        for slot in &mut *buf {
            *slot = self.byte;
        }
        Ok(buf.len())
    }

    #[inline]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> Result<usize> {
        let mut nwritten = 0;
        for buf in bufs {
            nwritten += self.read(buf)?;
        }
        Ok(nwritten)
    }

    #[inline]
    fn is_read_vectored(&self) -> bool {
        true
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

impl fmt::Debug for Repeat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Repeat").finish_non_exhaustive()
    }
}

/// A writer which will move data into the void.
///
/// This struct is generally created by calling [`sink`]. Please
/// see the documentation of [`sink()`] for more details.
#[non_exhaustive]
#[derive(Copy, Clone, Default)]
pub struct Sink;

/// Creates an instance of a writer which will successfully consume all data.
///
/// All calls to [`write`] on the returned instance will return `Ok(buf.len())`
/// and the contents of the buffer will not be inspected.
///
/// [`write`]: Write::write
///
/// # Examples
///
/// ```rust
/// use acid_io::Write;
///
/// let buffer = vec![1, 2, 3, 5, 8];
/// let num_bytes = acid_io::sink().write(&buffer).unwrap();
/// assert_eq!(num_bytes, 5);
/// ```
#[must_use]
pub const fn sink() -> Sink {
    Sink
}

impl Write for Sink {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum();
        Ok(total_len)
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

impl Write for &Sink {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        Ok(buf.len())
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> {
        let total_len = bufs.iter().map(|b| b.len()).sum();
        Ok(total_len)
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

impl fmt::Debug for Sink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sink").finish_non_exhaustive()
    }
}

/// Copies the entire contents of a reader into a writer.
///
/// This function will continuously read data from `reader` and then
/// write it into `writer` in a streaming fashion until `reader`
/// returns EOF.
///
/// On success, the total number of bytes that were copied from
/// `reader` to `writer` is returned.
///
/// If you’re wanting to copy the contents of one file to another and you’re
/// working with filesystem paths, see the [`fs::copy`] function.
///
/// [`fs::copy`]: crate::fs::copy
///
/// # Errors
///
/// This function will return an error immediately if any call to [`read`] or
/// [`write`] returns an error. All instances of [`ErrorKind::Interrupted`] are
/// handled by this function and the underlying operation is retried.
///
/// [`read`]: Read::read
/// [`write`]: Write::write
///
/// # Examples
///
/// ```
/// fn main() -> acid_io::Result<()> {
///     let mut reader: &[u8] = b"hello";
///     let mut writer: Vec<u8> = vec![];
///
///     acid_io::copy(&mut reader, &mut writer)?;
///
///     assert_eq!(&b"hello"[..], &writer[..]);
///     Ok(())
/// }
/// ```
pub fn copy<R: ?Sized, W: ?Sized>(reader: &mut R, writer: &mut W) -> Result<u64>
where
    R: Read,
    W: Write,
{
    // TODO(dataphract): std::io provides a specialized copy impl for BufWriter,
    // but we don't have access to specialization. Since copy_to is not a method,
    // the autoref/autoderef specialization tricks don't work in this context.
    // Adding copy_to to Write causes it to become non-object-safe, which makes
    // our API incompatible with std.
    //
    // As a result, until specialization becomes available, or another
    // workaround is found, we don't use the specialized impl for BufWriter.
    //
    // BufferedCopySpec::copy_to(reader, writer.as_self())
    stack_buffer_copy(reader, writer)
}

pub(crate) fn stack_buffer_copy<R: Read + ?Sized, W: Write + ?Sized>(
    reader: &mut R,
    writer: &mut W,
) -> Result<u64> {
    // TODO(dataphract): std::io uses a MaybeUninit<u8> buffer here, but we
    // don't have access to Initializer/ReadBuf, so we just zero the array. This
    // will be a perf hit.
    let mut buf = [0u8; crate::DEFAULT_BUF_SIZE];

    let mut written = 0;
    loop {
        let len = match reader.read(&mut buf) {
            Ok(0) => return Ok(written),
            Ok(len) => len,
            Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        };
        writer.write_all(&buf[..len])?;
        written += len as u64;
    }
}
