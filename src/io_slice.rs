use core::{
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    slice,
};

#[cfg(unix)]
use libc::{c_void, iovec};

// ----
// c_void and iovec for bare metal targets
#[cfg(not(any(unix, windows)))]
#[repr(u8)]
#[derive(Clone, Copy)]
enum c_void {
    #[doc(hidden)]
    __variant1,
    #[doc(hidden)]
    __variant2,
}
#[cfg(not(any(unix, windows)))]
#[derive(Clone, Copy)]
struct iovec {
    pub iov_base: *mut c_void,
    pub iov_len: usize,
}
// ----

#[cfg(not(windows))]
#[repr(transparent)]
struct RawIoSliceMut<'a>(iovec, PhantomData<&'a mut [u8]>);

#[cfg(not(windows))]
impl<'a> RawIoSliceMut<'a> {
    #[inline]
    fn new(buf: &'a mut [u8]) -> RawIoSliceMut<'a> {
        RawIoSliceMut(
            iovec {
                iov_base: buf.as_mut_ptr() as *mut c_void,
                iov_len: buf.len(),
            },
            PhantomData,
        )
    }

    #[inline]
    pub fn advance(&mut self, n: usize) {
        if self.0.iov_len < n {
            panic!("advancing IoSlice beyond its length");
        }

        unsafe {
            self.0.iov_len -= n;
            self.0.iov_base = self.0.iov_base.add(n);
        }
    }

    #[inline]
    fn as_slice(&self) -> &'a [u8] {
        // SAFETY: this type was initialized using a &mut [u8], so all
        // invariants of reconstructing that slice are upheld.
        unsafe { slice::from_raw_parts(self.0.iov_base as *const u8, self.0.iov_len) }
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &'a mut [u8] {
        // SAFETY: this type was initialized using a &mut [u8], so all
        // invariants of reconstructing that slice are upheld.
        unsafe { slice::from_raw_parts_mut(self.0.iov_base as *mut u8, self.0.iov_len) }
    }
}

#[cfg(not(windows))]
#[derive(Copy, Clone)]
#[repr(transparent)]
struct RawIoSlice<'a>(iovec, PhantomData<&'a [u8]>);

#[cfg(not(windows))]
impl<'a> RawIoSlice<'a> {
    #[inline]
    fn new(buf: &'a [u8]) -> RawIoSlice<'a> {
        RawIoSlice(
            iovec {
                iov_base: buf.as_ptr() as *mut u8 as *mut c_void,
                iov_len: buf.len(),
            },
            PhantomData,
        )
    }

    #[inline]
    pub fn advance(&mut self, n: usize) {
        if self.0.iov_len < n {
            panic!("advancing IoSlice beyond its length");
        }

        unsafe {
            self.0.iov_len -= n;
            self.0.iov_base = self.0.iov_base.add(n);
        }
    }

    #[inline]
    fn as_slice(&self) -> &'a [u8] {
        // SAFETY: this type was initialized using a &[u8], so all
        // invariants of reconstructing that slice are upheld.
        unsafe { slice::from_raw_parts(self.0.iov_base as *const u8, self.0.iov_len) }
    }
}

/// A buffer type used with `Read::read_vectored`.
///
/// It is semantically a wrapper around an `&mut [u8]`, but is guaranteed to be
/// ABI compatible with the `iovec` type on Unix platforms and `WSABUF` on
/// Windows.
#[repr(transparent)]
pub struct IoSliceMut<'a>(RawIoSliceMut<'a>);

unsafe impl<'a> Send for IoSliceMut<'a> {}
unsafe impl<'a> Sync for IoSliceMut<'a> {}
impl<'a> IoSliceMut<'a> {
    /// Creates a new `IoSliceMut` wrapping a byte slice.
    ///
    /// # Panics
    ///
    /// Panics on Windows if the slice is larger than 4GB.
    #[inline]
    pub fn new(buf: &'a mut [u8]) -> IoSliceMut<'a> {
        IoSliceMut(RawIoSliceMut::new(buf))
    }

    /// Advance the internal cursor of the slice.
    ///
    /// Also see [`IoSliceMut::advance_slices`] to advance the cursors of
    /// multiple buffers.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ops::Deref;
    /// use acid_io::IoSliceMut;
    ///
    /// let mut data = [1; 8];
    /// let mut buf = IoSliceMut::new(&mut data);
    ///
    /// // Mark 3 bytes as read.
    /// buf.advance(3);
    /// assert_eq!(buf.deref(), [1; 5].as_ref());
    /// ```
    #[doc(hidden)]
    #[inline]
    pub fn advance(&mut self, n: usize) {
        self.0.advance(n)
    }

    /// Advance the internal cursor of the slices.
    ///
    /// # Notes
    ///
    /// Elements in the slice may be modified if the cursor is not advanced to
    /// the end of the slice. For example if we have a slice of buffers with 2
    /// `IoSliceMut`s, both of length 8, and we advance the cursor by 10 bytes
    /// the first `IoSliceMut` will be untouched however the second will be
    /// modified to remove the first 2 bytes (10 - 8).
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ops::Deref;
    /// use acid_io::IoSliceMut;
    ///
    /// let mut buf1 = [1; 8];
    /// let mut buf2 = [2; 16];
    /// let mut buf3 = [3; 8];
    /// let mut bufs = &mut [
    ///     IoSliceMut::new(&mut buf1),
    ///     IoSliceMut::new(&mut buf2),
    ///     IoSliceMut::new(&mut buf3),
    /// ][..];
    ///
    /// // Mark 10 bytes as read.
    /// IoSliceMut::advance_slices(&mut bufs, 10);
    /// assert_eq!(bufs[0].deref(), [2; 14].as_ref());
    /// assert_eq!(bufs[1].deref(), [3; 8].as_ref());
    /// ```
    #[doc(hidden)]
    #[inline]
    pub fn advance_slices(bufs: &mut &mut [IoSliceMut<'a>], n: usize) {
        // Number of buffers to remove.
        let mut remove = 0;
        // Total length of all the to be removed buffers.
        let mut accumulated_len = 0;
        for buf in bufs.iter() {
            if accumulated_len + buf.len() > n {
                break;
            } else {
                accumulated_len += buf.len();
                remove += 1;
            }
        }

        *bufs = &mut mem::take(bufs)[remove..];
        if !bufs.is_empty() {
            bufs[0].advance(n - accumulated_len)
        }
    }
}

impl<'a> Deref for IoSliceMut<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl<'a> DerefMut for IoSliceMut<'a> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

/// A buffer type used with `Write::write_vectored`.
///
/// It is semantically a wrapper around a `&[u8]`, but is guaranteed to be
/// ABI compatible with the `iovec` type on Unix platforms and `WSABUF` on
/// Windows.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct IoSlice<'a>(RawIoSlice<'a>);

unsafe impl<'a> Send for IoSlice<'a> {}
unsafe impl<'a> Sync for IoSlice<'a> {}

impl<'a> IoSlice<'a> {
    /// Creates a new `IoSlice` wrapping a byte slice.
    ///
    /// # Panics
    ///
    /// Panics on Windows if the slice is larger than 4GB.
    #[inline]
    pub fn new(buf: &'a [u8]) -> IoSlice<'a> {
        IoSlice(RawIoSlice::new(buf))
    }

    /// Advance the internal cursor of the slice.
    ///
    /// Also see [`IoSlice::advance_slices`] to advance the cursors of multiple
    /// buffers.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ops::Deref;
    /// use acid_io::IoSlice;
    ///
    /// let mut data = [1; 8];
    /// let mut buf = IoSlice::new(&mut data);
    ///
    /// // Mark 3 bytes as read.
    /// buf.advance(3);
    /// assert_eq!(buf.deref(), [1; 5].as_ref());
    /// ```
    #[doc(hidden)]
    #[inline]
    pub fn advance(&mut self, n: usize) {
        self.0.advance(n)
    }

    /// Advance the internal cursor of the slices.
    ///
    /// # Notes
    ///
    /// Elements in the slice may be modified if the cursor is not advanced to
    /// the end of the slice. For example if we have a slice of buffers with 2
    /// `IoSlice`s, both of length 8, and we advance the cursor by 10 bytes the
    /// first `IoSlice` will be untouched however the second will be modified to
    /// remove the first 2 bytes (10 - 8).
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ops::Deref;
    /// use acid_io::IoSlice;
    ///
    /// let buf1 = [1; 8];
    /// let buf2 = [2; 16];
    /// let buf3 = [3; 8];
    /// let mut bufs = &mut [
    ///     IoSlice::new(&buf1),
    ///     IoSlice::new(&buf2),
    ///     IoSlice::new(&buf3),
    /// ][..];
    ///
    /// // Mark 10 bytes as written.
    /// IoSlice::advance_slices(&mut bufs, 10);
    /// assert_eq!(bufs[0].deref(), [2; 14].as_ref());
    /// assert_eq!(bufs[1].deref(), [3; 8].as_ref());
    #[doc(hidden)]
    #[inline]
    pub fn advance_slices(bufs: &mut &mut [IoSlice<'a>], n: usize) {
        // Number of buffers to remove.
        let mut remove = 0;
        // Total length of all the to be removed buffers.
        let mut accumulated_len = 0;
        for buf in bufs.iter() {
            if accumulated_len + buf.len() > n {
                break;
            } else {
                accumulated_len += buf.len();
                remove += 1;
            }
        }

        *bufs = &mut mem::take(bufs)[remove..];
        if !bufs.is_empty() {
            bufs[0].advance(n - accumulated_len)
        }
    }
}

impl<'a> Deref for IoSlice<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.0.as_slice()
    }
}
