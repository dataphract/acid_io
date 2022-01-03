use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    slice,
};

#[cfg(unix)]
use libc::{c_void, iovec};

#[cfg(unix)]
#[repr(transparent)]
struct RawIoSliceMut<'a>(iovec, PhantomData<&'a mut [u8]>);

#[cfg(unix)]
impl<'a> RawIoSliceMut<'a> {
    fn new(buf: &'a mut [u8]) -> RawIoSliceMut<'a> {
        RawIoSliceMut(
            iovec {
                iov_base: buf.as_mut_ptr() as *mut c_void,
                iov_len: buf.len(),
            },
            PhantomData,
        )
    }

    fn as_slice(&self) -> &'a [u8] {
        // SAFETY: this type was initialized using a &mut [u8], so all
        // invariants of reconstructing that slice are upheld.
        unsafe { slice::from_raw_parts(self.0.iov_base as *const u8, self.0.iov_len) }
    }

    fn as_mut_slice(&mut self) -> &'a mut [u8] {
        // SAFETY: this type was initialized using a &mut [u8], so all
        // invariants of reconstructing that slice are upheld.
        unsafe { slice::from_raw_parts_mut(self.0.iov_base as *mut u8, self.0.iov_len) }
    }
}

#[cfg(unix)]
#[derive(Copy, Clone)]
#[repr(transparent)]
struct RawIoSlice<'a>(iovec, PhantomData<&'a [u8]>);

#[cfg(unix)]
impl<'a> RawIoSlice<'a> {
    fn new(buf: &'a [u8]) -> RawIoSlice<'a> {
        RawIoSlice(
            iovec {
                iov_base: buf.as_ptr() as *mut u8 as *mut c_void,
                iov_len: buf.len(),
            },
            PhantomData,
        )
    }

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
}

impl<'a> Deref for IoSlice<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.0.as_slice()
    }
}
