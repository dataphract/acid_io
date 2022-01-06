#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! A pared-down version of [`std::io`] usable in `no_std` contexts.
//!
//! [`std::io`]: https://doc.rust-lang.org/std/io/index.html

#[cfg(all(not(feature = "std"), feature = "byteorder"))]
pub mod byteorder;
#[cfg(all(not(feature = "std"), feature = "alloc"))]
mod io_alloc;
#[cfg(not(feature = "std"))]
mod io_core;
#[cfg(not(feature = "std"))]
mod io_slice;
#[cfg(not(feature = "std"))]
pub mod prelude;

#[cfg(all(not(feature = "std"), test))]
mod tests;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
pub use io_alloc::{BufReader, BufWriter, IntoInnerError, LineWriter, Lines, Split};
#[cfg(not(feature = "std"))]
pub use io_core::{BufRead, Cursor, Error, ErrorKind, Read, Result, Seek, SeekFrom, Write};
#[cfg(not(feature = "std"))]
pub use io_slice::{IoSlice, IoSliceMut};

#[cfg(feature = "std")]
pub use std::io::{
    BufRead, BufReader, Bytes, Cursor, Error, ErrorKind, IoSlice, IoSliceMut, Lines, Split,
};
