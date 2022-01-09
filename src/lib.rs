#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! A pared-down version of [`std::io`] usable in `no_std` contexts.
//!
//! [`std::io`]: https://doc.rust-lang.org/std/io/index.html

#[cfg(all(not(feature = "std"), feature = "byteorder"))]
pub mod byteorder;
#[cfg(not(feature = "std"))]
mod error;
#[cfg(all(not(feature = "std"), feature = "alloc"))]
mod io_alloc;
#[cfg(not(feature = "std"))]
mod io_core;
#[cfg(not(feature = "std"))]
mod io_slice;
#[cfg(not(feature = "std"))]
pub mod prelude;
#[cfg(not(feature = "std"))]
pub(crate) mod util;

#[cfg(all(not(feature = "std"), test))]
mod tests;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
pub use error::{Error, ErrorKind, ErrorTrait, Result};
#[cfg(all(not(feature = "std"), feature = "alloc"))]
pub use io_alloc::{BufReader, BufWriter, IntoInnerError, LineWriter, Lines, Split};
#[cfg(not(feature = "std"))]
pub use io_core::{BufRead, Cursor, Read, Seek, SeekFrom, Write};
#[cfg(not(feature = "std"))]
pub use io_slice::{IoSlice, IoSliceMut};
#[cfg(not(feature = "std"))]
pub use util::{copy, empty, repeat, sink, Empty, Repeat, Sink};

#[cfg(all(feature = "std", feature = "byteorder"))]
pub use byteorder;
#[cfg(feature = "std")]
pub use std::io::{
    copy, empty, repeat, sink, BufRead, BufReader, BufWriter, Bytes, Cursor, Empty, Error,
    ErrorKind, IntoInnerError, IoSlice, IoSliceMut, LineWriter, Lines, Read, Repeat, Result, Seek,
    SeekFrom, Sink, Split, Write,
};

// Exact value copied from std::sys_common::io, which is not exposed publicly.
#[cfg(not(feature = "std"))]
pub(crate) const DEFAULT_BUF_SIZE: usize = 8 * 1024;
