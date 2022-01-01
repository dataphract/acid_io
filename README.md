# acid_io

A pared-down version of Rust's [`std::io`] usable in `no_std` contexts.

Rust's `std::io` provides common interfaces that are used widely in the Rust
ecosystem for reading and writing data.  There is an issue open since 2018(!) to
allow [using std::io::{Read, Write, Cursor} in a nostd
environment](https://github.com/rust-lang/rust/issues/48331).  Unfortunately,
these interfaces cannot be made available without the standard library because
they rely on [`io::Error`], which depends on backtrace functionality only
available in `std`.

In lieu of standard library support, this crate provides drop-in replacements
for the types and traits exposed by `std::io` which are usable without the
standard library. In particular, this crate provides:

- The `Read`, `Write`, and `Seek` traits
- An `acid_io::Error` type analogous to `io::Error`, but without requiring
  backtraces or allocation
- A `Cursor` type which functions the same way as the standard library version

In addition, this crate optionally provides (behind the `byteorder` feature flag)
implementations of `byteorder::ReadBytesExt` and `WriteBytesExt` which extend
`acid_io::Read` and `Write`.

[`std::io`]: https://doc.rust-lang.org/std/io/index.html
[`io::Error`]: https://doc.rust-lang.org/stable/std/io/struct.Error.html

## Acknowledgments

Much of this library is copied verbatim or with slight modifications from other Rust projects:

- [The Rust Standard Library, `std`](https://github.com/rust-lang/rust)
- [BurntSushi's `byteorder`](https://github.com/BurntSushi/byteorder)

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[TinyVG/examples]: https://github.com/TinyVG/examples
[mit-tinyvg]: https://github.com/TinyVG/examples/blob/b8d8c7e88ed221f2ce1100f9e25b5c6e7e6dc78d/LICENSE
