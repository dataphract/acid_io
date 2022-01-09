# acid_io

A pared-down version of Rust's [`std::io`] usable in `no_std` contexts.

---

Rust's `std::io` provides common interfaces that are used widely in the Rust
ecosystem for reading and writing data. However, as of 2022, these interfaces
are not available in `no_std` builds.

This crate provides drop-in replacements for the types and traits exposed by
`std::io` which can be used with `no_std`.

## Example

```rust
#![no_std]

use acid_io::{
    byteorder::{BE, LE, ReadBytesExt, WriteBytesExt},
    Cursor, Read, Seek, SeekFrom, Write,
};

let mut buf = [0u8; 10];
let mut curs = Cursor::new(&mut buf);

curs.write_u8(1)?;
curs.write_u16::<BE>(2)?;
curs.write_u32::<LE>(3)?;

curs.seek(SeekFrom::Start(0))?;

assert_eq!(curs.read_u8()?, 1);
assert_eq!(curs.read_u16::<BE>()?, 2);
assert_eq!(curs.read_u32::<LE>()?, 3);
```

## Feature flags

- `std`

  Replaces all items with re-exports of their counterparts in `std::io`. This
  effectively makes `acid_io` an alias of `std::io`, but missing any items that
  `acid_io` wouldn't otherwise provide.

- `alloc`

  Exposes `BufReader` and `BufWriter`, as well as those trait methods which
  take or return `Vec` or `String`.

- `byteorder`

  Exposes `acid_io::byteorder`, which contains implementations of
  `ReadBytesExt` and `WriteBytesExt` for `acid_io`'s `Read` and `Write` traits.
  Also re-exports the rest of `byteorder`.

## Acknowledgments

Much of this library is copied verbatim or with slight modifications from other
Rust projects:

- [The Rust Standard Library, `std`](https://github.com/rust-lang/rust)
- [BurntSushi's `byteorder`](https://github.com/BurntSushi/byteorder)

If you find this crate useful, please consider sponsoring members of the
[Library team] on GitHub.

[library team]: https://www.rust-lang.org/governance/teams/library

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[tinyvg/examples]: https://github.com/TinyVG/examples
[mit-tinyvg]: https://github.com/TinyVG/examples/blob/b8d8c7e88ed221f2ce1100f9e25b5c6e7e6dc78d/LICENSE
