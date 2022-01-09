#![cfg(all(not(feature = "std"), feature = "alloc"))]

// Some of the unit tests in std::io require other parts of the standard library
// to function, particularly std::panic and std::thread. We run those tests as
// integration tests: when acid_io gets compiled without the standard library,
// the integration tests are still compiled with it.

use std::{
    panic,
    sync::atomic::{AtomicUsize, Ordering},
    thread,
};

use acid_io::{
    prelude::*, BufReader, BufWriter, Cursor, Error, ErrorKind, IoSlice, LineWriter, SeekFrom,
};

#[test]
fn test_buffered_reader_stream_position_panic() {
    let inner: &[u8] = &[5, 6, 7, 0, 1, 2, 3, 4];
    let mut reader = BufReader::with_capacity(4, Cursor::new(inner));

    // cause internal buffer to be filled but read only partially
    let mut buffer = [0, 0];
    assert!(reader.read_exact(&mut buffer).is_ok());
    // rewinding the internal reader will cause buffer to loose sync
    let inner = reader.get_mut();
    assert!(inner.seek(SeekFrom::Start(0)).is_ok());
    // overflow when subtracting the remaining buffer size from current position
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| reader.stream_position().ok()));
    assert!(result.is_err());
}

#[test]
#[cfg_attr(target_os = "emscripten", ignore)]
fn panic_in_write_doesnt_flush_in_drop() {
    static WRITES: AtomicUsize = AtomicUsize::new(0);

    struct PanicWriter;

    impl Write for PanicWriter {
        fn write(&mut self, _: &[u8]) -> acid_io::Result<usize> {
            WRITES.fetch_add(1, Ordering::SeqCst);
            panic!();
        }

        fn flush(&mut self) -> acid_io::Result<()> {
            Ok(())
        }
    }

    std::thread::spawn(|| {
        let mut writer = BufWriter::new(PanicWriter);
        let _ = writer.write(b"hello world");
        let _ = writer.flush();
    })
    .join()
    .unwrap_err();

    assert_eq!(WRITES.load(Ordering::SeqCst), 1);
}

#[test]
fn line_vectored_partial_and_errors() {
    use std::collections::VecDeque;

    enum Call {
        Write {
            inputs: Vec<&'static [u8]>,
            output: acid_io::Result<usize>,
        },
        Flush {
            output: acid_io::Result<()>,
        },
    }

    #[derive(Default)]
    struct Writer {
        calls: VecDeque<Call>,
    }

    impl Write for Writer {
        fn write(&mut self, buf: &[u8]) -> acid_io::Result<usize> {
            self.write_vectored(&[IoSlice::new(buf)])
        }

        fn write_vectored(&mut self, buf: &[IoSlice<'_>]) -> acid_io::Result<usize> {
            match self.calls.pop_front().expect("unexpected call to write") {
                Call::Write { inputs, output } => {
                    assert_eq!(inputs, buf.iter().map(|b| &**b).collect::<Vec<_>>());
                    output
                }
                Call::Flush { .. } => panic!("unexpected call to write; expected a flush"),
            }
        }

        fn is_write_vectored(&self) -> bool {
            true
        }

        fn flush(&mut self) -> acid_io::Result<()> {
            match self.calls.pop_front().expect("Unexpected call to flush") {
                Call::Flush { output } => output,
                Call::Write { .. } => panic!("unexpected call to flush; expected a write"),
            }
        }
    }

    impl Drop for Writer {
        fn drop(&mut self) {
            if !thread::panicking() {
                assert_eq!(self.calls.len(), 0);
            }
        }
    }

    // partial writes keep going
    let mut a = LineWriter::new(Writer::default());
    a.write_vectored(&[IoSlice::new(&[]), IoSlice::new(b"abc")])
        .unwrap();

    a.get_mut().calls.push_back(Call::Write {
        inputs: vec![b"abc"],
        output: Ok(1),
    });
    a.get_mut().calls.push_back(Call::Write {
        inputs: vec![b"bc"],
        output: Ok(2),
    });
    a.get_mut().calls.push_back(Call::Write {
        inputs: vec![b"x", b"\n"],
        output: Ok(2),
    });

    a.write_vectored(&[IoSlice::new(b"x"), IoSlice::new(b"\n")])
        .unwrap();

    a.get_mut().calls.push_back(Call::Flush { output: Ok(()) });
    a.flush().unwrap();

    // erroneous writes stop and don't write more
    a.get_mut().calls.push_back(Call::Write {
        inputs: vec![b"x", b"\na"],
        output: Err(err()),
    });
    a.get_mut().calls.push_back(Call::Flush { output: Ok(()) });
    assert!(a
        .write_vectored(&[IoSlice::new(b"x"), IoSlice::new(b"\na")])
        .is_err());
    a.flush().unwrap();

    fn err() -> Error {
        ErrorKind::Other.into()
    }
}
