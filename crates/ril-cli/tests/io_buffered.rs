use std::{fs, process::Command};

const MEMORY: &str = r#"
use ril/io
use ril/bytes
type Reader = { data: bytes, mut offset: int, mut calls: int }
type Sink = { mut data: []u8, mut fail: bool }
fn read_memory(mut reader: Reader, maximum: int) -> Result<Io::ReadChunk, Io::IoError> &mut {
    reader.calls += 1
    if maximum == 0 { return Ok(.{ data: b"", end: false }) }
    let remaining = len(reader.data) - reader.offset
    let count = if maximum < remaining { maximum } else { remaining }
    let data = Bytes::slice(reader.data, reader.offset, reader.offset + count) ?? panic("bounds")
    reader.offset += count
    Ok(.{ data: data, end: reader.offset == len(reader.data) })
}
fn write_memory(mut sink: Sink, data: bytes) -> Io::WriteProgress &mut {
    if len(data) == 0 { return .{ written: 0, error: None } }
    let count = if len(data) > 2 { 2 } else { len(data) }
    for 0..count as index {
        sink.data !> Array::push(Bytes::at(data, index) ?? panic("bounds"))
    }
    .{ written: count, error: if sink.fail {
        Some(.{ kind: Io::ErrorKind::BrokenPipe, message: "retry", native_code: None })
    } else { None } }
}
fn bypass(mut reader: Reader, maximum: int) -> Result<Io::ReadChunk, Io::IoError> &mut {
    read_memory(mut reader, maximum)
}
"#;

fn executes(source: &str, runtime: &str) {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("buffered.ril");
    fs::write(&input, format!("{MEMORY}\n{source}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], runtime, "{report}");
}

#[test]
fn read_ahead_preserves_cached_bytes_eof_and_zero_request_validation() {
    executes(
        r#"
pub fn test_native() {
    let mut reader = Reader.{ data: b"abc", offset: 0, calls: 0 }
    let mut buffer = Io::read_buffer(2)
    let first = Io::read_buffered(mut buffer, mut reader, .{ read: read_memory }, 1) ?? \_error -> panic("read")
    assert(first.data == b"a" && !first.end && reader.offset == 2 && reader.calls == 1)
    let zero = Io::read_buffered(mut buffer, mut reader, .{ read: read_memory }, 0) ?? \_error -> panic("read")
    assert(zero.data == b"" && !zero.end && reader.offset == 2 && reader.calls == 2)
    let cached = Io::read_buffered(mut buffer, mut reader, .{ read: read_memory }, 1) ?? \_error -> panic("read")
    assert(cached.data == b"b" && !cached.end && reader.calls == 2)
    let ending_chunk = Io::read_buffered(mut buffer, mut reader, .{ read: read_memory }, 10) ?? \_error -> panic("read")
    assert(ending_chunk.data == b"c" && ending_chunk.end && reader.calls == 3)
    let mut other = Reader.{ data: b"z", offset: 0, calls: 0 }
    let reused = Io::read_buffered(mut buffer, mut other, .{ read: read_memory }, 1) ?? \_error -> panic("read")
    assert(reused.data == b"z" && reused.end)
}
"#,
        "returned-unit",
    );
}

#[test]
fn buffered_writes_report_accepted_bytes_and_preserve_short_error_suffixes() {
    executes(
        r#"
pub fn test_native() {
    let mut sink = Sink.{ data: [], fail: true }
    let mut buffer = Io::write_buffer(4)
    let progress = Io::write_buffered(mut buffer, mut sink, .{ write: write_memory }, b"abcdef")
    assert(progress.written == 4 && progress.error is Some(_))
    assert(Bytes::from_array(sink.data) == b"ab")
    sink.fail = false
    let retry = Io::write_buffered(mut buffer, mut sink, .{ write: write_memory }, b"ef")
    assert(retry.written == 2 && retry.error == None)
    assert(Io::flush(mut buffer, mut sink, .{ write: write_memory }) is Ok())
    assert(Bytes::from_array(sink.data) == b"abcdef")
    assert(Io::flush(mut buffer, mut sink, .{ write: write_memory }) is Ok())
    let empty = Io::write_buffered(mut buffer, mut sink, .{ write: write_memory }, b"")
    assert(empty.written == 0 && empty.error == None)
}
"#,
        "returned-unit",
    );
}

#[test]
fn direct_named_and_aliased_reads_cannot_skip_a_pending_read_buffer() {
    for direct in [
        "read_memory(mut reader, 1)",
        "read(mut reader, 1)",
        "bypass(mut reader, 1)",
    ] {
        executes(
            &format!(
                r#"
pub fn test_native() {{
    let mut reader = Reader.{{ data: b"abc", offset: 0, calls: 0 }}
    let mut buffer = Io::read_buffer(2)
    let read = read_memory
    let first = Io::read_buffered(mut buffer, mut reader, .{{ read: read_memory }}, 1) ?? \_error -> panic("read")
    assert(first.data == b"a")
    let result = {direct}
    assert(result is Ok(_))
}}
"#
            ),
            "language-panic",
        );
    }
}

#[test]
fn buffers_reject_switching_pending_streams_before_another_callback() {
    executes(
        r#"
pub fn test_native() {
    let mut reader = Reader.{ data: b"abc", offset: 0, calls: 0 }
    let mut other = Reader.{ data: b"z", offset: 0, calls: 0 }
    let mut buffer = Io::read_buffer(2)
    assert(Io::read_buffered(mut buffer, mut reader, .{ read: read_memory }, 1) is Ok(_))
    let result = Io::read_buffered(mut buffer, mut other, .{ read: read_memory }, 1)
    assert(result is Ok(_))
}
"#,
        "language-panic",
    );
    executes(
        r#"
pub fn test_native() {
    let mut first = Sink.{ data: [], fail: false }
    let mut second = Sink.{ data: [], fail: false }
    let mut buffer = Io::write_buffer(8)
    let progress = Io::write_buffered(mut buffer, mut first, .{ write: write_memory }, b"abc")
    assert(progress.error == None)
    assert(Io::flush(mut buffer, mut second, .{ write: write_memory }) is Ok())
}
"#,
        "language-panic",
    );
}

#[test]
fn buffered_callback_effects_and_budget_abort_use_native_continuations() {
    executes(
        r#"
eff Tick { now() -> () }
fn reading(mut reader: Reader, maximum: int) -> Result<Io::ReadChunk, Io::IoError> @Tick &mut {
    Tick::now()
    for 0..1000 as n { let unused = [n, n + 1] }
    read_memory(mut reader, maximum)
}

fn spin_read(mut reader: Reader, maximum: int) -> Result<Io::ReadChunk, Io::IoError> &mut { reader.calls += 1; loop {} }
fn attempt() -> bool {
    with Div::exhausted() -> true
    with Div::budget(20)
    let mut reader = Reader.{ data: b"q", offset: 0, calls: 0 }
    let mut buffer = Io::read_buffer(2)
    let result = Io::read_buffered(mut buffer, mut reader, .{ read: spin_read }, 1)
    assert(result is Ok(_))
    false
}
pub fn test_native() {
    with Tick::now() -> resume ()
    let operations = .{ read: reading }
    let mut reader = Reader.{ data: b"abc", offset: 0, calls: 0 }
    let mut buffer = Io::read_buffer(2)
    let first = Io::read_buffered(mut buffer, mut reader, operations, 1) ?? \_error -> panic("read")
    assert(first.data == b"a")
    let cached = Io::read_buffered(mut buffer, mut reader, operations, 1) ?? \_error -> panic("read")
    assert(cached.data == b"b")
    assert(attempt())
    let ending_chunk = Io::read_buffered(mut buffer, mut reader, .{ read: read_memory }, 1) ?? \_error -> panic("read")
    assert(ending_chunk.data == b"c")
}
"#,
        "returned-unit",
    );
}

#[test]
fn a_wrapped_file_reader_reserves_its_actual_file_endpoint() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("input");
    fs::write(&path, b"abc").unwrap();
    let path = serde_json::to_string(&path.to_string_lossy()).unwrap();
    executes(
        &format!(
            r#"
use ril/file
use ril/path
fn wrapped(mut file: File::Handle, maximum: int) -> Result<Io::ReadChunk, Io::IoError> @Fiber &mut {{
    File::read_chunk(mut file, maximum)
}}
pub fn test_native() @Fiber {{
    let scoped mut file = File::open_path(Path::from_string({path}), File::OpenMode::Read) ?? \_error -> panic("open")
    let mut buffer = Io::read_buffer(2)
    let first = Io::read_buffered(mut buffer, mut file, .{{ read: wrapped }}, 1) ?? \_error -> panic("read")
    assert(first.data == b"a")
    assert(File::read_chunk(mut file, 1) is Ok(_))
}}
"#
        ),
        "language-panic",
    );
}
