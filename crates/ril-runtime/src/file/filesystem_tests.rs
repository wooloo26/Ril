use super::*;
use ril_runtime_api::abi::OutcomeTag;
#[cfg(target_os = "linux")]
use std::{
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

fn prepare_request(runtime: &mut Runtime, path: &Path, name: &str, data: Option<&[u8]>) -> Request {
    let path = runtime
        .allocate(Object::Path(NativeString::from_os(path.as_os_str())))
        .unwrap();
    let mut args = vec![path];
    if let Some(data) = data {
        args.push(
            runtime
                .allocate(Object::Bytes(data.to_vec().into()))
                .unwrap(),
        );
    }
    if name == "File::open_path" {
        args.push(runtime.variant("File::OpenMode::Read", vec![]).unwrap());
    }
    prepare(runtime, name, &args).unwrap()
}

#[test]
fn filesystem_cancellation_precedes_io_and_respects_cleanup_mask() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("data");
    let mut runtime = Runtime::default();
    runtime.cancellation.request();
    let cancelled = prepare_request(&mut runtime, &path, "File::write_bytes", Some(b"cancelled"));
    assert!(matches!(cancelled.perform(), Err(error) if error.tag == OutcomeTag::Cancelled));
    assert!(!path.exists());
    runtime.cancellation_mask = 1;
    let protected = prepare_request(&mut runtime, &path, "File::write_bytes", Some(b"protected"));
    assert!(matches!(protected.perform().unwrap(), Reply::Unit(Ok(()))));
    assert_eq!(fs::read(&path).unwrap(), b"protected");
    let empty = prepare_request(&mut runtime, &path, "File::write_bytes", Some(b""));
    assert!(matches!(empty.perform().unwrap(), Reply::Unit(Ok(()))));
    assert!(fs::read(path).unwrap().is_empty());
}

#[cfg(target_os = "linux")]
fn fifo(path: &Path) {
    rustix::fs::mknodat(
        rustix::fs::CWD,
        path,
        rustix::fs::FileType::Fifo,
        rustix::fs::Mode::from_raw_mode(0o600),
        0,
    )
    .unwrap();
}

#[cfg(target_os = "linux")]
fn fifo_cases() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("fifo");
    fifo(&path);
    // An open without its peer must stay pending, not report an empty stream.
    for name in ["File::open_path", "File::read_bytes", "File::write_bytes"] {
        let mut runtime = Runtime::default();
        let cancellation = runtime.cancellation.clone();
        let request = prepare_request(
            &mut runtime,
            &path,
            name,
            (name == "File::write_bytes").then_some(b"x".as_slice()),
        );
        let (tx, rx) = mpsc::channel();
        let worker = thread::spawn(move || {
            tx.send(request.perform()).unwrap();
        });
        assert!(
            matches!(
                rx.recv_timeout(Duration::from_millis(50)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ),
            "{name} did not wait for a FIFO peer"
        );
        cancellation.request();
        assert!(
            matches!(rx.recv_timeout(Duration::from_secs(2)).unwrap(), Err(error) if error.tag == OutcomeTag::Cancelled),
            "{name}"
        );
        worker.join().unwrap();
    }
    // Canceling one request must leave the shared wake disposition installed
    // for another independently owned request that is still blocked.
    {
        let mut pending = Vec::new();
        for _ in 0..2 {
            let mut runtime = Runtime::default();
            let cancellation = runtime.cancellation.clone();
            let request = prepare_request(&mut runtime, &path, "File::read_bytes", None);
            let (tx, rx) = mpsc::channel();
            let worker = thread::spawn(move || {
                tx.send(request.perform()).unwrap();
            });
            pending.push((cancellation, rx, worker));
        }
        for (_, rx, _) in &pending {
            assert!(matches!(
                rx.recv_timeout(Duration::from_millis(50)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ));
        }
        for (cancellation, rx, worker) in pending {
            assert!(!cancellation.requested());
            cancellation.request();
            assert!(
                matches!(rx.recv_timeout(Duration::from_secs(2)).unwrap(), Err(error) if error.tag == OutcomeTag::Cancelled)
            );
            worker.join().unwrap();
        }
    }
    // Read a real prefix, then cancel while the writer remains alive. Returning
    // that prefix as success or EOF would violate the whole-file contract.
    {
        let mut runtime = Runtime::default();
        let cancellation = runtime.cancellation.clone();
        let request = prepare_request(&mut runtime, &path, "File::read_bytes", None);
        let (tx, rx) = mpsc::channel();
        let worker = thread::spawn(move || {
            tx.send(request.perform()).unwrap();
        });
        let mut writer = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        writer.write_all(b"prefix").unwrap();
        assert!(matches!(
            rx.recv_timeout(Duration::from_millis(50)),
            Err(mpsc::RecvTimeoutError::Timeout)
        ));
        cancellation.request();
        assert!(
            matches!(rx.recv_timeout(Duration::from_secs(2)).unwrap(), Err(error) if error.tag == OutcomeTag::Cancelled)
        );
        worker.join().unwrap();
        drop(writer);
    }
    // A blocked write can already have committed a prefix. Keep the reader
    // open without draining it until cancellation has actually joined IO.
    {
        let mut runtime = Runtime::default();
        let cancellation = runtime.cancellation.clone();
        let data = vec![b'x'; 1024 * 1024];
        let request = prepare_request(&mut runtime, &path, "File::write_bytes", Some(&data));
        let (tx, rx) = mpsc::channel();
        let worker = thread::spawn(move || {
            tx.send(request.perform()).unwrap();
        });
        let mut reader = File::open(&path).unwrap();
        assert!(matches!(
            rx.recv_timeout(Duration::from_millis(50)),
            Err(mpsc::RecvTimeoutError::Timeout)
        ));
        cancellation.request();
        assert!(
            matches!(rx.recv_timeout(Duration::from_secs(2)).unwrap(), Err(error) if error.tag == OutcomeTag::Cancelled)
        );
        worker.join().unwrap();
        let mut prefix = Vec::new();
        reader.read_to_end(&mut prefix).unwrap();
        assert!(!prefix.is_empty() && prefix.len() < data.len());
        assert!(prefix.iter().all(|&byte| byte == b'x'));
    }
    // Successful open does not prefetch data, and successful whole-file reading
    // waits for the actual peer to close before returning its complete bytes.
    {
        let mut runtime = Runtime::default();
        let request = prepare_request(&mut runtime, &path, "File::open_path", None);
        let worker = thread::spawn(move || request.perform());
        let mut writer = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        let Reply::Open(Ok(mut opened)) = worker.join().unwrap().unwrap() else {
            panic!("FIFO did not open")
        };
        writer.write_all(b"unconsumed").unwrap();
        drop(writer);
        let mut data = Vec::new();
        opened
            .file
            .as_mut()
            .unwrap()
            .read_to_end(&mut data)
            .unwrap();
        assert_eq!(data, b"unconsumed");
        drop(opened);
        let request = prepare_request(&mut runtime, &path, "File::read_bytes", None);
        let worker = thread::spawn(move || request.perform());
        let mut writer = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        writer.write_all(b"complete").unwrap();
        drop(writer);
        let Reply::Read(ReadKind::Bytes, Ok(data)) = worker.join().unwrap().unwrap() else {
            panic!("whole FIFO read failed")
        };
        assert_eq!(data, b"complete");
    }
}

#[cfg(target_os = "linux")]
#[test]
fn fifo_open_and_whole_file_waits_cancel_without_fabricating_eof_or_undoing_writes() {
    const FIXTURE: &str = "RIL_FILESYSTEM_FIFO_FIXTURE";
    if std::env::var_os(FIXTURE).is_some() {
        fifo_cases();
        return;
    }
    // A regression that fails to wake a syscall must fail this test rather than
    // leave a detached IO thread hanging in the shared test runner.
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "file::filesystem::tests::fifo_open_and_whole_file_waits_cancel_without_fabricating_eof_or_undoing_writes", "--nocapture"])
        .env(FIXTURE, "1").stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped()).spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(15);
    let timed_out = loop {
        if child.try_wait().unwrap().is_some() {
            break false;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            break true;
        }
        thread::sleep(Duration::from_millis(5));
    };
    let output = child.wait_with_output().unwrap();
    assert!(
        !timed_out && output.status.success(),
        "timeout={timed_out}\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
