use super::*;
use ril_runtime_api::abi::OutcomeTag;

fn open_request(runtime: &mut Runtime, path: &Path, mode: &str) -> Request {
    let path = runtime
        .allocate(Object::Path(NativeString::from_os(path.as_os_str())))
        .unwrap();
    let mode = runtime
        .variant(&format!("File::OpenMode::{mode}"), vec![])
        .unwrap();
    prepare(runtime, "File::open_path", &[path, mode]).unwrap()
}

#[test]
fn cancellation_precedes_open_and_respects_cleanup_mask() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("data");
    let mut runtime = Runtime::default();
    runtime.cancellation.request();
    let cancelled = open_request(&mut runtime, &path, "WriteTruncate");
    assert!(matches!(cancelled.perform(), Err(error) if error.tag == OutcomeTag::Cancelled));
    assert!(!path.exists());
    runtime.cancellation_mask = 1;
    let protected = open_request(&mut runtime, &path, "WriteTruncate");
    let Reply::Open(Ok(state)) = protected.perform().unwrap() else {
        panic!("expected file authority")
    };
    drop(state);
    assert!(fs::read(&path).unwrap().is_empty());
}

#[cfg(target_os = "linux")]
#[test]
fn fifo_open_waits_for_a_peer_and_cancels_without_creating_a_handle() {
    use std::{sync::mpsc, thread, time::Duration};
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("fifo");
    rustix::fs::mknodat(
        rustix::fs::CWD,
        &path,
        rustix::fs::FileType::Fifo,
        rustix::fs::Mode::from_raw_mode(0o600),
        0,
    )
    .unwrap();
    for mode in ["Read", "WriteTruncate", "Append"] {
        let mut runtime = Runtime::default();
        let cancellation = runtime.cancellation.clone();
        let request = open_request(&mut runtime, &path, mode);
        let (tx, rx) = mpsc::channel();
        let worker = thread::spawn(move || tx.send(request.perform()).unwrap());
        assert!(matches!(
            rx.recv_timeout(Duration::from_millis(50)),
            Err(mpsc::RecvTimeoutError::Timeout)
        ));
        cancellation.request();
        assert!(
            matches!(rx.recv_timeout(Duration::from_secs(2)).unwrap(), Err(error) if error.tag == OutcomeTag::Cancelled)
        );
        worker.join().unwrap();
        assert!(runtime.files.is_empty());
    }
}
