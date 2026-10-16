use super::*;
use crate::process_io::Cancellation;
use ril_runtime_api::abi::OutcomeTag;
use std::{
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

fn reader_file(reader: std::io::PipeReader) -> File {
    #[cfg(windows)]
    let owned: std::os::windows::io::OwnedHandle = reader.into();
    #[cfg(target_os = "linux")]
    let owned: std::os::fd::OwnedFd = reader.into();
    File::from(owned)
}

fn writer_file(writer: std::io::PipeWriter) -> File {
    #[cfg(windows)]
    let owned: std::os::windows::io::OwnedHandle = writer.into();
    #[cfg(target_os = "linux")]
    let owned: std::os::fd::OwnedFd = writer.into();
    File::from(owned)
}

#[test]
fn cancellation_completes_a_blocked_file_read_without_closing_its_authority() {
    let (reader, mut writer) = std::io::pipe().unwrap();
    let file = reader_file(reader);
    #[cfg(target_os = "linux")]
    let original_flags = rustix::fs::fcntl_getfl(&file).unwrap();
    let state = Arc::new(Mutex::new(FileState {
        file: Some(file),
        readable: true,
        writable: false,
    }));
    let cancellation = Arc::new(Cancellation::default());
    let request = Request {
        file: state.clone(),
        operation: Operation::Read(1),
        cancellation: cancellation.clone(),
    };
    let (send, receive) = mpsc::channel();
    let worker = thread::spawn(move || {
        send.send(request.perform().err().map(|error| error.tag))
            .unwrap()
    });
    let start = Instant::now();
    // The receiver owns this mutex for the entire pending OS transfer.
    while state.try_lock().is_ok() && start.elapsed() < Duration::from_secs(3) {
        thread::sleep(Duration::from_millis(1));
    }
    assert!(
        start.elapsed() < Duration::from_secs(3),
        "read never started"
    );
    assert!(
        receive.try_recv().is_err(),
        "empty pipe unexpectedly completed"
    );
    cancellation.request();
    assert_eq!(
        receive.recv_timeout(Duration::from_secs(3)).unwrap(),
        Some(OutcomeTag::Cancelled)
    );
    worker.join().unwrap();
    {
        let guard = state.lock().unwrap();
        let file = guard
            .file
            .as_ref()
            .expect("cancellation must not close a file");
        #[cfg(target_os = "linux")]
        assert_eq!(rustix::fs::fcntl_getfl(file).unwrap(), original_flags);
        #[cfg(not(target_os = "linux"))]
        let _ = file;
    }
    writer.write_all(b"x").unwrap();
    let request = Request {
        file: state,
        operation: Operation::Read(1),
        cancellation: Arc::new(Cancellation::default()),
    };
    let Reply::Read(Ok((bytes, end))) = request.perform().unwrap() else {
        panic!("subsequent read failed")
    };
    assert_eq!(bytes, b"x");
    assert!(!end);
}

#[test]
fn pre_cancelled_transfers_do_not_access_or_close_the_file() {
    let (reader, _writer) = std::io::pipe().unwrap();
    let state = Arc::new(Mutex::new(FileState {
        file: Some(reader_file(reader)),
        readable: true,
        writable: false,
    }));
    let cancellation = Arc::new(Cancellation::default());
    cancellation.request();
    let request = Request {
        file: state.clone(),
        operation: Operation::Close,
        cancellation,
    };
    assert_eq!(request.perform().err().unwrap().tag, OutcomeTag::Cancelled);
    assert!(state.lock().unwrap().file.is_some());
    release_host(&state);
    assert!(
        state.lock().unwrap().file.is_none(),
        "implicit cleanup is still available"
    );
}

#[test]
fn cancellation_completes_a_blocked_file_write_without_reporting_false_progress() {
    let (_reader, writer) = std::io::pipe().unwrap();
    let file = writer_file(writer);
    #[cfg(target_os = "linux")]
    {
        // Fill the pipe before requesting one more write. No reader can drain
        // it, so a successful write would be an incorrect cancellation result.
        let _mode = crate::platform_io::FileMode::nonblocking(&file).unwrap();
        let mut output = &file;
        loop {
            match output.write(&[b'p'; 4096]) {
                Ok(count) => assert!(count > 0),
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => break,
                Err(error) => panic!("cannot fill fixture pipe: {error}"),
            }
        }
    }
    let state = Arc::new(Mutex::new(FileState {
        file: Some(file),
        readable: false,
        writable: true,
    }));
    let cancellation = Arc::new(Cancellation::default());
    let request = Request {
        file: state.clone(),
        operation: Operation::Write(vec![b'x'; 8 * 1024 * 1024].into()),
        cancellation: cancellation.clone(),
    };
    let (send, receive) = mpsc::channel();
    let worker = thread::spawn(move || {
        send.send(request.perform().err().map(|error| error.tag))
            .unwrap()
    });
    let start = Instant::now();
    while state.try_lock().is_ok() && start.elapsed() < Duration::from_secs(3) {
        thread::sleep(Duration::from_millis(1));
    }
    assert!(
        start.elapsed() < Duration::from_secs(3),
        "write never started"
    );
    assert!(
        receive.try_recv().is_err(),
        "full pipe unexpectedly accepted all data"
    );
    cancellation.request();
    assert_eq!(
        receive.recv_timeout(Duration::from_secs(3)).unwrap(),
        Some(OutcomeTag::Cancelled)
    );
    worker.join().unwrap();
    assert!(state.lock().unwrap().file.is_some());
    release_host(&state);
}
