use super::*;
use rustix::fs::{OFlags, fcntl_getfl};
use std::{
    io::Read,
    os::{fd::OwnedFd, unix::net::UnixStream},
    process::{Command, Stdio},
    time::Instant,
};

const ALIAS_FIXTURE: &str = "RIL_STDIO_ALIAS_FIXTURE";

#[test]
#[ignore = "run in a separate process with aliased standard descriptors"]
fn aliased_standard_stream_fixture() {
    if std::env::var_os(ALIAS_FIXTURE).is_none() {
        return;
    }
    let original = fcntl_getfl(rustix::stdio::stdin()).unwrap();
    assert!(!original.contains(OFlags::NONBLOCK));
    let cancellation = Arc::new(Cancellation::default());
    let request = Request {
        operation: Operation::Read(1),
        cancellation: cancellation.clone(),
        print: false,
    };
    let reader = std::thread::spawn(move || request.perform());
    let deadline = Instant::now() + Duration::from_secs(3);
    while !fcntl_getfl(rustix::stdio::stdin())
        .unwrap()
        .contains(OFlags::NONBLOCK)
    {
        assert!(
            Instant::now() < deadline,
            "standard input never entered its host transfer"
        );
        std::thread::sleep(Duration::from_millis(1));
    }
    let request = Request {
        operation: Operation::Write {
            data: b"aliased transfer\n".to_vec().into(),
            stderr: true,
            all: true,
        },
        cancellation: Arc::default(),
        print: false,
    };
    assert!(matches!(request.perform().unwrap(), Reply::Unit(Ok(()))));
    assert!(
        fcntl_getfl(rustix::stdio::stderr())
            .unwrap()
            .contains(OFlags::NONBLOCK),
        "finishing one alias must not restore flags while a read still waits"
    );
    cancellation.request();
    assert!(
        matches!(reader.join().unwrap(), Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::Cancelled)
    );
    for descriptor in [
        rustix::stdio::stdin(),
        rustix::stdio::stdout(),
        rustix::stdio::stderr(),
    ] {
        assert_eq!(fcntl_getfl(descriptor).unwrap(), original);
    }
    // Host cleanup is cancellation-masked even though source cleanup cannot
    // carry a residual Fiber row. Exercise request preparation at that boundary.
    let mut runtime = Runtime::default();
    runtime.cancellation.request();
    runtime.cancellation_mask = 1;
    let text = runtime.string("protected cleanup\n".into()).unwrap();
    let protected = prepare(&runtime, "print", &[text]).unwrap();
    assert!(matches!(
        protected.perform().unwrap(),
        Reply::Printed(Ok(()))
    ));
    runtime.cancellation_mask = 0;
    let ordinary = prepare(&runtime, "print", &[text]).unwrap();
    assert!(
        matches!(ordinary.perform(), Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::Cancelled)
    );
}

#[test]
fn cancelling_aliased_standard_streams_restores_the_shared_host_flags() {
    let (stream, mut peer) = UnixStream::pair().unwrap();
    let original = fcntl_getfl(&stream).unwrap();
    let input: OwnedFd = stream.try_clone().unwrap().into();
    let output: OwnedFd = stream.try_clone().unwrap().into();
    let error: OwnedFd = stream.try_clone().unwrap().into();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--ignored",
            "--exact",
            "host_stdio::tests::aliased_standard_stream_fixture",
            "--nocapture",
        ])
        .env(ALIAS_FIXTURE, "1")
        .stdin(Stdio::from(input))
        .stdout(Stdio::from(output))
        .stderr(Stdio::from(error))
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("aliased standard stream cancellation did not finish");
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    assert_eq!(
        fcntl_getfl(&stream).unwrap(),
        original,
        "the embedding parent's alias must retain its original flags"
    );
    drop(stream);
    let mut output = String::new();
    peer.read_to_string(&mut output).unwrap();
    assert!(status.success(), "{output}");
}
