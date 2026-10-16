use super::*;
use std::{
    io::Read,
    process::{Command, Stdio},
    sync::mpsc,
    time::Duration,
};

#[test]
fn cancellation_after_spawn_before_publication_terminates_and_reaps_its_child() {
    ril_rt_init();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "process_io::tests::child_fixture",
            "--ignored",
            "--nocapture",
        ])
        .env("RIL_PROCESS_IO_FIXTURE", "sleep")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    let (send, receive) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut data = Vec::new();
        send.send(stdout.read_to_end(&mut data)).unwrap();
    });
    with_runtime(|runtime| runtime.cancellation.request());
    assert_eq!(
        finish_host_with_discard(
            Ok(crate::process::host::Reply::Spawn(Ok(child))),
            crate::process::host::finish,
            crate::process::host::discard
        ),
        0
    );
    receive
        .recv_timeout(Duration::from_secs(2))
        .unwrap()
        .unwrap();
    reader.join().unwrap();
    with_runtime(|runtime| {
        assert_eq!(runtime.fault.as_ref().unwrap().tag, OutcomeTag::Cancelled);
        assert!(
            runtime.children.is_empty(),
            "cancelled reply must not publish child authority"
        );
    });
}

#[test]
fn unpublished_reply_cleanup_failure_keeps_cancellation_as_its_primary_cause() {
    ril_rt_init();
    with_runtime(|runtime| runtime.cancellation.request());
    let mut discarded = false;
    assert_eq!(
        finish_host_with_discard(
            Ok(()),
            |runtime, ()| runtime.unit(),
            |()| {
                discarded = true;
                Err(RuntimeError::internal("reap failure"))
            }
        ),
        0
    );
    assert!(discarded);
    with_runtime(|runtime| {
        let fault = runtime.fault.as_ref().unwrap();
        assert_eq!(fault.tag, OutcomeTag::InternalFault);
        assert_eq!(fault.message, "reap failure");
        assert_eq!(fault.primary.as_ref().unwrap().tag, OutcomeTag::Cancelled);
    });
}
