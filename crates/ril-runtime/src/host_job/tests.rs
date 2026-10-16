use super::*;
use std::{
    num::NonZeroUsize,
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
};
fn discard(_: ()) -> Result<()> {
    Ok(())
}

#[test]
fn blocked_host_requests_leave_the_only_cpu_worker_available_for_cancellation() {
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let mut tokens = Vec::new();
    let mut jobs = Vec::new();
    for _ in 0..32 {
        let token = Arc::new(Cancellation::default());
        let request = token.clone();
        let job = Job::start(
            move || {
                assert!(!request.sleep(Duration::from_secs(60)));
                Err(RuntimeError::cancelled())
            },
            token.clone(),
            discard,
        )
        .unwrap();
        jobs.push(executor.spawn(job).unwrap());
        tokens.push(token);
    }
    let cancelling = tokens.clone();
    let (send, receive) = mpsc::channel();
    let cancel = executor
        .spawn(async move {
            for token in cancelling {
                token.request();
            }
            send.send(()).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(Duration::from_secs(2));
    for token in tokens {
        token.request();
    }
    progress.unwrap();
    cancel.wait().unwrap();
    for job in jobs {
        assert_eq!(
            job.wait().unwrap().unwrap_err().tag,
            ril_runtime_api::abi::OutcomeTag::Cancelled
        );
    }
    executor.shutdown_idle().unwrap();
}

#[test]
fn dropping_a_host_job_finishes_the_operation_and_discards_its_unpublished_reply() {
    let cancellation = Arc::new(Cancellation::default());
    let token = cancellation.clone();
    let finished = Arc::new(AtomicBool::new(false));
    let discarded = finished.clone();
    let job = Job::start(
        move || {
            assert!(!token.sleep(Duration::from_secs(60)));
            Ok(discarded)
        },
        cancellation,
        |done| {
            done.store(true, Ordering::Release);
            Ok(())
        },
    )
    .unwrap();
    drop(job);
    assert!(finished.load(Ordering::Acquire));
}

#[test]
fn unexpected_host_panic_is_an_internal_fault() {
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let job = Job::start(|| panic!("host failure"), Arc::default(), discard).unwrap();
    let error = executor.spawn(job).unwrap().wait().unwrap().unwrap_err();
    assert_eq!(error.tag, ril_runtime_api::abi::OutcomeTag::InternalFault);
    executor.shutdown_idle().unwrap();
}
