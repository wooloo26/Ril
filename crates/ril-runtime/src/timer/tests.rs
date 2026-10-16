use super::*;
use crate::scheduler::Executor;
use std::{num::NonZeroUsize, sync::mpsc};

#[test]
fn more_sleepers_than_workers_park_and_cancellation_wakes_them_all() {
    let executor = Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let token = Arc::new(Cancellation::default());
    let mut sleeping = Vec::new();
    for _ in 0..64 {
        sleeping.push(
            executor
                .spawn(Sleep::new(Duration::from_secs(60), token.clone()).unwrap())
                .unwrap(),
        );
    }
    let (send, receive) = mpsc::channel();
    let quick = executor
        .spawn(async move {
            send.send(()).unwrap();
        })
        .unwrap();
    receive
        .recv_timeout(Duration::from_secs(2))
        .expect("sleep blocked the sole CPU worker");
    token.request();
    assert!(quick.wait().is_ok());
    for sleep in sleeping {
        assert_eq!(
            sleep.wait().unwrap().unwrap_err().tag,
            ril_runtime_api::abi::OutcomeTag::Cancelled
        );
    }
    executor.shutdown_idle().unwrap();
}

#[test]
fn timer_deadlines_do_not_complete_early_and_zero_waits_need_no_service() {
    let executor = Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let start = Instant::now();
    assert!(
        executor
            .spawn(Sleep::new(Duration::from_millis(15), Arc::default()).unwrap())
            .unwrap()
            .wait()
            .unwrap()
            .is_ok()
    );
    assert!(start.elapsed() >= Duration::from_millis(15));
    let mut zero = Sleep::new(Duration::ZERO, Arc::default()).unwrap();
    let mut context = Context::from_waker(Waker::noop());
    assert!(matches!(
        Pin::new(&mut zero).poll(&mut context),
        Poll::Ready(Ok(()))
    ));
    assert!(zero.registration.is_none());
    executor.shutdown_idle().unwrap();
}

#[test]
fn dropping_pending_sleep_removes_its_timer_and_cancellation_registrations() {
    let token = Arc::new(Cancellation::default());
    let mut sleep = Sleep::new(Duration::from_secs(60), token).unwrap();
    let mut context = Context::from_waker(Waker::noop());
    assert!(Pin::new(&mut sleep).poll(&mut context).is_pending());
    let registration = sleep.registration.as_ref().unwrap();
    let service = registration.service.clone();
    let key = registration.key;
    let alarm = Arc::downgrade(&sleep.alarm);
    drop(sleep);
    assert!(!service.pending.lock().unwrap().alarms.contains_key(&key));
    assert!(alarm.upgrade().is_none());
}
