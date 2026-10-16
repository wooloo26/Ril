use super::*;
use std::{
    num::NonZeroUsize,
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
};

#[test]
fn draining_waits_for_queued_children_without_observing_their_results() {
    let scope = Scope::new(&Arc::default()).unwrap();
    let first = scope
        .reserve(Handle::INVALID, TaskOwner::default())
        .unwrap();
    let second = scope
        .reserve(Handle::INVALID, TaskOwner::default())
        .unwrap();
    let context = crate::channel::Context {
        owner: TaskOwner::default(),
        lineage: &[scope.id()],
    };
    let (sender, _) = crate::channel::bounded(1, scope.id(), context).unwrap();
    scope
        .register_channel(
            Handle::INVALID,
            crate::channel::Endpoint::Sender(sender.clone()),
        )
        .unwrap();
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let drain = executor.spawn(scope.finish_async(true)).unwrap();
    assert!(first.cancellation.requested());
    assert!(
        scope
            .reserve(Handle::INVALID, TaskOwner::default())
            .is_err()
    );
    let a = first.clone();
    let b = second.clone();
    let (send, receive) = mpsc::channel();
    let producer = executor
        .spawn(async move {
            b.complete(Err(RuntimeError::panic("second"))).unwrap();
            a.complete(Err(RuntimeError::panic("first"))).unwrap();
            send.send(()).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(Duration::from_secs(2));
    if progress.is_err() {
        let _ = first.complete(Err(RuntimeError::cancelled()));
        let _ = second.complete(Err(RuntimeError::cancelled()));
    }
    progress.unwrap();
    producer.wait().unwrap();
    assert_eq!(drain.wait().unwrap().unwrap().unwrap().message, "first");
    assert_eq!(
        first
            .join(&Cancellation::default())
            .unwrap()
            .unwrap_err()
            .message,
        "first"
    );
    assert_eq!(
        second
            .join(&Cancellation::default())
            .unwrap()
            .unwrap_err()
            .message,
        "second"
    );
    assert!(
        !sender
            .send(
                context,
                crate::channel::Message::new(Handle::INVALID, vec![]),
                &Cancellation::default()
            )
            .unwrap()
    );
    executor.shutdown_idle().unwrap();
}

#[test]
fn published_outcome_does_not_finish_scope_before_native_worker_retirement() {
    let scope = Scope::new(&Arc::default()).unwrap();
    let task = scope
        .reserve(Handle::INVALID, TaskOwner::default())
        .unwrap();
    let executing = task.clone();
    let retired = Arc::new(AtomicBool::new(false));
    let worker_retired = retired.clone();
    let (published, publication) = mpsc::channel();
    let (release, released) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        executing.complete(Ok(Handle::INVALID)).unwrap();
        published.send(()).unwrap();
        released.recv().unwrap();
        worker_retired.store(true, Ordering::Release);
    });
    task.install_worker(worker).unwrap();
    publication.recv_timeout(Duration::from_secs(2)).unwrap();
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let mut finish = scope.finish_async(false);
    let mut context = Context::from_waker(std::task::Waker::noop());
    assert!(Pin::new(&mut finish).poll(&mut context).is_pending());
    assert!(!retired.load(Ordering::Acquire));
    let finishing = executor.spawn(finish).unwrap();
    let releasing = release.clone();
    let (send, receive) = mpsc::channel();
    let producer = executor
        .spawn(async move {
            releasing.send(()).unwrap();
            send.send(()).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(Duration::from_secs(2));
    if progress.is_err() {
        let _ = release.send(());
    }
    progress.unwrap();
    producer.wait().unwrap();
    assert!(finishing.wait().unwrap().unwrap().is_none());
    assert!(retired.load(Ordering::Acquire));
    assert!(task.worker.lock().unwrap().is_none());
    executor.shutdown_idle().unwrap();
}
