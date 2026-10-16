use super::*;
use std::{
    sync::{
        Barrier,
        atomic::{AtomicBool, AtomicUsize, Ordering},
        mpsc,
    },
    time::Duration,
};

fn pool(workers: usize) -> Executor {
    Executor::new(NonZeroUsize::new(workers).unwrap()).unwrap()
}
fn finish<T: Send + 'static>(join: Join<T>) -> Result<T, JoinError> {
    let (send, receive) = mpsc::channel();
    let watcher = thread::spawn(move || {
        let _ = send.send(join.wait());
    });
    let result = receive
        .recv_timeout(Duration::from_secs(5))
        .expect("executor failed to complete");
    watcher.join().unwrap();
    result
}

struct SelfWake {
    polls: usize,
    target: usize,
    observed: Arc<AtomicUsize>,
}
impl Future for SelfWake {
    type Output = usize;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<usize> {
        self.polls += 1;
        self.observed.fetch_add(1, Ordering::SeqCst);
        if self.polls == self.target {
            return Poll::Ready(self.polls);
        }
        for _ in 0..12 {
            cx.waker().wake_by_ref();
        }
        Poll::Pending
    }
}

#[test]
fn duplicate_wakes_during_poll_do_not_disappear_or_create_parallel_polls() {
    let executor = pool(2);
    let observed = Arc::new(AtomicUsize::new(0));
    let join = executor
        .spawn(SelfWake {
            polls: 0,
            target: 1_000,
            observed: observed.clone(),
        })
        .unwrap();
    assert_eq!(finish(join), Ok(1_000));
    assert_eq!(observed.load(Ordering::SeqCst), 1_000);
    executor.shutdown_idle().unwrap();
}

#[test]
fn nested_joins_release_a_single_worker_for_queued_children() {
    let executor = pool(1);
    let inner = executor.clone();
    let join = executor
        .spawn(async move {
            let mut pending = Vec::new();
            for number in 1..=100 {
                let nested = inner.clone();
                pending.push(
                    inner
                        .spawn(async move {
                            nested.spawn(async move { number }).unwrap().await.unwrap()
                        })
                        .unwrap(),
                );
            }
            let mut sum = 0;
            for child in pending {
                sum += child.await.unwrap();
            }
            sum
        })
        .unwrap();
    assert_eq!(finish(join), Ok(5_050));
    executor.shutdown_idle().unwrap();
}

struct Event {
    ready: AtomicBool,
    waiter: Mutex<Option<Waker>>,
}
impl Event {
    fn set(&self) {
        self.ready.store(true, Ordering::Release);
        let waiter = self.waiter.lock().unwrap().take();
        if let Some(waiter) = waiter {
            waiter.wake();
        }
    }
}
struct Wait(Arc<Event>);
impl Future for Wait {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let mut waiter = self.0.waiter.lock().unwrap();
        if self.0.ready.load(Ordering::Acquire) {
            return Poll::Ready(());
        }
        *waiter = Some(cx.waker().clone());
        Poll::Pending
    }
}

#[test]
fn parked_tasks_survive_external_wake_races_and_busy_shutdown() {
    let executor = pool(2);
    let mut events = Vec::new();
    let mut joins = Vec::new();
    for index in 0..128 {
        let event = Arc::new(Event {
            ready: AtomicBool::new(false),
            waiter: Mutex::new(None),
        });
        if index % 2 == 0 {
            event.set();
        }
        joins.push(executor.spawn(Wait(event.clone())).unwrap());
        events.push(event);
    }
    assert_eq!(executor.shutdown_idle(), Err(Busy));
    let producer = thread::spawn(move || {
        for event in events {
            event.set();
        }
    });
    for join in joins {
        assert_eq!(finish(join), Ok(()));
    }
    producer.join().unwrap();
    executor.shutdown_idle().unwrap();
}

#[test]
fn worker_concurrency_is_bounded_and_threads_are_reused() {
    let executor = pool(2);
    let active = Arc::new(AtomicUsize::new(0));
    let maximum = Arc::new(AtomicUsize::new(0));
    let barrier = Arc::new(Barrier::new(2));
    let mut joins = Vec::new();
    for _ in 0..12 {
        let (active, maximum, barrier) = (active.clone(), maximum.clone(), barrier.clone());
        joins.push(
            executor
                .spawn(async move {
                    let count = active.fetch_add(1, Ordering::SeqCst) + 1;
                    maximum.fetch_max(count, Ordering::SeqCst);
                    barrier.wait();
                    let id = thread::current().id();
                    active.fetch_sub(1, Ordering::SeqCst);
                    id
                })
                .unwrap(),
        );
    }
    let mut threads = std::collections::HashSet::new();
    for join in joins {
        threads.insert(finish(join).unwrap());
    }
    assert_eq!(threads.len(), 2);
    assert_eq!(maximum.load(Ordering::SeqCst), 2);
    executor.shutdown_idle().unwrap();
    assert!(matches!(executor.spawn(async {}), Err(SubmitError::Closed)));
}

struct DropPanic;
impl Future for DropPanic {
    type Output = usize;
    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<usize> {
        Poll::Ready(7)
    }
}
impl Drop for DropPanic {
    fn drop(&mut self) {
        panic!("unexpected future destructor failure");
    }
}
#[test]
fn host_panics_are_failures_and_do_not_retire_a_worker() {
    let executor = pool(1);
    assert_eq!(
        finish(
            executor
                .spawn(async {
                    panic!("unexpected host failure");
                })
                .unwrap()
        ),
        Err(JoinError::Panicked)
    );
    assert_eq!(
        finish(executor.spawn(DropPanic).unwrap()),
        Err(JoinError::Panicked)
    );
    assert_eq!(finish(executor.spawn(async { 11 }).unwrap()), Ok(11));
    executor.shutdown_idle().unwrap();
}

#[test]
fn dropping_executor_owners_does_not_discard_parked_work() {
    let executor = pool(1);
    let event = Arc::new(Event {
        ready: AtomicBool::new(false),
        waiter: Mutex::new(None),
    });
    let join = executor.spawn(Wait(event.clone())).unwrap();
    drop(executor);
    event.set();
    assert_eq!(finish(join), Ok(()));
}
