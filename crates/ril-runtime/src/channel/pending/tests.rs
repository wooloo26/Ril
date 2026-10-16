use super::*;
use std::{
    num::NonZeroUsize,
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc,
    },
    task::{Wake, Waker},
};

fn authority() -> Context<'static> {
    Context {
        owner: TaskOwner::default(),
        lineage: &[7],
    }
}
fn message(value: u64) -> Message {
    Message::new(Handle(value), vec![])
}

#[test]
fn one_worker_drains_more_senders_than_capacity_in_fifo_order() {
    let (sender, receiver) = bounded(1, 7, authority()).unwrap();
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let cancellation = Arc::new(Cancellation::default());
    let mut sends = Vec::new();
    for value in 1..=128 {
        sends.push(
            executor
                .spawn(sender.send_async(authority(), message(value), cancellation.clone()))
                .unwrap(),
        );
    }
    let receiving = receiver.clone();
    let cancelled = cancellation.clone();
    let (send, receive) = mpsc::channel();
    let consumer = executor
        .spawn(async move {
            for value in 1..=128 {
                let receipt = receiving
                    .recv_async(authority(), cancelled.clone())
                    .await
                    .unwrap()
                    .unwrap();
                assert_eq!(receipt.value(), Handle(value));
                assert!(receiving.references().contains(&Handle(value)));
                receipt.ack();
            }
            send.send(()).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(Duration::from_secs(2));
    if progress.is_err() {
        cancellation.request();
    }
    progress.unwrap();
    consumer.wait().unwrap();
    for send in sends {
        assert!(send.wait().unwrap().unwrap());
    }
    assert!(receiver.references().is_empty());
    assert!(lock(&receiver.channel.state).waiters.is_empty());
    executor.shutdown_idle().unwrap();
}

#[derive(Default)]
struct Counter(AtomicUsize);
impl Wake for Counter {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }
}
#[test]
fn current_waker_is_notified_by_close_and_dropped_waits_unregister() {
    let (sender, receiver) = bounded(1, 7, authority()).unwrap();
    let first = Arc::new(Counter::default());
    let second = Arc::new(Counter::default());
    let first_waker = Waker::from(first.clone());
    let second_waker = Waker::from(second.clone());
    let mut pending = receiver.recv_async(authority(), Arc::default());
    assert!(
        Pin::new(&mut pending)
            .poll(&mut PollContext::from_waker(&first_waker))
            .is_pending()
    );
    assert!(
        Pin::new(&mut pending)
            .poll(&mut PollContext::from_waker(&second_waker))
            .is_pending()
    );
    sender.close(authority()).unwrap();
    assert_eq!(first.0.load(Ordering::Relaxed), 0);
    assert_eq!(second.0.load(Ordering::Relaxed), 1);
    assert!(matches!(
        Pin::new(&mut pending).poll(&mut PollContext::from_waker(&second_waker)),
        Poll::Ready(Ok(None))
    ));
    let (_, receiver) = bounded(1, 7, authority()).unwrap();
    let mut pending = receiver.recv_async(authority(), Arc::default());
    assert!(
        Pin::new(&mut pending)
            .poll(&mut PollContext::from_waker(&first_waker))
            .is_pending()
    );
    assert_eq!(lock(&receiver.channel.state).waiters.len(), 1);
    drop(pending);
    assert!(lock(&receiver.channel.state).waiters.is_empty());
}

#[test]
fn cancelled_and_dropped_full_sends_consume_then_close_payload_authority() {
    for cancel in [false, true] {
        let (sender, _) = bounded(1, 7, authority()).unwrap();
        sender
            .send(authority(), message(11), &Cancellation::default())
            .unwrap();
        let (payload_sender, payload_receiver) = bounded(1, 7, authority()).unwrap();
        let ticket = payload_receiver.detach(authority()).unwrap();
        let cancellation = Arc::new(Cancellation::default());
        let mut pending = sender.send_async(
            authority(),
            Message::new(Handle(19), vec![(Handle(19), ticket.clone())]),
            cancellation.clone(),
        );
        let mut context = PollContext::from_waker(Waker::noop());
        assert!(Pin::new(&mut pending).poll(&mut context).is_pending());
        assert!(ticket.attach(authority()).is_err());
        if cancel {
            cancellation.request();
            assert!(
                matches!(Pin::new(&mut pending).poll(&mut context), Poll::Ready(Err(error)) if error.tag == ril_runtime_api::abi::OutcomeTag::Cancelled)
            );
        }
        drop(pending);
        assert!(
            !payload_sender
                .send(authority(), message(23), &Cancellation::default())
                .unwrap()
        );
        assert!(lock(&sender.channel.state).waiters.is_empty());
        assert_eq!(sender.references(), [Handle(11)]);
    }
}
