use super::*;
use ril_runtime_api::abi::OutcomeTag;
use std::{sync::mpsc, thread};

const ROOT: TaskOwner = TaskOwner {
    scope: 0,
    ordinal: 0,
};
const CHILD: TaskOwner = TaskOwner {
    scope: 7,
    ordinal: 1,
};
fn root() -> Context<'static> {
    Context {
        owner: ROOT,
        lineage: &[7],
    }
}
fn child() -> Context<'static> {
    Context {
        owner: CHILD,
        lineage: &[7],
    }
}
fn value(handle: u64) -> Message {
    Message::new(Handle(handle), vec![])
}
fn receive(receiver: &Receiver, context: Context<'_>) -> Receipt {
    receiver
        .recv(context, &Cancellation::default())
        .unwrap()
        .unwrap()
}

#[test]
fn capacity_and_scope_checks_happen_before_creation() {
    for capacity in [0, -1, i128::MAX] {
        assert_eq!(
            bounded(capacity, 7, root()).unwrap_err().tag,
            OutcomeTag::LanguagePanic
        );
    }
    assert!(bounded(1, 0, root()).is_err());
    assert!(bounded(1, 9, root()).is_err());
    assert!(bounded(1, 7, root()).is_ok());
}

#[test]
fn fifo_drains_before_eof_and_receipts_hold_roots_until_ack() {
    let cancel = Cancellation::default();
    let (tx, rx) = bounded(2, 7, root()).unwrap();
    assert!(tx.send(root(), value(11), &cancel).unwrap());
    assert!(tx.send(root(), value(12), &cancel).unwrap());
    tx.close(root()).unwrap();
    let first = receive(&rx, root());
    assert_eq!(first.value(), Handle(11));
    assert_eq!(rx.references(), [Handle(11), Handle(12)]);
    first.ack();
    assert_eq!(rx.references(), [Handle(12)]);
    let second = receive(&rx, root());
    assert_eq!(second.value(), Handle(12));
    second.ack();
    assert!(rx.recv(root(), &cancel).unwrap().is_none());
    assert!(rx.references().is_empty());
}

#[test]
fn clone_source_has_no_child_authority_and_drop_does_not_close_a_sender() {
    let cancel = Cancellation::default();
    let (tx, rx) = bounded(2, 7, root()).unwrap();
    assert!(tx.send(child(), value(1), &cancel).is_err());
    assert!(tx.close(child()).is_err());
    assert!(tx.detach(child()).is_err());
    let local = tx.clone_for(child()).unwrap();
    tx.close_if_owned(CHILD);
    assert!(tx.send(root(), value(2), &cancel).unwrap());
    drop(tx);
    assert_eq!(
        lock(&rx.channel.state).senders,
        2,
        "reference loss must not synthesize EOF"
    );
    local.close_if_owned(CHILD);
    assert_eq!(lock(&rx.channel.state).senders, 1);
    let received = receive(&rx, root());
    assert_eq!(received.value(), Handle(2));
    received.ack();
    rx.close_in_scope(7);
    assert_eq!(lock(&rx.channel.state).senders, 0);
}

#[test]
fn detach_and_fork_transfer_invalidate_old_owner_and_attach_once() {
    let (tx, rx) = bounded(1, 7, root()).unwrap();
    let ticket = rx.detach(root()).unwrap();
    assert!(rx.recv(root(), &Cancellation::default()).is_err());
    assert!(ticket.attach(child()).is_err());
    ticket.transfer_owner(ROOT, child()).unwrap();
    assert!(ticket.attach(root()).is_err());
    let Endpoint::Receiver(local) = ticket.attach(child()).unwrap() else {
        panic!("receiver ticket");
    };
    assert!(ticket.attach(child()).is_err());
    tx.send(root(), value(42), &Cancellation::default())
        .unwrap();
    let message = receive(&local, child());
    assert_eq!(message.value(), Handle(42));
    message.ack();
    local.close_if_owned(ROOT);
    assert!(
        tx.send(root(), value(43), &Cancellation::default())
            .unwrap()
    );
    local.close_if_owned(CHILD);
    assert!(
        !tx.send(root(), value(44), &Cancellation::default())
            .unwrap()
    );
}

#[test]
fn same_task_send_receive_never_revives_old_ticket_aliases() {
    let cancel = Cancellation::default();
    let (control_tx, control_rx) = bounded(1, 7, root()).unwrap();
    let (payload_tx, payload_rx) = bounded(1, 7, root()).unwrap();
    let ticket = payload_tx.detach(root()).unwrap();
    let alias = ticket.clone();
    let message = Message::new(
        Handle(51),
        vec![(Handle(51), ticket.clone()), (Handle(52), alias.clone())],
    );
    assert!(control_tx.send(root(), message, &cancel).unwrap());
    assert!(ticket.attach(root()).is_err());
    let receipt = receive(&control_rx, root());
    assert_eq!(receipt.replacements().len(), 2);
    assert!(Arc::ptr_eq(
        &receipt.replacements()[0].1,
        &receipt.replacements()[1].1
    ));
    let received_ticket = receipt.replacements()[0].1.clone();
    assert!(!Arc::ptr_eq(&received_ticket, &ticket));
    receipt.ack();
    assert!(ticket.attach(root()).is_err());
    assert!(alias.attach(root()).is_err());
    let Endpoint::Sender(received) = received_ticket.attach(root()).unwrap() else {
        panic!("sender ticket");
    };
    received.send(root(), value(99), &cancel).unwrap();
    received.close(root()).unwrap();
    let payload = receive(&payload_rx, root());
    assert_eq!(payload.value(), Handle(99));
    payload.ack();
    assert!(payload_rx.recv(root(), &cancel).unwrap().is_none());
}

#[test]
fn failed_and_cancelled_sends_consume_and_close_submitted_tickets() {
    for cancelled in [false, true] {
        let cancel = Cancellation::default();
        let (tx, rx) = bounded(1, 7, root()).unwrap();
        let (payload_tx, payload_rx) = bounded(1, 7, root()).unwrap();
        let ticket = payload_tx.detach(root()).unwrap();
        if cancelled {
            cancel.request();
        } else {
            rx.close(root()).unwrap();
        }
        let result = tx.send(
            root(),
            Message::new(Handle(1), vec![(Handle(1), ticket.clone())]),
            &cancel,
        );
        if cancelled {
            assert_eq!(result.unwrap_err().tag, OutcomeTag::Cancelled);
        } else {
            assert!(!result.unwrap());
        }
        assert!(ticket.attach(root()).is_err());
        assert!(
            payload_rx
                .recv(root(), &Cancellation::default())
                .unwrap()
                .is_none()
        );
        rx.close_in_scope(7);
    }
}

#[test]
fn blocked_send_and_receive_observe_cancellation_without_fabricating_closed() {
    let (tx, rx) = bounded(1, 7, root()).unwrap();
    tx.send(root(), value(1), &Cancellation::default()).unwrap();
    let local = tx.clone_for(child()).unwrap();
    let cancel = Arc::new(Cancellation::default());
    let worker_cancel = cancel.clone();
    let (done_tx, done_rx) = mpsc::channel();
    let worker = thread::spawn(move || {
        done_tx
            .send(local.send(child(), value(2), &worker_cancel))
            .unwrap();
        local.close_if_owned(CHILD);
    });
    assert!(done_rx.recv_timeout(Duration::from_millis(20)).is_err());
    cancel.request();
    assert_eq!(
        done_rx
            .recv_timeout(Duration::from_secs(2))
            .unwrap()
            .unwrap_err()
            .tag,
        OutcomeTag::Cancelled
    );
    worker.join().unwrap();
    assert_eq!(lock(&rx.channel.state).queued.len(), 1);
    receive(&rx, root()).ack();

    let ticket = rx.detach(root()).unwrap();
    ticket.transfer_owner(ROOT, child()).unwrap();
    let Endpoint::Receiver(local) = ticket.attach(child()).unwrap() else {
        panic!("receiver ticket");
    };
    let cancel = Arc::new(Cancellation::default());
    let worker_cancel = cancel.clone();
    let (done_tx, done_rx) = mpsc::channel();
    let worker = thread::spawn(move || {
        done_tx.send(local.recv(child(), &worker_cancel)).unwrap();
        local.close_if_owned(CHILD);
    });
    assert!(done_rx.recv_timeout(Duration::from_millis(20)).is_err());
    cancel.request();
    assert_eq!(
        done_rx
            .recv_timeout(Duration::from_secs(2))
            .unwrap()
            .unwrap_err()
            .tag,
        OutcomeTag::Cancelled
    );
    worker.join().unwrap();
    tx.close(root()).unwrap();
}

#[test]
fn receiver_close_and_discard_close_unreceived_or_unpublished_transfer_once() {
    for discard_receipt in [false, true] {
        let cancel = Cancellation::default();
        let (tx, rx) = bounded(1, 7, root()).unwrap();
        let (payload_tx, payload_rx) = bounded(1, 7, root()).unwrap();
        let ticket = payload_rx.detach(root()).unwrap();
        tx.send(
            root(),
            Message::new(Handle(1), vec![(Handle(1), ticket.clone())]),
            &cancel,
        )
        .unwrap();
        if discard_receipt {
            receive(&rx, root()).discard();
        } else {
            rx.close(root()).unwrap();
        }
        assert!(!payload_tx.send(root(), value(2), &cancel).unwrap());
        assert!(ticket.attach(root()).is_err());
        rx.close_in_scope(7);
        rx.close_in_scope(7);
        assert!(rx.references().is_empty());
    }
}

#[test]
fn queued_and_inflight_transfers_trace_nested_channels_without_managed_ticket_objects() {
    let cancel = Cancellation::default();
    let (tx, rx) = bounded(1, 7, root()).unwrap();
    let (inner_tx, inner_rx) = bounded(1, 7, root()).unwrap();
    inner_tx.send(root(), value(88), &cancel).unwrap();
    let ticket = inner_rx.detach(root()).unwrap();
    tx.send(
        root(),
        Message::new(Handle(11), vec![(Handle(12), ticket)]),
        &cancel,
    )
    .unwrap();
    assert_eq!(rx.references(), [Handle(11), Handle(12), Handle(88)]);
    let receipt = receive(&rx, root());
    assert_eq!(rx.references(), [Handle(11), Handle(12), Handle(88)]);
    let received = receipt.replacements()[0].1.clone();
    receipt.ack();
    assert!(rx.references().is_empty());
    assert_eq!(received.references(), [Handle(88)]);
    received.close_if_owned(ROOT);
    assert!(!inner_tx.send(root(), value(89), &cancel).unwrap());
}

#[test]
fn scope_close_breaks_cross_channel_receiver_cycles_from_consumed_originals() {
    let cancel = Cancellation::default();
    let (a_tx, a_rx) = bounded(1, 7, root()).unwrap();
    let (b_tx, b_rx) = bounded(1, 7, root()).unwrap();
    let a_weak = Arc::downgrade(&a_rx.channel);
    let b_weak = Arc::downgrade(&b_rx.channel);
    let a_ticket = a_rx.detach(root()).unwrap();
    let b_ticket = b_rx.detach(root()).unwrap();
    a_tx.send(
        root(),
        Message::new(Handle(10), vec![(Handle(10), b_ticket.clone())]),
        &cancel,
    )
    .unwrap();
    b_tx.send(
        root(),
        Message::new(Handle(20), vec![(Handle(20), a_ticket.clone())]),
        &cancel,
    )
    .unwrap();
    assert_eq!(a_rx.references(), [Handle(10), Handle(20)]);
    a_rx.close_in_scope(999);
    assert_eq!(a_rx.references(), [Handle(10), Handle(20)]);
    a_rx.close_in_scope(7);
    assert!(a_rx.references().is_empty());
    assert!(b_rx.references().is_empty());
    drop((a_ticket, b_ticket, a_tx, a_rx, b_tx, b_rx));
    assert!(a_weak.upgrade().is_none());
    assert!(b_weak.upgrade().is_none());
}

#[test]
fn narrower_scope_tickets_cannot_escape_through_an_outer_channel() {
    let nested = Context {
        owner: ROOT,
        lineage: &[7, 8],
    };
    let (tx, rx) = bounded(1, 7, root()).unwrap();
    let (inner_tx, inner_rx) = bounded(1, 8, nested).unwrap();
    let ticket = inner_tx.detach(nested).unwrap();
    let error = tx
        .send(
            nested,
            Message::new(Handle(1), vec![(Handle(1), ticket.clone())]),
            &Cancellation::default(),
        )
        .unwrap_err();
    assert_eq!(error.tag, OutcomeTag::LanguagePanic);
    assert!(ticket.attach(nested).is_err());
    assert!(
        inner_rx
            .recv(nested, &Cancellation::default())
            .unwrap()
            .is_none()
    );
    assert!(rx.references().is_empty());
}

#[test]
fn a_child_returning_a_ticket_to_the_parent_does_not_revive_parent_aliases() {
    let (tx, rx) = bounded(1, 7, root()).unwrap();
    let original = rx.detach(root()).unwrap();
    original.transfer_owner(ROOT, child()).unwrap();
    let returned = original.reissue(child(), root()).unwrap();
    assert_eq!(returned.scope_id(), 7);
    assert!(original.attach(root()).is_err());
    assert!(original.attach(child()).is_err());
    original.close_if_owned(CHILD);
    let Endpoint::Receiver(received) = returned.attach(root()).unwrap() else {
        panic!("receiver ticket");
    };
    tx.send(root(), value(5), &Cancellation::default()).unwrap();
    let message = receive(&received, root());
    assert_eq!(message.value(), Handle(5));
    message.ack();
    assert!(returned.attach(root()).is_err());
}

#[test]
fn receiving_frees_pending_capacity_even_before_the_receipt_is_acknowledged() {
    let cancel = Cancellation::default();
    let (tx, rx) = bounded(1, 7, root()).unwrap();
    tx.send(root(), value(1), &cancel).unwrap();
    let local = tx.clone_for(child()).unwrap();
    let (done_tx, done_rx) = mpsc::channel();
    let worker = thread::spawn(move || {
        done_tx
            .send(local.send(child(), value(2), &Cancellation::default()))
            .unwrap();
        local.close_if_owned(CHILD);
    });
    assert!(done_rx.recv_timeout(Duration::from_millis(20)).is_err());
    let first = receive(&rx, root());
    assert!(
        done_rx
            .recv_timeout(Duration::from_secs(2))
            .unwrap()
            .unwrap()
    );
    worker.join().unwrap();
    assert_eq!(rx.references(), [Handle(1), Handle(2)]);
    first.ack();
    receive(&rx, root()).ack();
}

#[test]
fn long_transfer_cycles_trace_and_close_with_bounded_native_stack() {
    const COUNT: usize = 2048;
    let cancel = Cancellation::default();
    let channels: Vec<_> = (0..COUNT).map(|_| bounded(1, 7, root()).unwrap()).collect();
    let tickets: Vec<_> = channels
        .iter()
        .map(|(_, rx)| rx.detach(root()).unwrap())
        .collect();
    for (index, (tx, _)) in channels.iter().enumerate() {
        let handle = Handle(index as u64 + 1);
        tx.send(
            root(),
            Message::new(handle, vec![(handle, tickets[(index + 1) % COUNT].clone())]),
            &cancel,
        )
        .unwrap();
    }
    assert_eq!(channels[0].1.references().len(), COUNT);
    channels[0].1.close_in_scope(7);
    assert!(channels.iter().all(|(_, rx)| rx.references().is_empty()));
}
