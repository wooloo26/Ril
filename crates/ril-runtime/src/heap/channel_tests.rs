use super::*;
use crate::{
    channel::{self, Context},
    concurrent::TaskOwner,
};

fn tickets(heap: &mut Heap) -> (Handle, Handle) {
    let context = Context {
        owner: TaskOwner::default(),
        lineage: &[7],
    };
    let (_, receiver) = channel::bounded(1, 7, context).unwrap();
    let old = receiver.detach(context).unwrap();
    let fresh = old.reissue(context, context).unwrap();
    (
        heap.allocate(Object::ChannelDetached(old)).unwrap(),
        heap.allocate(Object::ChannelDetached(fresh)).unwrap(),
    )
}

#[test]
fn ticket_replacement_copies_only_affected_ancestors_and_preserves_cycles_and_aliases() {
    let mut heap = Heap::default();
    let (old, fresh) = tickets(&mut heap);
    let scalar = heap.allocate(Object::String("shared".into())).unwrap();
    let shared = heap.allocate(Object::Tuple(vec![scalar])).unwrap();
    let a = heap.allocate(Object::Unit).unwrap();
    let b = heap.allocate(Object::Tuple(vec![a, shared])).unwrap();
    *heap.get_mut(a).unwrap() = Object::Record([("ticket".into(), old), ("next".into(), b)].into());
    let root = heap.allocate(Object::Tuple(vec![a, a, shared])).unwrap();
    let before = heap.live_objects();
    let output = heap
        .replace_ticket_graph(root, &[(old, fresh)].into())
        .unwrap();
    assert_eq!(heap.live_objects(), before + 3);
    let Object::Tuple(values) = heap.get(output).unwrap() else {
        panic!("tuple output");
    };
    assert_eq!(values[0], values[1]);
    assert_eq!(values[2], shared);
    assert_ne!(values[0], a);
    let new_a = values[0];
    let Object::Record(fields) = heap.get(new_a).unwrap() else {
        panic!("record output");
    };
    assert_eq!(fields["ticket"], fresh);
    let Object::Tuple(next) = heap.get(fields["next"]).unwrap() else {
        panic!("cyclic tuple");
    };
    assert_eq!(next.as_slice(), &[new_a, shared]);
    let Object::Record(original) = heap.get(a).unwrap() else {
        panic!("original record");
    };
    assert_eq!(original["ticket"], old);
    heap.collect([output, root]).unwrap();
    assert!(heap.get(fresh).is_ok() && heap.get(old).is_ok());
}

#[test]
fn disconnected_replacements_leave_the_value_graph_unchanged() {
    let mut heap = Heap::default();
    let (old, fresh) = tickets(&mut heap);
    let root = heap.allocate(Object::String("unaffected".into())).unwrap();
    let before = heap.live_objects();
    assert_eq!(
        heap.replace_ticket_graph(root, &[(old, fresh)].into())
            .unwrap(),
        root
    );
    assert_eq!(heap.live_objects(), before);
}

#[test]
fn generic_deep_clone_rejects_channel_authority_even_in_aggregates() {
    let mut heap = Heap::default();
    let context = Context {
        owner: TaskOwner::default(),
        lineage: &[7],
    };
    let (sender, receiver) = channel::bounded(1, 7, context).unwrap();
    let ticket = receiver.detach(context).unwrap();
    for descriptor in [
        Object::ChannelSender(sender),
        Object::ChannelReceiver(receiver),
        Object::ChannelDetached(ticket),
    ] {
        let descriptor = heap.allocate(descriptor).unwrap();
        let aggregate = heap
            .allocate(Object::Tuple(vec![descriptor, descriptor]))
            .unwrap();
        let before = heap.live_objects();
        assert_eq!(heap.deep_clone(descriptor), Err(HeapError::NonClonable));
        assert_eq!(heap.deep_clone(aggregate), Err(HeapError::NonClonable));
        assert_eq!(heap.live_objects(), before);
    }
}

#[test]
fn gc_follows_channel_receipts_until_the_received_value_is_published() {
    let mut heap = Heap::default();
    let context = Context {
        owner: TaskOwner::default(),
        lineage: &[7],
    };
    let (sender, receiver) = channel::bounded(1, 7, context).unwrap();
    let descriptor = heap
        .allocate(Object::ChannelReceiver(receiver.clone()))
        .unwrap();
    let payload = heap.allocate(Object::String("in flight".into())).unwrap();
    sender
        .send(
            context,
            channel::Message::new(payload, vec![]),
            &crate::process_io::Cancellation::default(),
        )
        .unwrap();
    heap.collect([descriptor]).unwrap();
    let receipt = receiver
        .recv(context, &crate::process_io::Cancellation::default())
        .unwrap()
        .unwrap();
    heap.collect([descriptor]).unwrap();
    assert!(heap.get(payload).is_ok());
    let result = heap
        .allocate(Object::Variant {
            tag: "Ok".into(),
            fields: vec![receipt.value()],
        })
        .unwrap();
    receipt.ack();
    heap.collect([descriptor, result]).unwrap();
    assert!(heap.get(payload).is_ok());
    heap.collect([descriptor]).unwrap();
    assert_eq!(heap.get(payload), Err(HeapError::InvalidHandle));
}
