use super::*;
use crate::{
    concurrent::{Scope, TaskOwner},
    process_io::Cancellation,
};

fn runtime() -> Runtime {
    let mut runtime = Runtime::default();
    let scope = Scope::new(&runtime.cancellation).unwrap();
    runtime.scope_lineage.push(scope.id());
    runtime.scope_registry.push(scope);
    runtime
}
fn endpoints(runtime: &mut Runtime) -> (Handle, Handle) {
    let pair = runtime.create_channel(2).unwrap();
    let values = runtime.sequence(pair).unwrap();
    (values[0], values[1])
}
fn detach(runtime: &mut Runtime, endpoint: Handle) -> Handle {
    let ticket = runtime
        .channel_endpoint(endpoint)
        .unwrap()
        .detach(runtime.channel_context())
        .unwrap();
    runtime.allocate_channel_ticket(ticket).unwrap()
}

#[test]
fn capture_scan_does_not_transfer_tickets_hidden_in_an_opaque_channel_queue() {
    let mut runtime = runtime();
    let (control, _) = endpoints(&mut runtime);
    let (_, payload) = endpoints(&mut runtime);
    let ticket = detach(&mut runtime, payload);
    let message = channel::Message::new(ticket, runtime.channel_tickets(ticket).unwrap());
    let Object::ChannelSender(sender) = runtime.heap.get(control).unwrap() else {
        panic!("sender");
    };
    sender
        .send(runtime.channel_context(), message, &Cancellation::default())
        .unwrap();
    let cell = runtime.allocate(Object::Cell(control)).unwrap();
    let environment = runtime
        .allocate(Object::Record([("clone_source".into(), cell)].into()))
        .unwrap();
    let action = runtime
        .allocate(Object::Closure {
            function: 1,
            environment,
        })
        .unwrap();
    assert!(runtime.channel_tickets(action).unwrap().is_empty());
    let target = TaskOwner {
        scope: runtime.scope_lineage[0],
        ordinal: 1,
    };
    let lineage = runtime.scope_lineage.clone();
    assert!(
        runtime
            .transfer_captured_tickets(
                action,
                Context {
                    owner: target,
                    lineage: &lineage
                }
            )
            .unwrap()
            .is_empty()
    );
}

#[test]
fn capture_transfer_deduplicates_authority_across_distinct_managed_alias_handles() {
    let mut runtime = runtime();
    let (_, receiver) = endpoints(&mut runtime);
    let ticket = detach(&mut runtime, receiver);
    let Object::ChannelDetached(descriptor) = runtime.heap.get(ticket).unwrap().clone() else {
        panic!("ticket");
    };
    let alias = runtime
        .allocate(Object::ChannelDetached(descriptor.clone()))
        .unwrap();
    let root = runtime
        .allocate(Object::Tuple(vec![ticket, alias]))
        .unwrap();
    let target = TaskOwner {
        scope: runtime.scope_lineage[0],
        ordinal: 1,
    };
    let lineage = runtime.scope_lineage.clone();
    assert_eq!(
        runtime
            .transfer_captured_tickets(
                root,
                Context {
                    owner: target,
                    lineage: &lineage
                }
            )
            .unwrap()
            .len(),
        2
    );
    assert!(descriptor.attach(runtime.channel_context()).is_err());
    descriptor
        .attach(Context {
            owner: target,
            lineage: &lineage,
        })
        .unwrap();
}

#[test]
fn returned_ticket_graph_keeps_unaffected_children_and_never_revives_parent_aliases() {
    let mut runtime = runtime();
    let (_, receiver) = endpoints(&mut runtime);
    let original = detach(&mut runtime, receiver);
    let Object::ChannelDetached(ticket) = runtime.heap.get(original).unwrap().clone() else {
        panic!("ticket");
    };
    let parent = runtime.task_owner;
    let child = TaskOwner {
        scope: runtime.scope_lineage[0],
        ordinal: 1,
    };
    let lineage = runtime.scope_lineage.clone();
    ticket
        .transfer_owner(
            parent,
            Context {
                owner: child,
                lineage: &lineage,
            },
        )
        .unwrap();
    runtime.task_owner = child;
    let shared = runtime.allocate(Object::Record(BTreeMap::new())).unwrap();
    let root = runtime
        .allocate(Object::Tuple(vec![original, original, shared]))
        .unwrap();
    let returned = runtime
        .reissue_returned_tickets(
            root,
            Context {
                owner: parent,
                lineage: &lineage,
            },
        )
        .unwrap();
    let values = runtime.sequence(returned).unwrap();
    assert_eq!(values[0], values[1]);
    assert_ne!(values[0], original);
    assert_eq!(values[2], shared);
    assert_eq!(runtime.sequence(root).unwrap()[0], original);
    assert!(
        ticket
            .attach(Context {
                owner: parent,
                lineage: &lineage
            })
            .is_err()
    );
    runtime.task_owner = parent;
    runtime.adopt_received_tickets(returned).unwrap();
    runtime.root(1, returned).unwrap();
    runtime.statement_end();
    for _ in 0..1500 {
        runtime.string("garbage".into()).unwrap();
        runtime.statement_end();
    }
    assert!(runtime.heap.get(values[0]).is_ok());
    let Object::ChannelDetached(ticket) = runtime.heap.get(values[0]).unwrap() else {
        panic!("fresh ticket");
    };
    ticket.attach(runtime.channel_context()).unwrap();
}

#[test]
fn cloning_sender_registers_new_local_authority_and_generic_copy_remains_forbidden() {
    let mut runtime = runtime();
    let (sender, _) = endpoints(&mut runtime);
    let clone = runtime.clone_channel_sender(sender).unwrap().unwrap();
    assert_ne!(clone, sender);
    assert_eq!(runtime.owned_endpoints.len(), 3);
    assert!(runtime.copy(sender).is_err());
    let value = runtime.int(4).unwrap();
    assert!(runtime.clone_channel_sender(value).unwrap().is_none());
}
