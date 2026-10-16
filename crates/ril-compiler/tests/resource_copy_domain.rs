use ril_compiler::{
    Session,
    sema::{
        copy_contract::*,
        facts::{Multiplicity, NodeId},
        resource_copy::*,
    },
};

fn facts() -> ril_compiler::sema::SemanticFacts {
    let source = "use ril/concurrent/channel\nfn duplicate(tx:Channel::Sender<int>)->Channel::Sender<int> @Fiber{clone(tx)}";
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap()
        .facts()
        .clone()
}

fn contract(facts: &ril_compiler::sema::SemanticFacts, event: &ResourceCloneEvent) -> bool {
    let Some(call) = event
        .invocation
        .and_then(|id| facts.copy_invocations.get(id.0 as usize))
    else {
        return false;
    };
    let Some(syntax) = event
        .source_event
        .and_then(|id| facts.copy_call_events.get(id.0 as usize))
    else {
        return false;
    };
    sender_contract(event, call, syntax)
}

#[test]
fn formal_sender_uses_its_resource_anchor_without_ordinary_copy_authority() {
    let facts = facts();
    assert_eq!(facts.resource_clones.len(), 1);
    let event = &facts.resource_clones[0];
    assert!(contract(&facts, event));
    assert!(facts.copy_boundaries.is_empty());
    assert!(matches!(
        event.channel,
        Some(ResourceChannel::FromSourceDescriptor(_))
    ));
    assert!(event.source_descriptor.as_ref().unwrap().formal);
}

#[test]
fn concrete_endpoint_model_keeps_channel_and_owner_without_graph_isolation() {
    let facts = facts();
    let base = &facts.resource_clones[0];
    // Concrete oracle: an endpoint is a descriptor with a channel identity and
    // a task owner. Cloning preserves the channel, creates another descriptor,
    // and assigns the executing task. The source owner is not that task.
    for source_channel in 1..=2 {
        for output_channel in 1..=2 {
            for source_task in 1..=2 {
                for current_task in 1..=2 {
                    for output_task in 1..=2 {
                        let mut event = base.clone();
                        let source = event.source_descriptor.as_mut().unwrap();
                        source.channel = Some(NodeId(100 + source_channel));
                        source.task = Some(NodeId(200 + source_task));
                        let output = event.output_descriptor.as_mut().unwrap();
                        output.channel = Some(NodeId(100 + output_channel));
                        output.task = Some(NodeId(200 + output_task));
                        event.channel = Some(ResourceChannel::Known(NodeId(100 + source_channel)));
                        event.boundary.as_mut().unwrap().task = Some(NodeId(200 + current_task));
                        let prototype = event.anchors[0].clone();
                        for node in [
                            100 + source_channel,
                            100 + output_channel,
                            200 + source_task,
                            200 + current_task,
                            200 + output_task,
                        ] {
                            let mut fact = prototype.clone();
                            fact.origin = NodeId(node);
                            event.anchors.push(fact);
                        }
                        let expected =
                            source_channel == output_channel && current_task == output_task;
                        assert_eq!(contract(&facts, &event), expected);
                    }
                }
            }
        }
    }
}

#[test]
fn incomplete_mutated_and_foreign_invocation_witnesses_cannot_authorize_a_clone() {
    let facts = facts();
    let original = &facts.resource_clones[0];
    for mutate in [
        (|event: &mut ResourceCloneEvent| event.boundary = None) as fn(&mut ResourceCloneEvent),
        |event| event.source_event = None,
        |event| event.effect_registered = false,
        |event| event.source_descriptor = None,
        |event| event.output_descriptor = None,
        |event| event.channel = None,
        |event| {
            event.output_descriptor.as_mut().unwrap().origin =
                event.source_descriptor.as_ref().unwrap().origin
        },
        |event| event.output_descriptor.as_mut().unwrap().scope = NodeId(u32::MAX),
        |event| event.source.nodes[0].fact.multiplicity = Multiplicity::MayMany,
        |event| {
            event.source.value.pending_copies.insert(CopyBoundaryId(0));
        },
    ] {
        let mut event = original.clone();
        mutate(&mut event);
        assert!(!contract(&facts, &event), "{event:?}");
    }
    let call = &facts.copy_invocations[original.invocation.unwrap().0 as usize];
    let syntax = &facts.copy_call_events[original.source_event.unwrap().0 as usize];
    let mut failed = call.clone();
    failed.status = CopyInvocationStatus::Rejected;
    assert!(!sender_contract(original, &failed, syntax));
    failed.status = CopyInvocationStatus::Unsupported;
    assert!(!sender_contract(original, &failed, syntax));
    let mut wrong_operation = syntax.clone();
    wrong_operation.copy_operation = Some(CopyMode::Immutable);
    assert!(!sender_contract(original, call, &wrong_operation));
    wrong_operation = syntax.clone();
    wrong_operation.parent = None;
    assert!(!sender_contract(original, call, &wrong_operation));
}

#[test]
fn a_childs_clone_of_an_ancestor_sender_keeps_the_checked_scope_contract() {
    let source = r#"
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel
fn duplicate(tx:Channel::Sender<int>)->Channel::Sender<int> @Fiber{clone(tx)}
fn example() @Async{
    let result=scope \mut s -> {
        let (tx,rx)=Channel::bounded<int>(1)
        let child=s.fork(\->{let own=duplicate(tx);Channel::close(own)})
        child.join()?
        Channel::close(tx)
        Channel::close(rx)
        Ok()
    }
    assert(result is Ok())
}
"#;
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let events: Vec<_> = facts
        .resource_clones
        .iter()
        .filter(|event| {
            event
                .source_descriptor
                .as_ref()
                .zip(event.output_descriptor.as_ref())
                .is_some_and(|(source, output)| !source.formal && source.task != output.task)
        })
        .collect();
    assert!(!events.is_empty());
    for event in events {
        assert!(contract(facts, event));
    }
}
