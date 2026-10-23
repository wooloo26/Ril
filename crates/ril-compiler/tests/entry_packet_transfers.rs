use ril_compiler::{
    CheckOptions, Session,
    sema::{SemanticFacts, default_uses::ArgumentSource, validate::solved_facts},
};
use std::{collections::BTreeMap, sync::Arc};

fn assert_physical_birth(facts: &SemanticFacts, packet: &ril_compiler::sema::EvaluatedValue) {
    let birth = packet.birth_coordinates();
    let observation = birth
        .observation
        .expect("an actual written/default input has a physical birth");
    let record = &facts.evaluations[observation];
    assert_eq!(birth.identity, record.identity);
    assert_eq!(birth.context, Some(record.context));
    assert_eq!(birth.allocation_epoch, record.allocation_epoch);
    assert!(birth.environment.is_some());
    assert_eq!(birth.environment, record.environment);
}

fn verified(case: &str, layout: &str) -> SemanticFacts {
    let source = ril_test::case_source(&format!(
        "tests/regressions/evaluation-identity.ril::{case}"
    ));
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{case}/{layout}: {error:?}"));
    solved_facts(program.facts()).unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn actual_targets_keep_the_same_birth_after_an_earlier_target_allocates() {
    for layout in ["pointer32", "pointer64"] {
        let facts = verified("entry-packets-across-allocating-targets", layout);
        let mut events = BTreeMap::<_, Vec<_>>::new();
        for (index, call) in facts.copy_invocations.iter().enumerate() {
            if let Some(event) = call.source_event {
                events.entry(event).or_default().push(index);
            }
        }
        let pair = events
            .values()
            .find_map(|indices| {
                for &left in indices {
                    for &right in indices {
                        let (before, after) = (
                            &facts.copy_invocations[left],
                            &facts.copy_invocations[right],
                        );
                        if before.target != after.target
                            && before.entry.arguments.len() == 1
                            && after.entry.arguments.len() == 1
                            && before.entry.allocation_epoch < after.entry.allocation_epoch
                            && before.entry.arguments[0]
                                .packet
                                .birth_coordinates()
                                .identity
                                .is_some()
                        {
                            return Some((left, right));
                        }
                    }
                }
                None
            })
            .expect("a real joined callee must enter two targets across allocation recency");
        let (before, after) = (
            &facts.copy_invocations[pair.0],
            &facts.copy_invocations[pair.1],
        );
        let (original, transported) = (&before.entry.arguments[0], &after.entry.arguments[0]);
        let event = &facts.copy_call_events[before.source_event.unwrap().0 as usize];
        let callee = &facts.expressions[event.callee_expression.unwrap()].value;
        let targets: Vec<_> = callee
            .callables
            .iter()
            .filter_map(|callable| {
                let ril_compiler::sema::model::Callable::Named(index) = callable else {
                    return None;
                };
                Some(facts.functions[*index].definition)
            })
            .collect();
        assert!(
            targets.contains(&before.target) && targets.contains(&after.target),
            "the physical callee must really contain both targets"
        );
        assert_eq!(
            original.packet.birth_coordinates(),
            transported.packet.birth_coordinates()
        );
        assert_ne!(original.value().origins, transported.value().origins);
        assert!(
            facts.allocation_history[before.entry.allocation_epoch..after.entry.allocation_epoch]
                .iter()
                .any(
                    |(recent, older)| original.value().origins.nodes.contains(recent)
                        && transported.value().origins.nodes.contains(older)
                ),
            "the earlier target must promote the very allocation carried by the input"
        );
        assert_eq!(
            original.packet.current_epoch(),
            before.entry.allocation_epoch
        );
        assert_eq!(
            transported.packet.current_epoch(),
            after.entry.allocation_epoch
        );
        for call in [before, after] {
            let argument = &call.entry.arguments[0];
            assert_physical_birth(&facts, &argument.packet);
            assert_physical_birth(&facts, call.entry.callee.as_ref().unwrap());
            assert_eq!(
                argument.heap.as_ref().unwrap().allocation_epoch,
                call.entry.allocation_epoch
            );
            assert!(!argument.heap.as_ref().unwrap().nodes.is_empty());
            assert_eq!(
                call.entry.callee.as_ref().unwrap().current_epoch(),
                call.entry.allocation_epoch
            );
        }
        let mut changed = facts.clone();
        Arc::make_mut(&mut changed.copy_invocations[pair.1].entry.arguments)[0].packet =
            original.packet.clone();
        assert!(
            solved_facts(&changed).is_err(),
            "a later target borrowed an earlier target's current packet"
        );
        let mut changed = facts.clone();
        Arc::make_mut(&mut changed.copy_invocations[pair.1].entry.arguments)[0].heap =
            original.heap.clone();
        assert!(
            solved_facts(&changed).is_err(),
            "a later target borrowed an earlier epoch's heap"
        );
    }
}

#[test]
fn an_allocating_default_preserves_both_original_input_births() {
    for layout in ["pointer32", "pointer64"] {
        let facts = verified("entry-packets-after-allocating-default", layout);
        let (index, receipt) = facts
            .copy_invocations
            .iter()
            .enumerate()
            .find_map(|(index, call)| {
                let event = call.source_event?;
                let row = facts
                    .call_arguments
                    .iter()
                    .find(|row| row.source_event == event)?;
                match row.slots.as_slice() {
                    [ArgumentSource::Supplied, ArgumentSource::Default(receipt)] => {
                        Some((index, *receipt))
                    }
                    _ => None,
                }
            })
            .expect("the real application must evaluate its omitted second parameter");
        let call = &facts.copy_invocations[index];
        let explicit = &call.entry.arguments[0];
        let default = &call.entry.arguments[1];
        let birth = explicit.packet.birth_coordinates();
        let default_birth = default.packet.birth_coordinates();
        assert!(birth.allocation_epoch < call.entry.allocation_epoch);
        let physical = &facts.expressions[birth.observation.unwrap()].value;
        assert!(
            facts.allocation_history[birth.allocation_epoch..call.entry.allocation_epoch]
                .iter()
                .any(|(recent, older)| physical.origins.nodes.contains(recent)
                    && explicit.value().origins.nodes.contains(older)),
            "the default must promote the supplied input's actual allocation site"
        );
        assert_eq!(
            default_birth.observation,
            facts.default_uses[receipt.0 as usize].result_expression
        );
        assert_eq!(default_birth.context.unwrap().default_use, Some(receipt));
        assert_ne!(birth.identity, default_birth.identity);
        for argument in &*call.entry.arguments {
            assert_physical_birth(&facts, &argument.packet);
            assert_eq!(argument.packet.current_epoch(), call.entry.allocation_epoch);
            assert_eq!(
                argument.heap.as_ref().unwrap().allocation_epoch,
                call.entry.allocation_epoch
            );
        }
        let mut changed = facts.clone();
        Arc::make_mut(&mut changed.copy_invocations[index].entry.arguments)[0].packet =
            default.packet.clone();
        assert!(
            solved_facts(&changed).is_err(),
            "a supplied input borrowed the default's physical birth"
        );
        let mut changed = facts.clone();
        Arc::make_mut(&mut changed.copy_invocations[index].entry.arguments)[0].heap =
            default.heap.clone();
        assert!(
            solved_facts(&changed).is_err(),
            "a supplied input borrowed the default's heap graph"
        );
    }
}
