use ril_compiler::{
    CheckOptions, Session,
    sema::{SemanticFacts, validate::solved_facts},
};
use std::sync::Arc;

fn verified(case: &str, target: &str) -> ril_compiler::hir::VerifiedProgram {
    let program = Session::with_options(
        ril_test::case_bytes(case).to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{case}/{target}: {error:?}"));
    ril_compiler::lower::lower_core(&program).unwrap();
    program
}

#[test]
fn repeated_equal_results_keep_their_actual_application_occurrences() {
    for target in ["pointer32", "pointer64"] {
        let program = verified(
            "tests/regressions/application-results.ril::repeated-closure-results",
            target,
        );
        let facts = program.facts();
        let pair = facts
            .copy_call_events
            .iter()
            .enumerate()
            .find_map(|(index, left)| {
                let left_root = left.result_expression?;
                facts.copy_call_events[index + 1..]
                    .iter()
                    .find_map(|right| {
                        let right_root = right.result_expression?;
                        (left.source_id.is_some()
                            && left.source_id == right.source_id
                            && left.owner == right.owner
                            && left.parent == right.parent
                            && facts.expressions[left_root].value.cause
                                == facts.expressions[right_root].value.cause)
                            .then_some((left.id, right.id, left_root, right_root))
                    })
            })
            .expect("repeated applications with equal causes and partial caller coordinates");
        assert_ne!(pair.2, pair.3);
        assert_ne!(
            facts.evaluations[pair.2].identity,
            facts.evaluations[pair.3].identity
        );
        let mut changed = facts.clone();
        changed.copy_call_events[pair.1.0 as usize].result_expression = Some(pair.2);
        assert!(
            solved_facts(&changed).is_err(),
            "another equal result cannot certify this call"
        );
    }
}

fn closure_defaults(facts: &SemanticFacts) -> Vec<usize> {
    facts
        .default_uses
        .iter()
        .enumerate()
        .filter_map(|(index, default)| {
            (matches!(
                default.owner,
                Some(ril_compiler_core::ids::CallableOwner::Lambda(_))
            ) && default.target.is_none()
                && matches!(
                    default.origin,
                    ril_compiler::sema::default_uses::DefaultOrigin::Call(_)
                )
                && default.evaluation_complete)
                .then_some(index)
        })
        .collect()
}

#[test]
fn closure_defaults_keep_preparation_declarations_and_actual_entry_packets_separate() {
    for target in ["pointer32", "pointer64"] {
        verified(
            "tests/regressions/application-results.ril::early-formal-default",
            target,
        );
        let program = verified(
            "tests/regressions/nested-closures.ril::nested-default-environments-pointer64",
            target,
        );
        let facts = program.facts();
        let defaults = closure_defaults(facts);
        assert!(defaults.len() >= 2);
        let mut entries = Vec::new();
        for &index in &defaults {
            let default = &facts.default_uses[index];
            let root = default.result_expression.unwrap();
            let evaluation = &facts.evaluations[root];
            assert_eq!(evaluation.context.default_use, Some(default.id));
            assert_eq!(
                evaluation.context.closure_invocation,
                default.caller.closure_invocation
            );
            assert!(
                default.entered.is_empty(),
                "a closure default must not invent a named entry"
            );
            assert!(facts.bindings.iter().any(|binding| binding.parameter
                && binding.owner == evaluation.scope
                && binding.context.owner == default.owner
                && binding.context.closure_invocation == default.caller.closure_invocation));
            let call = facts
                .closure_invocations
                .iter()
                .enumerate()
                .find(|(_, call)| {
                    call.entry.caller_context == default.caller
                        && call
                            .entry
                            .arguments
                            .get(default.parameter as usize)
                            .is_some_and(|argument| {
                                argument.packet.birth_coordinates().observation == Some(root)
                            })
                })
                .expect("the actual body entry must use this default's packet");
            assert_ne!(Some(call.1.id), evaluation.context.closure_invocation);
            entries.push((call.0, default.parameter as usize));
        }
        let mut changed = facts.clone();
        let replacement = facts.closure_invocations[entries[0].0].entry.arguments[entries[0].1]
            .packet
            .clone();
        Arc::make_mut(&mut changed.closure_invocations[entries[1].0].entry.arguments)
            [entries[1].1]
            .packet = replacement;
        assert!(
            solved_facts(&changed).is_err(),
            "equal-type defaults cannot exchange their births"
        );
        let mut changed = facts.clone();
        changed.default_uses[defaults[0]].parameter = 0;
        assert!(
            solved_facts(&changed).is_err(),
            "a default cannot authorize a later formal"
        );
    }
}

#[test]
fn abrupt_defaults_keep_their_prefix_without_inventing_a_body_entry() {
    for target in ["pointer32", "pointer64"] {
        let program = verified(
            "tests/regressions/application-results.ril::early-formal-before-abrupt-default",
            target,
        );
        let facts = program.facts();
        let default = facts
            .default_uses
            .iter()
            .find(|default| {
                matches!(
                    default.owner,
                    Some(ril_compiler_core::ids::CallableOwner::Lambda(_))
                ) && !default.evaluation_complete
                    && matches!(
                        default.origin,
                        ril_compiler::sema::default_uses::DefaultOrigin::Call(_)
                    )
            })
            .expect("an actually evaluated abrupt lambda default");
        let ril_compiler::sema::default_uses::DefaultOrigin::Call(event) = default.origin else {
            unreachable!()
        };
        let root = default.result_expression.unwrap();
        assert_eq!(
            facts.evaluations[root].context.default_use,
            Some(default.id)
        );
        assert!(facts.bindings.iter().any(
            |binding| binding.name == "seen" && binding.owner == facts.evaluations[root].scope
        ));
        assert!(!facts.closure_invocations.iter().any(|call|
            matches!(call.entry.origin, ril_compiler::sema::application_effect::EntryOrigin::Application(actual) if actual == event)));
        assert!(default.entered.is_empty());
    }
}
