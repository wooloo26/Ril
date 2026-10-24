use ril_compiler::{
    CheckOptions, Session,
    sema::application_effect::{EntryOrigin, InputOrigin},
};

#[test]
fn concurrency_fault_payloads_keep_their_catalog_declarations_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes(
                "tests/regressions/generated-scopes.ril::scope-fault-declarations",
            )
            .to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn physical_scope_tokens_reach_inferred_callback_parameters() {
    for target in ["pointer32", "pointer64"] {
        for case in ["scope-token", "repeated-scope-token"] {
            let program = Session::with_options(
                ril_test::case_bytes(&format!("tests/regressions/generated-scopes.ril::{case}"))
                    .to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
            let _core = ril_compiler::lower::lower_core(&program).unwrap();
            let _facts = program.facts();
        }
    }
}

#[test]
fn scope_token_receipts_cannot_borrow_another_application_or_lifetime() {
    use ril_compiler::sema::{SemanticFacts, validate::solved_facts};
    use std::sync::Arc;
    let program = Session::new(
        ril_test::case_bytes("tests/regressions/generated-scopes.ril::repeated-scope-token")
            .to_vec(),
    )
    .verify()
    .unwrap();
    let facts = program.facts();
    let entries: Vec<_> = facts
        .closure_invocations
        .iter()
        .enumerate()
        .filter_map(|(ordinal, call)| {
            if let EntryOrigin::Generated { inputs, .. } = &call.entry.origin
                && let [InputOrigin::Scope(index)] = inputs.as_slice()
            {
                Some((ordinal, *index as usize))
            } else {
                None
            }
        })
        .collect();
    assert!(entries.len() >= 2);
    let (first, first_boundary) = entries[0];
    let (other, other_boundary) = entries[1];
    let original = facts.concurrent_boundaries[first_boundary]
        .input
        .as_ref()
        .unwrap();
    let replacement = facts.concurrent_boundaries[other_boundary]
        .input
        .as_ref()
        .unwrap();
    assert_ne!(original.application, replacement.application);
    assert_ne!(original.anchor, replacement.anchor);
    for mutation in 0..15 {
        let mut changed: SemanticFacts = facts.clone();
        match mutation {
            0 => changed.concurrent_boundaries[first_boundary].input = None,
            1 => changed.concurrent_boundaries[first_boundary].input = Some(replacement.clone()),
            2 => {
                changed.concurrent_boundaries[first_boundary]
                    .input
                    .as_mut()
                    .unwrap()
                    .application = replacement.application
            }
            3 => {
                changed.concurrent_boundaries[first_boundary]
                    .input
                    .as_mut()
                    .unwrap()
                    .anchor = replacement.anchor
            }
            4 => {
                changed.concurrent_boundaries[first_boundary]
                    .input
                    .as_mut()
                    .unwrap()
                    .node = ril_compiler::sema::facts::NodeId(u32::MAX)
            }
            5 => {
                changed.concurrent_boundaries[first_boundary]
                    .input
                    .as_mut()
                    .unwrap()
                    .allocation_epoch = usize::MAX
            }
            6 => {
                changed.concurrent_boundaries[first_boundary]
                    .input
                    .as_mut()
                    .unwrap()
                    .cause = ril_compiler_core::diagnostic::CauseId(u32::MAX)
            }
            7 => {
                changed.concurrent_boundaries[first_boundary].scope =
                    ril_compiler::sema::facts::NodeId(u32::MAX)
            }
            8 => {
                changed.closure_invocations[first].entry.arguments =
                    changed.closure_invocations[other].entry.arguments.clone()
            }
            9 => {
                changed.closure_invocations[first].entry.origin =
                    changed.closure_invocations[other].entry.origin.clone()
            }
            10 => {
                Arc::make_mut(&mut changed.closure_invocations[first].entry.arguments)[0].mode =
                    ril_syntax::ast::ParameterMode::Read
            }
            11 => {
                Arc::make_mut(&mut changed.closure_invocations[first].entry.arguments)[0].heap =
                    None
            }
            12 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.closure_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                inputs[0] = InputOrigin::Scope(other_boundary as u32);
            }
            13 => changed.closure_invocations[first].entry.origin = EntryOrigin::Unresolved,
            14 => {
                changed.concurrent_boundaries[first_boundary].kind =
                    ril_compiler::sema::ConcurrentBoundaryKind::Fork
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "scope input mutation {mutation} was accepted"
        );
    }
}
