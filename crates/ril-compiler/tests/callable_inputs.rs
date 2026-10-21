use ril_compiler::sema::application_effect::{EntryOrigin, InputOrigin};
use ril_compiler::{CheckOptions, Session, sema::validate::solved_facts};

fn verified(name: &str, layout: &str) -> ril_compiler::hir::VerifiedProgram {
    let source = ril_test::case_source(&format!("tests/regressions/callable-inputs.ril::{name}"));
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{name} {layout}: {outcome:?}"))
}

#[test]
fn original_inputs_cross_ordinary_and_generated_callable_entries_on_both_layouts() {
    for layout in ["pointer32", "pointer64"] {
        for name in [
            "inferred-fixed-input",
            "derive-clone-view",
            "derive-repeated-activation",
            "derive-construction",
            "derive-nested-fixed-input",
            "derive-named-construction",
            "derive-named-repeated-activation",
        ] {
            let program = verified(name, layout);
            let core = ril_compiler::lower::lower_core(&program).unwrap();
            assert_eq!(
                core.provenance.activations.len(),
                program.facts().activations.len()
            );
            assert_eq!(
                core.provenance.closure_invocations.len(),
                program.facts().closure_invocations.len()
            );
            assert_eq!(
                core.provenance.copy_invocations.len(),
                program.facts().copy_invocations.len()
            );
        }
    }
}

#[test]
fn generated_input_cannot_borrow_another_occurrence_copy_or_loan() {
    let program = verified("derive-repeated-activation", "pointer64");
    let facts = program.facts();
    let candidates: Vec<_> = facts
        .closure_invocations
        .iter()
        .enumerate()
        .filter(|(_, call)| matches!(call.entry.origin, EntryOrigin::Generated { .. }))
        .map(|(index, _)| index)
        .collect();
    assert!(candidates.len() >= 2);
    let (first, other) = (candidates[0], candidates[1]);
    for mutation in 0..11 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.closure_invocations[first].entry.arguments = std::sync::Arc::new(vec![]),
            1 => changed.closure_invocations[first].entry.origin = EntryOrigin::Unresolved,
            2 => {
                changed.closure_invocations[first].entry.parent =
                    changed.closure_invocations[other].entry.parent
            }
            3 => changed.closure_invocations[first].entry.allocation_epoch = usize::MAX,
            4 => {
                changed.closure_invocations[first].entry.origin =
                    changed.closure_invocations[other].entry.origin.clone()
            }
            5 => {
                let replacement = changed.closure_invocations[other].entry.origin.clone();
                let EntryOrigin::Generated {
                    callee: replacement,
                    ..
                } = replacement
                else {
                    unreachable!()
                };
                let EntryOrigin::Generated { callee, .. } =
                    &mut changed.closure_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                *callee = replacement;
            }
            6 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.closure_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                let InputOrigin::Copied { boundary, .. } = &mut inputs[0] else {
                    unreachable!()
                };
                boundary.0 = u32::MAX;
            }
            7 => {
                let InputOrigin::Copied { boundary, .. } =
                    (match &changed.closure_invocations[first].entry.origin {
                        EntryOrigin::Generated { inputs, .. } => &inputs[0],
                        _ => unreachable!(),
                    })
                else {
                    unreachable!()
                };
                changed.copy_boundaries[boundary.0 as usize].output_allocation_epoch = None;
            }
            8 => {
                let id = changed.closure_invocations[first].id;
                let loan = changed
                    .invocation_loan_starts
                    .iter_mut()
                    .find(|loan| loan.closure == Some(id))
                    .unwrap();
                loan.bindings.clear();
            }
            9 => {
                std::sync::Arc::make_mut(&mut changed.closure_invocations[first].entry.arguments)
                    [0]
                .1
                .permission = ril_compiler::sema::facts::Permission::Read
            }
            10 => {
                changed.closure_invocations[first].entry =
                    changed.closure_invocations[other].entry.clone()
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "generated input mutation {mutation}"
        );
    }
}

#[test]
fn named_generated_input_retains_its_actual_target_body_and_copy() {
    let program = verified("derive-named-repeated-activation", "pointer64");
    let facts = program.facts();
    let candidates: Vec<_> = facts
        .copy_invocations
        .iter()
        .enumerate()
        .filter(|(_, call)| matches!(call.entry.origin, EntryOrigin::Generated { .. }))
        .map(|(index, _)| index)
        .collect();
    assert!(candidates.len() >= 2);
    let (first, other) = (candidates[0], candidates[1]);
    for mutation in 0..15 {
        let mut changed = facts.clone();
        let id = changed.copy_invocations[first].id;
        match mutation {
            0 => changed.copy_invocations[first].entry.arguments.clear(),
            1 => changed.copy_invocations[first].entry.origin = EntryOrigin::Unresolved,
            2 => {
                changed.copy_invocations[first].entry.parent =
                    changed.copy_invocations[other].entry.parent
            }
            3 => changed.copy_invocations[first].entry.allocation_epoch = usize::MAX,
            4 => {
                changed.copy_invocations[first].entry.origin =
                    changed.copy_invocations[other].entry.origin.clone()
            }
            5 => {
                let EntryOrigin::Generated {
                    callee: replacement,
                    ..
                } = changed.copy_invocations[other].entry.origin
                else {
                    unreachable!()
                };
                let EntryOrigin::Generated { callee, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                *callee = replacement;
            }
            6 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                let InputOrigin::Copied { boundary, .. } = &mut inputs[0] else {
                    unreachable!()
                };
                boundary.0 = u32::MAX;
            }
            7 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                let InputOrigin::Copied { boundary, .. } = inputs[0] else {
                    unreachable!()
                };
                changed.copy_boundaries[boundary.0 as usize].output_allocation_epoch = None;
            }
            8 => changed.copy_invocations[first].entry.caller_context.owner = None,
            9 => {
                changed.copy_invocations[first].entry.arguments[0].0 =
                    ril_compiler::sema::model::Mode::Read
            }
            10 => {
                changed.copy_invocations[first].entry =
                    changed.copy_invocations[other].entry.clone()
            }
            11 => {
                changed
                    .invocation_calls
                    .iter_mut()
                    .find(|row| row.invocation == id)
                    .unwrap()
                    .caller_owner = None
            }
            12 => changed.invocations.retain(|summary| {
                summary
                    .context
                    .is_none_or(|context| context.invocation != Some(id))
            }),
            13 => changed.copy_invocations[first].entry.arguments[0]
                .1
                .value
                .origins
                .nodes
                .clear(),
            14 => {
                changed.copy_invocations.remove(first);
            }
            _ => unreachable!(),
        };
        assert!(
            solved_facts(&changed).is_err(),
            "named generated input mutation {mutation}"
        );
    }
}

#[test]
fn original_dimensions_permissions_and_draft_escape_rules_still_reject() {
    for layout in ["pointer32", "pointer64"] {
        for (name, code) in [
            ("derive-nested-dimension-mismatch", "E0301"),
            ("inferred-read-cannot-write", "E0520"),
            ("derive-live-input", "E0536"),
            ("derive-draft-escape", "E0607"),
            ("derive-named-dimension-mismatch", "E0301"),
            ("derive-copy-cannot-reopen-construction", "E0301"),
            ("derive-named-draft-escape", "E0607"),
        ] {
            let source =
                ril_test::case_source(&format!("tests/regressions/callable-inputs.ril::{name}"));
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, ril_compiler::CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{name} {layout}: {outcome:?}"
            );
        }
    }
}
