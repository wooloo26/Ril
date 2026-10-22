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

fn assert_generated_origin_retained(
    original: &EntryOrigin,
    retained: &ril_ir::provenance::EntryOrigin,
) {
    use ril_ir::provenance as core;
    let EntryOrigin::Generated {
        anchor,
        callee,
        inputs,
    } = original
    else {
        panic!("expected actual generated entry")
    };
    let core::EntryOrigin::Generated {
        anchor: retained_anchor,
        callee: retained_callee,
        inputs: retained_inputs,
    } = retained
    else {
        panic!("Core lost generated origin")
    };
    assert_eq!(anchor, retained_anchor);
    assert_eq!(callee, retained_callee);
    assert_eq!(inputs.len(), retained_inputs.len());
    for (input, retained) in inputs.iter().zip(retained_inputs) {
        match (input, retained) {
            (InputOrigin::Observed(value), core::InputOrigin::Observed(retained))
            | (InputOrigin::Widened(value), core::InputOrigin::Widened(retained)) => {
                assert_eq!(value, retained)
            }
            (
                InputOrigin::Copied {
                    observation,
                    boundary,
                },
                core::InputOrigin::Copied {
                    observation: retained_observation,
                    boundary: retained_boundary,
                },
            ) => {
                assert_eq!(observation, retained_observation);
                assert_eq!(boundary.0, retained_boundary.0);
            }
            (InputOrigin::Scalar(value), core::InputOrigin::Scalar(retained)) => {
                use ril_compiler::sema::application_effect::ScalarInput;
                match (value, retained) {
                    (ScalarInput::PositiveInt, core::ScalarInput::PositiveInt) => {}
                    (ScalarInput::ByteSuffix(value), core::ScalarInput::ByteSuffix(retained))
                    | (
                        ScalarInput::BufferedBytes(value),
                        core::ScalarInput::BufferedBytes(retained),
                    ) => assert_eq!(value, retained),
                    _ => panic!("Core changed a generated scalar recipe"),
                }
            }
            _ => panic!("Core changed a generated input recipe"),
        }
    }
}

fn assert_context_retained(
    original: ril_compiler::sema::effect_identity::InvocationContext,
    retained: ril_ir::provenance::ResumptionContext,
) {
    assert_eq!(original.owner, retained.owner);
    assert_eq!(
        original.invocation.map(|id| id.0),
        retained.invocation.map(|id| id.0)
    );
    assert_eq!(original.closure, retained.closure.map(|id| id.0 as usize));
    assert_eq!(original.closure_invocation, retained.closure_invocation);
    assert_eq!(
        original.default_use.map(|id| id.0),
        retained.default_use.map(|id| id.0)
    );
    assert_eq!(original.budget_validation, retained.budget_validation);
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
            "derive-distinct-targets",
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
            for (original, retained) in program
                .facts()
                .closure_invocations
                .iter()
                .zip(&core.provenance.closure_invocations)
            {
                if matches!(original.entry.origin, EntryOrigin::Generated { .. }) {
                    assert_generated_origin_retained(
                        &original.entry.origin,
                        &retained.entry.origin,
                    );
                    assert_eq!(original.entry.parent, retained.entry.parent);
                    assert_eq!(
                        original.entry.allocation_epoch as u64,
                        retained.entry.allocation_epoch
                    );
                    assert_eq!(
                        original.entry.arguments.len(),
                        retained.entry.arguments.len()
                    );
                    assert_context_retained(
                        original.entry.caller_context,
                        retained.entry.caller_context,
                    );
                }
            }
            for (original, retained) in program
                .facts()
                .copy_invocations
                .iter()
                .zip(&core.provenance.copy_invocations)
            {
                if matches!(original.entry.origin, EntryOrigin::Generated { .. }) {
                    assert_generated_origin_retained(
                        &original.entry.origin,
                        &retained.entry.origin,
                    );
                    assert_eq!(original.target, retained.target);
                    assert_eq!(original.entry.parent, retained.entry.parent);
                    assert_eq!(
                        original.entry.allocation_epoch as u64,
                        retained.entry.allocation_epoch
                    );
                    assert_eq!(
                        original.entry.arguments.len(),
                        retained.entry.arguments.len()
                    );
                    assert_context_retained(
                        original.entry.caller_context,
                        retained.entry.caller_context,
                    );
                }
            }
        }
    }
}

#[test]
fn a_named_recipe_receives_the_actual_resume_completion_occurrence() {
    for layout in ["pointer32", "pointer64"] {
        let program = verified("derive-resume-completion", layout);
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let identity = facts
            .copy_invocations
            .iter()
            .find_map(|call| {
                let EntryOrigin::Generated { inputs, .. } = &call.entry.origin else {
                    return None;
                };
                inputs.iter().find_map(|input| {
                    let InputOrigin::Copied { observation, .. } = input else {
                        return None;
                    };
                    let identity = facts.evaluations[observation.0 as usize].identity?;
                    matches!(
                        &hir.expression(identity.source)?.kind,
                        ril_compiler::hir::nodes::ExprKind::Control {
                            operation: ril_syntax::ast::ControlOperation::Resume,
                            ..
                        }
                    )
                    .then_some(identity)
                })
            })
            .expect("derive must consume the actual resume completion occurrence");
        assert_eq!(
            facts.activations[identity.activation.0 as usize].kind,
            ril_compiler::sema::application_effect::ActivationKind::ControlTransfer
        );
        let retained = &core.provenance.activations[identity.activation.0 as usize];
        assert_eq!(retained.source, Some(identity.source));
        assert_eq!(
            retained.kind,
            ril_ir::provenance::ActivationKind::ControlTransfer
        );
    }
}

#[test]
fn an_inferred_protected_answer_keeps_its_source_through_an_inline_recipe() {
    for layout in ["pointer32", "pointer64"] {
        let program = verified("derive-resumed-answer", layout);
        ril_compiler::lower::lower_core(&program).unwrap();
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
    for mutation in 0..14 {
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
                assert!(
                    !loan.bindings.is_empty(),
                    "the original loan must bind its formal parameter"
                );
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
            11 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.closure_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                inputs.clear();
            }
            12 => {
                std::sync::Arc::make_mut(&mut changed.closure_invocations[first].entry.arguments)
                    [0]
                .0 = ril_syntax::ast::ParameterMode::Read
            }
            13 => {
                changed.closure_invocations[first]
                    .entry
                    .caller_context
                    .owner = None
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
    for mutation in 0..16 {
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
            15 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                inputs.clear();
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
fn same_signature_generated_named_targets_remain_distinct() {
    let program = verified("derive-distinct-targets", "pointer64");
    let facts = program.facts();
    let calls: Vec<_> = facts
        .copy_invocations
        .iter()
        .enumerate()
        .filter(|(_, call)| matches!(call.entry.origin, EntryOrigin::Generated { .. }))
        .map(|(index, _)| index)
        .collect();
    let first = calls[0];
    let other = *calls
        .iter()
        .find(|&&index| {
            facts.copy_invocations[index].target != facts.copy_invocations[first].target
        })
        .unwrap();
    let EntryOrigin::Generated {
        callee: first_callee,
        ..
    } = facts.copy_invocations[first].entry.origin
    else {
        unreachable!()
    };
    let EntryOrigin::Generated {
        callee: other_callee,
        ..
    } = facts.copy_invocations[other].entry.origin
    else {
        unreachable!()
    };
    assert_eq!(
        facts.expressions[first_callee.0 as usize].value.ty,
        facts.expressions[other_callee.0 as usize].value.ty
    );
    assert_ne!(
        facts.copy_invocations[first].target,
        facts.copy_invocations[other].target
    );
    for mutation in 0..6 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.copy_invocations[first].target = changed.copy_invocations[other].target,
            1 => {
                let EntryOrigin::Generated { callee, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                *callee = other_callee;
            }
            2 => {
                changed.copy_invocations[first].target = changed.copy_invocations[other].target;
                let EntryOrigin::Generated { callee, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                *callee = other_callee;
            }
            3 => {
                let EntryOrigin::Generated { callee, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                *callee = ril_compiler_core::ids::EvaluationOccurrenceId(u32::MAX);
            }
            4 => {
                changed.copy_invocations[first].entry.origin =
                    changed.copy_invocations[other].entry.origin.clone()
            }
            5 => {
                changed.copy_invocations[first].entry =
                    changed.copy_invocations[other].entry.clone();
                changed.copy_invocations[first].target = changed.copy_invocations[other].target;
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "same-signature generated target mutation {mutation}"
        );
    }
}

fn operation_entry(
    facts: &ril_compiler::sema::SemanticFacts,
    scope: ril_compiler::sema::facts::ScopeId,
) -> &ril_compiler::sema::scopes::OperationEntry {
    let ril_compiler::sema::scopes::ScopeOrigin::Operation(entry) =
        &facts.scopes.get(&scope).unwrap().origin
    else {
        unreachable!()
    };
    entry
}

#[test]
fn zero_argument_generated_exhaustion_authenticates_the_actual_budget_call() {
    use ril_compiler::sema::{model::Callable, scopes::ScopeOrigin};
    use ril_compiler_core::ids::EvaluationOccurrenceId;
    let source = ril_test::case_source("tests/conformance/totality.ril::zero-one-budget");
    for layout in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("zero-one-budget {layout}: {error:?}"));
        let facts = program.facts();
        let operation = facts.operations["Div::exhausted"].identity;
        assert!(facts.operations["Div::exhausted"].parameters.is_empty());
        let scopes: Vec<_> = facts
            .scopes
            .records()
            .filter_map(|record| match &record.origin {
                ScopeOrigin::Operation(entry)
                    if entry.operation == operation
                        && matches!(entry.origin, EntryOrigin::Generated { .. }) =>
                {
                    Some(record.id)
                }
                _ => None,
            })
            .collect();
        let first = scopes[0];
        let entry = operation_entry(facts, first);
        let EntryOrigin::Generated {
            anchor,
            callee,
            ref inputs,
        } = entry.origin
        else {
            unreachable!()
        };
        assert!(inputs.is_empty());
        let other = *scopes.iter().find(|&&scope| {
            let other = operation_entry(facts, scope);
            matches!(other.origin, EntryOrigin::Generated { callee: other_callee, .. } if other_callee != callee)
                && other.parent != entry.parent
        }).expect("repeated budgets must retain distinct physical entries");
        let other_entry = operation_entry(facts, other).clone();
        let EntryOrigin::Generated {
            anchor: other_anchor,
            callee: other_callee,
            ..
        } = other_entry.origin
        else {
            unreachable!()
        };
        assert_eq!(
            facts.expressions[callee.0 as usize].source_id,
            facts.expressions[other_callee.0 as usize].source_id,
            "the negative control borrows another execution of the same written callee"
        );
        assert_eq!(
            facts.expressions[callee.0 as usize].value.ty,
            facts.expressions[other_callee.0 as usize].value.ty
        );
        assert!(
            matches!(facts.expressions[callee.0 as usize].value.callables.as_slice(), [Callable::Builtin(name)] if name == "Div::budget")
        );
        let event = facts
            .copy_call_events
            .iter()
            .position(|event| {
                event.callee_expression == Some(callee.0 as usize)
                    && event.source_id == facts.activations[anchor.0 as usize].source
            })
            .unwrap();
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        let retained = core
            .provenance
            .scopes
            .iter()
            .find(|record| record.id == first.0)
            .unwrap();
        let ril_ir::provenance::ScopeOrigin::Operation {
            handler,
            operation: retained_operation,
            body,
            parent,
            caller_context,
            context,
            origin,
            allocation_epoch,
        } = &retained.origin
        else {
            unreachable!()
        };
        assert_eq!(*handler as usize, entry.handler);
        assert_eq!(*retained_operation, entry.operation);
        assert_eq!(*body, entry.body);
        assert_eq!(*parent, entry.parent);
        assert_eq!(*allocation_epoch, entry.allocation_epoch as u64);
        assert_context_retained(entry.caller_context, *caller_context);
        assert_context_retained(entry.context, *context);
        assert_generated_origin_retained(&entry.origin, origin);

        for mutation in 0..15 {
            let mut changed = facts.clone();
            let ScopeOrigin::Operation(entry) = &mut changed.scopes.get_mut(&first).unwrap().origin
            else {
                unreachable!()
            };
            match mutation {
                0 => {
                    let EntryOrigin::Generated { callee, .. } = &mut entry.origin else {
                        unreachable!()
                    };
                    *callee = EvaluationOccurrenceId(u32::MAX);
                }
                1 => {
                    let EntryOrigin::Generated { callee, .. } = &mut entry.origin else {
                        unreachable!()
                    };
                    *callee = other_callee;
                }
                2 => entry.origin = other_entry.origin.clone(),
                3 => {
                    let EntryOrigin::Generated { anchor, .. } = &mut entry.origin else {
                        unreachable!()
                    };
                    *anchor = other_anchor;
                }
                4 => entry.parent = None,
                5 => entry.caller_context = other_entry.caller_context,
                6 => entry.allocation_epoch = usize::MAX,
                7 => {
                    changed.expressions[callee.0 as usize].value.callables =
                        vec![Callable::Builtin("Div::exhausted".into())]
                }
                8 => {
                    changed.copy_call_events[event].callee_expression =
                        Some(other_callee.0 as usize)
                }
                9 => {
                    let EntryOrigin::Generated { callee, .. } = &mut entry.origin else {
                        unreachable!()
                    };
                    *callee = other_callee;
                    changed.copy_call_events[event].callee_expression =
                        Some(other_callee.0 as usize);
                }
                10 => entry.origin = EntryOrigin::Unresolved,
                11 => {
                    let EntryOrigin::Generated { inputs, .. } = &mut entry.origin else {
                        unreachable!()
                    };
                    inputs.push(InputOrigin::Scalar(
                        ril_compiler::sema::application_effect::ScalarInput::PositiveInt,
                    ));
                }
                12 => entry.context = other_entry.context,
                13 => *entry = other_entry.clone(),
                14 => changed.expressions[callee.0 as usize]
                    .value
                    .callables
                    .clear(),
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "zero-argument generated operation mutation {mutation}, {layout}"
            );
        }
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
