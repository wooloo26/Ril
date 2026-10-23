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

#[test]
fn shared_entry_packets_keep_the_actual_callee_input_and_heap_epoch() {
    use std::sync::Arc;
    for (name, named) in [
        ("derive-repeated-activation", false),
        ("derive-named-repeated-activation", true),
    ] {
        let program = verified(name, "pointer64");
        let facts = program.facts();
        let entries: Vec<_> = if named {
            facts
                .copy_invocations
                .iter()
                .enumerate()
                .filter_map(|(index, call)| {
                    matches!(call.entry.origin, EntryOrigin::Generated { .. })
                        .then_some((index, &call.entry))
                })
                .collect()
        } else {
            facts
                .closure_invocations
                .iter()
                .enumerate()
                .filter_map(|(index, call)| {
                    matches!(call.entry.origin, EntryOrigin::Generated { .. })
                        .then_some((index, &call.entry))
                })
                .collect()
        };
        assert!(
            entries.len() >= 2,
            "the original corpus must really enter both repeated recipes"
        );
        let (first, other) = (entries[0], entries[1]);
        assert!(first.1.callee.is_some() && other.1.callee.is_some());
        assert!(!first.1.arguments.is_empty() && first.1.arguments[0].heap.is_some());
        let first_callee = first.1.callee.as_ref().unwrap().birth_coordinates();
        let other_environment = facts
            .evaluations
            .iter()
            .filter_map(|record| record.environment)
            .find(|environment| Some(*environment) != first_callee.environment)
            .expect("the real repeated recipe must retain another evaluation environment");
        for mutation in 0..8 {
            let mut changed = facts.clone();
            let entry = if named {
                &mut changed.copy_invocations[first.0].entry
            } else {
                &mut changed.closure_invocations[first.0].entry
            };
            match mutation {
                0 => entry.callee = None,
                1 => entry.callee = other.1.callee.clone(),
                2 => {
                    Arc::make_mut(&mut entry.arguments)[0].packet =
                        other.1.arguments[0].packet.clone()
                }
                3 => {
                    Arc::make_mut(&mut entry.arguments)[0].mode =
                        ril_syntax::ast::ParameterMode::Read
                }
                4 => Arc::make_mut(&mut entry.arguments)[0].heap = None,
                5 => {
                    Arc::make_mut(
                        Arc::make_mut(&mut entry.arguments)[0]
                            .heap
                            .as_mut()
                            .unwrap(),
                    )
                    .allocation_epoch = usize::MAX
                }
                6 => entry.allocation_epoch = usize::MAX,
                7 => {
                    changed.evaluations[first_callee.observation.unwrap()].environment =
                        Some(other_environment)
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "{name}: shared packet mutation {mutation}"
            );
        }
    }
}

#[test]
fn same_named_empty_headers_keep_their_original_declaration_introducers() {
    // Static scope normalization gives these two written `same` declarations
    // different canonical names. Calibrate the source names before that pass;
    // select their empty integer headers by structure in the canonical HIR.
    let source =
        ril_test::case_source("tests/regressions/callable-inputs.ril::named-empty-header-scopes");
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok());
    let written: Vec<_> = parsed
        .program
        .statements
        .iter()
        .filter_map(|statement| {
            let ril_syntax::ast::StmtKind::Function(function) = &statement.kind else {
                return None;
            };
            function.body.as_ref()
        })
        .flat_map(|body| &body.where_items)
        .filter_map(|statement| {
            let ril_syntax::ast::StmtKind::Function(function) = &statement.kind else {
                return None;
            };
            (function.name == "same").then_some(function)
        })
        .collect();
    assert_eq!(written.len(), 2);
    assert!(written.iter().all(|header| header.name == "same"
        && header.parameters.is_empty()
        && header.generics.is_empty()));
    for target in ["pointer32", "pointer64"] {
        let program = verified("named-empty-header-scopes", target);
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let originals: Vec<_> = facts
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(binding, info)| {
                let declaration = info.declaration?;
                let ril_compiler::hir::nodes::StmtKind::Function(header) =
                    &hir.statement(declaration)?.kind
                else {
                    return None;
                };
                (header.parameters.is_empty() && header.generics.is_empty()
                    && header.return_type.and_then(|ty| hir.type_expression(ty)).is_some_and(|ty| matches!(&ty.kind,
                        ril_compiler::hir::nodes::TypeKind::Name { path, arguments } if path == &["int"] && arguments.is_empty()
                    ))).then_some((
                    binding,
                    declaration,
                    &header.name,
                ))
            })
            .collect();
        let declarations: std::collections::BTreeSet<_> = originals
            .iter()
            .map(|(_, declaration, _)| *declaration)
            .collect();
        assert_eq!(
            declarations.len(),
            2,
            "both original declarations must survive normalization: {originals:?}"
        );
        assert!(originals.len() >= declarations.len());
        for actual in &originals {
            let sibling = *declarations
                .iter()
                .find(|declaration| **declaration != actual.1)
                .unwrap();
            for replacement in [None, Some(sibling)] {
                let mut changed = facts.clone();
                changed.bindings[actual.0].declaration = replacement;
                assert!(
                    solved_facts(&changed).is_err(),
                    "a named binding borrowed another empty header's declaration: binding={} replacement={replacement:?}",
                    actual.0
                );
            }
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
