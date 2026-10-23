//! Deep corruption controls moved from integration tests. Production exposes
//! immutable packet evidence; these models alter only a cloned current value.
use super::{application_effect::EntryArgument, copy_contract::CopyHeapSnapshot, model::Value};
use std::sync::Arc;

fn value_mut(argument: &mut EntryArgument) -> &mut Value {
    &mut Arc::make_mut(&mut argument.packet).value
}
fn heap_mut(argument: &mut EntryArgument) -> &mut CopyHeapSnapshot {
    Arc::make_mut(
        argument
            .heap
            .as_mut()
            .expect("the original entry has actual heap evidence"),
    )
}
mod callable_inputs {
    use super::value_mut;
    use crate as ril_compiler;
    use crate::sema::application_effect::{EntryOrigin, InputOrigin};
    use crate::{CheckOptions, Session, sema::validate::solved_facts};
    fn verified(name: &str, layout: &str) -> ril_compiler::hir::VerifiedProgram {
        let source =
            ril_test::case_source(&format!("tests/regressions/callable-inputs.ril::{name}"));
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
                0 => {
                    changed.closure_invocations[first].entry.arguments = std::sync::Arc::new(vec![])
                }
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
                    value_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.closure_invocations[first].entry.arguments,
                        )[0],
                    )
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
                    std::sync::Arc::make_mut(
                        &mut changed.closure_invocations[first].entry.arguments,
                    )[0]
                    .mode = ril_syntax::ast::ParameterMode::Read
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
                0 => std::sync::Arc::make_mut(&mut changed.copy_invocations[first].entry.arguments)
                    .clear(),
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
                    std::sync::Arc::make_mut(&mut changed.copy_invocations[first].entry.arguments)
                        [0]
                    .mode = ril_syntax::ast::ParameterMode::Read
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
                13 => value_mut(
                    &mut std::sync::Arc::make_mut(
                        &mut changed.copy_invocations[first].entry.arguments,
                    )[0],
                )
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
}

mod closed_standard_data {
    use super::heap_mut;
    use super::value_mut;
    use crate as ril_compiler;
    use crate::Session;

    #[test]
    fn generated_record_callbacks_cannot_borrow_another_receiver_field_or_scalar() {
        use ril_compiler::sema::{
            application_effect::{EntryOrigin, InputOrigin, ScalarInput},
            validate::solved_facts,
        };
        let source =
            ril_test::case_source("tests/regressions/closed-standard-data.ril::repeated-reader");
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let facts = program.facts();
        let calls: Vec<_> = facts
            .copy_invocations
            .iter()
            .enumerate()
            .filter(|(_, call)| {
                matches!(&call.entry.origin,
        EntryOrigin::Generated { inputs, .. } if inputs.len()==2)
            })
            .map(|(index, _)| index)
            .collect();
        assert!(calls.len() >= 2);
        let (first, other) = (calls[0], calls[1]);
        for mutation in 0..10 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.copy_invocations[first].entry.origin = EntryOrigin::Unresolved,
                1 => {
                    changed.copy_invocations[first].entry.origin =
                        changed.copy_invocations[other].entry.origin.clone()
                }
                2 => {
                    let EntryOrigin::Generated { inputs, .. } =
                        &mut changed.copy_invocations[first].entry.origin
                    else {
                        unreachable!()
                    };
                    inputs[0] = InputOrigin::Widened(
                        ril_compiler_core::ids::EvaluationOccurrenceId(u32::MAX),
                    );
                }
                3 => {
                    let EntryOrigin::Generated { inputs, .. } =
                        &mut changed.copy_invocations[first].entry.origin
                    else {
                        unreachable!()
                    };
                    inputs[1] = InputOrigin::Scalar(ScalarInput::ByteSuffix(
                        ril_compiler_core::ids::EvaluationOccurrenceId(0),
                    ));
                }
                4 => {
                    value_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.copy_invocations[first].entry.arguments,
                        )[0],
                    )
                    .temporary = false
                }
                5 => {
                    value_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.copy_invocations[first].entry.arguments,
                        )[0],
                    )
                    .permission = ril_compiler::sema::facts::Permission::Read
                }
                6 => {
                    value_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.copy_invocations[first].entry.arguments,
                        )[1],
                    )
                    .ty = ril_compiler::sema::model::Ty::Bytes
                }
                7 => value_mut(
                    &mut std::sync::Arc::make_mut(
                        &mut changed.copy_invocations[first].entry.arguments,
                    )[0],
                )
                .origins
                .nodes
                .clear(),
                8 => {
                    let EntryOrigin::Generated { callee, .. } =
                        changed.copy_invocations[first].entry.origin
                    else {
                        unreachable!()
                    };
                    changed.expressions[callee.0 as usize]
                        .value
                        .corrupt_value(&mut 1_000_000)
                        .unwrap()
                        .callables
                        .clear();
                }
                9 => {
                    changed.copy_invocations[first].entry =
                        changed.copy_invocations[other].entry.clone()
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "record callback mutation {mutation}"
            );
        }
    }

    #[test]
    fn signature_assumptions_are_universal_formals_and_cannot_supply_concrete_data() {
        use ril_compiler::sema::{application_effect::EntryOrigin, validate::solved_facts};
        let source =
            ril_test::case_source("tests/regressions/closed-standard-data.ril::repeated-reader");
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let facts = program.facts();
        let first = facts
            .copy_invocations
            .iter()
            .position(|call| matches!(call.entry.origin, EntryOrigin::SignatureProbe(_)))
            .unwrap();
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        let EntryOrigin::SignatureProbe(source) = &facts.copy_invocations[first].entry.origin
        else {
            unreachable!()
        };
        let ril_ir::provenance::EntryOrigin::SignatureProbe(retained) =
            &core.provenance.copy_invocations[first].entry.origin
        else {
            unreachable!()
        };
        assert_eq!(retained.source, source.source);
        assert_eq!(retained.path, *source.path);
        assert!(
            !source.path.is_empty(),
            "record callback retains its real field projection"
        );
        assert_eq!(retained.formals.len(), source.formals.len());
        for (retained_formal, formal) in retained.formals.iter().zip(source.formals.iter()) {
            assert_eq!(retained_formal.slot, formal.slot);
            assert_eq!(retained_formal.binding as usize, formal.binding);
            assert_eq!(
                retained.environment,
                core.provenance.bindings[formal.binding].typing_environment
            );
        }
        let mut relocated = facts.clone();
        let EntryOrigin::SignatureProbe(source) =
            &mut relocated.copy_invocations[first].entry.origin
        else {
            unreachable!()
        };
        let header = std::sync::Arc::make_mut(&mut std::sync::Arc::make_mut(source).header);
        header.span.start = header.span.start.saturating_add(1);
        assert!(
            solved_facts(&relocated).is_ok(),
            "signature header spans are diagnostic locations"
        );
        for mutation in 0..16 {
            let mut changed = facts.clone();
            let binding = *value_mut(
                &mut std::sync::Arc::make_mut(&mut changed.copy_invocations[first].entry.arguments)
                    [0],
            )
            .sources
            .first()
            .unwrap();
            match mutation {
                0 => {
                    value_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.copy_invocations[first].entry.arguments,
                        )[0],
                    )
                    .source_type_witness = None
                }
                1 => {
                    value_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.copy_invocations[first].entry.arguments,
                        )[0],
                    )
                    .constant = Some(ril_compiler::sema::model::Constant::Bool(false))
                }
                2 => changed.bindings[binding].parameter = false,
                3 => {
                    changed.bindings[binding].pattern =
                        Some(ril_compiler_core::ids::PatternId(u32::MAX))
                }
                4 => {
                    heap_mut(
                        &mut std::sync::Arc::make_mut(
                            &mut changed.copy_invocations[first].entry.arguments,
                        )[0],
                    )
                    .nodes[0]
                        .fact
                        .kind = ril_compiler::sema::facts::OriginKind::Opaque
                }
                5 => {
                    changed.copy_invocations[first].source_event =
                        Some(ril_compiler::sema::copy_contract::CopyCallEventId(0))
                }
                6 => heap_mut(
                    &mut std::sync::Arc::make_mut(
                        &mut changed.copy_invocations[first].entry.arguments,
                    )[0],
                )
                .nodes
                .clear(),
                7 => changed.copy_invocations[first].entry.origin = EntryOrigin::Unresolved,
                8..16 => {
                    let EntryOrigin::SignatureProbe(source) =
                        &mut changed.copy_invocations[first].entry.origin
                    else {
                        unreachable!()
                    };
                    let source = std::sync::Arc::make_mut(source);
                    match mutation {
                        8 => source.source = ril_compiler_core::ids::TypeExprId(u32::MAX),
                        9 => source.environment = source.environment.thaw().freeze(),
                        10 => std::sync::Arc::make_mut(&mut source.formals)[0].slot = u32::MAX,
                        11 => std::sync::Arc::make_mut(&mut source.formals)[0].binding = usize::MAX,
                        12 => {
                            std::sync::Arc::make_mut(&mut source.path).push(
                                ril_compiler_core::projection::TypeProjection::Field(
                                    "ril__missing".into(),
                                ),
                            );
                        }
                        13 => {
                            let header = std::sync::Arc::make_mut(&mut source.header);
                            header.kind = ril_syntax::ast::TypeKind::Name {
                                path: vec!["bool".into()],
                                arguments: Vec::new(),
                            };
                        }
                        14 => {
                            let header = std::sync::Arc::make_mut(&mut source.header);
                            let child = match &mut header.kind {
                                ril_syntax::ast::TypeKind::Name { arguments, .. } => {
                                    &mut arguments[0]
                                }
                                ril_syntax::ast::TypeKind::Callable { parameters, .. } => {
                                    parameters[0].ty.as_mut().unwrap()
                                }
                                ril_syntax::ast::TypeKind::Record { fields, .. } => {
                                    &mut fields[0].ty
                                }
                                _ => unreachable!(),
                            };
                            child.hir_id = Some(ril_compiler_core::ids::TypeExprId(u32::MAX));
                        }
                        15 => std::sync::Arc::make_mut(&mut source.path).clear(),
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "signature assumption mutation {mutation}"
            );
        }
    }
}

mod channel_message_results {
    use super::value_mut;
    use crate as ril_compiler;
    use crate::Session;
    fn rejected(facts: &ril_compiler::sema::SemanticFacts) {
        let issues = ril_compiler::sema::validate::solved_facts(facts).unwrap_err();
        assert!(
            issues.iter().any(|issue| matches!(
                issue.kind,
                ril_compiler::sema::validate::ValidationIssueKind::ChannelMessage(_)
            )),
            "{issues:?}"
        );
    }

    #[test]
    fn independent_formal_optional_paths_cannot_be_unified_even_with_one_valid_cause() {
        let source = ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
        );
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        let mut changed = verified.facts().clone();
        let invocation = changed
            .copy_invocations
            .iter_mut()
            .find(|invocation| {
                invocation.declaration_probe
                    && invocation.caller_activation.is_none()
                    && invocation.entry.arguments.len() == 2
                    && invocation.entry.arguments[0]
                        .value()
                        .option_identity
                        .is_some()
                    && invocation.entry.arguments[1]
                        .value()
                        .option_identity
                        .is_some()
            })
            .unwrap();
        let identity = invocation.entry.arguments[0]
            .value()
            .option_identity
            .unwrap();
        assert_ne!(
            Some(identity),
            invocation.entry.arguments[1].value().option_identity
        );
        value_mut(&mut std::sync::Arc::make_mut(&mut invocation.entry.arguments)[1])
            .option_identity = Some(identity);
        value_mut(&mut std::sync::Arc::make_mut(&mut invocation.entry.arguments)[1]).cause =
            changed.optional_tags[identity.0 as usize].cause;
        // The arena entry, payload type, owner and ancestry are all individually
        // valid. The two actual symbolic input positions must still be independent.
        rejected(&changed);
    }

    #[test]
    fn formal_optional_independence_cannot_be_disabled_by_a_registered_owner() {
        let source = ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
        );
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let mut changed = verified.facts().clone();
        let invocation = changed
            .copy_invocations
            .iter_mut()
            .find(|invocation| {
                invocation.declaration_probe
                    && invocation.caller_activation.is_none()
                    && invocation.entry.arguments.len() == 2
                    && invocation.entry.arguments[0]
                        .value()
                        .option_identity
                        .is_some()
                    && invocation.entry.arguments[1]
                        .value()
                        .option_identity
                        .is_some()
            })
            .unwrap();
        let identity = invocation.entry.arguments[0]
            .value()
            .option_identity
            .unwrap();
        assert_ne!(
            Some(identity),
            invocation.entry.arguments[1].value().option_identity
        );
        value_mut(&mut std::sync::Arc::make_mut(&mut invocation.entry.arguments)[1])
            .option_identity = Some(identity);
        value_mut(&mut std::sync::Arc::make_mut(&mut invocation.entry.arguments)[1]).cause =
            changed.optional_tags[identity.0 as usize].cause;
        // Registry-valid owner metadata must not change which actual declaration
        // parameter paths are independent symbolic inputs.
        changed.optional_tags[identity.0 as usize].creation_owner =
            *changed.scopes.iter().next().unwrap();
        rejected(&changed);
    }

    #[test]
    fn formal_optional_independence_survives_every_entry_selector_combination() {
        let source = ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
        );
        let actual_alias = format!(
            "{source}\nfn alias_unknown_optional(value:Option<Result<int,str>>)->Result<(),Concurrent::TaskFault> @Async{{consume(value,value)}}\nfn named_optional_callback(value:Option<Result<int,str>>) @Async{{assert(consume(value,value) is Ok()|Err(_))}}\nfn through_named_optional_callback(value:Option<Result<int,str>>) @Async{{named_optional_callback(value)}}\nfn through_single_optional_callback(value:Option<Result<int,str>>) @Async{{let mapped=Array::map([1],\\number:int->{{named_optional_callback(value);number}})}}\n"
        );
        let alias_verified = Session::new(actual_alias.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("lawful actual input alias: {error:?}"));
        ril_compiler::lower::lower_core(&alias_verified).unwrap();
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let original = verified.facts().clone();
        let entry = original
            .copy_invocations
            .iter()
            .find(|invocation| {
                invocation.declaration_probe
                    && invocation.caller_activation.is_none()
                    && invocation.entry.arguments.len() == 2
                    && invocation.entry.arguments[0]
                        .value()
                        .option_identity
                        .is_some()
                    && invocation.entry.arguments[1]
                        .value()
                        .option_identity
                        .is_some()
            })
            .unwrap();
        let header = original
            .functions
            .iter()
            .find(|function| function.definition == entry.target)
            .unwrap();
        assert_eq!(entry.span, header.syntax.span);
        let scope = *original.scopes.iter().next().unwrap();
        let actual_source = original
            .copy_call_events
            .iter()
            .find(|event| event.target == Some(entry.target))
            .unwrap()
            .id;
        let parent = original
            .copy_invocations
            .iter()
            .find(|candidate| candidate.id != entry.id && candidate.parent.is_none())
            .unwrap()
            .id;
        println!(
            "real declaration entry={:?}, target={:?}, header={:?}, parameters={}",
            entry.id,
            entry.target,
            header.syntax.span,
            header.syntax.parameters.len()
        );
        let mut accepted = Vec::new();
        let mut unrelated_rejections = Vec::new();
        for selectors in 0u8..16 {
            let mut changed = original.clone();
            let invocation = &mut changed.copy_invocations[entry.id.0 as usize];
            let identity = invocation.entry.arguments[0]
                .value()
                .option_identity
                .unwrap();
            assert_ne!(
                Some(identity),
                invocation.entry.arguments[1].value().option_identity
            );
            value_mut(&mut std::sync::Arc::make_mut(&mut invocation.entry.arguments)[1])
                .option_identity = Some(identity);
            value_mut(&mut std::sync::Arc::make_mut(&mut invocation.entry.arguments)[1]).cause =
                changed.optional_tags[identity.0 as usize].cause;
            // All substituted identities are registered. The original real
            // declaration span and two frozen symbolic input paths stay intact.
            changed.optional_tags[identity.0 as usize].creation_owner = scope;
            if selectors & 1 != 0 {
                invocation.declaration_probe = false;
            }
            if selectors & 2 != 0 {
                invocation.caller_activation = Some(scope);
            }
            if selectors & 4 != 0 {
                invocation.source_event = Some(actual_source);
            }
            if selectors & 8 != 0 {
                invocation.parent = Some(parent);
            }
            match ril_compiler::sema::validate::solved_facts(&changed) {
                Ok(structure) => {
                    println!("entry selectors={selectors:04b}: ACCEPTED {structure:?}");
                    accepted.push(selectors);
                }
                Err(issues) => {
                    println!("entry selectors={selectors:04b}: rejected {issues:?}");
                    if !issues.iter().any(|issue| {
                    matches!(&issue.kind, ril_compiler::sema::validate::ValidationIssueKind::ChannelMessage(message)
                        if message.contains("independent symbolic formal parameter paths"))
                }) {
                    unrelated_rejections.push(selectors);
                }
                }
            }
        }
        assert!(
            accepted.is_empty(),
            "real independent formal paths were accepted after changing entry selectors: {accepted:?}"
        );
        assert!(
            unrelated_rejections.is_empty(),
            "entry selectors did not reconstruct the actual formal independence duty: {unrelated_rejections:?}"
        );
    }
}

mod source_type_witness {
    use super::value_mut;
    use crate as ril_compiler;
    use crate::Session;
    fn forwarding_fixture() -> &'static str {
        ril_test::case_source("tests/regressions/source-types.ril::forwarding")
    }

    #[test]
    fn tampering_only_frozen_snapshot_syntax_is_rejected_even_when_value_equality_hides_it() {
        let verified = Session::new(forwarding_fixture().as_bytes().to_vec())
            .verify()
            .unwrap();
        let mut facts = verified.facts().clone();
        let value = facts
            .copy_invocations
            .iter_mut()
            .flat_map(|invocation| {
                std::sync::Arc::make_mut(&mut invocation.entry.arguments).iter_mut()
            })
            .map(value_mut)
            .find(|value| value.source_type_witness.is_some())
            .unwrap();
        let before = value.clone();
        let witness = std::sync::Arc::make_mut(value.source_type_witness.as_mut().unwrap());
        witness.syntax.kind = ril_syntax::ast::TypeKind::Name {
            path: vec!["UnresolvedT".into()],
            arguments: vec![],
        };
        assert_eq!(
            before, *value,
            "canonical-key equality intentionally ignores presentation syntax"
        );
        let issues = ril_compiler::sema::validate::solved_facts(&facts).unwrap_err();
        assert!(
            issues.iter().any(|issue| matches!(
                issue.kind,
                ril_compiler::sema::validate::ValidationIssueKind::SourceTypeWitness
            )),
            "{issues:?}"
        );
    }

    #[test]
    fn a_consistent_key_cannot_turn_an_unresolved_binder_spelling_into_a_nominal_type() {
        let verified = Session::new(forwarding_fixture().as_bytes().to_vec())
            .verify()
            .unwrap();
        let mut facts = verified.facts().clone();
        let value = facts
            .copy_invocations
            .iter_mut()
            .flat_map(|invocation| {
                std::sync::Arc::make_mut(&mut invocation.entry.arguments).iter_mut()
            })
            .map(value_mut)
            .find(|value| value.source_type_witness.is_some())
            .unwrap();
        let witness = std::sync::Arc::make_mut(value.source_type_witness.as_mut().unwrap());
        witness.syntax.kind = ril_syntax::ast::TypeKind::Name {
            path: vec!["UnresolvedT".into()],
            arguments: vec![],
        };
        witness.key = "UnresolvedT<>".into();
        assert!(
            witness.validate_closed(),
            "structural closedness alone cannot resolve a name"
        );
        let issues = ril_compiler::sema::validate::solved_facts(&facts).unwrap_err();
        assert!(
            issues.iter().any(|issue| matches!(
                issue.kind,
                ril_compiler::sema::validate::ValidationIssueKind::SourceTypeWitness
            )),
            "{issues:?}"
        );
    }
}
