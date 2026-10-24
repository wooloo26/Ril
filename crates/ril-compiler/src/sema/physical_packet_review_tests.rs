//! Original integration corruption controls, kept private so physical packets expose only reads.
mod generic_prefix_sources {
    use crate::hir::nodes::ExprKind;
    use crate::sema::{
        model::Callable,
        record_bound_validation::OriginalOperandSources,
        source_types::{
            WorkLimit,
            projection_receipts::{ProjectionOccurrence, ProjectionReceipts},
        },
        source_types_ref::SourceTypesRef,
    };
    use crate::{CheckOptions, Session};

    #[test]
    fn ordinary_type_prefixes_keep_the_actual_base_source_and_original_environment() {
        for name in ["generic-array-return", "partial-static-argument-inference"] {
            let source =
                ril_test::case_source(&format!("tests/regressions/source-transport.ril::{name}"));
            for layout in ["pointer32", "pointer64"] {
                let program = Session::with_options(
                    source.as_bytes().to_vec(),
                    CheckOptions {
                        target: layout.into(),
                        ..Default::default()
                    },
                )
                .verify()
                .unwrap_or_else(|error| panic!("{name}/{layout}: {error:?}"));
                let facts = program.facts();
                let hir = facts.semantic_hir.as_deref().unwrap();
                let mut work = 4_000_000;
                let query = OriginalOperandSources::new_with_work(facts, &mut work).unwrap();
                let mut count = 0;
                for (observation, fact) in facts.expressions.iter().enumerate() {
                    let Some(source) = fact.source_id else {
                        continue;
                    };
                    let ExprKind::Generic { base, .. } = &hir.expression(source).unwrap().kind
                    else {
                        continue;
                    };
                    let [Callable::Named(_)] = fact.value.callables.as_slice() else {
                        continue;
                    };
                    count += 1;
                    let record = &facts.evaluations[observation];
                    let child = ProjectionReceipts::from_facts(facts)
                        .child_observation(
                            ProjectionOccurrence {
                                identity: record.identity.unwrap(),
                                context: record.context,
                                cause: fact.value.cause,
                            },
                            *base,
                            &mut WorkLimit::new(16384),
                        )
                        .unwrap()
                        .0 as usize;
                    let child_fact = &facts.expressions[child];
                    assert!(!fact.value.packet().shares_birth(child_fact.value.packet()));
                    let mut graph_work = WorkLimit::new(16384);
                    let captured = fact
                        .value
                        .packet()
                        .birth_source(SourceTypesRef::Frozen(&facts.source_types), &mut graph_work)
                        .unwrap();
                    let base_source = child_fact
                        .value
                        .packet()
                        .birth_source(SourceTypesRef::Frozen(&facts.source_types), &mut graph_work)
                        .unwrap();
                    assert_eq!(captured.environment.id(), base_source.environment.id());
                    let (replayed, environment) = query
                        .observed_with_work(source, observation, &mut work)
                        .unwrap()
                        .0
                        .expect("an ordinary explicit prefix retains its original callable Source");
                    assert_eq!(captured.environment.id(), environment.id());
                    assert!(
                        captured
                            .schema
                            .as_ref()
                            .unwrap()
                            .equivalent_in(
                                &replayed,
                                &captured.environment,
                                &environment,
                                &mut graph_work,
                            )
                            .unwrap()
                    );
                    assert!(
                        captured
                            .schema
                            .as_ref()
                            .unwrap()
                            .equivalent_in(
                                base_source.schema.as_ref().unwrap(),
                                &captured.environment,
                                &base_source.environment,
                                &mut graph_work,
                            )
                            .unwrap()
                    );

                    let mut changed = facts.clone();
                    let identity = changed.evaluations[child].identity.unwrap();
                    changed.activations[identity.activation.0 as usize].parent = None;
                    let rejected = OriginalOperandSources::new_with_work(&changed, &mut 4_000_000)
                        .and_then(|query| {
                            query.observed_with_work(source, observation, &mut 4_000_000)
                        });
                    assert!(
                        rejected.is_err(),
                        "{name}/{layout}: a detached base supplied the prefix Source"
                    );

                    let mut changed = facts.clone();
                    let binding = *child_fact.value.sources.first().unwrap();
                    assert!(changed.bindings[binding].declaration.take().is_some());
                    let rejected = OriginalOperandSources::new_with_work(&changed, &mut 4_000_000)
                        .and_then(|query| {
                            query.observed_with_work(source, observation, &mut 4_000_000)
                        });
                    assert!(
                        rejected.is_err(),
                        "{name}/{layout}: an unanchored declaration supplied the prefix Source"
                    );
                    assert!(
                        query
                            .observed_with_work(source, observation, &mut 0)
                            .is_err()
                    );
                }
                assert!(count > 0, "{name}/{layout}: no actual ordinary Type prefix");
            }
        }
    }
    #[test]
    fn constrained_parameter_products_and_selected_results_keep_their_original_graphs() {
        for case in [
            "bounded-record-tuple-return",
            "composed-row-with-array-and-callback",
        ] {
            let source =
                ril_test::case_source(&format!("tests/regressions/source-transport.ril::{case}"));
            for layout in ["pointer32", "pointer64"] {
                let program = Session::with_options(
                    source.as_bytes().to_vec(),
                    CheckOptions {
                        target: layout.into(),
                        ..Default::default()
                    },
                )
                .verify()
                .unwrap_or_else(|error| panic!("{case}/{layout}: {error:?}"));
                let facts = program.facts();
                let hir = facts.semantic_hir.as_deref().unwrap();
                let mut work = 4_000_000;
                let query = OriginalOperandSources::new_with_work(facts, &mut work).unwrap();
                let outer = facts
                    .functions
                    .iter()
                    .find(|function| function.syntax.name == "outer")
                    .map(|function| function.definition);
                let mut checked = 0;
                let mut constrained = 0;
                for (observation, fact) in facts.expressions.iter().enumerate() {
                    let Some(source) = fact.source_id else {
                        continue;
                    };
                    let original = hir.expression(source).unwrap();
                    let field =
                        matches!(&original.kind, ExprKind::Field { field, .. } if field == "items");
                    let returned = matches!(original.kind, ExprKind::Call { .. })
                        && outer.is_some_and(|owner| {
                            facts.evaluations[observation].context.owner
                                == Some(ril_compiler_core::ids::CallableOwner::Function(owner))
                        });
                    if !field && !returned {
                        continue;
                    }
                    checked += 1;
                    let mut graph_work = WorkLimit::new(16384);
                    let captured = fact
                        .value
                        .packet()
                        .birth_source(SourceTypesRef::Frozen(&facts.source_types), &mut graph_work)
                        .unwrap();
                    let captured_schema = captured
                        .schema
                        .as_ref()
                        .expect("a guaranteed member or selected result retains its Source");
                    let (expected, environment) = query
                        .observed_with_work(source, observation, &mut work)
                        .unwrap()
                        .0
                        .unwrap();
                    assert_eq!(
                        captured.environment.id(),
                        environment.id(),
                        "{case}/{layout}: projection changed Γ"
                    );
                    assert!(
                        captured_schema
                            .equivalent_in(
                                &expected,
                                &captured.environment,
                                &environment,
                                &mut graph_work
                            )
                            .unwrap()
                    );
                    assert!(
                        query
                            .observed_with_work(source, observation, &mut 0)
                            .is_err()
                    );
                    if let ExprKind::Field { base, .. } = &original.kind
                        && field
                    {
                        let record = &facts.evaluations[observation];
                        let receiver = ProjectionReceipts::from_facts(facts)
                            .child_observation(
                                ProjectionOccurrence {
                                    identity: record.identity.unwrap(),
                                    context: record.context,
                                    cause: fact.value.cause,
                                },
                                *base,
                                &mut graph_work,
                            )
                            .unwrap()
                            .0 as usize;
                        let receiver_source = facts.expressions[receiver]
                            .value
                            .packet()
                            .birth_source(
                                SourceTypesRef::Frozen(&facts.source_types),
                                &mut graph_work,
                            )
                            .unwrap();
                        let Some(identity) = receiver_source
                            .schema
                            .as_ref()
                            .unwrap()
                            .bare_binder_identity(&mut graph_work)
                            .unwrap()
                        else {
                            continue;
                        };
                        constrained += 1;
                        let mut changed = facts.clone();
                        let bound = changed
                            .record_bounds
                            .iter_mut()
                            .find(|bound| bound.binder == identity)
                            .unwrap();
                        bound.fields.retain(|field| field.label != "items");
                        assert!(
                            OriginalOperandSources::new_with_work(&changed, &mut 4_000_000)
                                .and_then(|query| query.observed_with_work(
                                    source,
                                    observation,
                                    &mut 4_000_000
                                ))
                                .is_err(),
                            "{case}/{layout}: a missing genuine bound field supplied its Source"
                        );
                    }
                }
                assert!(
                    checked > 0,
                    "{case}/{layout}: no actual constrained projection or selected result"
                );
                if case == "bounded-record-tuple-return" {
                    assert!(
                        constrained > 0,
                        "the negative must exercise a genuine rigid bound"
                    );
                }
            }
        }
    }
}

mod binding_projections {
    use crate as ril_compiler;
    use crate::{Session, sema::validate::solved_facts};
    #[test]
    fn a_source_read_cannot_borrow_a_same_named_sibling_invocations_graph() {
        let source = ril_test::case_source(
            "tests/conformance/rest-patterns.ril::repeated-record-rest-views-pointer64",
        );
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let facts = program.facts();
        let row = facts
            .binding_sources
            .iter()
            .rfind(|row| {
                row.context.invocation.is_some() && facts.bindings[row.binding].name == "alias"
            })
            .unwrap();
        let sibling = facts
            .bindings
            .iter()
            .enumerate()
            .find(|(id, binding)| {
                binding.name == "rest"
                    && *id < row.binding
                    && binding.owner != row.activation
                    && binding.context.invocation.is_some()
            })
            .map(|(id, _)| id)
            .unwrap();
        let mut changed = facts.clone();
        changed.expressions[row.initializer.expression]
            .value
            .corrupt_value(&mut 4_000_000)
            .unwrap()
            .sources = [sibling].into();
        let errors = solved_facts(&changed)
            .expect_err("a same-spelled sibling binding supplied a Source graph");
        assert!(
            format!("{errors:?}").contains("another lexical activation"),
            "{errors:?}"
        );
    }

    fn guarded_receipts_remain_required(case: &str, alternative: bool, declarations: usize) {
        use ril_compiler::hir::nodes::PatternKind;
        use std::collections::BTreeSet;

        let source = ril_test::case_source(&format!("tests/conformance/patterns.ril::{case}"));
        let program = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        let facts = program.facts();
        let hir = facts.semantic_hir.as_ref().unwrap();
        let rows: Vec<_> = facts
            .binding_sources
            .iter()
            .filter(|row| {
                facts.bindings[row.binding].name == "value"
                    && match &hir.pattern(row.declaration).unwrap().kind {
                        PatternKind::Alternative(_) => alternative,
                        PatternKind::Constructor { .. } => !alternative,
                        _ => false,
                    }
            })
            .collect();
        assert_eq!(
            rows.iter()
                .map(|row| row.declaration)
                .collect::<BTreeSet<_>>()
                .len(),
            declarations,
            "{case} did not exercise every original guarded declaration"
        );
        for row in rows {
            if alternative {
                assert_eq!(facts.bindings[row.binding].pattern, Some(row.declaration));
            }
            let mut diagnostics = facts.clone();
            diagnostics.expressions[row.initializer.expression].span = facts.expressions[0].span;
            solved_facts(&diagnostics)
                .expect("initializer locations cannot replace its HIR birth identity");
            if !alternative {
                let aliases: Vec<_> = facts
                    .bindings
                    .iter()
                    .filter(|binding| {
                        binding.name == "value"
                            && binding.owner == row.activation
                            && binding.birth.is_some_and(|birth| {
                                matches!(
                                    &hir.expression(birth.source).unwrap().kind,
                                    ril_compiler::hir::nodes::ExprKind::Match { .. }
                                        | ril_compiler::hir::nodes::ExprKind::For { .. }
                                )
                            })
                    })
                    .collect();
                assert!(
                    aliases.len() >= 2,
                    "missing actual same-scope match/for receivers"
                );
                for alias in aliases {
                    for borrow_birth in [false, true] {
                        let mut changed = facts.clone();
                        changed
                            .binding_sources
                            .retain(|other| other.binding != row.binding);
                        changed.bindings[row.binding].pattern = alias.pattern;
                        if borrow_birth {
                            changed.bindings[row.binding].birth = alias.birth;
                        }
                        assert!(
                            solved_facts(&changed).is_err(),
                            "{case}: another pattern role/birth replaced guarded receiver {}",
                            row.binding
                        );
                    }
                }
            }
            let mut changed = facts.clone();
            changed
                .binding_sources
                .retain(|other| other.binding != row.binding);
            changed.bindings[row.binding].pattern = None;
            assert!(
                solved_facts(&changed).is_err(),
                "{case}: guarded receiver {} lost its pattern and receipt",
                row.binding
            );
            let initializer = changed.expressions[row.initializer.expression]
                .value
                .corrupt_value(&mut 4_000_000)
                .unwrap();
            if let Some(present) = &mut initializer.option_tag {
                *present = !*present;
            } else if let Some(tag) = &mut initializer.variant_tag {
                *tag = "Empty".into();
            } else {
                continue;
            }
            assert!(
                solved_facts(&changed).is_err(),
                "{case}: a forged failed tag erased guarded receiver {}",
                row.binding
            );
            changed.source_types = Default::default();
            let errors = solved_facts(&changed)
                .expect_err("deleting the Source index also erased an actual guarded receiver");
            assert!(
                format!("{errors:?}").contains("lost its original HIR introducer"),
                "{case}: a missing Source index replaced independent binding-origin replay: {errors:?}"
            );
            changed.bindings[row.binding].birth = None;
            assert!(
                solved_facts(&changed).is_err(),
                "removing the whole binding origin erased its reception duty"
            );
        }
    }

    #[test]
    fn shadowed_and_sibling_guarded_receivers_keep_independent_reception_duties() {
        guarded_receipts_remain_required("guarded-binding-shadowed-receivers", false, 3);
    }

    #[test]
    fn alternative_common_binders_keep_the_whole_patterns_reception_duty() {
        guarded_receipts_remain_required("guarded-binding-alternative-receivers", true, 1);
    }
}
mod callable_inputs {
    use crate as ril_compiler;
    use crate::{
        CheckOptions, Session,
        sema::{
            application_effect::{EntryOrigin, InputOrigin},
            validate::solved_facts,
        },
    };

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
            let _core = ril_compiler::lower::lower_core(&program).unwrap();

            for mutation in 0..15 {
                let mut changed = facts.clone();
                let ScopeOrigin::Operation(entry) =
                    &mut changed.scopes.get_mut(&first).unwrap().origin
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
                        changed.expressions[callee.0 as usize]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .callables = vec![Callable::Builtin("Div::exhausted".into())]
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
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
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
}
mod callable_row_uses {
    use crate as ril_compiler;
    use crate::Session;
    #[test]
    fn entered_symbolic_uses_survive_summaries_and_reject_forged_coverage() {
        let source = ril_test::case_source(
            "tests/regressions/source-observations.ril::callable-product-open-row",
        );
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let facts = program.facts();
        let (summary_index, summary) = facts
            .invocations
            .iter()
            .enumerate()
            .find(|(_, summary)| !summary.symbolic_uses.is_empty())
            .unwrap();
        let observed = *summary.symbolic_uses.first().unwrap();
        let mut removed = facts.clone();
        removed.invocations.clear();
        removed.definition_checks.clear();
        assert!(
            ril_compiler::sema::validate::solved_facts(&removed)
                .unwrap_err()
                .iter()
                .any(|issue| matches!(
                    issue.kind,
                    ril_compiler::sema::validate::ValidationIssueKind::SymbolicRow(_)
                ))
        );
        let _core = ril_compiler::lower::lower_core(&program).unwrap();
        for mutation in 0..6 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.invocations[summary_index].symbolic_uses.clear(),
                1 => {
                    changed.invocations[summary_index]
                        .symbolic_uses
                        .insert(ril_compiler_core::ids::EvaluationOccurrenceId(u32::MAX));
                }
                2 => changed.invocations[summary_index].activation = None,
                3 => {
                    changed.evaluations[observed.0 as usize]
                        .context
                        .budget_validation = true;
                    changed.invocation_expressions[observed.0 as usize]
                        .context
                        .budget_validation = true;
                }
                4 => {
                    changed.expressions[observed.0 as usize]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .callable_bounds[0]
                        .source = Some(ril_compiler_core::ids::CallableContractSource::Type(
                        ril_compiler_core::ids::TypeExprId(u32::MAX),
                    ));
                }
                5 => {
                    changed.expressions[observed.0 as usize]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .callable_bounds[0]
                        .annotations[0]
                        .text = "&{}".into();
                }
                _ => unreachable!(),
            }
            assert!(
                ril_compiler::sema::validate::solved_facts(&changed).is_err(),
                "symbolic row mutation {mutation}"
            );
        }
    }
}
mod closure_occurrences {
    use crate as ril_compiler;
    use crate::{
        CheckOptions, Session,
        sema::{SemanticFacts, validate::solved_facts},
    };
    use ril_compiler_core::ids::{CallableOwner, ClosureSiteId, ExprId};
    fn verified(name: &str, layout: &str) -> SemanticFacts {
        let source = ril_test::case_source(&format!(
            "tests/regressions/closure-occurrences.ril::{name}"
        ));
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{name} {layout}: {error:?}"));
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        for site in &program.facts().closure_sites {
            assert!(
                core.metadata
                    .closure_sites
                    .iter()
                    .any(|lowered| lowered.id == site.id && lowered.source == site.source)
            );
        }
        program.facts().clone()
    }

    #[test]
    fn deleting_or_substituting_site_identity_never_erases_a_closure_obligation() {
        let facts = verified("two-written", "pointer64");
        assert!(facts.closure_sites.len() >= 2);
        for mutation in 0..9 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.closure_sites.clear(),
                1 => changed.closure_sites[0].source = changed.closure_sites[1].source,
                2 => changed.closure_sites[0].source = ExprId(u32::MAX),
                3 => changed.closure_sites[0].owner = CallableOwner::Lambda(ClosureSiteId(0)),
                4 => changed.closures[0].hir_id = changed.closures[1].hir_id,
                5 => changed.closures[0].site = None,
                6 => {
                    changed.closure_sites.clear();
                    changed.closures.clear();
                    for expression in &mut changed.expressions {
                        expression
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .callables
                            .clear();
                    }
                }
                7 => changed.closure_sites[1].id = changed.closure_sites[0].id,
                8 => {
                    changed.closures.clear();
                    for expression in &mut changed.expressions {
                        expression
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .callables
                            .clear();
                    }
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "closure site mutation {mutation}"
            );
        }
    }
}
mod record_bound_validation {
    use crate as ril_compiler;
    use crate::{
        Session,
        sema::{
            SemanticFacts,
            validate::{ValidationIssueKind, solved_facts},
        },
    };
    fn verified(source: &str) -> SemanticFacts {
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let facts = verified.facts().clone();
        solved_facts(&facts).unwrap();
        facts
    }

    fn rejected(facts: &SemanticFacts) {
        let issues = solved_facts(facts).unwrap_err();
        assert!(
            issues
                .iter()
                .any(|issue| matches!(issue.kind, ValidationIssueKind::RecordBound(_))),
            "{issues:?}"
        );
    }

    #[test]
    fn readonly_stored_edge_cannot_gain_permission_even_if_output_metadata_agrees() {
        let source = "fn first<T:{items:[2]int,..R}>(value:T)->int{value.items[0]}\npub fn test_native(){let items:[2]int=[7,9];assert(first(.{items:items})==7)}";
        let facts = verified(source);
        let index = facts
            .generic_bound_projections
            .iter()
            .position(|projection| {
                projection.output.value.ty
                    == ril_compiler::sema::model::Ty::Array(Box::new(
                        ril_compiler::sema::model::Ty::Int("int".into()),
                    ))
            })
            .unwrap();
        let mut damaged = facts.clone();
        let cause = damaged.generic_bound_projections[index].output.value.cause;
        damaged.generic_bound_projections[index]
            .output
            .value
            .permission = ril_compiler::sema::facts::Permission::Write;
        for expression in &mut damaged.expressions {
            if expression.value.cause == cause {
                expression
                    .value
                    .corrupt_value(&mut 4_000_000)
                    .unwrap()
                    .permission = ril_compiler::sema::facts::Permission::Write
            }
        }
        rejected(&damaged);
        let mut damaged = facts;
        damaged.generic_bound_projections[index].access =
            ril_compiler::sema::record_bounds::BoundAccess::Write;
        rejected(&damaged);
    }

    #[test]
    fn symbolic_keyof_replay_preserves_all_origins_without_selecting_a_member() {
        let source =
            ril_test::case_source("tests/regressions/record-bounds.ril::symbolic-coordinate");
        let direct = verified(&source.replace("record.(key)", "record.(K)"));
        assert!(direct.expressions.iter().any(|expression| matches!(
            expression.value.ty,
            ril_compiler::sema::model::Ty::Projection { .. }
        )));
        let facts = verified(source);
        let output = facts
            .expressions
            .iter()
            .position(|expression| {
                matches!(
                    expression.value.ty,
                    ril_compiler::sema::model::Ty::Projection { .. }
                )
            })
            .unwrap();
        let cause = facts.expressions[output].value.cause;
        let parents = facts.explanations.causes[cause.0 as usize].parents.clone();
        assert_eq!(parents.len(), 2);
        for mutation in 0..12 {
            let mut damaged = facts.clone();
            match mutation {
                0 => {
                    damaged.expressions[output]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .permission = ril_compiler::sema::facts::Permission::Write
                }
                1 => damaged.expressions[output]
                    .value
                    .corrupt_value(&mut 4_000_000)
                    .unwrap()
                    .origins
                    .nodes
                    .clear(),
                2 => damaged.expressions[output]
                    .value
                    .corrupt_value(&mut 4_000_000)
                    .unwrap()
                    .results
                    .clear(),
                3 => {
                    damaged.expressions[output]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .must_results
                        .insert(*facts.expressions[output].value.results.first().unwrap());
                }
                4 => {
                    damaged.expressions[output]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .construction = true
                }
                5 => damaged.explanations.causes[cause.0 as usize]
                    .parents
                    .reverse(),
                6 => damaged.invocation_expressions.retain(|observation| {
                    damaged.expressions[observation.expression].value.cause != parents[0]
                }),
                7 => damaged.invocation_expressions.retain(|observation| {
                    damaged.expressions[observation.expression].value.cause != parents[1]
                }),
                8 => damaged.expressions[output]
                    .value
                    .corrupt_value(&mut 4_000_000)
                    .unwrap()
                    .participants
                    .clear(),
                9 => {
                    let key_owner = damaged
                        .functions
                        .iter_mut()
                        .find(|function| function.syntax.name == "get_field")
                        .unwrap();
                    let bound = key_owner.syntax.generics[1].bound.as_mut().unwrap();
                    let ril_syntax::ast::TypeKind::KeyOf(receiver) = &mut bound.kind else {
                        unreachable!()
                    };
                    receiver.kind = ril_syntax::ast::TypeKind::Name {
                        path: vec!["str".into()],
                        arguments: vec![],
                    };
                }
                10 => {
                    let source = facts
                        .expressions
                        .iter()
                        .find(|expression| expression.value.cause == parents[0])
                        .unwrap();
                    let forged = if source.value.publication
                        == ril_compiler::sema::facts::Publication::Immutable
                    {
                        ril_compiler::sema::facts::Publication::Live
                    } else {
                        ril_compiler::sema::facts::Publication::Immutable
                    };
                    for expression in &mut damaged.expressions {
                        if expression.value.cause == parents[0] || expression.value.cause == cause {
                            expression
                                .value
                                .corrupt_value(&mut 4_000_000)
                                .unwrap()
                                .publication = forged;
                        }
                    }
                }
                _ => {
                    let source = facts
                        .expressions
                        .iter()
                        .find(|expression| expression.value.cause == parents[0])
                        .unwrap();
                    let binding = *source.value.sources.first().unwrap();
                    let genuine =
                        ril_compiler::sema::facts::Participant::Root(facts.bindings[binding].root);
                    let borrowed = ril_compiler::sema::facts::RootId(binding as u32 + 1);
                    damaged.bindings[binding].root = borrowed;
                    for expression in &mut damaged.expressions {
                        if expression.value.cause == parents[0] || expression.value.cause == cause {
                            expression
                                .value
                                .corrupt_value(&mut 4_000_000)
                                .unwrap()
                                .participants
                                .remove(&genuine);
                            expression
                                .value
                                .corrupt_value(&mut 4_000_000)
                                .unwrap()
                                .participants
                                .insert(ril_compiler::sema::facts::Participant::Root(borrowed));
                        }
                    }
                }
            }
            rejected(&damaged);
        }
        let mut damaged = facts;
        damaged
            .invocation_expressions
            .retain(|observation| observation.expression != output);
        rejected(&damaged);
    }

    #[test]
    fn literal_coordinates_need_their_actual_key_and_named_field_observations() {
        for coordinate in [r#""id""#, "`id`", r#""i\u{64}""#] {
            let source = format!(
                "fn read<T:{{id:int,tag:int,..R}}>(value:T)->int{{value.({coordinate})}}\npub fn test_native(){{assert(read(.{{id:7,tag:9}})==7)}}"
            );
            let facts = verified(&source);
            let projection = facts
                .generic_bound_projections
                .iter()
                .find(|projection| {
                    matches!(
                        &projection.source.value.ty,
                        ril_compiler::sema::model::Ty::Generic(_)
                    ) && projection.slot == ril_compiler::sema::facts::Slot::Field("id".into())
                })
                .unwrap();
            let context = projection.context;
            let key = facts
                .invocation_expressions
                .iter()
                .find(|observation| {
                    observation.context == context
                        && facts.expressions[observation.expression]
                            .value
                            .static_coordinate
                            == Some(ril_compiler::sema::model::StaticCoordinate::Label(
                                "id".into(),
                            ))
                })
                .unwrap()
                .expression;
            for mutation in 0..4 {
                let mut damaged = facts.clone();
                match mutation {
                    0 => damaged.invocation_expressions.retain(|observation| {
                        observation.context != context || observation.expression != key
                    }),
                    1 => {
                        damaged.expressions[key]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .static_coordinate = Some(
                            ril_compiler::sema::model::StaticCoordinate::Label("tag".into()),
                        );
                    }
                    2 => {
                        damaged.expressions[key]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .ty = ril_compiler::sema::model::Ty::Int("int".into());
                    }
                    _ => damaged.generic_bound_projections.retain(|observation| {
                        observation.context != context || observation.cause != projection.cause
                    }),
                }
                rejected(&damaged);
            }
            ril_compiler::lower::lower_core(
                &Session::new(source.as_bytes().to_vec()).verify().unwrap(),
            )
            .unwrap();
        }
        let runtime_key = "fn read<T:{id:int,..R}>(value:T,key:str)->int{value.(key)}";
        assert!(matches!(
            Session::new(runtime_key.as_bytes().to_vec()).check(),
            ril_compiler::CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0324")
        ));
    }
}
mod storage_callable {
    use crate as ril_compiler;
    use crate::Session;
    #[test]
    fn primitive_declaration_receipts_cannot_be_deleted_swapped_or_monomorphized() {
        use ril_compiler::sema::{builtin_sources::BuiltinDeclaration, validate::solved_facts};
        use ril_compiler_core::builtin_calls::GenericBuiltin;
        let source = "fn example(){let raw=Array::push;let append:fn(mut [][0][2]int,[0][2]int)->() &mut=raw;let mut items:[][0][2]int=[];append(mut items,[])}";
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        for mutation in 0..8 {
            let mut facts = program.facts().clone();
            let observation = facts
                .builtin_source_observations
                .iter()
                .position(|row| row.identity == "Array::push")
                .unwrap();
            match mutation {
                0 => {
                    facts.builtin_source_observations.remove(observation);
                }
                1 => {
                    facts.builtin_source_observations[observation].full_header =
                        BuiltinDeclaration::Generic(GenericBuiltin::ArrayInsert)
                }
                2 => facts.builtin_source_observations[observation]
                    .written_formals
                    .clear(),
                3 => {
                    let entry = facts.builtin_source_observations[observation].expression;
                    facts.expressions[entry]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .signature = Some(vec![]);
                }
                4 => facts
                    .bindings
                    .iter_mut()
                    .find(|binding| binding.name == "append")
                    .unwrap()
                    .value
                    .callables
                    .clear(),
                5 => {
                    let entry = facts.builtin_source_observations[observation].expression;
                    facts.expressions[entry]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .ty = ril_compiler::sema::model::Ty::Unit;
                }
                6 | 7 => {
                    let signature = if mutation == 6 {
                        "fn(mut [][0][3]int,[0][3]int)->()&mut"
                    } else {
                        "fn(mut [][0][2]int,[0][2]int)->()&{}"
                    };
                    let replacement = Session::new(
                        format!("fn other(){{let changed:{signature}=Array::push}}").into_bytes(),
                    )
                    .analyze();
                    let witness = replacement
                        .facts()
                        .unwrap()
                        .bindings
                        .iter()
                        .find(|binding| binding.name == "changed")
                        .unwrap()
                        .value
                        .source_type_witness
                        .clone()
                        .unwrap();
                    let value = &mut facts
                        .bindings
                        .iter_mut()
                        .find(|binding| binding.name == "append")
                        .unwrap()
                        .value;
                    value.source_type_witness = Some(witness);
                    value.callable_bounds.clear();
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&facts).is_err(),
                "primitive declaration mutation {mutation}"
            );
        }
    }
}
mod storage_source_receiving {
    use crate as ril_compiler;
    use crate::{CheckOptions, Session};
    #[test]
    fn deleting_a_write_and_forging_a_never_rhs_cannot_erase_reception() {
        use ril_compiler::sema::{
            model::Ty,
            validate::{ValidationIssueKind, solved_facts},
        };
        for case in [
            "tests/regressions/source-observations.ril::matching-variable-replacement",
            "tests/regressions/source-observations.ril::matching-record-member-replacement",
            "tests/regressions/source-observations.ril::matching-array-element-replacement",
        ] {
            for target in ["pointer32", "pointer64"] {
                let verified = Session::with_options(
                    ril_test::case_bytes(case).to_vec(),
                    CheckOptions {
                        target: target.into(),
                        ..Default::default()
                    },
                )
                .verify()
                .unwrap_or_else(|outcome| panic!("{case}, {target}: {outcome:?}"));
                let facts = verified.facts();
                solved_facts(facts).unwrap();
                let write = facts
                    .storage_writes
                    .first()
                    .expect("fixture has an actual replacement");
                let rhs = write.rhs.expression;
                assert_ne!(facts.expressions[rhs].value.ty, Ty::Never);
                for forge_never in [false, true] {
                    let mut changed = facts.clone();
                    changed.storage_writes.remove(0);
                    if forge_never {
                        changed.expressions[rhs]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .ty = Ty::Never;
                    }
                    let issues = solved_facts(&changed).unwrap_err();
                    assert!(
                        issues.iter().any(|issue| matches!(
                            issue.kind,
                            ValidationIssueKind::StorageSource(_)
                        )),
                        "{case}, {target}, forged Never={forge_never}: {issues:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn forged_never_receivers_and_selectors_cannot_claim_an_aborted_write() {
        use ril_compiler::sema::{
            model::Ty,
            storage_sources::StorageDestination,
            validate::{ValidationIssueKind, solved_facts},
        };
        for case in [
            "tests/regressions/source-observations.ril::matching-record-member-replacement",
            "tests/regressions/source-observations.ril::matching-array-element-replacement",
        ] {
            for target in ["pointer32", "pointer64"] {
                let verified = Session::with_options(
                    ril_test::case_bytes(case).to_vec(),
                    CheckOptions {
                        target: target.into(),
                        ..Default::default()
                    },
                )
                .verify()
                .unwrap_or_else(|outcome| panic!("{case}, {target}: {outcome:?}"));
                let facts = verified.facts();
                solved_facts(facts).unwrap();
                let original = facts
                    .storage_writes
                    .first()
                    .expect("fixture has an actual replacement");
                assert!(original.completed && original.expected.is_some());
                let StorageDestination::Projection {
                    receiver, selector, ..
                } = &original.destination
                else {
                    panic!("fixture has an original member/index destination")
                };
                let (receiver, selector) = (*receiver, *selector);
                for corrupt_selector in [false, true] {
                    let observation = if corrupt_selector {
                        let Some(selector) = selector else { continue };
                        selector
                    } else {
                        receiver
                    };
                    assert_ne!(
                        facts.expressions[observation.expression].value.ty,
                        Ty::Never
                    );
                    let mut changed = facts.clone();
                    changed.expressions[observation.expression]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .ty = Ty::Never;
                    let write = &mut changed.storage_writes[0];
                    write.completed = false;
                    write.expected = None;
                    if !corrupt_selector {
                        let StorageDestination::Projection { selector, .. } =
                            &mut write.destination
                        else {
                            unreachable!()
                        };
                        *selector = None;
                    }
                    let issues = solved_facts(&changed).unwrap_err();
                    assert!(
                        issues.iter().any(|issue| matches!(
                            issue.kind,
                            ValidationIssueKind::StorageSource(_)
                        )),
                        "{case}, {target}, corrupt selector={corrupt_selector}: {issues:?}"
                    );
                }
            }
        }
    }
}
mod io_fixed_receivers {
    use crate as ril_compiler;
    use crate::Session;
    #[test]
    fn builtin_identity_validation_rejects_forged_names_and_builtin_type_arguments() {
        use ril_syntax::ast::{TypeExpr, TypeKind};
        let verified = Session::new(
            ril_test::case_bytes("tests/regressions/io.ril::io-fixed-receiver").to_vec(),
        )
        .verify()
        .unwrap();
        for (name, arguments, key) in [
            ("File::Forged", vec![], "File::Forged<>"),
            (
                "File::Handle",
                vec![TypeExpr {
                    hir_id: None,
                    span: verified.facts().expressions[0].span,
                    text: String::new(),
                    kind: TypeKind::Name {
                        path: vec!["int".into()],
                        arguments: vec![],
                    },
                }],
                "File::Handle<int<>>",
            ),
        ] {
            let mut facts = verified.facts().clone();
            let value = facts.expressions[0]
                .value
                .corrupt_value(&mut 4_000_000)
                .unwrap();
            let witness = ril_compiler::sema::model::SourceTypeWitness {
                syntax: TypeExpr {
                    hir_id: None,
                    span: verified.facts().expressions[0].span,
                    text: String::new(),
                    kind: TypeKind::Name {
                        path: name.split("::").map(str::to_owned).collect(),
                        arguments,
                    },
                },
                key: key.into(),
            };
            assert!(witness.validate_closed());
            value.source_type_witness = Some(std::sync::Arc::new(witness));
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
}
mod record_bound_nested {
    use crate as ril_compiler;
    use crate::{
        Session,
        sema::{
            SemanticFacts,
            validate::{ValidationIssueKind, solved_facts},
        },
    };
    fn tuple_fixture() -> &'static str {
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-tuple")
    }

    fn verified(source: &str) -> SemanticFacts {
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let facts = program.facts().clone();
        solved_facts(&facts).unwrap();
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
        facts
    }

    fn damaged(facts: &SemanticFacts) {
        let errors = solved_facts(facts).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|issue| matches!(issue.kind, ValidationIssueKind::RecordBound(_))),
            "{errors:?}"
        );
    }

    #[test]
    fn nested_read_reception_cannot_gain_authority_or_lose_its_root_observation() {
        let facts = verified(tuple_fixture());
        let projection = facts
            .generic_bound_projections
            .iter()
            .find(|projection| {
                matches!(
                    &projection.source.value.ty,
                    ril_compiler::sema::model::Ty::Generic(_)
                )
            })
            .unwrap();
        let context = projection.context;
        let cause = projection.source.value.cause;
        for mutation in 0..6 {
            let mut copy = facts.clone();
            if mutation == 3 {
                copy.invocation_expressions.retain(|observation| {
                    observation.context != context
                        || !matches!(
                            copy.expressions[observation.expression].value.ty,
                            ril_compiler::sema::model::Ty::Tuple(_)
                        )
                });
            } else if mutation >= 4 {
                let root = copy
                    .invocation_expressions
                    .iter()
                    .find(|observation| {
                        observation.context == context
                            && matches!(
                                copy.expressions[observation.expression].value.ty,
                                ril_compiler::sema::model::Ty::Tuple(_)
                            )
                    })
                    .unwrap()
                    .expression;
                let other = copy
                    .invocation_expressions
                    .iter()
                    .filter(|observation| observation.context == context)
                    .map(|observation| &copy.expressions[observation.expression])
                    .find(|expression| {
                        expression.source_id.is_some()
                            && expression.source_id != copy.expressions[root].source_id
                    })
                    .unwrap()
                    .source_id;
                copy.expressions[root].source_id = if mutation == 4 { None } else { other };
            } else {
                for value in copy
                    .expressions
                    .iter_mut()
                    .filter(|expression| expression.value.cause == cause)
                    .map(|expression| expression.value.corrupt_value(&mut 4_000_000).unwrap())
                    .chain(
                        copy.generic_bound_projections
                            .iter_mut()
                            .filter(|projection| {
                                projection.context == context
                                    && projection.source.value.cause == cause
                            })
                            .map(|projection| &mut projection.source.value),
                    )
                {
                    match mutation {
                        0 => value.permission = ril_compiler::sema::facts::Permission::Write,
                        1 => value.construction = true,
                        _ => value.participants.clear(),
                    }
                }
            }
            damaged(&copy);
        }
    }
}

mod non_tail_reference_answers {
    use crate as ril_compiler;
    use crate::{Session, sema};
    fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        sema::resumption::validate(verified.facts()).unwrap();
        let _core = ril_compiler::lower::lower_core(&verified).unwrap();
        verified
    }

    #[test]
    fn helper_recency_moves_transport_actual_answers_without_rewriting_snapshots() {
        let verified = accepted(ril_test::case_source(
            "tests/regressions/effects.ril::non-tail-reference-answer-recency",
        ));
        assert!(
            verified
                .facts()
                .resumption_steps
                .iter()
                .any(|step| step.completion_epoch > step.continuation_epoch)
        );
        assert_original_resumption_epochs(verified.facts());
    }

    #[test]
    fn original_resumption_epochs_are_independently_checked_in_incomplete_analysis() {
        let source = ril_test::case_source(
            "tests/regressions/effects.ril::non-tail-reference-answer-recency",
        );
        let analysis = Session::new(source.as_bytes().to_vec()).analyze();
        let facts = analysis.facts().expect("actual continuation observations");
        // This checks the resumption domain alone. The acceptance test above
        // continues to require independent validation of every domain and Core.
        sema::resumption::validate(facts).unwrap();
        assert!(!facts.resumption_steps.is_empty());
        assert_original_resumption_epochs(facts);
    }

    fn assert_original_resumption_epochs(facts: &sema::SemanticFacts) {
        let mut work = 4_000_000;
        for step in &facts.resumption_steps {
            for (index, epoch) in [
                (step.continuation_expression, step.continuation_epoch),
                (step.arm_expression, step.completion_epoch),
            ] {
                assert_eq!(facts.expressions[index].allocation_epoch, epoch);
                let mut damaged = facts.clone();
                damaged.expressions[index].allocation_epoch = epoch + 1;
                assert!(
                    sema::resumption::validate(&damaged).is_err(),
                    "a matching value from another epoch is not this resumption observation"
                );
            }
        }
        let step = facts
            .resumption_steps
            .iter()
            .find(|step| {
                let fact = &facts.expressions[step.continuation_expression];
                fact.value_at(
                    facts.allocation_history.len(),
                    &facts.allocation_history,
                    &mut work,
                )
                .is_some_and(|later| later.origins != fact.value.origins)
            })
            .expect("the real helper allocation must age an earlier continuation answer");
        let mut damaged = facts.clone();
        let fact = &mut damaged.expressions[step.continuation_expression];
        let replacement = fact
            .value_at(
                facts.allocation_history.len(),
                &facts.allocation_history,
                &mut work,
            )
            .unwrap();
        *fact.value.corrupt_value(&mut work).unwrap() = replacement;
        assert!(
            sema::resumption::validate(&damaged).is_err(),
            "replacing history with a final graph must not satisfy the original snapshot"
        );
    }
}
