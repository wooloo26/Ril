//! Mutation tests consume real ordinary producer facts after Root registers the
//! independent replay. They never hand-assemble successful application proofs.
use ril_compiler::{
    Session,
    sema::{
        SemanticFacts,
        validate::{ValidationIssueKind, solved_facts},
    },
};

const SOURCE: &str = include_str!("fixtures/record_bounds/original_projection.ril");

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
fn source_declarations_and_actual_checks_have_independent_nonvacuous_coverage() {
    let facts = verified(SOURCE);
    assert!(
        !facts.record_bounds.is_empty()
            && !facts.generic_bound_checks.is_empty()
            && !facts.generic_bound_projections.is_empty()
    );
    for removed in 0..4 {
        let mut damaged = facts.clone();
        match removed {
            0 => damaged.record_bounds.clear(),
            1 => damaged.bound_rows.clear(),
            2 => damaged.generic_bound_checks.clear(),
            _ => damaged.generic_bound_projections.clear(),
        }
        rejected(&damaged);
    }
}

#[test]
fn actual_call_identity_argument_path_epoch_and_activation_cannot_be_borrowed() {
    let source = "fn read<T:{id:int,..R}>(value:T)->int{value.id}\npub fn test_native(){assert(read(.{id:7,tag:\"first\"})==7);assert(read(.{id:8,tag:\"second\"})==8)}";
    let facts = verified(source);
    let actual: Vec<_> = facts
        .generic_bound_checks
        .iter()
        .enumerate()
        .filter(|(_, check)| {
            matches!(
                check.actual_schema.source,
                ril_compiler::sema::record_bounds::StructuralSchemaSource::Closed(_)
            )
        })
        .map(|(index, _)| index)
        .collect();
    assert!(actual.len() >= 2);
    for mutation in 0..5 {
        let mut damaged = facts.clone();
        let first = actual[0];
        let second = actual[1];
        match mutation {
            0 => {
                damaged.generic_bound_checks[first].actual =
                    facts.generic_bound_checks[second].actual.clone()
            }
            1 => {
                damaged.generic_bound_checks[first].context =
                    facts.generic_bound_checks[second].context
            }
            2 => damaged.generic_bound_checks[first].argument_index += 1,
            3 => damaged.generic_bound_checks[first].allocation_epoch += 1,
            _ => {
                damaged.generic_bound_checks[first].activation =
                    ril_compiler::sema::facts::ScopeId(0)
            }
        }
        rejected(&damaged);
    }
    let mut damaged = facts;
    damaged.generic_bound_checks[actual[0]]
        .selection_path
        .push(ril_compiler::sema::record_bounds::BoundTypeSelectionStep::ArrayElement);
    rejected(&damaged);
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
            expression.value.permission = ril_compiler::sema::facts::Permission::Write
        }
    }
    rejected(&damaged);
    let mut damaged = facts;
    damaged.generic_bound_projections[index].access =
        ril_compiler::sema::record_bounds::BoundAccess::Write;
    rejected(&damaged);
}

#[test]
fn fixed_storage_is_frozen_before_the_actual_application_entry() {
    let source = "fn first<T:{items:[2]int,..R}>(value:T)->int{value.items[0]}\npub fn test_native(){let items:[2]int=[7,9];assert(first(.{items:items})==7)}";
    let mut facts = verified(source);
    let check = facts
        .generic_bound_checks
        .iter_mut()
        .find(|check| {
            matches!(
                check.actual_schema.source,
                ril_compiler::sema::record_bounds::StructuralSchemaSource::Closed(_)
            )
        })
        .unwrap();
    let origin = check
        .actual
        .nodes
        .iter()
        .find(|node| node.fixed)
        .unwrap()
        .origin;
    let invocation = check.context.invocation.unwrap();
    let argument = check.argument_index as usize;
    for node in &mut check.actual.nodes {
        if node.origin == origin {
            node.fixed = false;
        }
    }
    let (_, actual) = &mut facts.copy_invocations[invocation.0 as usize].arguments[argument];
    for node in &mut actual.nodes {
        if node.origin == origin {
            node.fixed = false;
        }
    }
    rejected(&facts);
}

#[test]
fn forged_field_identity_and_row_absences_do_not_revalidate_one_another() {
    let facts = verified(SOURCE);
    let mut damaged = facts.clone();
    damaged.record_bounds[0].fields[0].key =
        ril_compiler::sema::effect_identity::ArgumentKey::Name {
            name: "str".into(),
            arguments: vec![],
        };
    rejected(&damaged);
    let mut damaged = facts;
    damaged.bound_rows[0].lacks.insert("invented".into());
    rejected(&damaged);
}

#[test]
fn symbolic_keyof_replay_preserves_all_origins_without_selecting_a_member() {
    let source = include_str!("fixtures/record_bounds/symbolic_coordinate.ril");
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
                damaged.expressions[output].value.permission =
                    ril_compiler::sema::facts::Permission::Write
            }
            1 => damaged.expressions[output].value.origins.nodes.clear(),
            2 => damaged.expressions[output].value.results.clear(),
            3 => {
                damaged.expressions[output]
                    .value
                    .must_results
                    .insert(*facts.expressions[output].value.results.first().unwrap());
            }
            4 => damaged.expressions[output].value.construction = true,
            5 => damaged.explanations.causes[cause.0 as usize]
                .parents
                .reverse(),
            6 => damaged.invocation_expressions.retain(|observation| {
                damaged.expressions[observation.expression].value.cause != parents[0]
            }),
            7 => damaged.invocation_expressions.retain(|observation| {
                damaged.expressions[observation.expression].value.cause != parents[1]
            }),
            8 => damaged.expressions[output].value.participants.clear(),
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
                        expression.value.publication = forged;
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
                        expression.value.participants.remove(&genuine);
                        expression
                            .value
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
                    damaged.expressions[key].value.static_coordinate = Some(
                        ril_compiler::sema::model::StaticCoordinate::Label("tag".into()),
                    );
                }
                2 => {
                    damaged.expressions[key].value.ty =
                        ril_compiler::sema::model::Ty::Int("int".into());
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

#[test]
fn a_declared_type_row_keeps_the_actual_selected_type_of_its_other_argument() {
    let source = "fn read<R,T:{id:int,..R}>(value:T,row:R)->int{value.id}\npub fn test_native(){assert(read(.{id:7,tag:\"ok\"},.{tag:\"ok\"})==7)}";
    let facts = verified(source);
    let row = facts
        .bound_rows
        .iter()
        .find_map(|row| match &row.role {
            ril_compiler::sema::record_bounds::BoundRowRole::DeclaredTypeParameter { binder } => {
                Some(binder.clone())
            }
            _ => None,
        })
        .unwrap();
    let index = facts
        .generic_bound_checks
        .iter()
        .position(|check| {
            matches!(
                check.actual_schema.source,
                ril_compiler::sema::record_bounds::StructuralSchemaSource::Closed(_)
            )
        })
        .unwrap();
    let invocation = facts.generic_bound_checks[index]
        .context
        .invocation
        .unwrap();
    let event = facts
        .effect_invocations
        .iter()
        .position(|event| event.invocation == Some(invocation))
        .unwrap();
    let argument = facts.effect_invocations[event]
        .arguments
        .iter()
        .position(|argument| argument.binder == row)
        .unwrap();
    let mut damaged = facts.clone();
    let forged = ril_compiler::sema::effect_identity::ArgumentKey::Record {
        fields: vec![],
        row: None,
    };
    damaged.effect_invocations[event].arguments[argument].key = Some(forged.clone());
    damaged.effect_invocations[event].arguments[argument]
        .syntax
        .as_mut()
        .unwrap()
        .kind = ril_syntax::ast::TypeKind::Record {
        fields: vec![],
        row: None,
    };
    damaged.generic_bound_checks[index]
        .substitutions
        .insert(row, forged);
    rejected(&damaged);
    let wrong = source.replace(".{tag:\"ok\"})", ".{tag:9})");
    assert!(matches!(
        Session::new(wrong.as_bytes().to_vec()).check(),
        ril_compiler::CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")
    ));
}
