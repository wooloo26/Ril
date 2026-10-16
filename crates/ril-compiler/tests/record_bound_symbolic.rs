use ril_compiler::sema::{
    effect_identity::ArgumentKey, effect_identity::StaticBinderSort, facts::Slot,
};
use ril_compiler::{
    CheckOptions, CompilationOutcome, Session,
    sema::{
        SemanticFacts,
        model::Ty,
        validate::{ValidationIssueKind, solved_facts},
    },
};

fn array_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-array")
}
fn empty_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-empty")
}
fn callable_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-callable")
}

fn verified(source: &str, target: &str) -> SemanticFacts {
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap();
    let facts = program.facts().clone();
    assert!(
        !facts.scoped_source_identities.is_empty(),
        "did not exercise scoped source identity"
    );
    solved_facts(&facts).unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    assert_eq!(
        core.provenance.scoped_source_identities.len(),
        facts.scoped_source_identities.len()
    );
    if target == "pointer64" {
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
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
fn a_symbolic_array_member_keeps_its_genuine_u_and_complete_fixed_shape() {
    for target in ["pointer32", "pointer64"] {
        verified(array_fixture(), target);
    }
}

#[test]
fn an_empty_outer_member_does_not_invent_a_u_element_or_erase_inner_dimensions() {
    for target in ["pointer32", "pointer64"] {
        let facts = verified(empty_fixture(), target);
        assert!(
            facts
                .scoped_source_identities
                .iter()
                .any(|identity| identity.occurrences.len() == 2)
        );
    }
}

#[test]
fn a_symbolic_callable_member_keeps_its_parameter_and_return_interfaces() {
    for target in ["pointer32", "pointer64"] {
        verified(callable_fixture(), target);
    }
}

#[test]
fn a_known_inner_dimension_conflict_remains_a_type_error_under_symbolic_u() {
    let source = ril_test::case_source(
        "tests/regressions/record-bounds.ril::scoped-symbolic-wrong-dimension",
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
        if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
        "{outcome:?}"
    );
}

#[test]
fn a_numeric_receiver_cannot_override_the_type_of_the_actual_fixed_input() {
    let source = array_fixture().replace(
        "assert(forward((.{items:items,tag:\"same\"},0))==7)",
        "let wrong:f64=forward((.{items:items,tag:\"same\"},0))",
    );
    assert_ne!(
        source,
        array_fixture(),
        "negative did not change the real receiving position"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
        if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
        "{outcome:?}"
    );
}

#[test]
fn a_true_expected_only_numeric_instance_still_needs_its_separate_proof() {
    let source = "fn value<U>()->U{panic(\"never\")}\nfn use_value(){let selected:int=value()}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    // This is a retained implementation boundary, not a desired language
    // rejection or a completed native case for a diverging generic function.
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn different_unproved_binders_and_readonly_writes_cannot_be_authorized() {
    for source in [
        ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-wrong-binder"),
        ril_test::case_source(
            "tests/regressions/record-bounds.ril::scoped-symbolic-readonly-write",
        ),
    ] {
        // A retained NI is a nonauthorization guard, not a successful negative
        // language conformance case. In particular U/V is not disjointness.
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            !matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{outcome:?}"
        );
    }
}

#[test]
fn deleted_coverage_missing_entry_tables_and_wrong_epochs_never_issue_member_tokens() {
    let facts = verified(empty_fixture(), "pointer64");
    let identity = &facts.scoped_source_identities[0];
    let mut copy = facts.clone();
    copy.scoped_source_identities.clear();
    for call in &mut copy.copy_invocations {
        call.declaration_probe = true;
    }
    damaged(&copy);
    for invocation in [
        identity.context.invocation.unwrap(),
        identity.occurrences[0].formal.invocation,
    ] {
        let mut copy = facts.clone();
        copy.copy_invocations[invocation.0 as usize]
            .arguments
            .clear();
        damaged(&copy);
    }
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].occurrences.pop();
    damaged(&copy);
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].occurrences[0]
        .formal
        .entry_allocation_epoch += 1;
    damaged(&copy);
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].occurrences[0]
        .formal
        .root_expression = usize::MAX;
    damaged(&copy);
}

#[test]
fn a_dependent_owned_u_requires_its_actual_static_argument_position() {
    let facts = verified(empty_fixture(), "pointer64");
    let source = &facts.scoped_source_identities[0];
    let check = facts
        .generic_bound_checks
        .iter()
        .find(|check| check.required == source.required && check.context == source.context)
        .unwrap();
    let target = facts.copy_invocations[check.context.invocation.unwrap().0 as usize].target;
    let binder = check
        .substitutions
        .iter()
        .find_map(|(binder, key)| {
            (facts
                .generic_binders
                .get(binder)
                .is_some_and(|owner| owner.definition == target)
                && matches!(key, ArgumentKey::Binder { identity, .. } if identity != binder
                && source.scope.types.values().any(|id| id == identity)))
            .then_some(binder.clone())
        })
        .expect("source did not select a real dependent owned U");
    for move_to_captured in [false, true] {
        let mut copy = facts.clone();
        let observed = copy
            .effect_invocations
            .iter_mut()
            .find(|event| event.invocation == check.context.invocation && event.function == target)
            .unwrap();
        let index = observed
            .arguments
            .iter()
            .position(|argument| argument.binder == binder)
            .unwrap();
        let removed = observed.arguments.remove(index);
        if move_to_captured {
            observed.captured_arguments.push(removed);
        }
        damaged(&copy);
    }
}

#[test]
fn actual_snapshot_bridges_fixed_storage_and_symbolic_sources_are_independent_obligations() {
    let facts = verified(array_fixture(), "pointer64");
    let identity = &facts.scoped_source_identities[0];
    let check = facts
        .generic_bound_checks
        .iter()
        .find(|check| check.context == identity.context && check.required == identity.required)
        .unwrap();
    let mut copy = facts.clone();
    let mut changed = 0;
    for node in &mut copy.generic_bound_checks[check.id.0 as usize].actual.nodes {
        if node.fixed {
            node.fixed = false;
            changed += 1;
        }
    }
    assert!(changed > 0, "mutation did not alter an actual fixed member");
    damaged(&copy);
    let original = identity.occurrences[0].formal.invocation;
    let mut copy = facts.clone();
    let mut changed = 0;
    for (_, snapshot) in &mut copy.copy_invocations[original.0 as usize].arguments {
        for node in &mut snapshot.nodes {
            for (_, value) in &mut node.fields {
                if matches!(value.ty, Ty::Generic(_)) && !value.origins.nodes.is_empty() {
                    value.origins.nodes.clear();
                    changed += 1;
                }
            }
        }
    }
    assert!(
        changed > 0,
        "mutation did not erase a real symbolic U source"
    );
    damaged(&copy);
}

#[test]
fn a_callable_cannot_borrow_another_members_signature_or_drop_its_received_returns() {
    let facts = verified(callable_fixture(), "pointer64");
    let original = facts.scoped_source_identities[0].occurrences[0]
        .formal
        .invocation;
    for erase_signature in [false, true] {
        let mut copy = facts.clone();
        let mut changed = 0;
        for (_, snapshot) in &mut copy.copy_invocations[original.0 as usize].arguments {
            for node in &mut snapshot.nodes {
                for (_, value) in &mut node.fields {
                    if matches!(value.ty, Ty::Callable(..)) {
                        if erase_signature {
                            value.signature = None;
                        } else {
                            value.callable_returns.clear();
                        }
                        changed += 1;
                    }
                }
            }
        }
        assert!(
            changed > 0,
            "mutation did not alter a stored callable member"
        );
        damaged(&copy);
    }
}

#[test]
fn dependent_u_must_match_its_original_stored_field_and_complete_coordinates() {
    let facts = verified(array_fixture(), "pointer64");
    let source = &facts.scoped_source_identities[0];
    let check = facts
        .generic_bound_checks
        .iter()
        .find(|check| check.required == source.required && check.context == source.context)
        .unwrap();
    let (dependent, caller) = check
        .substitutions
        .iter()
        .find_map(|(binder, key)| {
            let ArgumentKey::Binder { identity, .. } = key else {
                return None;
            };
            (identity != binder && source.scope.types.values().any(|id| id == identity))
                .then_some((binder.clone(), identity.clone()))
        })
        .expect("source did not exercise an open dependent U selection");
    let other = source
        .scope
        .types
        .values()
        .find(|id| **id != caller)
        .unwrap()
        .clone();
    let mut copy = facts.clone();
    copy.generic_bound_checks[check.id.0 as usize]
        .substitutions
        .insert(
            dependent,
            ArgumentKey::Binder {
                identity: other,
                sort: StaticBinderSort::Type,
            },
        );
    damaged(&copy);
    let mut copy = facts.clone();
    let invocation = check.context.invocation.unwrap();
    for snapshot in [
        &mut copy.copy_invocations[invocation.0 as usize].arguments[check.argument_index as usize]
            .1,
        &mut copy.generic_bound_checks[check.id.0 as usize].actual,
    ] {
        let mut removed = 0;
        for node in &mut snapshot.nodes {
            let before = node.fields.len();
            node.fields
                .retain(|(slot, _)| slot != &Slot::Field("items".into()));
            removed += before - node.fields.len();
        }
        assert!(
            removed > 0,
            "mutation did not delete the actual promised member"
        );
    }
    damaged(&copy);

    let facts = verified(callable_fixture(), "pointer64");
    let source = &facts.scoped_source_identities[0];
    let check = facts
        .generic_bound_checks
        .iter()
        .find(|check| check.required == source.required && check.context == source.context)
        .unwrap();
    let mut copy = facts.clone();
    let field = copy.generic_bound_checks[check.id.0 as usize]
        .actual_schema
        .fields
        .iter_mut()
        .find(|field| field.label == "action")
        .unwrap();
    let ArgumentKey::Callable { parameters, .. } = &mut field.key else {
        panic!("missing callable key");
    };
    parameters[0].0 = ril_syntax::ast::ParameterMode::Mut;
    let ril_syntax::ast::TypeKind::Callable { parameters, .. } = &mut field.syntax.kind else {
        panic!("missing callable source syntax");
    };
    parameters[0].mode = ril_syntax::ast::ParameterMode::Mut;
    damaged(&copy);

    let facts = verified(empty_fixture(), "pointer64");
    let mut copy = facts.clone();
    let key = &mut copy.scoped_source_identities[0].key;
    let ArgumentKey::Record { fields, .. } = key else {
        panic!("missing record key");
    };
    let (_, _, key) = fields
        .iter_mut()
        .find(|(name, _, _)| name == "items")
        .unwrap();
    let ArgumentKey::Array { element, .. } = key else {
        panic!("missing empty outer array");
    };
    let ArgumentKey::Array { length, .. } = element.as_mut() else {
        panic!("missing inner array");
    };
    *length = Some("const(int:3)".into());
    damaged(&copy);
}
