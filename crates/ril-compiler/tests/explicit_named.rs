//! Unregistered source and independent replay checks for immediate named Types.
use ril_compiler::sema::{
    SemanticFacts,
    effect_identity::ArgumentKey,
    validate::{ValidationIssueKind, solved_facts},
};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

const ARRAY: &str =
    include_str!("fixtures/record_bounds/pending/scoped_symbolic_array_explicit.ril");
const EMPTY: &str =
    include_str!("fixtures/record_bounds/pending/scoped_symbolic_empty_explicit.ril");
const CALLABLE: &str =
    include_str!("fixtures/record_bounds/pending/scoped_symbolic_callable_explicit.ril");
const PREFIX: &str =
    include_str!("fixtures/record_bounds/pending/explicit_named_prefix.ril.pending");

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
    solved_facts(&facts).unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    if target == "pointer64" {
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
    facts
}

fn explicit_damaged(facts: &SemanticFacts) {
    let errors = solved_facts(facts).unwrap_err();
    assert!(
        errors.iter().any(|issue| matches!(&issue.kind,
        ValidationIssueKind::RecordBound(message) if message.contains("explicit"))),
        "{errors:?}"
    );
}

#[test]
fn the_three_preserved_explicit_sources_have_real_source_and_core_proofs() {
    for source in [ARRAY, EMPTY, CALLABLE] {
        for target in ["pointer32", "pointer64"] {
            verified(source, target);
        }
    }
}

#[test]
fn explicit_unused_type_and_partial_prefix_keep_complete_source_identity() {
    for target in ["pointer32", "pointer64"] {
        verified(PREFIX, target);
    }
}

#[test]
fn explicit_and_input_disagreement_cannot_replace_the_prefix() {
    for source in [
        "fn id<T>(value:T)->T{value}\nfn example(){let value=id<bool>(1)}",
        "fn id<T>(value:T)->T{value}\nfn example(){let items:[3]int=[1,2,3];let value=id<[2]int>(items)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{outcome:?}"
        );
    }
}

#[test]
fn an_applied_named_value_still_needs_storage_and_escape_transport() {
    for source in [
        "fn id<T>(value:T)->T{value}\nfn example(){let applied=id<int>;let value=applied(1)}",
        "fn id<T>(value:T)->T{value}\nfn example(){let alias=id;let value=alias<int>(1)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            !matches!(
                &outcome,
                CompilationOutcome::Accepted { .. } | CompilationOutcome::Built { .. }
            ),
            "{outcome:?}"
        );
    }
}

#[test]
fn removing_an_unused_explicit_own_row_or_its_application_is_not_vacuous() {
    let facts = verified(PREFIX, "pointer64");
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "unused")
        .unwrap()
        .definition;
    let instance = facts
        .copy_invocations
        .iter()
        .find(|invocation| invocation.target == target && invocation.source_event.is_some())
        .unwrap();
    let mut missing = facts.clone();
    let row = missing
        .effect_invocations
        .iter_mut()
        .find(|row| row.invocation == Some(instance.id))
        .unwrap();
    assert_eq!(row.arguments.len(), 1);
    row.arguments.clear();
    explicit_damaged(&missing);
    let mut missing = facts.clone();
    let event = instance.source_event.unwrap();
    let row = &mut missing.copy_call_events[event.0 as usize];
    row.target = None;
    explicit_damaged(&missing);
}

#[test]
fn a_consistent_static_dimension_change_cannot_change_the_explicit_source() {
    let facts = verified(PREFIX, "pointer64");
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "unused")
        .unwrap()
        .definition;
    let instance = facts
        .copy_invocations
        .iter()
        .find(|invocation| invocation.target == target && invocation.source_event.is_some())
        .unwrap()
        .id;
    let mut changed = facts.clone();
    let row = changed
        .effect_invocations
        .iter_mut()
        .find(|row| row.invocation == Some(instance))
        .unwrap();
    let other_source = PREFIX
        .replace("[2]int", "[3]int")
        .replace("[13,17]", "[13,17,19]")
        .replace("[7,9]", "[7,9,11]");
    assert_ne!(other_source, PREFIX);
    let other = verified(&other_source, "pointer64");
    let other_target = other
        .functions
        .iter()
        .find(|function| function.syntax.name == "unused")
        .unwrap()
        .definition;
    let other_instance = other
        .copy_invocations
        .iter()
        .find(|invocation| invocation.target == other_target && invocation.source_event.is_some())
        .unwrap()
        .id;
    let other_row = other
        .effect_invocations
        .iter()
        .find(|row| row.invocation == Some(other_instance))
        .unwrap();
    assert_ne!(row.arguments[0].key, other_row.arguments[0].key);
    row.arguments[0].key = other_row.arguments[0].key.clone();
    row.arguments[0].syntax = other_row.arguments[0].syntax.clone();
    explicit_damaged(&changed);
}

#[test]
fn another_caller_u_cannot_replace_the_exact_explicit_type_binder() {
    let facts = verified(ARRAY, "pointer64");
    let callee = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "first")
        .unwrap()
        .definition;
    let caller = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "forward")
        .unwrap()
        .definition;
    let other = facts
        .generic_binders
        .values()
        .find(|binder| binder.definition == caller && binder.index == 1)
        .unwrap()
        .identity
        .clone();
    let instance = facts
        .copy_invocations
        .iter()
        .find(|invocation| {
            invocation.target == callee
                && invocation.source_event.is_some()
                && invocation.caller == Some(caller)
        })
        .unwrap()
        .id;
    let mut changed = facts.clone();
    let row = changed
        .effect_invocations
        .iter_mut()
        .find(|row| row.invocation == Some(instance))
        .unwrap();
    row.arguments[0].key = Some(ArgumentKey::Binder {
        identity: other.clone(),
        sort: ril_compiler::sema::effect_identity::StaticBinderSort::Type,
    });
    let token = format!("\0effect-binder:{other}");
    let syntax = row.arguments[0].syntax.as_mut().unwrap();
    syntax.kind = ril_syntax::ast::TypeKind::Name {
        path: vec![token],
        arguments: vec![],
    };
    explicit_damaged(&changed);
}
