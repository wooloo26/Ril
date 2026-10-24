//! Unregistered source and independent replay checks for immediate named Types.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn array_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-array-explicit")
}
fn empty_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-empty-explicit")
}
fn callable_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-callable-explicit")
}
fn prefix_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::explicit-named-prefix")
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
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    if target == "pointer64" {
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
    facts
}

#[test]
fn the_three_preserved_explicit_sources_have_real_source_and_core_proofs() {
    for source in [array_fixture(), empty_fixture(), callable_fixture()] {
        for target in ["pointer32", "pointer64"] {
            verified(source, target);
        }
    }
}

#[test]
fn explicit_unused_type_and_partial_prefix_keep_complete_source_identity() {
    for target in ["pointer32", "pointer64"] {
        verified(prefix_fixture(), target);
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
