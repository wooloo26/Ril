use ril_compiler::{CheckOptions, CompilationOutcome, Session, sema::SemanticFacts};

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
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    if target == "pointer64" {
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
    facts
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
