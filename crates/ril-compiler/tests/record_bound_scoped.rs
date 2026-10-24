use ril_compiler::{
    CheckOptions, CompilationOutcome, Session,
    sema::{SemanticFacts, record_bounds::BoundTypeSelectionStep},
};

fn fixed_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-fixed")
}
fn empty_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-empty-inner-dimension")
}
fn callable_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-callable-mut")
}
fn immutable_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-immutable-field")
}

fn verified(source: &str) -> SemanticFacts {
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts().clone();
    assert!(
        !facts.scoped_source_identities.is_empty(),
        "source did not exercise scoped identity"
    );
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    facts
}

#[test]
fn fixed_fields_have_complete_source_header_and_existing_product_receipts() {
    let facts = verified(fixed_fixture());
    let identity = &facts.scoped_source_identities[0];
    assert!(!identity.key.is_closed());
    assert!(
        identity
            .occurrences
            .iter()
            .all(|occurrence| !occurrence.selection_path.is_empty()
                && !occurrence.formal.type_path.is_empty())
    );
    assert!(
        identity
            .occurrences
            .iter()
            .all(|occurrence| facts.bindings[occurrence.formal.binding].parameter)
    );
    let pointer32 = Session::with_options(
        fixed_fixture().as_bytes().to_vec(),
        CheckOptions {
            target: "pointer32".into(),
            ..CheckOptions::default()
        },
    )
    .verify()
    .unwrap();
    assert!(!pointer32.facts().scoped_source_identities.is_empty());
}

#[test]
fn an_empty_outer_array_keeps_the_inner_dimension_without_inventing_t_elements() {
    let facts = verified(empty_fixture());
    assert_eq!(facts.scoped_source_identities[0].occurrences.len(), 2);
    assert!(
        facts.scoped_source_identities[0]
            .occurrences
            .iter()
            .all(
                |occurrence| occurrence.selection_path.iter().all(|step| matches!(
                    step,
                    BoundTypeSelectionStep::Tuple(_) | BoundTypeSelectionStep::Field(_)
                ))
            )
    );
}

#[test]
fn callable_parameter_modes_effect_qualifications_and_immutable_fields_survive() {
    for source in [callable_fixture(), immutable_fixture()] {
        verified(source);
    }
}

#[test]
fn complete_known_field_dimension_and_callable_mode_conflicts_are_type_errors() {
    for source in [
        ril_test::case_source(
            "tests/regressions/record-bounds.ril::scoped-wrong-empty-inner-dimension",
        ),
        ril_test::case_source("tests/regressions/record-bounds.ril::scoped-wrong-callable-mode"),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0301")),
            "{outcome:?}"
        );
    }
}
