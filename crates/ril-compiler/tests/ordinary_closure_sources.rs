//! Lambda Source types retain their real creator, body and parameter scopes.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn step_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::closure-captured-step")
}

fn verified(source: &str) -> SemanticFacts {
    let mut facts = None;
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
        facts = Some(program.facts().clone());
    }
    facts.unwrap()
}

#[test]
fn nested_generic_stages_keep_each_enclosing_binding() {
    verified(ril_test::case_source(
        "tests/regressions/nested-closures.ril::generic-three-stage-pointer64",
    ));
    verified(ril_test::case_source(
        "tests/regressions/nested-closures.ril::generic-interface-shadow-pointer64",
    ));
}

#[test]
fn separate_generic_instances_keep_types_and_hidden_dimensions() {
    for case in [
        "reject-generic-instance-mix",
        "reject-generic-instance-hidden-extent",
    ] {
        let source =
            ril_test::case_source(&format!("tests/regressions/nested-closures.ril::{case}"));
        for target in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{case} {target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn real_lambda_bodies_and_immutable_generic_locals_supply_complete_source() {
    for source in [
        step_fixture(),
        ril_test::case_source("tests/regressions/source-observations.ril::closure-generic-return"),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generic-immutable-empty-local",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generic-tuple-projection",
        ),
    ] {
        verified(source);
    }
}

#[test]
fn an_open_public_fn_view_does_not_recover_the_original_parameter_view() {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::reject-open-fn-fixed-recovery",
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
        if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn captured_named_headers_keep_their_own_type_selection_at_each_entry() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::named-generic-captured-header-where",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::named-generic-distinct-instances-where",
        ),
    ] {
        verified(source);
    }
}

#[test]
fn open_callable_rows_survive_real_product_operands() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::callable-product-open-row",
        ),
        ril_test::case_source("tests/regressions/record-bounds.ril::scoped-callable-mut"),
    ] {
        verified(source);
    }
}
