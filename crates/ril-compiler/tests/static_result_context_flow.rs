use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn valid_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/static.ril::static-result-context-flow")
}
fn containers_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/static.ril::static-result-context-containers")
}
fn shadow_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/static.ril::static-result-context-shadow")
}

#[test]
fn result_contexts_follow_returns_constructor_payloads_and_fallbacks() {
    for target in ["pointer32", "pointer64"] {
        for source in [valid_fixture(), containers_fixture(), shadow_fixture()] {
            let verified = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap();
            ril_compiler::lower::lower_core(&verified).unwrap();
        }
    }
}

#[test]
fn an_outer_dimension_cannot_replace_the_nearer_local_dimension() {
    let source = shadow_fixture().replace("Ok([1, 2, 3])", "Ok([1, 2])");
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
            matches!(&outcome, CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{outcome:?}"
        );
    }
}

#[test]
fn contextual_receiving_and_presence_do_not_inspect_the_producer() {
    for source in [
        valid_fixture().replace("assert(final.0 is Ok(_))", "assert(wrapped is Some(_))"),
        valid_fixture().replace("assert(final.0 is Ok(_))", "assert(len(final.1) == 0)"),
        containers_fixture().replace(
            "assert(kept.0 is Ok(_))",
            "assert(table[\"item\"] is Some(_))",
        ),
    ] {
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
            "{outcome:?}"
        );
    }
}

#[test]
fn changing_a_contextual_result_inspection_matches_a_fresh_session() {
    let mut incremental = Session::new(valid_fixture().as_bytes().to_vec());
    incremental.verify().unwrap();
    let dropped = valid_fixture().replace("assert(final.0 is Ok(_))", "assert(wrapped is Some(_))");
    for source in [dropped.as_str(), valid_fixture()] {
        incremental.update(source.as_bytes().to_vec());
        let fresh = Session::new(source.as_bytes().to_vec());
        assert_eq!(
            serde_json::to_value(incremental.check()).unwrap(),
            serde_json::to_value(fresh.check()).unwrap(),
        );
    }
}

#[test]
fn an_actual_finite_argument_cannot_prove_a_universal_dynamic_length_branch() {
    let source = r#"
meta fn ignored(items: []int) -> int {
    let pending: Result<int, str> = Ok(7)
    if len(items) == 0 {} else { assert(pending is Ok(_)) }
    7
}
meta let ANSWER = ignored([])
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::NotImplemented { .. })
            || matches!(&outcome, CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}
