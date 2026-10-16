use ril_compiler::{CheckOptions, CompilationOutcome, Session};

const VALID: &str = include_str!("fixtures/static_result_context_flow.ril");
const CONTAINERS: &str = include_str!("fixtures/static_result_context_containers.ril");
const SHADOW: &str = include_str!("fixtures/static_result_context_shadow.ril");

#[test]
fn result_contexts_follow_returns_constructor_payloads_and_fallbacks() {
    for target in ["pointer32", "pointer64"] {
        for source in [VALID, CONTAINERS, SHADOW] {
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
    let source = SHADOW.replace("Ok([1, 2, 3])", "Ok([1, 2])");
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
        VALID.replace("assert(final.0 is Ok(_))", "assert(wrapped is Some(_))"),
        VALID.replace("assert(final.0 is Ok(_))", "assert(len(final.1) == 0)"),
        CONTAINERS.replace(
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
    let mut incremental = Session::new(VALID.as_bytes().to_vec());
    incremental.verify().unwrap();
    let dropped = VALID.replace("assert(final.0 is Ok(_))", "assert(wrapped is Some(_))");
    for source in [dropped.as_str(), VALID] {
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
