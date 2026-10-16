use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn positive_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/static.ril::static-const-result-flow")
}

#[test]
fn const_roles_survive_block_pattern_and_loop_shadows_without_changing_result_identity() {
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            positive_fixture().as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        if target == "pointer64" {
            ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
        }
    }
}

#[test]
fn passing_a_const_and_receiving_its_result_does_not_inspect_that_result() {
    let source = r#"
meta fn echo<n:int>()->Result<int,str>{Ok(n)}
meta let ANSWER={let unhandled=echo<7>();7}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}

#[test]
fn a_closed_actual_const_cannot_discharge_a_duty_on_another_universal_branch() {
    let source = r#"
meta fn hidden<n:int>()->int{
    if n==2 {0} else {let dropped:Result<int,str>=Ok(n);0}
}
meta let ACTUAL=hidden<2>()
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    // An unresolved branch feasibility proof remains NI. This is a Rust
    // nonauthorization check, not a completed negative language case if NI.
    assert!(
        matches!(&outcome, CompilationOutcome::NotImplemented { .. })
            || matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}

#[test]
fn removing_a_local_inspection_matches_a_fresh_session() {
    let mut incremental = Session::new(positive_fixture().as_bytes().to_vec());
    incremental.verify().unwrap();
    let changed = positive_fixture().replacen("assert(local is Ok(_)|Err(_))", "assert(n==11)", 1);
    for source in [changed.as_str(), positive_fixture()] {
        incremental.update(source.as_bytes().to_vec());
        let fresh = Session::new(source.as_bytes().to_vec());
        let fresh_outcome = fresh.check();
        if source == changed {
            assert!(
                matches!(&fresh_outcome, CompilationOutcome::Rejected { diagnostics }
                    if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
                "{fresh_outcome:?}"
            );
        }
        assert_eq!(
            serde_json::to_value(incremental.check()).unwrap(),
            serde_json::to_value(fresh_outcome).unwrap()
        );
    }
}
