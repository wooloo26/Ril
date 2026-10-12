use ril_test::*;
use std::path::Path;

fn expected(mode: Mode) -> ExpectedOutcome {
    ExpectedOutcome {
        mode,
        errors: if mode == Mode::CheckFail {
            vec!["E0301".into()]
        } else {
            vec![]
        },
        exit: None,
        stdout: None,
        stderr: None,
    }
}
fn observed(runtime: RuntimeStatus) -> ObservedOutcome {
    ObservedOutcome {
        static_status: Some(StaticStatus::Accepted),
        build: Some(BuildStatus::Succeeded),
        runtime: Some(runtime),
        ..Default::default()
    }
}
#[test]
fn diagnostic_codes_are_structured_and_warnings_advisory() {
    let expectation = expected(Mode::CheckFail);
    for (status, codes, verdict) in [
        (StaticStatus::Rejected, vec!["E0301"], Verdict::Pass),
        (StaticStatus::Rejected, vec!["E0204"], Verdict::Fail),
        (StaticStatus::Accepted, vec![], Verdict::Fail),
        (
            StaticStatus::Rejected,
            vec!["E0344", "E0301"],
            Verdict::Pass,
        ),
        (StaticStatus::CompilerCrash, vec!["E0301"], Verdict::Fail),
    ] {
        let actual = ObservedOutcome {
            static_status: Some(status),
            errors: codes.into_iter().map(str::to_owned).collect(),
            ..Default::default()
        };
        assert_eq!(judge_outcome(&expectation, Some(&actual)), verdict);
    }
    let stderr_only = ObservedOutcome {
        static_status: Some(StaticStatus::Rejected),
        stderr: Some(b"Error E0301".to_vec()),
        ..Default::default()
    };
    assert_eq!(
        judge_outcome(&expectation, Some(&stderr_only)),
        Verdict::Fail
    );
    assert!(
        serde_json::from_str::<ObservedOutcome>(r#"{"static":"rejected","errors":"E0301"}"#)
            .is_err()
    );
    for warnings in [vec![], vec!["W0001".to_owned()]] {
        let actual = ObservedOutcome {
            static_status: Some(StaticStatus::Accepted),
            warnings,
            ..Default::default()
        };
        assert_eq!(
            judge_outcome(&expected(Mode::CheckPass), Some(&actual)),
            Verdict::Pass
        );
    }
    assert_eq!(judge_outcome(&expectation, None), Verdict::HarnessError);
    assert_eq!(
        judge_outcome(
            &expectation,
            Some(&ObservedOutcome {
                environment: Some("compiler-not-found".into()),
                ..Default::default()
            })
        ),
        Verdict::HarnessError
    );
}
#[test]
fn run_pass_requires_a_successful_build_and_normal_return() {
    use RuntimeStatus::*;
    for runtime in [
        ReturnedUnit,
        ReturnedOk,
        ReturnedErr,
        LanguagePanic,
        Cancelled,
        DoubleFault,
        NativeCrash,
        Timeout,
    ] {
        assert_eq!(
            judge_outcome(&expected(Mode::RunPass), Some(&observed(runtime))),
            if matches!(runtime, ReturnedUnit | ReturnedOk) {
                Verdict::Pass
            } else {
                Verdict::Fail
            }
        );
    }
    let mut actual = observed(ReturnedUnit);
    actual.build = Some(BuildStatus::Failed);
    assert_eq!(
        judge_outcome(&expected(Mode::RunPass), Some(&actual)),
        Verdict::Fail
    );
}
#[test]
fn panic_requires_the_designated_operation() {
    use RuntimeStatus::*;
    for runtime in [
        ReturnedErr,
        NativeCrash,
        Timeout,
        DoubleFault,
        Cancelled,
        ReturnedUnit,
    ] {
        let mut actual = observed(runtime);
        actual.exit = Some(1);
        assert_eq!(
            judge_outcome(&expected(Mode::RunPanic), Some(&actual)),
            Verdict::Fail
        );
    }
    let mut actual = observed(LanguagePanic);
    actual.origin = Some(PanicOrigin::DesignatedOperation);
    assert_eq!(
        judge_outcome(&expected(Mode::RunPanic), Some(&actual)),
        Verdict::Pass
    );
    actual.origin = Some(PanicOrigin::FixtureSetup);
    assert_eq!(
        judge_outcome(&expected(Mode::RunPanic), Some(&actual)),
        Verdict::Fail
    );
    actual.static_status = Some(StaticStatus::Rejected);
    actual.errors = vec!["E0831".into()];
    assert_eq!(
        judge_outcome(&expected(Mode::RunPanic), Some(&actual)),
        Verdict::Fail
    );
}
#[test]
fn program_outputs_are_byte_exact_and_exit_contracts_are_enforced() {
    use RuntimeStatus::*;
    let mut expectation = expected(Mode::RunProgram);
    expectation.exit = Some(0);
    expectation.stdout = Some(b"a\n".to_vec());
    let mut actual = observed(Exited);
    actual.exit = Some(0);
    actual.stdout = Some(b"a\r\n".to_vec());
    assert_eq!(judge_outcome(&expectation, Some(&actual)), Verdict::Fail);
    actual.stdout = Some(b"a\n".to_vec());
    assert_eq!(judge_outcome(&expectation, Some(&actual)), Verdict::Pass);
    actual.stdout = None;
    assert_eq!(judge_outcome(&expectation, Some(&actual)), Verdict::Fail);
    for (runtime, required_exit) in [
        (ReturnedUnit, 0),
        (ReturnedOk, 0),
        (ReturnedErr, 1),
        (LanguagePanic, 1),
        (DoubleFault, 1),
        (Cancelled, 1),
    ] {
        for exit in [0, 1, 2] {
            let mut expectation = expected(Mode::RunProgram);
            expectation.exit = Some(exit);
            let mut actual = observed(runtime);
            actual.exit = Some(exit);
            assert_eq!(
                judge_outcome(&expectation, Some(&actual)),
                if exit == required_exit {
                    Verdict::Pass
                } else {
                    Verdict::Fail
                }
            );
        }
    }
    for runtime in [NativeCrash, Timeout] {
        let mut actual = observed(runtime);
        actual.exit = Some(1);
        let mut expectation = expected(Mode::RunProgram);
        expectation.exit = Some(1);
        assert_eq!(judge_outcome(&expectation, Some(&actual)), Verdict::Fail);
    }
}
#[test]
fn classified_failures_cannot_pass_a_successful_corpus_case() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let cases = discover_cases(&root).unwrap();
    let case = cases
        .iter()
        .find(|case| case.id == "tests/integration/entry.ril::unit-success")
        .unwrap();
    let expectation = expected_outcome(case).unwrap();
    for runtime in [
        RuntimeStatus::ReturnedErr,
        RuntimeStatus::LanguagePanic,
        RuntimeStatus::DoubleFault,
        RuntimeStatus::Cancelled,
    ] {
        let mut actual = observed(runtime);
        actual.exit = Some(0);
        actual.stdout = Some(vec![]);
        actual.stderr = Some(vec![]);
        assert_eq!(judge_outcome(&expectation, Some(&actual)), Verdict::Fail);
    }
}
#[test]
fn empty_partial_unimplemented_or_invalid_reports_never_pass() {
    assert_eq!(
        summarize_execution(&ExecutionReport::default()),
        Verdict::Incomplete
    );
    for report in [
        ExecutionReport {
            selected: 1,
            unsupported_environment: 1,
            ..Default::default()
        },
        ExecutionReport {
            selected: 1,
            unimplemented: 1,
            ..Default::default()
        },
        ExecutionReport {
            selected: 2,
            attempted: 1,
            passed: 1,
            ..Default::default()
        },
    ] {
        assert_eq!(summarize_execution(&report), Verdict::Incomplete);
    }
    assert_eq!(
        summarize_execution(&ExecutionReport {
            selected: 2,
            attempted: 2,
            passed: 1,
            failed: 1,
            ..Default::default()
        }),
        Verdict::Fail
    );
    assert_eq!(
        summarize_execution(&ExecutionReport {
            harness_error: 1,
            ..Default::default()
        }),
        Verdict::HarnessError
    );
    assert_eq!(
        summarize_execution(&ExecutionReport {
            selected: 1,
            attempted: 1,
            passed: 1,
            ..Default::default()
        }),
        Verdict::Pass
    );
    assert!(
        serde_json::from_str::<ExecutionReport>(r#"{"selected":-1,"attempted":-1,"passed":-1}"#)
            .is_err()
    );
    for status in [
        StaticStatus::NotImplemented,
        StaticStatus::UnsupportedEnvironment,
    ] {
        let actual = ObservedOutcome {
            static_status: Some(status),
            ..Default::default()
        };
        for mode in Mode::ALL {
            assert_eq!(
                judge_outcome(&expected(mode), Some(&actual)),
                Verdict::Incomplete
            );
        }
    }
}
