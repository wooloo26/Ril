//! Handler receivers have their own actual frame and complete Source header.
use ril_compiler::{CheckOptions, Session};

fn accepts(case: &str) {
    let source = ril_test::case_source(&format!("tests/conformance/effects.ril::{case}"));
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{case}, {target}: {error:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn zero_argument_and_forwarded_handlers_keep_their_actual_activation() {
    for case in [
        "deep-resumption",
        "outer-handler-forwarding",
        "system-yield-local-handling",
    ] {
        accepts(case);
    }
}

#[test]
fn operation_parameters_use_their_operation_header() {
    for case in [
        "accept-handler-parameter-mode",
        "accept-ended-operation-loan",
    ] {
        accepts(case);
    }
}

#[test]
fn operation_and_resume_boundaries_keep_complete_source_views() {
    for case in ["fixed-operation-view", "generic-operation-view"] {
        let source = ril_test::case_source(&format!(
            "tests/regressions/effect-source-views.ril::{case}"
        ));
        for target in ["pointer32", "pointer64"] {
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{case}, {target}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
    for case in [
        "reject-operation-hidden-dimension",
        "reject-resumption-hidden-dimension",
    ] {
        let source = ril_test::case_source(&format!(
            "tests/regressions/effect-source-views.ril::{case}"
        ));
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, ril_compiler::CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{case}: {outcome:?}"
        );
    }
}
