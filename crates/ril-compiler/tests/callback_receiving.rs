use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn session(case: &str, target: &str) -> Session {
    let source =
        ril_test::case_source(&format!("tests/regressions/callback-receiving.ril::{case}"));
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
}

#[test]
fn callback_inputs_keep_the_actual_complete_types() {
    for target in ["pointer32", "pointer64"] {
        let program = session("inputs-native", target)
            .verify()
            .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn complete_inputs_do_not_amplify_types_permissions_effects_or_inspection() {
    for target in ["pointer32", "pointer64"] {
        for (case, code) in [
            ("reject-tuple-dimension", "E0301"),
            ("reject-fallback-dimension", "E0301"),
            ("reject-dynamic-fallback-dimension", "E0301"),
            ("reject-fallback-write", "E0520"),
            ("reject-nested-duty", "E0720"),
            ("reject-callback-effect-erasure", "E0534"),
        ] {
            let outcome = session(case, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case}/{target}: {outcome:?}"
            );
        }
    }
}
