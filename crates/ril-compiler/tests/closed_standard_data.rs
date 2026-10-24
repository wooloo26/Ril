use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn closed_standard_sources_keep_nominal_identity_dynamic_views_and_fresh_authority() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "command-derive",
            "byte-array-fresh",
            "repeated-reader",
            "closed-constructors",
            "buffered-callback-source",
        ] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/closed-standard-data.ril::{case}"
            ));
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{case} {target}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
        for case in [
            "command-args-not-fixed",
            "command-mode-type",
            "repeated-reader-mismatch",
        ] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/closed-standard-data.ril::{case}"
            ));
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{case} {target}: {outcome:?}"
            );
        }
    }
}
