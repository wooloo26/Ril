use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn resumed_expression_contexts_receive_the_actual_owned_answer() {
    for target in ["pointer32", "pointer64"] {
        for case in ["scalar-native", "suffix-order", "derived-native"] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/resumption-expressions.ril::{case}"
            ));
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{case}/{target}: {outcome:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
            assert!(!program.facts().resumption_steps.is_empty());
        }
    }
}

#[test]
fn resumed_expressions_keep_receiving_loans_and_affine_use_rules() {
    for target in ["pointer32", "pointer64"] {
        for (case, code) in [
            ("reject-derived-dimension", "E0301"),
            ("reject-readonly-answer", "E0520"),
            ("reject-ended-operation-loan", "E0540"),
            ("reject-terminated-answer", "E0625"),
            ("reject-affine-resumption", "E0610"),
        ] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/resumption-expressions.ril::{case}"
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
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case}/{target}: {outcome:?}"
            );
        }
    }
}
