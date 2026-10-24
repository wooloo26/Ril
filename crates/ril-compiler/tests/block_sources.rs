use ril_compiler::{CheckOptions, Session};

#[test]
fn normal_and_aborting_block_results_keep_owned_types() {
    let case = "tests/regressions/closures.ril::nested-and-budget";
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes(case).to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{case} {target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn aborts_and_resumption_binders_preserve_hidden_dimensions() {
    for target in ["pointer32", "pointer64"] {
        let options = CheckOptions {
            target: target.into(),
            ..Default::default()
        };
        let program = Session::with_options(
            ril_test::case_bytes(
                "tests/regressions/block-sources.ril::owned-boundary-arrays-pointer64",
            )
            .to_vec(),
            options.clone(),
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
        for case in [
            "reject-abort-hidden-dimension",
            "reject-resume-answer-hidden-dimension",
        ] {
            let input =
                ril_test::case_bytes(&format!("tests/regressions/block-sources.ril::{case}"));
            let outcome = Session::with_options(input.to_vec(), options.clone()).check();
            assert!(
                matches!(&outcome, ril_compiler::CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{case} {target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn empty_blocks_keep_their_actual_expression_owners() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes("tests/regressions/block-sources.ril::empty-block-contexts")
                .to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}
