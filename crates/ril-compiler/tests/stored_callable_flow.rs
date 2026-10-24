use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn stored_callable_contracts_and_loop_captures_keep_complete_types() {
    for case in [
        "tests/regressions/source-receiving.ril::storage-callable-contracts-pointer64",
        "tests/conformance/conditional-bindings.ril::while-let-capture-occurrences-pointer64",
    ] {
        for layout in ["pointer32", "pointer64"] {
            let program = Session::with_options(
                ril_test::case_bytes(case).to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{case} {layout}: {outcome:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
}

#[test]
fn stored_callbacks_check_latent_effects_and_unreachable_writes_remain_unused() {
    for (name, code) in [
        ("reject-stored-callable-effect", "E0534"),
        ("reject-nested-stored-callable-effect", "E0534"),
        ("reject-unreachable-loop-writer", "E0527"),
    ] {
        let case = format!("tests/regressions/source-receiving.ril::{name}");
        for layout in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                ril_test::case_bytes(&case).to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case} {layout}: {outcome:?}"
            );
        }
    }
}
