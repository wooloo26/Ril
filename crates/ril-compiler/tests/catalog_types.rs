use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn catalog_constants_keep_their_original_generated_pattern_reads() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes("tests/regressions/catalog-types.ril::catalog-constant-patterns")
                .to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{target}: {error:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn catalog_payloads_keep_their_numeric_views_through_nested_patterns() {
    for target in ["pointer32", "pointer64"] {
        let options = CheckOptions {
            target: target.into(),
            ..Default::default()
        };
        let program = Session::with_options(
            ril_test::case_bytes(
                "tests/regressions/catalog-types.ril::nested-constructor-patterns",
            )
            .to_vec(),
            options.clone(),
        )
        .verify()
        .unwrap_or_else(|error| panic!("{target}: {error:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
        let outcome = Session::with_options(
            ril_test::case_bytes(
                "tests/regressions/catalog-types.ril::constructor-pattern-overflow",
            )
            .to_vec(),
            options,
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0326")),
            "{target}: {outcome:?}"
        );
    }
}
