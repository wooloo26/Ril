use ril_compiler::{CheckOptions, Session};

#[test]
fn concurrency_fault_payloads_keep_their_catalog_declarations_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes(
                "tests/regressions/generated-scopes.ril::scope-fault-declarations",
            )
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

#[test]
fn physical_scope_tokens_reach_inferred_callback_parameters() {
    for target in ["pointer32", "pointer64"] {
        for case in ["scope-token", "repeated-scope-token"] {
            let program = Session::with_options(
                ril_test::case_bytes(&format!("tests/regressions/generated-scopes.ril::{case}"))
                    .to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
            let _core = ril_compiler::lower::lower_core(&program).unwrap();
            let _facts = program.facts();
        }
    }
}
