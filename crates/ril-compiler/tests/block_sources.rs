use ril_compiler::{CheckOptions, Session};

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
