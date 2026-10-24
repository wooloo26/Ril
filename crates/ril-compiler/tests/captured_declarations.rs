use ril_compiler::{CheckOptions, Session};

#[test]
fn closure_defaults_keep_lexical_captures_and_ordered_parameter_environments() {
    let source = ril_test::case_source(
        "tests/regressions/evaluation-identity.ril::closure-default-lexical-environment",
    );
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}
