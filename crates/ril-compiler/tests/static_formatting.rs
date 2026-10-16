use ril_compiler::{CheckOptions, CompilationOutcome, Session};
fn check(source: &str, target: &str) -> CompilationOutcome {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .check()
}
#[test]
fn static_interpolation_executes_the_complete_scalar_rules() {
    let source = r#"
meta let _=assert("{-42:05}"=="-0042")
meta let _=assert("{255bigint:04X}"=="00FF")
meta let _=assert("{1.25:.1f}"=="1.2")
meta let _=assert("{12.5:.2e}"=="1.25e1")
meta let _=assert("{9.99:.1e}"=="1.0e1")
meta let _=assert("{1.2f32}"=="1.2")
meta let _=assert("{-0.0}"=="-0.0")
meta let _=assert("{1.0e-7}"=="1e-7")
meta let _=assert("{1.0e20}"=="100000000000000000000.0")
meta let TEXT="é🙂x"
meta let _=assert("{TEXT:🙂^5.2s}"=="🙂é🙂🙂🙂")
meta let _=assert("{true:>6}"=="  true")
"#;
    for target in ["pointer32", "pointer64"] {
        let outcome = check(source, target);
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{target}: {outcome:?}"
        );
    }
}
#[test]
fn target_bounds_are_checked_even_without_static_execution() {
    for prefix in ["fn", "meta fn"] {
        let source = format!("{prefix} wide(value:int)->str {{\"{{value:2147483648}}\"}}");
        let narrow = check(&source, "pointer32");
        assert!(
            matches!(narrow,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|d|d.code=="E0112")),
            "{narrow:?}"
        );
        let wide = check(&source, "pointer64");
        assert!(
            matches!(wide, CompilationOutcome::Accepted { .. }),
            "{wide:?}"
        );
    }
    let outcome = check("meta let TEXT=\"{1:2147483648}\"", "pointer64");
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}
#[test]
fn unevaluated_static_formats_still_require_compatible_types() {
    for source in [
        "meta fn wrong(value:f64)->str{\"{value:.2}\"}",
        "meta fn wrong(value:int)->str{\"{value:.2f}\"}",
        "meta fn wrong(value:bool)->str{\"{value:s}\"}",
    ] {
        let outcome = check(source, "pointer64");
        assert!(
            matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|d|d.code=="E0329")),
            "{outcome:?}"
        );
    }
}
