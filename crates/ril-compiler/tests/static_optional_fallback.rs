use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn optional_fallback_returns_the_original_or_reached_producer_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes("tests/regressions/static.ril::static-optional-result-fallback")
                .to_vec(),
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

#[test]
fn neither_presence_nor_actual_some_can_discharge_an_uninspected_result() {
    for source in [
        "meta let _={let pending:Result<int,str>=Ok(7);let selected:?Result<int,str>=Some(pending);let returned=selected??Err(\"unused\");()}",
        "meta let _={let selected:?Result<int,str>=None;let returned=selected??Err(\"reached\");()}",
        "meta fn ignored(value:?Result<int,str>){let returned=value??Err(\"fallback\");()}\nmeta let _={let pending:Result<int,str>=Ok(7);ignored(Some(pending));assert(pending is Ok(_))}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
            "{source}\n{outcome:?}"
        );
    }
}
