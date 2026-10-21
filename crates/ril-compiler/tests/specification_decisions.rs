use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn confirmed_specification_rules_preserve_their_required_distinctions() {
    for layout in ["pointer32", "pointer64"] {
        for (id, rejection) in [
            (
                "tests/conformance/static.ril::runtime-meta-named-source",
                None,
            ),
            (
                "tests/conformance/static.ril::runtime-meta-missing-source",
                Some("E0510"),
            ),
            (
                "tests/conformance/static.ril::static-meta-source-exemption",
                None,
            ),
            (
                "tests/conformance/parallel.ril::square-all-immutable-input",
                None,
            ),
            (
                "tests/conformance/parallel.ril::square-all-live-read-input",
                Some("E0605"),
            ),
            (
                "tests/conformance/parallel.ril::square-all-unbounded-callback",
                Some("E0820"),
            ),
            (
                "tests/regressions/evaluation-identity.ril::application-mutating-computed-callee-order",
                None,
            ),
            (
                "tests/regressions/evaluation-identity.ril::application-callee-selected-before-written-mutation",
                None,
            ),
            ("tests/stdlib/io.ril::buffered-seek-released", None),
            ("tests/stdlib/io.ril::buffered-seek-reserved", None),
        ] {
            let source = ril_test::case_source(id);
            let result = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify();
            if let Some(code) = rejection {
                assert!(
                    matches!(&result, Err(CompilationOutcome::Rejected { diagnostics })
                    if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                    "{id} {layout}: {result:?}"
                );
            } else {
                let program = result.unwrap_or_else(|error| panic!("{id} {layout}: {error:?}"));
                ril_compiler::lower::lower_core(&program).unwrap();
            }
        }
    }
}
