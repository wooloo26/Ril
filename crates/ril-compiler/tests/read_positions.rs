use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn guarded_positions_keep_original_types_and_receiver_contracts_on_both_layouts() {
    for layout in ["pointer32", "pointer64"] {
        for (name, diagnostic) in [
            ("position-identity-copy", None),
            ("position-cache-and-zero", None),
            ("position-other-identity", None),
            ("position-different-callback", None),
            ("position-buffer-switch", None),
            ("position-seek-reserved", None),
            ("position-shared-identity", None),
            ("position-budget-abort", None),
            ("position-requires-identity", Some("E0301")),
            ("position-no-type-arguments", Some("E0340")),
            ("position-static-reflection", None),
            ("position-static-no-type-arguments", Some("E0340")),
            ("position-runtime-only-factory", Some("E0810")),
        ] {
            let id = format!("tests/stdlib/io.ril::{name}");
            let result = Session::with_options(
                ril_test::case_source(&id).as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify();
            if let Some(code) = diagnostic {
                assert!(
                    matches!(&result, Err(CompilationOutcome::Rejected { diagnostics }) if diagnostics.iter().any(|item| item.code == code)),
                    "{id} {layout}: {result:?}"
                );
            } else {
                let verified = result.unwrap_or_else(|error| panic!("{id} {layout}: {error:?}"));
                ril_compiler::lower::lower_core(&verified).unwrap();
            }
        }
    }
}
