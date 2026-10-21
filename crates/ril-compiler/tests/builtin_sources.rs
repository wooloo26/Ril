use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn native_and_path_declarations_reach_core_on_both_layouts() {
    for layout in ["pointer32", "pointer64"] {
        for id in [
            "tests/stdlib/native.ril::posix-bytes",
            "tests/stdlib/native.ril::unicode-round-trip",
            "tests/stdlib/native.ril::windows-units",
            "tests/stdlib/path.ril::lexical-components",
            "tests/stdlib/path.ril::posix-lexical",
            "tests/stdlib/path.ril::windows-lexical",
        ] {
            let verified = Session::with_options(
                ril_test::case_source(id).as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{id} {layout}: {outcome:?}"));
            ril_compiler::lower::lower_core(&verified).unwrap();
        }
    }
}

#[test]
fn closed_declarations_preserve_source_views_across_receiving_boundaries() {
    for layout in ["pointer32", "pointer64"] {
        for (name, diagnostic) in [
            ("declared-boundaries", None),
            ("callable-pipeline-and-labels", None),
            ("handler-and-resumption", None),
            ("channel-transport", None),
            ("shadowed-effect-declaration", None),
            ("atomic-static-reflection", None),
            ("dynamic-array-is-not-fixed", Some("E0301")),
            ("closed-declaration-no-generics", Some("E0340")),
        ] {
            let id = format!("tests/regressions/builtin-source.ril::{name}");
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
