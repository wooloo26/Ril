use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn closed_standard_sources_keep_nominal_identity_dynamic_views_and_fresh_authority() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "command-derive",
            "byte-array-fresh",
            "repeated-reader",
            "closed-constructors",
            "buffered-callback-source",
        ] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/closed-standard-data.ril::{case}"
            ));
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{case} {target}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
        for case in [
            "command-args-not-fixed",
            "command-mode-type",
            "repeated-reader-mismatch",
        ] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/closed-standard-data.ril::{case}"
            ));
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{case} {target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn standard_constructor_payloads_keep_their_declaration_even_without_a_user_type_header() {
    use ril_compiler::sema::validate::solved_facts;
    let source =
        ril_test::case_source("tests/regressions/closed-standard-data.ril::closed-constructors");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    for mutation in 0..3 {
        let mut facts = program.facts().clone();
        let input = facts.constructors["Process::Input::Data"]
            .payload_syntax
            .clone();
        let constructor = facts
            .constructors
            .get_mut("Process::ExitStatus::Exited")
            .unwrap();
        match mutation {
            0 => constructor.payload_syntax = input,
            1 => constructor.owner = ril_compiler::sema::model::Ty::Named("Process::Input".into()),
            2 => constructor.has_payload = false,
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&facts).is_err(),
            "standard constructor mutation {mutation}"
        );
    }
}
