use ril_compiler::{CheckOptions, CompilationOutcome, Session, sema::validate::solved_facts};

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

#[test]
fn catalog_constructor_metadata_cannot_replace_its_actual_declaration() {
    let program = Session::new(
        ril_test::case_bytes("tests/regressions/catalog-types.ril::nested-constructor-patterns")
            .to_vec(),
    )
    .verify()
    .unwrap();
    for mutation in 0..7 {
        let mut facts = program.facts().clone();
        let other_payload = facts.constructors["Process::Input::Data"]
            .payload_syntax
            .clone();
        let constructor = facts
            .constructors
            .get_mut("Process::ExitStatus::Exited")
            .unwrap();
        match mutation {
            0 => constructor.tag = "Process::ExitStatus::Signaled".into(),
            1 => constructor.typing_environment = Default::default(),
            2 => constructor.owner = ril_compiler::sema::model::Ty::Named("Process::Input".into()),
            3 => constructor.payload = ril_compiler::sema::model::Ty::Int("u64".into()),
            4 => constructor.payload_syntax = other_payload,
            5 => constructor.has_payload = false,
            6 => constructor.nominal = true,
            _ => unreachable!(),
        }
        assert!(solved_facts(&facts).is_err(), "catalog mutation {mutation}");
    }
}
