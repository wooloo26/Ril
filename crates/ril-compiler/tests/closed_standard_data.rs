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

#[test]
fn generated_record_callbacks_cannot_borrow_another_receiver_field_or_scalar() {
    use ril_compiler::sema::{
        application_effect::{EntryOrigin, InputOrigin, ScalarInput},
        validate::solved_facts,
    };
    let source =
        ril_test::case_source("tests/regressions/closed-standard-data.ril::repeated-reader");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let calls: Vec<_> = facts
        .copy_invocations
        .iter()
        .enumerate()
        .filter(|(_, call)| {
            matches!(&call.entry.origin,
        EntryOrigin::Generated { inputs, .. } if inputs.len()==2)
        })
        .map(|(index, _)| index)
        .collect();
    assert!(calls.len() >= 2);
    let (first, other) = (calls[0], calls[1]);
    for mutation in 0..10 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.copy_invocations[first].entry.origin = EntryOrigin::Unresolved,
            1 => {
                changed.copy_invocations[first].entry.origin =
                    changed.copy_invocations[other].entry.origin.clone()
            }
            2 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                inputs[0] =
                    InputOrigin::Widened(ril_compiler_core::ids::EvaluationOccurrenceId(u32::MAX));
            }
            3 => {
                let EntryOrigin::Generated { inputs, .. } =
                    &mut changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                inputs[1] = InputOrigin::Scalar(ScalarInput::ByteSuffix(
                    ril_compiler_core::ids::EvaluationOccurrenceId(0),
                ));
            }
            4 => {
                changed.copy_invocations[first].entry.arguments[0]
                    .1
                    .value
                    .temporary = false
            }
            5 => {
                changed.copy_invocations[first].entry.arguments[0]
                    .1
                    .value
                    .permission = ril_compiler::sema::facts::Permission::Read
            }
            6 => {
                changed.copy_invocations[first].entry.arguments[1]
                    .1
                    .value
                    .ty = ril_compiler::sema::model::Ty::Bytes
            }
            7 => changed.copy_invocations[first].entry.arguments[0]
                .1
                .value
                .origins
                .nodes
                .clear(),
            8 => {
                let EntryOrigin::Generated { callee, .. } =
                    changed.copy_invocations[first].entry.origin
                else {
                    unreachable!()
                };
                changed.expressions[callee.0 as usize]
                    .value
                    .callables
                    .clear();
            }
            9 => {
                changed.copy_invocations[first].entry =
                    changed.copy_invocations[other].entry.clone()
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "record callback mutation {mutation}"
        );
    }
}

#[test]
fn signature_assumptions_are_universal_formals_and_cannot_supply_concrete_data() {
    use ril_compiler::sema::{application_effect::EntryOrigin, validate::solved_facts};
    let source =
        ril_test::case_source("tests/regressions/closed-standard-data.ril::repeated-reader");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let first = facts
        .copy_invocations
        .iter()
        .position(|call| call.entry.origin == EntryOrigin::SignatureProbe)
        .unwrap();
    for mutation in 0..7 {
        let mut changed = facts.clone();
        let binding = *changed.copy_invocations[first].entry.arguments[0]
            .1
            .value
            .sources
            .first()
            .unwrap();
        match mutation {
            0 => {
                changed.copy_invocations[first].entry.arguments[0]
                    .1
                    .value
                    .source_type_witness = None
            }
            1 => {
                changed.copy_invocations[first].entry.arguments[0]
                    .1
                    .value
                    .constant = Some(ril_compiler::sema::model::Constant::Bool(false))
            }
            2 => changed.bindings[binding].parameter = false,
            3 => {
                changed.bindings[binding].pattern =
                    Some(ril_compiler_core::ids::PatternId(u32::MAX))
            }
            4 => {
                changed.copy_invocations[first].entry.arguments[0].1.nodes[0]
                    .fact
                    .kind = ril_compiler::sema::facts::OriginKind::Opaque
            }
            5 => {
                changed.copy_invocations[first].source_event =
                    Some(ril_compiler::sema::copy_contract::CopyCallEventId(0))
            }
            6 => changed.copy_invocations[first].entry.arguments[0]
                .1
                .nodes
                .clear(),
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "signature assumption mutation {mutation}"
        );
    }
}
