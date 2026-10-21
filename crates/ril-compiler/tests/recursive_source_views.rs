use ril_compiler::{CheckOptions, Session, sema::validate::solved_facts};

#[test]
fn recursive_copies_and_abrupt_optional_fallbacks_keep_original_source_views() {
    let source = ril_test::case_source("tests/regressions/copy.ril::binary-recursive-copy");
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
        let facts = program.facts();
        solved_facts(facts).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        for name in ["child", "shared"] {
            let binding = facts
                .bindings
                .iter()
                .position(|binding| binding.name == name)
                .unwrap();
            let view = facts.source_types.binding_view(binding).unwrap();
            assert!(matches!(facts.source_types.key(view.ty).unwrap(),
                ril_compiler::sema::effect_identity::ArgumentKey::Name { arguments, .. } if arguments.is_empty()));
        }
        let mut damaged = facts.clone();
        damaged.source_types = Default::default();
        assert!(solved_facts(&damaged).is_err());
        let call = facts
            .copy_call_events
            .iter()
            .find(|event| event.copy_operation.is_some())
            .unwrap();
        let mut damaged = facts.clone();
        damaged
            .call_arguments
            .iter_mut()
            .find(|row| row.source_event == call.id)
            .unwrap()
            .supplied
            .get_mut(&0)
            .unwrap()
            .expression = call.result_expression.unwrap();
        assert!(solved_facts(&damaged).is_err());
        let mut damaged = facts.clone();
        damaged.copy_call_events[call.id.0 as usize].copy_operation = None;
        assert!(solved_facts(&damaged).is_err());
    }
}
