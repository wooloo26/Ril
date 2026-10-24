//! Source declaration views follow original HIR binders and typed projections.
use ril_compiler::{CheckOptions, Session, hir::VerifiedProgram, sema::validate::solved_facts};
use ril_compiler_core::projection::TypeProjection;

fn fixture(target: &str) -> VerifiedProgram {
    let source =
        ril_test::case_source("tests/conformance/rest-patterns.ril::record-rest-schema-pointer64");
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{target}: {error:?}"))
}

#[test]
fn binding_introducers_and_record_remainders_reach_core_with_complete_source() {
    use ril_compiler::sema::effect_identity::ArgumentKey;
    for target in ["pointer32", "pointer64"] {
        let program = fixture(target);
        let facts = program.facts();
        let (rest, _) = facts
            .bindings
            .iter()
            .enumerate()
            .find(|(_, binding)| binding.name == "rest")
            .unwrap();
        let id = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "id")
            .unwrap();
        let row = facts
            .binding_sources
            .iter()
            .find(|row| row.binding == id)
            .unwrap();
        assert_ne!(facts.bindings[id].pattern, Some(row.declaration));
        let row = facts
            .binding_sources
            .iter()
            .find(|row| row.binding == rest)
            .unwrap();
        assert_eq!(facts.bindings[rest].pattern, Some(row.declaration));
        assert!(
            matches!(row.path.as_deref(), Some([TypeProjection::RecordRemainder(fields)]) if fields.iter().map(String::as_str).collect::<Vec<_>>() == ["id"])
        );
        let source = facts.source_types.binding_type(rest).unwrap();
        let key = facts.source_types.key(source).unwrap();
        let ArgumentKey::Record { fields, .. } = key else {
            panic!("rest must retain a record view")
        };
        assert!(!fields.iter().any(|field| field.0 == "id"));
        assert!(fields.iter().any(|field| field.0 == "items" && matches!(&field.2,
            ArgumentKey::Array { length: Some(outer), element }
            if outer == "const(int:0)" && matches!(&**element, ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"))));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn projection_receipts_cannot_borrow_roots_paths_environments_or_other_binders() {
    let program = fixture("pointer64");
    let facts = program.facts();
    let rest = facts
        .bindings
        .iter()
        .position(|binding| binding.name == "rest")
        .unwrap();
    let field = facts
        .bindings
        .iter()
        .position(|binding| binding.name == "id")
        .unwrap();
    let position = facts
        .binding_sources
        .iter()
        .position(|row| row.binding == rest)
        .unwrap();
    for mutation in 0..8 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.bindings[rest].pattern = None,
            1 => {
                changed.bindings[field].pattern =
                    Some(changed.binding_sources[position].declaration)
            }
            2 => changed.binding_sources[position].path = Some(vec![]),
            3 => changed.binding_sources[position].path = None,
            4 => changed.bindings[rest].typing_environment = Default::default(),
            5 => {
                changed.binding_sources.remove(position);
            }
            6 => changed.source_types = Default::default(),
            _ => {
                changed.binding_sources.retain(|row| row.binding != field);
                changed.bindings[field].pattern = None;
            }
        }
        assert!(
            solved_facts(&changed).is_err(),
            "mutation {mutation} issued an unchecked binding projection"
        );
    }
    let mut reordered = facts.clone();
    reordered.binding_sources.reverse();
    solved_facts(&reordered).unwrap();
    let mut diagnostics = facts.clone();
    diagnostics.bindings[field].span = facts.bindings[rest].span;
    solved_facts(&diagnostics).expect("a diagnostic span must not choose a different binder");
}

#[test]
fn hir_projection_work_exhaustion_never_returns_a_partial_binding_plan() {
    let program = fixture("pointer64");
    let facts = program.facts();
    let rest = facts
        .bindings
        .iter()
        .position(|binding| binding.name == "rest")
        .unwrap();
    let row = facts
        .binding_sources
        .iter()
        .find(|row| row.binding == rest)
        .unwrap();
    let hir = facts.semantic_hir.as_ref().unwrap();
    let complete = hir.pattern_bindings(row.declaration, &mut 4096).unwrap();
    assert_eq!(complete.len(), 2);
    assert!(hir.pattern_bindings(row.declaration, &mut 0).is_err());
    assert_eq!(
        hir.pattern_bindings(row.declaration, &mut 4096)
            .unwrap()
            .len(),
        complete.len()
    );
}

#[test]
fn nested_projections_and_aliases_keep_their_original_frozen_interpretation() {
    let source = ril_test::case_source(
        "tests/conformance/rest-patterns.ril::nested-record-rest-view-pointer64",
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
        .unwrap_or_else(|error| panic!("{target}: {error:?}"));
        let facts = program.facts();
        let rest = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "rest")
            .unwrap();
        let alias = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "alias")
            .unwrap();
        assert_eq!(
            facts.bindings[rest].typing_environment.id(),
            facts.bindings[alias].typing_environment.id()
        );
        let row = facts
            .binding_sources
            .iter()
            .find(|row| row.binding == rest)
            .unwrap();
        assert!(
            matches!(row.path.as_deref(), Some([TypeProjection::Tuple(0), TypeProjection::RecordRemainder(fields)]) if fields.contains("id"))
        );
        let original = facts
            .source_types
            .key(facts.source_types.binding_type(rest).unwrap())
            .unwrap();
        let received = facts
            .source_types
            .key(facts.source_types.binding_type(alias).unwrap())
            .unwrap();
        assert_eq!(original, received);
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn guarded_receivers_cannot_hide_by_deleting_both_pattern_and_receipt() {
    let source = ril_test::case_source("tests/conformance/patterns.ril::guarded-binding");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let bindings: Vec<_> = facts
        .binding_sources
        .iter()
        .filter(|row| facts.bindings[row.binding].name == "value")
        .map(|row| row.binding)
        .collect();
    assert!(!bindings.is_empty());
    for binding in bindings {
        let mut changed = facts.clone();
        changed.binding_sources.retain(|row| row.binding != binding);
        changed.bindings[binding].pattern = None;
        assert!(
            solved_facts(&changed).is_err(),
            "guarded receiver {binding} lost its identity"
        );
    }
}

#[test]
fn protected_answer_birth_requires_its_own_answer_emission_and_resumption_step() {
    use ril_compiler::sema::application_effect::ActivationKind;
    let source = ril_test::case_source("tests/regressions/effects.ril::non-tail-reference-answer");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let receivers: Vec<_> = facts
        .binding_sources
        .iter()
        .filter(|row| {
            facts.bindings[row.binding].name == "answer"
                && facts
                    .resumption_steps
                    .iter()
                    .any(|step| step.continuation_expression == row.initializer.expression)
        })
        .collect();
    assert!(!receivers.is_empty());
    for row in receivers {
        let birth = facts.bindings[row.binding].birth.unwrap();
        assert_eq!(
            facts.activations[birth.activation.0 as usize].kind,
            ActivationKind::Emission
        );
        let step = facts
            .resumption_steps
            .iter()
            .find(|step| step.continuation_expression == row.initializer.expression)
            .unwrap();
        let request = facts
            .activations
            .iter()
            .find(|activation| {
                activation.kind == ActivationKind::ControlTransfer
                    && activation.source == Some(birth.source)
                    && activation.scope == row.activation
                    && activation.context == row.context
            })
            .unwrap();
        let ordinary = facts.evaluations[step.arm_expression].identity.unwrap();
        let sibling = facts
            .resumption_steps
            .iter()
            .find(|other| other.continuation_expression != row.initializer.expression)
            .unwrap();
        let sibling = facts.evaluations[sibling.continuation_expression]
            .identity
            .unwrap();
        for replacement in [
            ril_compiler::sema::application_effect::OccurrenceIdentity {
                source: birth.source,
                activation: request.id,
            },
            ordinary,
            sibling,
        ] {
            let mut changed = facts.clone();
            changed.bindings[row.binding].birth = Some(replacement);
            assert!(
                solved_facts(&changed).is_err(),
                "another request, emission or answer supplied the binding birth"
            );
        }
        let mut missing = facts.clone();
        missing
            .resumption_steps
            .retain(|step| step.continuation_expression != row.initializer.expression);
        assert!(
            solved_facts(&missing).is_err(),
            "an answer without its resumption step became an initializer"
        );
        let mut missing = facts.clone();
        missing
            .binding_sources
            .retain(|other| other.binding != row.binding);
        assert!(
            solved_facts(&missing).is_err(),
            "an emitted answer lost its receiving row"
        );
    }
}

fn optional_fixture(target: &str) -> VerifiedProgram {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::optional-projection-paths-pointer64",
    );
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{target}: {error:?}"))
}

#[test]
fn original_optional_reads_project_at_each_real_base_and_only_once_at_the_receiver() {
    use ril_compiler::sema::effect_identity::ArgumentKey;
    for target in ["pointer32", "pointer64"] {
        let program = optional_fixture(target);
        let facts = program.facts();
        for name in [
            "named", "field", "computed", "member", "selected", "indexed", "twice", "once",
        ] {
            let receivers: Vec<_> = facts
                .bindings
                .iter()
                .enumerate()
                .filter(|(_, binding)| binding.name == name)
                .collect();
            assert!(!receivers.is_empty(), "{name}");
            for (id, _) in receivers {
                let key = facts
                    .source_types
                    .key(facts.source_types.binding_type(id).unwrap())
                    .unwrap();
                if name == "once" {
                    assert!(
                        matches!(&key, ArgumentKey::Name { name, arguments }
                        if name == "Option" && matches!(arguments.as_slice(), [ArgumentKey::Array {length:Some(length),..}] if length=="const(int:2)")),
                        "{key:?}"
                    );
                } else {
                    assert!(
                        matches!(&key, ArgumentKey::Array { length:Some(length),.. } if length=="const(int:2)"),
                        "{name}: {key:?}"
                    );
                }
            }
        }
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn optional_projection_receipts_require_their_own_actual_occurrence() {
    use ril_compiler::sema::effect_identity::InvocationWitnessKind;
    let program = optional_fixture("pointer64");
    let facts = program.facts();
    let row = facts
        .binding_sources
        .iter()
        .rfind(|row| facts.bindings[row.binding].name == "named")
        .unwrap();
    let original = facts.evaluations[row.initializer.expression]
        .identity
        .unwrap();
    let receipt = facts.invocation_witnesses.iter().position(|row|
        matches!(&row.kind, InvocationWitnessKind::ImplicitUnwrap(proof) if proof.occurrence == original)
    ).unwrap();
    let sibling = facts
        .invocation_witnesses
        .iter()
        .find_map(|row| match &row.kind {
            InvocationWitnessKind::ImplicitUnwrap(proof)
                if proof.occurrence.source == original.source && proof.occurrence != original =>
            {
                Some(proof.occurrence)
            }
            _ => None,
        })
        .unwrap();
    for mutation in 0..5 {
        let mut changed = facts.clone();
        if mutation == 0 {
            changed.invocation_witnesses.remove(receipt);
        } else if let InvocationWitnessKind::ImplicitUnwrap(proof) =
            &mut changed.invocation_witnesses[receipt].kind
        {
            match mutation {
                1 => proof.occurrence = sibling,
                2 => proof.depth = 2,
                3 => proof.tags = vec!["None".into()],
                _ => proof.cause = facts.expressions[0].value.cause,
            }
        }
        assert!(
            solved_facts(&changed).is_err(),
            "optional receipt mutation {mutation}"
        );
    }
    let mut diagnostics = facts.clone();
    diagnostics.invocation_witnesses[receipt].span = facts.expressions[0].span;
    solved_facts(&diagnostics).expect("a diagnostic span cannot choose a Source projection");
}
