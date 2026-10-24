use ril_compiler::{
    CheckOptions, Session,
    sema::{SemanticFacts, validate::solved_facts},
};
use ril_compiler_core::ids::{ActivationEpochId, EvaluationOccurrenceId};
use std::collections::{BTreeMap, BTreeSet};

fn facts(layout: &str) -> SemanticFacts {
    facts_for("application-repeated-ordinary-and-pipeline", layout)
}

fn facts_for(name: &str, layout: &str) -> SemanticFacts {
    let source = ril_test::case_source(&format!(
        "tests/regressions/evaluation-identity.ril::{name}"
    ));
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap();
    let _core = ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn repeated_nodes_have_distinct_occurrences_and_preserve_their_birth_epochs() {
    for layout in ["pointer32", "pointer64"] {
        let facts = facts(layout);
        solved_facts(&facts).unwrap();
        let mut nodes = BTreeMap::<_, BTreeSet<_>>::new();
        for (index, record) in facts.evaluations.iter().enumerate() {
            assert_eq!(record.id, EvaluationOccurrenceId(index as u32));
            let identity = record.identity.unwrap();
            assert!(
                nodes
                    .entry(identity.source)
                    .or_default()
                    .insert(identity.activation)
            );
            assert_eq!(
                record.allocation_epoch,
                facts.expressions[index].allocation_epoch
            );
        }
        assert!(nodes.values().any(|activations| activations.len() > 1));
    }
}

#[test]
fn removing_or_cross_binding_any_occurrence_material_prevents_verification() {
    let facts = facts("pointer64");
    let mut damaged = facts.clone();
    damaged.evaluations.clear();
    assert!(solved_facts(&damaged).is_err());

    let mut damaged = facts.clone();
    damaged.evaluations.pop();
    assert!(solved_facts(&damaged).is_err());

    let mut damaged = facts.clone();
    damaged.evaluations[0].identity.as_mut().unwrap().activation = ActivationEpochId(u32::MAX);
    assert!(solved_facts(&damaged).is_err());

    let mut damaged = facts.clone();
    damaged.evaluations[0].allocation_epoch = usize::MAX;
    assert!(solved_facts(&damaged).is_err());

    let mut damaged = facts.clone();
    damaged.evaluations.swap(0, 1);
    assert!(solved_facts(&damaged).is_err());

    let mut damaged = facts.clone();
    damaged.evaluations[0].scope = ril_compiler::sema::facts::ScopeId(u32::MAX);
    assert!(solved_facts(&damaged).is_err());

    let mut reordered = facts.clone();
    reordered.invocation_expressions.reverse();
    solved_facts(&reordered).unwrap();
    reordered.invocation_expressions[0] = reordered.invocation_expressions[1].clone();
    assert!(solved_facts(&reordered).is_err());
}

#[test]
fn binding_declarations_cannot_borrow_another_patterns_identity() {
    let facts = facts_for("application-ordinary-complete-order", "pointer64");
    let mut damaged = facts.clone();
    let first = damaged.binding_sources[0].declaration;
    let other = damaged
        .binding_sources
        .iter()
        .position(|row| row.declaration != first)
        .unwrap();
    damaged.binding_sources[0].declaration = damaged.binding_sources[other].declaration;
    assert!(solved_facts(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.binding_sources.clear();
    assert!(solved_facts(&damaged).is_err());

    let (binding, view) = facts
        .binding_sources
        .iter()
        .find_map(|row| {
            facts
                .source_types
                .binding_view(row.binding)
                .map(|view| (row.binding, view))
        })
        .unwrap();
    assert_eq!(
        view.environment,
        facts.bindings[binding].typing_environment.id()
    );
    let mut damaged = facts.clone();
    // Equal contents are a fresh capture. They cannot replace the immutable
    // interpretation which the SourceTypeId was admitted under.
    damaged.bindings[binding].typing_environment =
        facts.bindings[binding].typing_environment.thaw().freeze();
    assert!(solved_facts(&damaged).is_err());
}

#[test]
fn activation_parents_and_intervals_cannot_be_deleted_or_rebound() {
    let facts = facts("pointer64");
    assert!(facts.activations.iter().any(|frame| frame.parent.is_some()));
    assert!(
        facts
            .evaluations
            .iter()
            .any(|record| record.identity.unwrap().activation.0 != record.id.0)
    );
    for mutation in 0..10 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.activations.clear(),
            1 => {
                changed.activations.pop();
            }
            2 => changed.activations.swap(0, 1),
            3 => changed.activations[0].parent = Some(changed.activations[0].id),
            4 => changed.activations[0].result = None,
            5 => changed.activations[0].end_expression = Some(0),
            6 => changed.activations[0].start_expression = usize::MAX,
            7 => changed.activations[0].scope = ril_compiler::sema::facts::ScopeId(u32::MAX),
            8 => changed.activations[0].source = Some(ril_compiler_core::ids::ExprId(u32::MAX)),
            9 => {
                let child = changed
                    .activations
                    .iter()
                    .position(|frame| frame.parent.is_some())
                    .unwrap();
                changed.activations[child].parent = None;
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "activation graph mutation {mutation}"
        );
    }
}
