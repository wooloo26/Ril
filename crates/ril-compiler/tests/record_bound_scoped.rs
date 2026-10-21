use ril_compiler::{
    CheckOptions, CompilationOutcome, Session,
    sema::{
        SemanticFacts,
        effect_identity::ArgumentKey,
        record_bounds::BoundTypeSelectionStep,
        validate::{ValidationIssueKind, solved_facts},
    },
};

fn fixed_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-fixed")
}
fn empty_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-empty-inner-dimension")
}
fn callable_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-callable-mut")
}
fn immutable_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::scoped-immutable-field")
}

fn verified(source: &str) -> SemanticFacts {
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts().clone();
    assert!(
        !facts.scoped_source_identities.is_empty(),
        "source did not exercise scoped identity"
    );
    solved_facts(&facts).unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    assert_eq!(
        core.provenance.scoped_source_identities.len(),
        facts.scoped_source_identities.len()
    );
    for (source, lowered) in facts
        .scoped_source_identities
        .iter()
        .zip(&core.provenance.scoped_source_identities)
    {
        assert_eq!(source.id, lowered.id);
        assert_eq!(source.cause, lowered.cause);
        assert_eq!(source.occurrences.len(), lowered.occurrences.len());
        let original = &source.occurrences[0].formal;
        let binding = core
            .provenance
            .bindings
            .iter()
            .find(|binding| binding.id as usize == original.binding)
            .unwrap();
        assert_eq!(lowered.environment, binding.typing_environment);
        let environment = &core.provenance.frozen_environments[lowered.environment.0 as usize];
        assert_eq!(
            environment.generic_context,
            source
                .typing_environment
                .generic_context
                .iter()
                .map(|(name, identity)| (name.clone(), identity.clone()))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            environment.generic_substitutions.len(),
            source.typing_environment.generic_substitutions.len()
        );
        assert_eq!(
            environment.generic_sources.len(),
            source.typing_environment.generic_sources.len()
        );
        for (source, lowered) in source.occurrences.iter().zip(&lowered.occurrences) {
            assert_eq!(
                source.formal.root_expression,
                lowered.formal.root_expression
            );
            assert_eq!(
                source.formal.type_path.len(),
                lowered.formal.type_path.len()
            );
            assert_eq!(source.selection_path.len(), lowered.selection_path.len());
        }
    }
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    facts
}

fn damaged(facts: &SemanticFacts) {
    let errors = solved_facts(facts).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|issue| matches!(issue.kind, ValidationIssueKind::RecordBound(_))),
        "{errors:?}"
    );
}

#[test]
fn fixed_fields_have_complete_source_header_and_existing_product_receipts() {
    let facts = verified(fixed_fixture());
    let identity = &facts.scoped_source_identities[0];
    assert!(!identity.key.is_closed());
    assert!(
        identity
            .occurrences
            .iter()
            .all(|occurrence| !occurrence.selection_path.is_empty()
                && !occurrence.formal.type_path.is_empty())
    );
    assert!(
        identity
            .occurrences
            .iter()
            .all(|occurrence| facts.bindings[occurrence.formal.binding].parameter)
    );
    let pointer32 = Session::with_options(
        fixed_fixture().as_bytes().to_vec(),
        CheckOptions {
            target: "pointer32".into(),
            ..CheckOptions::default()
        },
    )
    .verify()
    .unwrap();
    assert!(!pointer32.facts().scoped_source_identities.is_empty());
}

#[test]
fn an_empty_outer_array_keeps_the_inner_dimension_without_inventing_t_elements() {
    let facts = verified(empty_fixture());
    assert_eq!(facts.scoped_source_identities[0].occurrences.len(), 2);
    assert!(
        facts.scoped_source_identities[0]
            .occurrences
            .iter()
            .all(
                |occurrence| occurrence.selection_path.iter().all(|step| matches!(
                    step,
                    BoundTypeSelectionStep::Tuple(_) | BoundTypeSelectionStep::Field(_)
                ))
            )
    );
}

#[test]
fn callable_parameter_modes_effect_qualifications_and_immutable_fields_survive() {
    for source in [callable_fixture(), immutable_fixture()] {
        verified(source);
    }
}

#[test]
fn complete_known_field_dimension_and_callable_mode_conflicts_are_type_errors() {
    for source in [
        ril_test::case_source(
            "tests/regressions/record-bounds.ril::scoped-wrong-empty-inner-dimension",
        ),
        ril_test::case_source("tests/regressions/record-bounds.ril::scoped-wrong-callable-mode"),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0301")),
            "{outcome:?}"
        );
    }
}

#[test]
fn deleted_certificate_and_probe_flags_never_make_complete_source_coverage_vacuous() {
    let facts = verified(fixed_fixture());
    for flags in [false, true] {
        let mut copy = facts.clone();
        copy.scoped_source_identities.clear();
        if flags {
            for call in &mut copy.copy_invocations {
                call.declaration_probe = true;
            }
        }
        damaged(&copy);
    }
    let mut copy = facts;
    copy.scoped_source_identities[0].occurrences.clear();
    damaged(&copy);
}

#[test]
fn original_and_current_entry_tables_require_full_arity_before_selection() {
    let facts = verified(empty_fixture());
    let identity = &facts.scoped_source_identities[0];
    let current = identity.context.invocation.unwrap().0 as usize;
    let source = identity.occurrences[0].formal.invocation.0 as usize;
    for invocation in [current, source] {
        let mut copy = facts.clone();
        copy.copy_invocations[invocation].entry.arguments.clear();
        damaged(&copy);
        let mut copy = facts.clone();
        let extra = copy.copy_invocations[invocation].entry.arguments[0].clone();
        copy.copy_invocations[invocation]
            .entry
            .arguments
            .push(extra);
        damaged(&copy);
    }
}

#[test]
fn each_t_occurrence_requires_its_actual_original_formal_path() {
    let facts = verified(empty_fixture());
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].occurrences.pop();
    damaged(&copy);
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].occurrences[0]
        .formal
        .type_path = vec![BoundTypeSelectionStep::Tuple(99)];
    damaged(&copy);
    let mut copy = facts;
    copy.scoped_source_identities[0].occurrences[1].formal = copy.scoped_source_identities[0]
        .occurrences[0]
        .formal
        .clone();
    damaged(&copy);
}

#[test]
fn original_source_name_and_actual_parent_callee_tokens_cannot_be_replaced_by_metadata() {
    let facts = verified(fixed_fixture());
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].occurrences[0]
        .formal
        .root_expression = usize::MAX;
    damaged(&copy);
    let mut copy = facts.clone();
    copy.invocation_expressions.clear();
    damaged(&copy);
    let mut copy = facts.clone();
    let anchor = copy.scoped_source_identities[0].occurrences[0]
        .formal
        .clone();
    copy.bindings[anchor.binding].name = "renamed_without_token".into();
    for function in &mut copy.functions {
        if function.definition == anchor.definition {
            function.syntax.parameters[anchor.parameter_index as usize]
                .pattern
                .kind = ril_syntax::ast::PatternKind::Name("renamed_without_token".into());
        }
    }
    damaged(&copy);
    let mut copy = facts;
    let invocation = copy.scoped_source_identities[0]
        .context
        .invocation
        .unwrap()
        .0 as usize;
    copy.copy_invocations[invocation].source_event = None;
    damaged(&copy);
}

#[test]
fn matching_descriptor_edits_cannot_rewrite_the_original_inner_dimension() {
    let mut facts = verified(empty_fixture());
    let identity = &mut facts.scoped_source_identities[0];
    let ArgumentKey::Record { fields, .. } = &mut identity.key else {
        unreachable!()
    };
    let ArgumentKey::Array { element, .. } = &mut fields
        .iter_mut()
        .find(|field| field.0 == "items")
        .unwrap()
        .2
    else {
        unreachable!()
    };
    let ArgumentKey::Array { length, .. } = element.as_mut() else {
        unreachable!()
    };
    *length = Some("const(int:3)".into());
    let ril_syntax::ast::TypeKind::Record { fields, .. } = &mut identity.syntax.kind else {
        unreachable!()
    };
    let ril_syntax::ast::TypeKind::Array { element, .. } = &mut fields
        .iter_mut()
        .find(|field| field.name == "items")
        .unwrap()
        .ty
        .kind
    else {
        unreachable!()
    };
    let ril_syntax::ast::TypeKind::Array {
        length: Some(length),
        ..
    } = &mut element.kind
    else {
        unreachable!()
    };
    length.kind = ril_syntax::ast::ExprKind::Literal(ril_syntax::ast::Literal::Integer("3".into()));
    damaged(&facts);
}

#[test]
fn scoped_identity_arena_context_and_epoch_require_real_registered_anchors() {
    let facts = verified(fixed_fixture());
    let mut unrelated = Session::new(b"fn example(){}".to_vec())
        .verify()
        .unwrap()
        .facts()
        .clone();
    unrelated
        .scoped_source_identities
        .push(facts.scoped_source_identities[0].clone());
    damaged(&unrelated);
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].id.0 += 1;
    damaged(&copy);
    let mut copy = facts.clone();
    copy.scoped_source_identities[0].context.invocation = None;
    damaged(&copy);
    let mut copy = facts.clone();
    let original = copy.scoped_source_identities[0].typing_environment.clone();
    let equal_contents = original.thaw().freeze();
    assert_eq!(original, equal_contents);
    assert_ne!(original.id(), equal_contents.id());
    copy.scoped_source_identities[0].typing_environment = equal_contents;
    damaged(&copy);
    let mut copy = facts.clone();
    let identity = &mut copy.scoped_source_identities[0];
    let forged = identity.typing_environment.thaw().freeze();
    identity.typing_environment = forged.clone();
    let binding = identity.occurrences[0].formal.binding;
    copy.bindings[binding].typing_environment = forged;
    damaged(&copy);
    let mut copy = facts;
    copy.scoped_source_identities[0].occurrences[0]
        .formal
        .entry_allocation_epoch += 1;
    damaged(&copy);
}
