use ril_compiler::{
    CompilationOutcome, Session,
    sema::{
        SemanticFacts,
        facts::{Participant, Permission},
        validate::{ValidationIssueKind, solved_facts},
    },
};

const SOURCE: &str = include_str!("fixtures/record_bounds/write_scalar.ril");

fn facts() -> SemanticFacts {
    let program = Session::new(SOURCE.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts().clone();
    assert!(!facts.bound_field_writes.is_empty());
    solved_facts(&facts).unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    assert_eq!(
        core.provenance.bound_field_writes.len(),
        facts.bound_field_writes.len()
    );
    assert_eq!(
        core.provenance.observed_accesses.len(),
        facts.observed_accesses.len()
    );
    for (source, lowered) in facts
        .observed_accesses
        .iter()
        .zip(&core.provenance.observed_accesses)
    {
        assert_eq!(source.id, lowered.id);
        assert_eq!(
            source.access.observed_recency as u64,
            lowered.access.observed_allocation_epoch
        );
        assert_eq!(
            source.access.recency as u64,
            lowered.access.allocation_epoch
        );
    }
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    facts
}

fn damaged(facts: &SemanticFacts) {
    let issues = solved_facts(facts).unwrap_err();
    assert!(
        issues
            .iter()
            .any(|issue| matches!(issue.kind, ValidationIssueKind::RecordBound(_))),
        "{issues:?}"
    );
}

#[test]
fn actual_mutable_assignment_keeps_the_receiver_old_member_and_real_access() {
    facts();
    let program = Session::with_options(
        SOURCE.as_bytes().to_vec(),
        ril_compiler::CheckOptions {
            target: "pointer32".into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap();
    solved_facts(program.facts()).unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
}

#[test]
fn deleting_assignment_or_access_evidence_does_not_turn_a_write_into_a_read() {
    let original = facts();
    let mut missing = original.clone();
    missing.bound_field_writes.clear();
    missing.observed_accesses.clear();
    damaged(&missing);
    let mut missing = original;
    missing.observed_accesses.clear();
    damaged(&missing);
}

#[test]
fn access_receipts_cannot_recover_erased_permission_or_lose_their_real_loan() {
    let original = facts();
    let index = original.bound_field_writes[0].projection_index;
    let mut readonly = original.clone();
    readonly.generic_bound_projections[index]
        .source
        .value
        .permission = Permission::Read;
    damaged(&readonly);
    let mut detached = original.clone();
    detached.observed_accesses[0].access.participants =
        [Participant::Root(ril_compiler::sema::facts::RootId(0))].into();
    damaged(&detached);
    let mut wrong = original;
    wrong.observed_accesses[0].access.recency += 1;
    damaged(&wrong);
}

#[test]
fn assignment_tokens_order_and_whole_argument_arity_are_independently_required() {
    let original = facts();
    let mut swapped = original.clone();
    let write = &mut swapped.bound_field_writes[0];
    std::mem::swap(&mut write.rhs_expression, &mut write.receiver_expression);
    damaged(&swapped);
    let mut no_arguments = original.clone();
    let projection = &no_arguments.generic_bound_projections
        [no_arguments.bound_field_writes[0].projection_index];
    no_arguments.copy_invocations[projection.context.invocation.unwrap().0 as usize]
        .arguments
        .clear();
    damaged(&no_arguments);
    let mut duplicate = original;
    duplicate
        .bound_field_writes
        .push(duplicate.bound_field_writes[0].clone());
    damaged(&duplicate);
}

#[test]
fn scalar_store_cannot_modify_another_field_or_forge_its_replacement() {
    let original = facts();
    let mut changed = original.clone();
    changed.bound_field_writes[0].replacement.value.ty = ril_compiler::sema::model::Ty::Bool;
    damaged(&changed);
    let mut changed = original;
    changed.bound_field_writes[0]
        .updated_receiver
        .value
        .permission = Permission::Read;
    damaged(&changed);
}

#[test]
fn historical_ownership_and_mut_reception_restrictions_cannot_be_replaced() {
    let original = facts();
    let mut changed = original.clone();
    changed.observed_accesses[0]
        .access
        .origin_owners
        .values_mut()
        .for_each(|owner| *owner = ril_compiler::sema::model::AccessOwners::Unknown);
    damaged(&changed);
    let mut changed = original;
    let projection =
        &changed.generic_bound_projections[changed.bound_field_writes[0].projection_index];
    let loan = changed
        .invocation_loan_starts
        .iter_mut()
        .find(|loan| {
            loan.named == projection.context.invocation
                && loan.origins == projection.source.value.origins
        })
        .unwrap();
    loan.source.temporary = false;
    damaged(&changed);
}

#[test]
fn writing_does_not_disappear_from_the_actual_invocation_summary() {
    let mut changed = facts();
    let projection =
        &changed.generic_bound_projections[changed.bound_field_writes[0].projection_index];
    let summary = changed
        .invocations
        .iter_mut()
        .find(|summary| summary.context == Some(projection.context))
        .unwrap();
    summary
        .accesses
        .retain(|access| access.access != ril_compiler::sema::summary::Access::Write);
    damaged(&changed);
}

#[test]
fn source_readonly_paths_and_immutable_members_remain_type_permission_errors() {
    for source in [
        "fn replace<T:{mut value:int,..R}>(object:T){object.value=7}",
        "fn replace<T:{value:int,..R}>(mut object:T)&mut{object.value=7}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0520")),
            "{outcome:?}"
        );
    }
}
