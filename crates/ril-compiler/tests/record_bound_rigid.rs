use ril_compiler::{
    CompilationOutcome, Session,
    sema::{
        SemanticFacts,
        record_bounds::StructuralSchemaSource,
        validate::{ValidationIssueKind, solved_facts},
    },
};

fn tuple_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-tuple")
}
fn shared_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-shared-row")
}

fn verified(source: &str) -> SemanticFacts {
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    program.facts().clone()
}

fn rejected(facts: &SemanticFacts) {
    let errors = solved_facts(facts).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|issue| matches!(issue.kind, ValidationIssueKind::RecordBound(_))),
        "{errors:?}"
    );
}

#[test]
fn tuple_field_and_shared_row_forward_actual_rigid_formal_children() {
    for source in [
        tuple_fixture(),
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-field"),
        shared_fixture(),
    ] {
        let facts = verified(source);
        assert!(facts.generic_bound_checks.iter().any(|check| {
            !check.selection_path.is_empty()
                && matches!(
                    check.actual_schema.source,
                    StructuralSchemaSource::RigidParameter { .. }
                )
                && check
                    .rows
                    .iter()
                    .any(|row| row.source_type_witness.is_none())
        }));
    }
}

#[test]
fn rigid_child_schema_cannot_borrow_another_parameter_scope_or_type_subterm() {
    let facts = verified(shared_fixture());
    let actual: Vec<_> = facts
        .generic_bound_checks
        .iter()
        .enumerate()
        .filter(|(_, check)| {
            matches!(
                check.actual_schema.source,
                StructuralSchemaSource::RigidParameter { .. }
            )
        })
        .map(|(index, _)| index)
        .collect();
    assert_eq!(actual.len(), 2);
    let mut copy = facts.clone();
    copy.generic_bound_checks[actual[0]].actual_schema.source = facts.generic_bound_checks
        [actual[1]]
        .actual_schema
        .source
        .clone();
    rejected(&copy);
    let mut copy = facts.clone();
    let StructuralSchemaSource::RigidParameter {
        parameter_index, ..
    } = &mut copy.generic_bound_checks[actual[0]].actual_schema.source
    else {
        unreachable!()
    };
    *parameter_index += 1;
    rejected(&copy);
    let mut copy = facts;
    let StructuralSchemaSource::RigidParameter { scope, .. } =
        &mut copy.generic_bound_checks[actual[0]].actual_schema.source
    else {
        unreachable!()
    };
    scope.types.clear();
    rejected(&copy);
}

#[test]
fn opaque_rigid_rows_cannot_be_closed_or_gain_new_absence_premises() {
    let facts = verified(tuple_fixture());
    let index = facts
        .generic_bound_checks
        .iter()
        .position(|check| {
            matches!(
                check.actual_schema.source,
                StructuralSchemaSource::RigidParameter { .. }
            )
        })
        .unwrap();
    let mut copy = facts.clone();
    copy.generic_bound_checks[index].actual_schema.tail =
        ril_compiler::sema::model::rows::RowTail::Closed;
    rejected(&copy);
    let mut copy = facts;
    let ril_compiler::sema::model::rows::RowTail::Open(tail) =
        &mut copy.generic_bound_checks[index].actual_schema.tail
    else {
        unreachable!()
    };
    tail.lacks.insert("invented".into());
    rejected(&copy);
}

#[test]
fn missing_guaranteed_members_and_mutability_are_real_type_errors() {
    for source in [
        "fn read<T:{id:int,..R}>(value:(T,int))->int{value.(0).id}\nfn forward<S>(value:({tag:str,..S},int))->int{read(value)}",
        "fn read<T:{mut id:int,..R}>(value:(T,int))->int{value.(0).id}\nfn forward<S>(value:({id:int,tag:str,..S},int))->int{read(value)}",
    ] {
        assert!(
            matches!(Session::new(source.as_bytes().to_vec()).check(), CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{source}"
        );
    }
}

#[test]
fn fixed_rigid_fields_transport_the_complete_scoped_source_identity() {
    let source = ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-fixed");
    let facts = verified(source);
    assert!(!facts.scoped_source_identities.is_empty());
}
