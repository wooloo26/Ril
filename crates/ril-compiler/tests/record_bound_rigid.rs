use ril_compiler::{
    CompilationOutcome, Session,
    sema::{SemanticFacts, record_bounds::StructuralSchemaSource},
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
