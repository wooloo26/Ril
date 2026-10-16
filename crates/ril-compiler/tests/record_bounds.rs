use ril_compiler::sema::record_bounds::{BoundRowRole, StructuralSchemaSource};
use ril_compiler::{CompilationOutcome, Session};

fn original_projection_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::original-projection")
}

fn rejected(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn original_spec_projection_keeps_t_and_publishes_application_evidence() {
    let program = Session::new(original_projection_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let facts = program.facts();
    assert_eq!(facts.record_bounds.len(), 1);
    assert_eq!(facts.bound_rows.len(), 1);
    let bound = &facts.record_bounds[0];
    assert_eq!(bound.fields[0].label, "id");
    assert!(facts.generic_binders.contains_key(&bound.binder));
    assert!(matches!(
        facts.bound_rows[0].role,
        BoundRowRole::ImplicitResidual
    ));
    assert!(
        !facts
            .generic_binders
            .values()
            .any(|binder| binder.name == "R")
    );
    assert!(facts.generic_bound_checks.iter().any(|check| {
        check.required == bound.id
            && check.argument_index == 0
            && check.selection_path.is_empty()
            && matches!(
                check.actual_schema.source,
                StructuralSchemaSource::Closed(_)
            )
            && check
                .rows
                .iter()
                .any(|row| row.fields.iter().any(|field| field.label == "tag"))
    }));
    assert!(!facts.generic_bound_projections.is_empty());
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
}

#[test]
fn caller_bounds_and_rigid_open_parameters_forward_without_closing_the_tail() {
    for source in [
        "fn read<T:{id:int,..R}>(value:T)->int{value.id}\nfn forward<U:{id:int,tag:str,..S}>(value:U)->int{read(value)}\npub fn test_native(){assert(forward(.{id:7,tag:\"ok\"})==7)}",
        "fn read<T:{id:int,..R}>(value:T)->int{value.id}\nfn forward<S>(value:{id:int,tag:str,..S})->int{read(value)}\npub fn test_native(){assert(forward(.{id:7,tag:\"ok\"})==7)}",
    ] {
        let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        assert!(program.facts().generic_bound_checks.iter().any(|check| {
            matches!(
                check.actual_schema.source,
                StructuralSchemaSource::CallerBound(_)
                    | StructuralSchemaSource::RigidParameter { .. }
            ) && check
                .rows
                .iter()
                .any(|row| row.source_type_witness.is_none())
        }));
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
}

#[test]
fn missing_fields_and_mutability_are_checked_universally_and_at_the_call() {
    for source in [
        "fn read<T:{id:int,..R}>(value:T)->int{value.absent}",
        "fn read<T:{tag:str,..R}>(value:T)->int{value.id}",
    ] {
        rejected(source, "E0336");
    }
    for source in [
        "fn read<T:{id:int,..R}>(value:T)->int{value.id}\nfn example(){let value=read(.{tag:\"ok\"})}",
        "fn read<T:{id:int,..R}>(value:T)->int{value.id}\nfn example(){let value=read(.{id:\"wrong\"})}",
        "fn read<T:{mut id:int,..R}>(value:T)->int{value.id}\nfn example(){let value=read(.{id:7})}",
    ] {
        rejected(source, "E0301");
    }
    rejected("fn write<T:{id:int,..R}>(mut value:T){value.id=9}", "E0520");
}

#[test]
fn one_shared_residual_is_solved_once_for_the_whole_application() {
    let source = "fn both<T:{id:int,..R},U:{flag:bool,..R}>(left:T,right:U)->int{left.id}\npub fn test_native(){assert(both(.{id:7,tag:\"ok\"},.{flag:true,tag:\"ok\"})==7)}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    assert_eq!(program.facts().bound_rows.len(), 1);
    assert_eq!(program.facts().bound_rows[0].declaration_paths.len(), 2);
    assert_eq!(
        program.facts().bound_rows[0]
            .lacks
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["flag", "id"]
    );
    ril_compiler::lower::lower_core(&program).unwrap();
    rejected(
        "fn both<T:{id:int,..R},U:{flag:bool,..R}>(left:T,right:U)->int{left.id}\nfn example(){let value=both(.{id:7,tag:\"ok\"},.{flag:true,tag:9})}",
        "E0301",
    );
}

#[test]
fn fixed_dimensions_and_readonly_child_access_are_not_erased_by_the_bound() {
    let source = "fn first<T:{items:[2]int,..R}>(value:T)->int{value.items[0]}\npub fn test_native(){let items:[2]int=[7,9];assert(first(.{items:items})==7)}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    let source = "fn first<T:{items:[2]int,..R}>(value:T)->int{value.items[0]}\nfn example(){let items:[]int=[7,9];let value=first(.{items:items})}";
    assert!(!matches!(
        Session::new(source.as_bytes().to_vec()).check(),
        CompilationOutcome::Accepted { .. }
    ));
    rejected(
        "type Cell={mut value:int}\nfn write<T:{child:Cell,..R}>(mut value:T){value.child.value=9}\nfn example(){let mut cell=Cell.{value:7};let view observed=cell;let mut record=.{child:observed};write(mut record)}",
        "E0520",
    );
}
