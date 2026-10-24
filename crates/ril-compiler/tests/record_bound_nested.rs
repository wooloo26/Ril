use ril_compiler::{
    CompilationOutcome, Session,
    sema::{SemanticFacts, record_bounds::StructuralSchemaSource},
};

fn tuple_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-tuple")
}
fn fixed_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-fixed")
}
fn alias_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::nested-alias")
}

fn verified(source: &str) -> SemanticFacts {
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts().clone();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    facts
}

#[test]
fn precise_products_keep_the_whole_actual_argument_and_existing_selected_object() {
    for source in [
        tuple_fixture(),
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-field"),
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-mixed"),
        fixed_fixture(),
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-readonly"),
    ] {
        let facts = verified(source);
        let check = facts
            .generic_bound_checks
            .iter()
            .find(|check| {
                matches!(
                    check.actual_schema.source,
                    StructuralSchemaSource::Closed(_)
                )
            })
            .unwrap();
        assert!(!check.selection_path.is_empty());
        assert!(matches!(
            check.actual.value.ty,
            ril_compiler::sema::model::Ty::Tuple(_) | ril_compiler::sema::model::Ty::Record(_)
        ));
        let invocation = &facts.copy_invocations[check.context.invocation.unwrap().0 as usize];
        assert_eq!(
            &check.actual.value,
            invocation.entry.arguments[check.argument_index as usize].value()
        );
    }
}

#[test]
fn nested_caller_bounds_keep_their_rigid_open_tail() {
    for source in [
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-tuple-forward"),
        ril_test::case_source("tests/regressions/record-bounds.ril::nested-field-forward"),
    ] {
        let facts = verified(source);
        assert!(facts.generic_bound_checks.iter().any(|check| {
            !check.selection_path.is_empty()
                && matches!(
                    check.actual_schema.source,
                    StructuralSchemaSource::CallerBound(_)
                )
                && check
                    .rows
                    .iter()
                    .any(|row| row.source_type_witness.is_none())
        }));
    }
}

#[test]
fn repeated_nested_t_preserves_the_actual_alias_without_inventing_independence() {
    let facts = verified(alias_fixture());
    let check = facts
        .generic_bound_checks
        .iter()
        .find(|check| {
            matches!(
                check.actual_schema.source,
                StructuralSchemaSource::Closed(_)
            )
        })
        .unwrap();
    let root = *check.actual.value.origins.nodes.first().unwrap();
    let tuple = check
        .actual
        .nodes
        .iter()
        .find(|node| node.origin == root)
        .unwrap();
    let items: Vec<_> = tuple
        .fields
        .iter()
        .filter(|(slot, _)| matches!(slot, ril_compiler::sema::facts::Slot::Tuple(_)))
        .collect();
    assert_eq!(items.len(), 2);
    assert_eq!(items[0].1.origins.nodes, items[1].1.origins.nodes);
}

#[test]
fn real_nested_mismatches_and_readonly_writes_are_rejected() {
    for source in [
        tuple_fixture().replace("id:7,tag:\"ok\"", "tag:\"wrong\""),
        "fn both<T:{id:int,..R}>(value:(T,T))->int{value.(0).id}\npub fn test_native(){assert(both((.{id:7},.{id:\"wrong\"}))==7)}".into(),
        fixed_fixture().replace("let items:[2]int=[7,9]", "let items:[3]int=[7,9,11]"),
        "fn both<T:{items:[2]int,..R}>(value:(T,T))->int{value.(0).items[0]}\npub fn test_native(){let left:[2]int=[7,9];let right:[3]int=[7,9,11];assert(both((.{items:left},.{items:right}))==7)}".into(),
    ] {
        assert!(matches!(Session::new(source.as_bytes().to_vec()).check(), CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")), "{source}");
    }
    let source = "fn write<T:{mut id:int,..R}>(value:(T,int)){value.(0).id=9}";
    assert!(
        matches!(Session::new(source.as_bytes().to_vec()).check(), CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0520"))
    );
}
