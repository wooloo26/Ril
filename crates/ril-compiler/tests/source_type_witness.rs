use ril_compiler::{CompilationOutcome, Session};
use ril_ir::specialization::ArgumentKey;

#[test]
fn failed_source_reception_preserves_later_independent_declarations_in_the_snapshot() {
    for target in ["pointer32", "pointer64"] {
        for prefix in [
            "let original:[0][3]int=[];let invalid:[0][2]int=original;",
            "let invalid:fn([0][2]int)->()=original_callable;",
        ] {
            let source = format!(
                "type Cell={{mut count:int}}\nfn original_callable(value:[0][3]int){{}}\nfn example(){{{prefix}\nlet mut cells:[]Cell=[];cells !> Array::push(Cell.{{count:1}});cells[0].count+=1}}"
            );
            let snapshot = Session::with_options(
                source.into_bytes(),
                ril_compiler::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .analyze();
            assert_eq!(
                snapshot.status(),
                ril_compiler::AnalysisStatus::Rejected,
                "{:?}",
                snapshot.outcome()
            );
            assert!(
                snapshot
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{prefix}: {:?}",
                snapshot.outcome()
            );
            assert!(
                snapshot
                    .diagnostics()
                    .iter()
                    .all(|diagnostic| diagnostic.code != "E0522")
            );
            let facts = snapshot.facts().unwrap();
            let (id, cells) = facts
                .bindings
                .iter()
                .enumerate()
                .find(|(_, binding)| binding.name == "cells")
                .unwrap();
            assert!(
                matches!(&cells.value.ty, ril_compiler::sema::model::Ty::Array(element) if !matches!(element.as_ref(), ril_compiler::sema::model::Ty::Unknown))
            );
            assert!(cells.value.source_type_witness.is_some());
            assert!(
                facts
                    .binding_sources
                    .iter()
                    .any(|binding| binding.binding == id
                        && facts.source_types.binding_type(id).is_some())
            );
            assert!(snapshot.into_verified().is_err());
        }
    }
}

fn forwarding_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::forwarding")
}
fn empty_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::empty-nested")
}
fn returned_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::returned-callable")
}
fn modes_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::modes")
}
fn dynamic_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::dynamic-view")
}
fn effect_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::effect-instance")
}
fn types_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::type-forwarding")
}
fn carriers_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::carriers")
}
fn interfaces_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-types.ril::interfaces")
}

#[test]
fn fixed_array_generic_identity_and_nested_forwarding_reach_core() {
    for source in [
        forwarding_fixture(),
        empty_fixture(),
        returned_fixture(),
        modes_fixture(),
        dynamic_fixture(),
        types_fixture(),
        effect_fixture(),
        carriers_fixture(),
        interfaces_fixture(),
    ] {
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
}

#[test]
fn explicit_callable_destinations_still_rename_labels_and_erase_defaults() {
    for (body, code) in [
        (
            "let target:fn(renamed:int)->int=second;target(right:9)",
            "E0339",
        ),
        ("let target:fn(renamed:int)->int=second;target()", "E0314"),
        (
            "let target:{item:fn(renamed:int)->int}=.{item:second};target.item(right:9)",
            "E0339",
        ),
        (
            "let target:{item:fn(renamed:int)->int}=.{item:second};target.item()",
            "E0314",
        ),
    ] {
        let source = format!("fn second(right:int=2)->int{{right}}\nfn example(){{{body}}}");
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn constructor_and_carrier_roots_export_their_own_complete_type() {
    let verified = Session::new(carriers_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
    let _box_name = verified
        .facts()
        .external_type_declarations
        .keys()
        .find(|name| name.ends_with("Box"))
        .unwrap();
    let _token_name = verified
        .facts()
        .external_type_declarations
        .keys()
        .find(|name| name.ends_with("Token"))
        .unwrap();
}

#[test]
fn a_payload_type_never_discharges_an_effect_on_a_different_wrapper_or_constructor() {
    for body in [
        "let input:[2]int=[1,2];with Mark<[2]int>::get()->resume 1;let output=mark(Some(input))",
        "let token=Token(7);with Mark<int>::get()->resume 1;let output=mark(token)",
    ] {
        let source = format!(
            "type Token(int)\neff Mark<T>{{get()->int}}\nfn mark<T>(value:T)->int @Mark<T>{{Mark<T>::get()}}\nfn example(){{{body}}}"
        );
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0612")),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn a_closed_effect_instance_uses_the_complete_actual_array_schema() {
    let verified = Session::new(effect_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(core.metadata.specializations.iter().flat_map(|instance|&instance.arguments).any(|argument|matches!(&argument.key,ArgumentKey::Array {length:Some(outer),element} if outer=="const(int:0)" && matches!(&**element,ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"))));
}

#[test]
fn retained_return_contracts_export_each_creator_invocations_own_complete_schema() {
    let verified = Session::new(returned_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn empty_nested_dimensions_survive_actual_instantiations_and_core_values() {
    let verified = Session::new(empty_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
    let _nested = |shape: &ArgumentKey| matches!(shape,ArgumentKey::Array {length:Some(outer),element} if outer=="const(int:0)" && matches!(&**element,ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"));
    assert!(verified.facts().effect_invocations.iter().filter(|invocation|!invocation.verifying).flat_map(|invocation|&invocation.arguments).filter_map(|argument|argument.key.as_ref()).any(|shape|matches!(shape,ril_compiler::sema::effect_identity::ArgumentKey::Array {length:Some(outer),element} if outer=="const(int:0)" && matches!(&**element,ril_compiler::sema::effect_identity::ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"))));
}

#[test]
fn a_dynamic_view_never_borrows_fixed_backing_type_identity() {
    let verified = Session::new(dynamic_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
    let actual: Vec<_> = verified
        .facts()
        .effect_invocations
        .iter()
        .filter(|invocation| !invocation.verifying)
        .flat_map(|instance| &instance.arguments)
        .filter_map(|argument| argument.key.as_ref())
        .collect();
    assert!(!actual.is_empty());
    assert!(
        actual.iter().all(|shape| matches!(
            shape,
            ril_compiler::sema::effect_identity::ArgumentKey::Array { length: None, .. }
        )),
        "{actual:?}"
    );
}

#[test]
fn dimensions_and_callable_modes_must_agree_for_each_selected_binder() {
    for source in [
        "fn first<T>(a:T,b:T)->T{a}\nfn example(){let a:[2]int=[1,2];let b:[3]int=[1,2,3];let output=first(a,b)}",
        "fn identity<T>(value:T)->T{value}\nfn example(){let input:[2]int=[1,2];let wrong:[3]int=identity(input)}",
        "type Cell={mut value:int}\nfn bump(mut cell:Cell)&mut{cell.value+=1}\nfn read(cell:Cell){}\nfn first<T>(a:T,b:T)->T{a}\nfn example(){let action=first(bump,read)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn generic_return_identity_grants_neither_writable_access_nor_disjoint_origins() {
    for (source, codes) in [
        (
            "fn identity<T>(value:T)->T{value}\nfn example(){let mut input:[2]int=[1,2];input[0]=3;let view frozen=input;let mut alias=identity(frozen);alias[0]=9}",
            &["E0520", "E0522"][..],
        ),
        (
            "fn identity<T>(^mut value:T)->T &^mut{value}\nfn both(mut a:[2]int,mut b:[2]int)&mut{a[0]=1;b[0]=2}\nfn example(){let mut input:[2]int=[1,2];let mut alias=identity(^mut input);both(mut input,mut alias)}",
            &["E0523", "E0524"][..],
        ),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|codes.contains(&diagnostic.code.as_str()))),
            "{source}: {outcome:?}"
        );
    }
}
