use ril_compiler::{CompilationOutcome, Session};
use ril_ir::specialization::ArgumentKey;

const FORWARDING: &str = include_str!("fixtures/source_type_witness/forwarding.ril");
const EMPTY: &str = include_str!("fixtures/source_type_witness/empty_nested.ril");
const RETURNED: &str = include_str!("fixtures/source_type_witness/returned_callable.ril");
const MODES: &str = include_str!("fixtures/source_type_witness/modes.ril");
const DYNAMIC: &str = include_str!("fixtures/source_type_witness/dynamic_view.ril");
const EFFECT: &str = include_str!("fixtures/source_type_witness/effect_instance.ril");
const TYPES: &str = include_str!("fixtures/source_type_witness/type_forwarding.ril");
const CARRIERS: &str = include_str!("fixtures/source_type_witness/carriers.ril");
const INTERFACES: &str = include_str!("fixtures/source_type_witness/interfaces.ril");

#[test]
fn fixed_array_generic_identity_and_nested_forwarding_reach_core() {
    for source in [
        FORWARDING, EMPTY, RETURNED, MODES, DYNAMIC, TYPES, EFFECT, CARRIERS, INTERFACES,
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
    let verified = Session::new(CARRIERS.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let box_name = verified
        .facts()
        .external_type_declarations
        .keys()
        .find(|name| name.ends_with("Box"))
        .unwrap();
    let token_name = verified
        .facts()
        .external_type_declarations
        .keys()
        .find(|name| name.ends_with("Token"))
        .unwrap();
    let schemas: Vec<_> = core
        .provenance
        .bindings
        .iter()
        .filter_map(|binding| binding.value.source_type_witness.as_ref())
        .map(|witness| &witness.shape)
        .collect();
    assert!(schemas.iter().any(|shape|matches!(shape,ArgumentKey::Name {name,arguments} if name==box_name && matches!(arguments.as_slice(),[ArgumentKey::Array {length:Some(length),..}] if length=="const(int:2)"))),"{schemas:#?}");
    assert!(
        schemas
            .iter()
            .any(|shape| matches!(shape,ArgumentKey::Name {name,..} if name=="Option"))
    );
    assert!(
        schemas
            .iter()
            .any(|shape| matches!(shape,ArgumentKey::Name {name,..} if name=="Result"))
    );
    assert!(
        schemas
            .iter()
            .any(|shape| matches!(shape,ArgumentKey::Name {name,..} if name==token_name))
    );
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
    let verified = Session::new(EFFECT.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(core.provenance.specializations.iter().flat_map(|instance|&instance.arguments).any(|argument|matches!(&argument.key,ArgumentKey::Array {length:Some(outer),element} if outer=="const(int:0)" && matches!(&**element,ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"))));
}

#[test]
fn retained_return_contracts_export_each_creator_invocations_own_complete_schema() {
    let verified = Session::new(RETURNED.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let schemas: Vec<_> = core
        .provenance
        .callable_return_contracts
        .iter()
        .flat_map(|bound| &bound.generic_type_witnesses)
        .map(|(_, witness)| &witness.shape)
        .collect();
    for expected in ["const(int:0)", "const(int:2)", "const(int:3)"] {
        assert!(schemas.iter().any(|schema|matches!(schema,ArgumentKey::Array {length:Some(length),..} if length==expected)),"{expected}: {schemas:?}");
    }
}

#[test]
fn empty_nested_dimensions_survive_actual_instantiations_and_core_values() {
    let verified = Session::new(EMPTY.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let nested = |shape: &ArgumentKey| matches!(shape,ArgumentKey::Array {length:Some(outer),element} if outer=="const(int:0)" && matches!(&**element,ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"));
    assert!(verified.facts().effect_invocations.iter().filter(|invocation|!invocation.verifying).flat_map(|invocation|&invocation.arguments).filter_map(|argument|argument.key.as_ref()).any(|shape|matches!(shape,ril_compiler::sema::effect_identity::ArgumentKey::Array {length:Some(outer),element} if outer=="const(int:0)" && matches!(&**element,ril_compiler::sema::effect_identity::ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"))));
    assert!(
        core.provenance
            .bindings
            .iter()
            .filter_map(|binding| binding.value.source_type_witness.as_ref())
            .any(|witness| nested(&witness.shape))
    );
}

#[test]
fn a_dynamic_view_never_borrows_fixed_backing_type_identity() {
    let verified = Session::new(DYNAMIC.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
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
    assert!(
        core.provenance
            .bindings
            .iter()
            .filter_map(|binding| binding.value.source_type_witness.as_ref())
            .any(|witness| matches!(witness.shape, ArgumentKey::Array { length: None, .. }))
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

#[test]
fn tampering_only_frozen_snapshot_syntax_is_rejected_even_when_value_equality_hides_it() {
    let verified = Session::new(FORWARDING.as_bytes().to_vec())
        .verify()
        .unwrap();
    let mut facts = verified.facts().clone();
    let value = facts
        .copy_invocations
        .iter_mut()
        .flat_map(|invocation| &mut invocation.arguments)
        .map(|(_, snapshot)| &mut snapshot.value)
        .find(|value| value.source_type_witness.is_some())
        .unwrap();
    let before = value.clone();
    let witness = std::sync::Arc::make_mut(value.source_type_witness.as_mut().unwrap());
    witness.syntax.kind = ril_syntax::ast::TypeKind::Name {
        path: vec!["UnresolvedT".into()],
        arguments: vec![],
    };
    assert_eq!(
        before, *value,
        "canonical-key equality intentionally ignores presentation syntax"
    );
    let issues = ril_compiler::sema::validate::solved_facts(&facts).unwrap_err();
    assert!(
        issues.iter().any(|issue| matches!(
            issue.kind,
            ril_compiler::sema::validate::ValidationIssueKind::SourceTypeWitness
        )),
        "{issues:?}"
    );
}

#[test]
fn a_consistent_key_cannot_turn_an_unresolved_binder_spelling_into_a_nominal_type() {
    let verified = Session::new(FORWARDING.as_bytes().to_vec())
        .verify()
        .unwrap();
    let mut facts = verified.facts().clone();
    let value = facts
        .copy_invocations
        .iter_mut()
        .flat_map(|invocation| &mut invocation.arguments)
        .map(|(_, snapshot)| &mut snapshot.value)
        .find(|value| value.source_type_witness.is_some())
        .unwrap();
    let witness = std::sync::Arc::make_mut(value.source_type_witness.as_mut().unwrap());
    witness.syntax.kind = ril_syntax::ast::TypeKind::Name {
        path: vec!["UnresolvedT".into()],
        arguments: vec![],
    };
    witness.key = "UnresolvedT<>".into();
    assert!(
        witness.validate_closed(),
        "structural closedness alone cannot resolve a name"
    );
    let issues = ril_compiler::sema::validate::solved_facts(&facts).unwrap_err();
    assert!(
        issues.iter().any(|issue| matches!(
            issue.kind,
            ril_compiler::sema::validate::ValidationIssueKind::SourceTypeWitness
        )),
        "{issues:?}"
    );
}

#[test]
fn continuation_scope_history_checks_identity_metadata_on_every_protection_root() {
    let source = r#"type Cell={mut value:int}
type Graph={mut count:int,child:Cell}
eff Read{get()->int}
fn answer(child:Immut<Cell>)->Graph{with Read::get()->{let answer=resume 7;assert(answer.count==8&&answer.child.value==3);clone(answer)};let mut graph=Graph.{count:Read::get(),child:child};graph.count+=1;graph}
fn example(){let child=Cell.{value:3};let result=answer(child);assert(result.child.value==3)}"#;
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let step = facts
        .resumption_steps
        .iter()
        .position(|step| {
            step.scope_exit.as_ref().is_some_and(|exit| {
                !exit.bindings.is_empty() && exit.nodes.iter().any(|node| !node.fields.is_empty())
            })
        })
        .expect("fixture must retain bindings and stored protection roots");
    for location in 0..6 {
        let mut damaged = facts.clone();
        let current = &mut damaged.resumption_steps[step];
        let value = match location {
            0 => &mut current.continuation_value.value,
            1 => &mut current.arm_value.value,
            2 => &mut current.scope_exit.as_mut().unwrap().answer_before.value,
            3 => &mut current.scope_exit.as_mut().unwrap().answer_received.value,
            4 => &mut current.scope_exit.as_mut().unwrap().bindings[0].value,
            _ => {
                &mut current
                    .scope_exit
                    .as_mut()
                    .unwrap()
                    .nodes
                    .iter_mut()
                    .find(|node| !node.fields.is_empty())
                    .unwrap()
                    .fields[0]
                    .1
            }
        };
        value.source_type_witness = Some(std::sync::Arc::new(
            ril_compiler::sema::model::SourceTypeWitness {
                syntax: ril_syntax::ast::TypeExpr {
                    text: String::new(),
                    span: value
                        .source_type_witness
                        .as_ref()
                        .map_or(current.span, |witness| witness.syntax.span),
                    kind: ril_syntax::ast::TypeKind::Name {
                        path: vec!["UnresolvedT".into()],
                        arguments: vec![],
                    },
                },
                key: "UnresolvedT<>".into(),
            },
        ));
        let issues = ril_compiler::sema::validate::solved_facts(&damaged).unwrap_err();
        assert!(
            issues.iter().any(|issue| matches!(
                issue.kind,
                ril_compiler::sema::validate::ValidationIssueKind::SourceTypeWitness
            )),
            "snapshot {location}: {issues:?}"
        );
    }
}
