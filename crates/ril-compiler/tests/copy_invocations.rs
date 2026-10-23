use ril_compiler::sema::{copy_contract::CopyInvocationStatus, model::Ty};
use ril_compiler_core::source::FileId;

#[test]
fn same_site_substitutions_keep_separate_actual_argument_graphs() {
    let source = "fn relay<T>(source:T)->T{source}\nfn forward<T>(source:T)->T{relay(source)}\nfn example(){assert(forward(1)==1);assert(forward(\"x\")==\"x\")}";
    let parsed = ril_syntax::parse(source);
    let analyzed = ril_compiler::sema::analyze(&parsed.program, FileId(0));
    let verified = analyzed
        .program
        .as_ref()
        .unwrap_or_else(|| panic!("{analyzed:?}"));
    let facts = verified.facts();
    let relay = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "relay")
        .unwrap()
        .definition;
    let records: Vec<_> = facts
        .copy_invocations
        .iter()
        .filter(|record| record.target == relay && !record.declaration_probe)
        .collect();
    let integer = records
        .iter()
        .find(|record| matches!(record.entry.arguments[0].value().ty, Ty::Int(_)))
        .unwrap();
    let string = records
        .iter()
        .find(|record| record.entry.arguments[0].value().ty == Ty::Str)
        .unwrap();
    assert_eq!(integer.span, string.span);
    assert_ne!(integer.id, string.id);
    assert_ne!(integer.parent, string.parent);
    assert_eq!(integer.status, CopyInvocationStatus::Completed);
    assert_eq!(string.status, CopyInvocationStatus::Completed);
    assert_eq!(
        integer.result.as_ref().unwrap().value.ty,
        Ty::Int("int".into())
    );
    assert_eq!(string.result.as_ref().unwrap().value.ty, Ty::Str);
    let core = ril_compiler::lower::lower_core(verified).unwrap();
    assert_eq!(
        core.provenance.copy_invocations.len(),
        facts.copy_invocations.len()
    );
    assert!(core.provenance.copy_template_closure.is_none());
}

#[test]
fn explicit_sender_resource_contract_is_not_an_ordinary_copy_instance() {
    let source = "fn duplicate(tx:Channel::Sender<int>)->Channel::Sender<int> @Fiber{clone(tx)}";
    let parsed = ril_syntax::parse(source);
    let analyzed = ril_compiler::sema::analyze(&parsed.program, FileId(0));
    let verified = analyzed
        .program
        .as_ref()
        .unwrap_or_else(|| panic!("{analyzed:?}"));
    let facts = verified.facts();
    let record = facts
        .copy_invocations
        .iter()
        .find(|record| !record.resource_copies.is_empty())
        .unwrap();
    assert!(record.boundaries.is_empty());
    assert_eq!(record.resource_copies.len(), 1);
    assert_eq!(record.status, CopyInvocationStatus::Completed);
    let event = &facts.resource_clones[record.resource_copies[0].0 as usize];
    assert!(!event.source.value.origins.nodes.is_empty());
    assert!(!event.source.nodes.is_empty());
    assert!(ril_compiler::sema::resource_copy::sender_contract(
        event,
        record,
        &facts.copy_call_events[event.source_event.unwrap().0 as usize]
    ));
}
