use ril_compiler::{
    Session,
    sema::{
        effect_identity::{ArgumentKey, InvocationWitnessKind},
        model::Callable,
    },
};
use ril_compiler_core::ids::CallableOwner;
use std::collections::BTreeSet;

fn verified(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"))
}

#[test]
fn each_closed_call_has_its_own_operations_arguments_and_parent_edge() {
    let program = verified(
        "eff Read<T>{get()->T}\nfn read<T>(witness:T)->T @Read<T>{Read<T>::get()}\nfn forward<U>(value:U)->U @Read<U>{read(value)}\nfn example(){with {Read<int>::get()->resume 7,Read<str>::get()->resume \"seven\"};assert(forward(0)==7&&forward(\"\")==\"seven\")}",
    );
    let facts = program.facts();
    assert_eq!(facts.invocation_expressions.len(), facts.expressions.len());
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "read")
        .unwrap()
        .definition;
    let calls: Vec<_> = facts
        .effect_invocations
        .iter()
        .filter(|call| {
            call.function == target
                && !call.verifying
                && call
                    .arguments
                    .iter()
                    .all(|argument| argument.key.as_ref().is_some_and(ArgumentKey::is_closed))
        })
        .collect();
    assert_eq!(calls.len(), 2);
    let mut selected = BTreeSet::new();
    for call in calls {
        let id = call.invocation.unwrap();
        assert!(
            call.arguments
                .iter()
                .all(|argument| argument.syntax.is_some() && argument.definition == target)
        );
        let invocation = &facts.copy_invocations[id.0 as usize];
        assert_eq!(invocation.target, target);
        assert!(invocation.parent.is_some());
        assert!(
            facts
                .invocation_calls
                .iter()
                .any(|edge| edge.invocation == id && edge.caller_owner.is_some())
        );
        let operations: BTreeSet<_> = facts
            .invocation_expressions
            .iter()
            .filter(|observation| {
                observation.context.invocation == Some(id)
                    && observation.context.owner == Some(CallableOwner::Function(target))
            })
            .flat_map(|observation| {
                facts.expressions[observation.expression]
                    .value
                    .callables
                    .iter()
            })
            .filter_map(|callable| match callable {
                Callable::Builtin(name) => facts
                    .operations
                    .get(name)
                    .map(|operation| operation.identity),
                _ => None,
            })
            .collect();
        assert_eq!(operations, call.operations);
        assert_eq!(operations.len(), 1);
        assert!(selected.insert(*operations.first().unwrap()));
    }
}

#[test]
fn handler_targets_keep_the_invocation_of_their_lexical_definition() {
    let program = verified(
        "eff Read<T>{get()->T}\nfn local<T>(value:T)->T{with Read<T>::get()->resume value;Read<T>::get()}\nfn example(){assert(local(7)==7&&local(\"seven\")==\"seven\")}",
    );
    let facts = program.facts();
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "local")
        .unwrap()
        .definition;
    let calls: Vec<_> = facts
        .effect_invocations
        .iter()
        .filter(|call| call.function == target && !call.verifying)
        .collect();
    assert_eq!(calls.len(), 2);
    let mut operations = BTreeSet::new();
    for call in calls {
        let handlers: Vec<_> = facts
            .invocation_witnesses
            .iter()
            .filter(|event| {
                event.context.invocation == call.invocation
                    && event.context.owner == Some(CallableOwner::Function(target))
            })
            .filter_map(|event| {
                if let InvocationWitnessKind::Handler(index) = event.kind {
                    Some(&facts.handlers[index])
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(handlers.len(), 1);
        assert_eq!(handlers[0].operations.len(), 1);
        assert!(operations.insert(handlers[0].operations[0]));
        for arm in &handlers[0].arms {
            assert!(facts.invocation_expressions.iter().any(|observation| {
                observation.context.invocation == call.invocation
                    && facts.expressions[observation.expression].span == arm.operation.span
            }));
        }
    }
}

#[test]
fn numeric_unwrap_and_budget_witnesses_do_not_borrow_a_global_span_entry() {
    let program = verified(
        "eff Read{get()->int}\nfn read()->int @Read{Read::get()}\nfn optional(value:?int)->int{if value is Some(_){value}else{0}}\nfn work()->int{with Read::get()->resume 7;with Div::exhausted()->0;Div::budget(3,read)}\nfn narrow()->i8{1}\nfn example(){assert(optional(Some(7))==7&&optional(Some(9))==9);assert(work()==7&&work()==7);assert(narrow()==1i8)}",
    );
    let facts = program.facts();
    let mut unwraps = BTreeSet::new();
    let mut budgets = BTreeSet::new();
    let mut causes = BTreeSet::new();
    let mut numeric = false;
    for event in &facts.invocation_witnesses {
        match &event.kind {
            InvocationWitnessKind::ImplicitUnwrap(_) => {
                unwraps.insert(event.context.invocation.unwrap().0);
            }
            InvocationWitnessKind::Budget(proof) => {
                budgets.insert(event.context.invocation.unwrap().0);
                assert!(causes.insert(proof.cause.0));
                assert!(!proof.callee_coverage.is_empty());
            }
            InvocationWitnessKind::ContextualType(_) => numeric = true,
            _ => {}
        }
    }
    assert!(unwraps.len() >= 3);
    assert!(budgets.len() >= 3);
    assert!(numeric);
    assert_eq!(facts.budget_proofs.len(), 1);
}

#[test]
fn result_and_user_sum_projection_witnesses_keep_the_actual_invocation() {
    let program = verified(
        "type Entry{Pair(int,str),Row({label:str}),One(int)}\nfn pair(value:Entry)->str{if value is Entry::Pair(_,_){value.1}else{\"\"}}\nfn row(value:Entry)->str{if value is Entry::Row(_){value.label}else{\"\"}}\nfn one(value:Entry)->int{if value is Entry::One(_){value.0}else{0}}\nfn result(value:Result<int,str>)->int{if value is Ok(_){value.0}else{0}}\nfn example(){assert(pair(Entry::Pair(1,\"one\"))==\"one\");assert(pair(Entry::Pair(2,\"two\"))==\"two\");assert(row(Entry::Row(.{label:\"row\"}))==\"row\");assert(one(Entry::One(7))==7);assert(result(Ok(9))==9)}",
    );
    let facts = program.facts();
    let mut calls = BTreeSet::new();
    let mut direct = false;
    let mut product = false;
    for event in &facts.invocation_witnesses {
        if let InvocationWitnessKind::VariantProjection(proof) = &event.kind {
            calls.insert(event.context.invocation.unwrap().0);
            assert!(event.context.owner.is_some());
            direct |= proof.direct;
            product |= !proof.direct;
            let written = facts
                .variant_projections
                .get(&(event.span.file.0, event.span.start, event.span.end))
                .unwrap();
            assert_eq!(written.tag, proof.tag);
            assert_eq!(written.direct, proof.direct);
        }
    }
    assert!(calls.len() >= 9);
    assert!(direct && product);
}
