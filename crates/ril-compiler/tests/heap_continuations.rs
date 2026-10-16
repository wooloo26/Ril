use ril_compiler::Session;
use ril_ir::{core::ChargeEvent, cps::Terminator, native::Body};

#[test]
fn heap_callbacks_are_continuations_and_internal_sifts_add_no_loop_charges() {
    let source = br#"
use ril/heap
use ril/order
eff Read{get()->int}
fn compare(left:int,right:int)->Order::Ordering{
    with Read::get()->resume left
    Order::compare_int(Read::get(),right)
}
pub fn test_native(){
    let mut ordinary=Heap::new<int>(.{compare:compare});Heap::push(mut ordinary,2);Heap::push(mut ordinary,1);assert(Heap::pop(mut ordinary)==Some(1))
    with Div::exhausted()->()
    Div::budget(100,\->{
        let mut heap=Heap::new<int>(.{compare:compare});Heap::push(mut heap,2);Heap::push(mut heap,1);assert(Heap::pop(mut heap)==Some(1))
    })
}

"#;
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let native = ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    let mut normal_callbacks = 0;
    let mut metered_callbacks = 0;
    for function in &native.functions {
        if let Body::Cps(body) = &function.body {
            for block in &body.blocks {
                assert!(
                    !matches!(
                        block.terminator,
                        Terminator::Charge {
                            event: ChargeEvent::LoopIteration,
                            ..
                        }
                    ),
                    "generated heap sifts must not introduce language loop events"
                );
                if matches!(
                    block.terminator,
                    Terminator::Call {
                        callback_entry: true,
                        ..
                    }
                ) {
                    if body.metered {
                        metered_callbacks += 1;
                    } else {
                        normal_callbacks += 1;
                    }
                }
            }
        }
    }
    assert!(
        normal_callbacks > 0 && metered_callbacks > 0,
        "ordinary Heap calls and budget Heap calls must retain callbacks: normal={normal_callbacks}, metered={metered_callbacks}"
    );
}

#[test]
fn heap_budget_coverage_retains_the_actual_comparator_evidence() {
    let source=b"use ril/heap\nuse ril/order\nfn example(){with Div::exhausted()->();Div::budget(100,\\->{let mut heap=Heap::new<int>(.{compare:Order::compare_int});Heap::push(mut heap,1)})}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let facts = verified.facts();
    assert!(!facts.budget_proofs.is_empty());
    for proof in &facts.budget_proofs {
        assert!(
            proof
                .callee_coverage
                .iter()
                .any(
                    |id| facts.explanations.causes.iter().any(|cause| cause.id == *id
                        && cause
                            .description
                            .contains("receiver's complete retained comparator witness")
                        && cause.parents.len() == 2)
                )
        );
        assert!(
            facts
                .budget_termination
                .iter()
                .any(|witness| witness.span == proof.span && witness.cause == proof.cause)
        );
    }
}

#[test]
fn heap_budget_does_not_certify_an_escaping_comparator_handler() {
    let source = br#"
use ril/heap
use ril/order
eff Read{get()->int}
fn example(){
    with Read::get()->resume 1
    with Div::exhausted()->()
    Div::budget(10,\->{let mut heap=Heap::new<int>(.{compare:\left,right->Order::compare_int(Read::get(),right)});Heap::push(mut heap,1)})
}
"#;
    let outcome = Session::new(source.to_vec()).check();
    assert!(
        matches!(&outcome, ril_compiler::CompilationOutcome::NotImplemented { reason }
            if reason.stage == ril_compiler_core::phase::Stage::Provenance
                && (reason.detail.contains("ordering comparator finite dependency proof")
                    || reason.detail.contains("exact retained comparator coverage"))
        ),
        "{outcome:?}"
    );
}
