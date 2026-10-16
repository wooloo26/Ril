//! Lambda Source types retain their real creator, body and parameter scopes.
use ril_compiler::sema::{SemanticFacts, facts::ScopeId, validate::solved_facts};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

const STEP: &str = "fn apply(callback:fn(int)->int,x:int)->int{callback(x)}\nfn example(){let step=\\n:int->n+1;let callback=\\n->apply(step,n);assert(callback(1)==2)}";

fn verified(source: &str) -> SemanticFacts {
    let mut facts = None;
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
        solved_facts(program.facts()).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        facts = Some(program.facts().clone());
    }
    facts.unwrap()
}

#[test]
fn real_lambda_bodies_and_immutable_generic_locals_supply_complete_source() {
    for source in [
        STEP,
        "fn make<T>(value:T)->fn(T)->T{\\argument:T->argument}\nfn consume<T>(value:T){let action=make(1);assert(action(2)==2)}",
        "fn empty<T>()->[]T{let values:[]T=[];values}\nfn example(){let values:[]int=empty()}",
        "type Number=int\nfn first<T>(value:(T,T))->T{value.0}\nfn example(){let number:Number=first((1,2));assert(number==1)}",
    ] {
        verified(source);
    }
}

#[test]
fn an_open_public_fn_view_does_not_recover_the_original_parameter_view() {
    let source = "fn example<T>(values:[]T){let callback:fn([2]T)->int=\\items:[]T->0;let number=callback(values)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
        if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn closure_activation_and_formal_owner_cannot_be_deleted_or_borrowed() {
    let facts = verified(STEP);
    let probe = facts
        .closure_invocations
        .iter()
        .find(|call| call.probe && call.activation.is_some())
        .unwrap();
    let activation = probe.activation.unwrap();
    let parameter = facts.closures[probe.closure].parameters[0].pattern.span;
    let mut changed = facts.clone();
    changed.closure_invocations[probe.id.0 as usize].activation = None;
    assert!(solved_facts(&changed).is_err());
    let mut changed = facts.clone();
    changed
        .bindings
        .iter_mut()
        .find(|binding| {
            binding.parameter && binding.owner == activation && binding.span == parameter
        })
        .unwrap()
        .owner = ScopeId(0);
    assert!(solved_facts(&changed).is_err());
}

#[test]
fn captured_named_headers_keep_their_own_type_selection_at_each_entry() {
    for source in [
        "fn make<T>(value:T)->fn(T)->T{fn same(argument:T)->T{argument};same}\nfn consume<T>(value:T){let action=make(1);assert(action(2)==2)}",
        "fn make<T>(value:T)->fn(T)->T{fn same(argument:T)->T{argument};same}\nfn example(){let number=make(1);let word=make(\"one\");assert(number(2)==2);assert(word(\"two\")==\"two\")}",
    ] {
        verified(source);
    }
}

#[test]
fn open_callable_rows_survive_real_product_operands() {
    for source in [
        "var calls=0\nfn step(value:int)->int &{mut calls}{calls+=1;value}\nfn invoke(value:{step:fn(int)->int &{mut calls}})&{mut calls}{assert(value.step(1)==1)}\nfn example()&{mut calls}{invoke(.{step:step})}",
        include_str!("fixtures/record_bounds/scoped_callable_mut.ril"),
    ] {
        verified(source);
    }
}

#[test]
fn a_creation_probe_cannot_be_relabelled_as_an_unrecorded_runtime_call() {
    let facts = verified(STEP);
    let probe = facts
        .closure_invocations
        .iter()
        .find(|invocation| {
            invocation.probe
                && facts.closures[invocation.closure]
                    .parameters
                    .iter()
                    .all(|parameter| parameter.ty.is_some())
        })
        .unwrap();
    let mut changed = facts.clone();
    changed.closure_invocations[probe.id.0 as usize].probe = false;
    assert!(solved_facts(&changed).is_err());
}
