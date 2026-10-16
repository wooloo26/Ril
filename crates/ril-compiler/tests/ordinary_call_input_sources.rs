//! Original input schemas are obligations even when an application arena is
//! damaged; fresh receiving comes only from the actual operand syntax.
use ril_compiler::sema::{SemanticFacts, validate::solved_facts};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn verified(source: &str) -> SemanticFacts {
    let program = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
    solved_facts(program.facts()).unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

fn type_conflict(source: &str) {
    for target in ["pointer32", "pointer64"] {
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn a_stored_array_never_borrows_its_backing_count_for_receiving() {
    for source in [
        "fn exact(value:[2]int)->int{0}\nfn example()->int{let values:[]int=[7,9];exact(values)}",
        "fn exact<T>(value:[2]T)->int{0}\nfn example()->int{let values:[]int=[7,9];exact(values)}",
        "fn exact<T>(value:[2]T)->int{0}\nfn example()->int{let values:[]int=[7,9];exact<int>(values)}",
        "fn id<T>(value:T)->T{value}\nfn example(){let values:[]int=[7,9];let fixed=id<[2]int>(values)}",
        "fn exact<T>(value:[0][2]T)->int{0}\nfn example()->int{let values:[0][3]int=[];exact(values)}",
        "fn exact(value:[][]int)->int{0}\nfn example()->int{let values:[0][3]int=[];exact(values)}",
    ] {
        type_conflict(source);
    }
}

#[test]
fn callable_dimensions_are_checked_inside_the_original_signature() {
    type_conflict(
        "fn take(callback:fn([2]int)->int)->int{0}\nfn triple(values:[3]int)->int{0}\nfn example()->int{take(triple)}",
    );
}

#[test]
fn a_fresh_returned_shell_does_not_make_a_default_a_literal() {
    type_conflict(
        "fn dynamic()->[]int{[7,9]}\nfn take(value:[2]int=dynamic())->int{0}\nfn example()->int{take()}",
    );
}

#[test]
fn direct_literal_and_earlier_parameter_defaults_keep_their_real_receiving_context() {
    for source in [
        "fn take(value:[2]int)->int{value[0]}\nfn example()->int{take([7,9])}",
        "fn take(value:[2]int=[7,9])->int{value[0]}\nfn example()->int{take()}",
        "fn take(first:[2]int,second:[2]int=first)->int{second[0]}\nfn example()->int{take([7,9])}",
        "fn defaulted<T>(value:int=7)->int{value}\nfn example()->int{defaulted<str>()}",
        "fn id<T>(value:T)->T{value}\nfn example()->[2]int{id<[2]int>([7,9])}",
    ] {
        verified(source);
    }
}

#[test]
fn mutable_forwarding_keeps_its_source_type_and_its_original_loan_mode() {
    verified(
        "fn take(mut values:[2]int)&mut{values[0]=1}\nfn forward(mut values:[2]int)&mut{take(mut values)}\nfn example(){let mut values:[2]int=[7,9];forward(mut values)}",
    );
}

#[test]
fn deleting_the_call_tables_or_the_program_cannot_make_source_coverage_vacuous() {
    let facts = verified("fn take(values:[2]int){}\nfn example(){take([7,9])}");
    let mut deleted = facts.clone();
    deleted.copy_invocations.clear();
    deleted.copy_call_events.clear();
    deleted.call_arguments.clear();
    deleted.invocation_calls.clear();
    deleted.effect_invocations.clear();
    assert!(solved_facts(&deleted).is_err());
    deleted.source_program = None;
    assert!(solved_facts(&deleted).is_err());
    deleted.source_program = verified("fn take(values:[2]int){}\nfn example(){}").source_program;
    assert!(solved_facts(&deleted).is_err());
}

#[test]
fn changing_a_sensitive_target_to_a_scalar_target_cannot_skip_the_source_gate() {
    let facts =
        verified("fn take(values:[2]int){}\nfn scalar(value:int){}\nfn example(){take([7,9])}");
    let take = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "take")
        .unwrap()
        .definition;
    let scalar = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "scalar")
        .unwrap()
        .definition;
    let mut changed = facts.clone();
    let call = changed
        .copy_invocations
        .iter_mut()
        .find(|call| call.target == take && call.source_event.is_some())
        .unwrap();
    call.target = scalar;
    call.direct = false;
    assert!(solved_facts(&changed).is_err());
}

#[test]
fn a_supplied_token_and_its_emission_must_name_this_exact_event_and_slot() {
    let facts = verified(
        "fn take(values:[2]int){}\nfn example(){let values:[2]int=[7,9];take(values);take(values)}",
    );
    let take = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "take")
        .unwrap()
        .definition;
    let events: Vec<_> = facts
        .copy_call_events
        .iter()
        .filter(|event| event.target == Some(take))
        .map(|event| event.id)
        .collect();
    assert!(events.len() >= 2);
    let first = facts
        .call_arguments
        .iter()
        .find(|row| row.source_event == events[0])
        .unwrap()
        .supplied[&0];
    let later = facts
        .call_arguments
        .iter()
        .find(|row| row.source_event == events[1])
        .unwrap()
        .supplied[&0];
    assert_ne!(first.expression, later.expression);
    let mut changed = facts.clone();
    changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == events[0])
        .unwrap()
        .supplied
        .insert(0, later);
    assert!(solved_facts(&changed).is_err());
    let mut changed = facts.clone();
    changed
        .invocation_expressions
        .iter_mut()
        .find(|row| row.expression == first.expression)
        .unwrap()
        .argument_of = Some((events[1], 0));
    assert!(solved_facts(&changed).is_err());
}

#[test]
fn a_symbolic_public_callable_cannot_receive_a_stored_dynamic_array_as_fixed() {
    type_conflict(
        "fn call(callback:fn([2]int)->int,values:[]int)->int{callback(values)}\nfn example(){}",
    );
}
