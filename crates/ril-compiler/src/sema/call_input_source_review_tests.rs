//! Independent source-coverage and physical-receipt regressions.
//! Prepared for the coordinated active integration gate; not yet compiled or
//! run at creation. Parent module registration belongs to the root owner.
use super::{SemanticFacts, record_bound_validation};
use crate::sema::copy_contract::CopyCallEventId;
use crate::sema::default_uses::{ArgumentSource, DefaultOrigin};

fn checked(source: &str) -> SemanticFacts {
    crate::Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|failure| panic!("{source}\n{failure:?}"))
        .facts()
        .clone()
}

fn accepts(facts: &SemanticFacts) {
    assert_eq!(record_bound_validation::validate(facts), Ok(()));
}

fn rejects(facts: &SemanticFacts, change: &str) {
    assert!(
        record_bound_validation::validate(facts).is_err(),
        "independent source replay accepted {change}"
    );
}

fn erase_applications(facts: &mut SemanticFacts) {
    facts.copy_invocations.clear();
    facts.copy_call_events.clear();
    facts.copy_references.clear();
    facts.call_arguments.clear();
    facts.invocation_calls.clear();
    facts.effect_invocations.clear();
    facts.default_uses.clear();
}

fn call_event(facts: &SemanticFacts, name: &str) -> CopyCallEventId {
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == name)
        .unwrap()
        .definition;
    facts
        .copy_invocations
        .iter()
        .find(|call| call.target == target && call.source_event.is_some())
        .unwrap()
        .source_event
        .unwrap()
}

#[test]
fn ordinary_full_source_obligations_survive_joint_application_arena_deletion() {
    for source in [
        "fn take(value:[2]int){}\nfn example(){take([7,9])}",
        "fn identity(value:[2]int)->int{value[0]}\nfn take(callback:fn([2]int)->int){}\nfn example(){take(identity)}",
    ] {
        let baseline = checked(source);
        accepts(&baseline);
        assert!(baseline.record_bounds.is_empty());
        let mut erased = baseline.clone();
        erase_applications(&mut erased);
        rejects(
            &erased,
            "all ordinary application arenas erased with real Call Source retained",
        );

        erased.source_program = None;
        rejects(
            &erased,
            "the real Program and all ordinary application arenas erased together",
        );
    }
}

#[test]
fn declaration_only_program_cannot_hide_registered_executable_function_bodies() {
    let baseline = checked("fn take(value:[2]int){}\nfn example(){take([7,9])}");
    accepts(&baseline);
    let parsed = ril_syntax::parse("fn take(value:[2]int){}\nfn example(){0          }");
    assert!(parsed.is_ok());
    let mut changed = baseline;
    erase_applications(&mut changed);
    changed.source_program = Some(std::sync::Arc::new(parsed.program));
    rejects(
        &changed,
        "declaration-only Program used to hide a different registered Call body",
    );
}

#[test]
fn unused_explicit_type_still_requires_its_actual_prefix_and_static_environment() {
    let baseline =
        checked("fn choose<T>(value:int=7)->int{value}\nfn example(){assert(choose<str>()==7)}");
    accepts(&baseline);
    assert!(baseline.record_bounds.is_empty());
    let mut erased = baseline.clone();
    erase_applications(&mut erased);
    rejects(&erased, "unused explicit T application coverage erased");
    let mut erased = baseline;
    erased.effect_invocations.clear();
    rejects(
        &erased,
        "unused explicit T's complete owned static rows erased",
    );
}

#[test]
fn ordinary_callee_identity_precedes_sensitive_formal_shortcuts() {
    let baseline =
        checked("fn take(value:[2]int){}\nfn scalar(value:int){}\nfn example(){take([7,9])}");
    accepts(&baseline);
    let event = call_event(&baseline, "take");
    let scalar = baseline
        .functions
        .iter()
        .find(|function| function.syntax.name == "scalar")
        .unwrap()
        .definition;
    let mut changed = baseline.clone();
    let call = changed
        .copy_invocations
        .iter_mut()
        .find(|call| call.source_event == Some(event))
        .unwrap();
    call.target = scalar;
    call.direct = false;
    rejects(
        &changed,
        "sensitive actual callee changed to an insensitive function",
    );

    let mut changed = baseline.clone();
    changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap()
        .target = Some(scalar);
    rejects(
        &changed,
        "argument preparation borrowed another callee target",
    );

    let mut changed = baseline;
    changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap()
        .evaluation_complete = false;
    rejects(
        &changed,
        "incomplete preparation attached to an entered sensitive call",
    );
}

#[test]
fn actual_source_name_cannot_be_retargeted_by_consistent_callee_metadata() {
    use crate::sema::model::Callable;
    let baseline =
        checked("fn take(value:[2]int){}\nfn scalar(value:int){}\nfn example(){take([7,9])}");
    accepts(&baseline);
    let event = call_event(&baseline, "take");
    let (scalar_index, scalar) = baseline
        .functions
        .iter()
        .enumerate()
        .find(|(_, function)| function.syntax.name == "scalar")
        .map(|(index, function)| (index, function.definition))
        .unwrap();
    let mut changed = baseline;
    let callee = changed.copy_call_events[event.0 as usize]
        .callee_expression
        .unwrap();
    changed.copy_call_events[event.0 as usize].target = Some(scalar);
    changed.expressions[callee]
        .value
        .corrupt_value(&mut 4_000_000)
        .unwrap()
        .callables = vec![Callable::Named(scalar_index)];
    // Leave the actual Program's Name("take"), its span and its genuine binding
    // untouched. Agreement among the following metadata is not source proof.
    for call in &mut changed.copy_invocations {
        if call.source_event == Some(event) {
            call.target = scalar;
            for row in &mut changed.effect_invocations {
                if row.invocation == Some(call.id) {
                    row.function = scalar;
                }
            }
        }
    }
    for reference in &mut changed.copy_references {
        if reference.direct_call == Some(event) {
            reference.target = scalar;
        }
    }
    rejects(
        &changed,
        "joint callee metadata retargeting with real Source Name unchanged",
    );
}

#[test]
fn earlier_parameter_default_uses_callee_lexical_source_and_outer_caller_identity() {
    for source in [
        "fn take(first:[2]int,second:[2]int=first){}\nfn example(){take([7,9])}",
        "fn take<T>(first:[2]int,second:[2]int=first){}\nfn example(){take<str>([7,9])}",
    ] {
        let facts = checked(source);
        accepts(&facts);
    }
}

#[test]
fn fixed_array_formal_forwarding_keeps_its_real_mutable_access_mode() {
    let facts = checked(
        "fn take(mut values:[2]int)&mut{values[0]=1}\nfn forward(mut values:[2]int)&mut{take(mut values)}\nfn example(){let mut values:[2]int=[7,9];forward(mut values)}",
    );
    accepts(&facts);
}

#[test]
fn all_dynamic_array_roots_keep_stored_nested_element_dimensions_invariant() {
    let source = "fn take(values:[][]int){}\nfn example(){let stored:[0][3]int=[];take(stored)}";
    let outcome = crate::Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,crate::CompilationOutcome::Rejected{diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn source_calls_with_proven_absent_body_entry_remain_lawful() {
    for source in [
        "fn take(value:[2]int){}\nfn example(){return;take([7,9])}",
        "fn take(value:[2]int){}\nfn example(){take(panic(\"stop\"))}",
    ] {
        let facts = checked(source);
        accepts(&facts);
    }
}

#[test]
fn default_completion_epoch_and_identity_cannot_be_removed_or_borrowed() {
    let baseline = checked("fn take(value:[2]int=[7,9]){}\nfn example(){take();take()}");
    accepts(&baseline);
    let event = call_event(&baseline, "take");
    let default = baseline
        .default_uses
        .iter()
        .find(|usage| usage.origin == DefaultOrigin::Call(event))
        .unwrap()
        .id;
    let mut changed = baseline.clone();
    changed.default_uses[default.0 as usize].result_allocation_epoch = None;
    rejects(&changed, "default's actual completion epoch removed");

    let other = baseline
        .default_uses
        .iter()
        .find(|usage| {
            matches!(usage.origin, DefaultOrigin::Call(other) if other != event)
                && usage.span == baseline.default_uses[default.0 as usize].span
        })
        .unwrap()
        .id;
    let mut changed = baseline;
    let preparation = changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap();
    let slot = preparation
        .slots
        .iter_mut()
        .find(|slot| **slot == ArgumentSource::Default(default))
        .unwrap();
    *slot = ArgumentSource::Default(other);
    rejects(
        &changed,
        "another event's equal-span completed default identity borrowed",
    );
}

#[test]
fn later_same_span_and_caller_operand_cannot_pay_an_earlier_physical_application() {
    let baseline = checked(ril_test::case_source(
        "tests/regressions/evaluation-identity.ril::application-repeated-source-interval",
    ));
    accepts(&baseline);
    let take = baseline
        .functions
        .iter()
        .find(|function| function.syntax.name == "take")
        .unwrap()
        .definition;
    let mut candidates = vec![];
    for call in &baseline.copy_invocations {
        if call.target != take {
            continue;
        }
        let Some(event) = call.source_event else {
            continue;
        };
        let preparation = baseline
            .call_arguments
            .iter()
            .find(|row| row.source_event == event)
            .unwrap();
        let Some(token) = preparation.supplied.get(&0).copied() else {
            continue;
        };
        let context = baseline
            .invocation_expressions
            .iter()
            .find(|row| row.expression == token.expression)
            .unwrap()
            .context;
        candidates.push((event, token, context));
    }
    let mut pair = None;
    for (earlier_event, earlier_token, earlier_context) in &candidates {
        for (later_event, later_token, later_context) in &candidates {
            if earlier_event != later_event
                && earlier_token.expression < later_token.expression
                && earlier_token.allocation_epoch == later_token.allocation_epoch
                && earlier_context == later_context
                && baseline.expressions[earlier_token.expression].span
                    == baseline.expressions[later_token.expression].span
            {
                pair = Some((*earlier_event, *later_event, *later_token));
                break;
            }
        }
    }
    // The scalar count transition forces a real second fixed-point visit:
    // constant zero first widens to unknown, then reaches a stable integer.
    // If ordinary loop analysis changes its observation policy, replace the
    // fixture with an equivalent real repeated occurrence; do not fabricate
    // same-span physical receipts or silently skip this prerequisite.
    let (event, later_event, later_token) =
        pair.expect("fixture needs two real same-context loop observations");
    let earlier_token = baseline
        .call_arguments
        .iter()
        .find(|row| row.source_event == event)
        .unwrap()
        .supplied[&0];
    let mut changed = baseline.clone();
    *changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap()
        .supplied
        .get_mut(&0)
        .unwrap() = later_token;
    rejects(
        &changed,
        "later equal-span/context supplied operand grafted into an earlier event",
    );

    // Swap both physical operands, their prefix tokens and their slot tags.
    // Global uniqueness and slot cardinality remain intact; the canonical
    // evaluation interval must still reject the later root at the earlier call.
    let mut changed = baseline;
    *changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap()
        .supplied
        .get_mut(&0)
        .unwrap() = later_token;
    *changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == later_event)
        .unwrap()
        .supplied
        .get_mut(&0)
        .unwrap() = earlier_token;
    for row in &mut changed.invocation_expressions {
        if row.expression == earlier_token.expression {
            row.argument_of = Some((later_event, 0));
        }
        if row.expression == later_token.expression {
            row.argument_of = Some((event, 0));
        }
    }
    let step = changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap()
        .evaluated
        .iter_mut()
        .find(|step| step.observation == earlier_token)
        .unwrap();
    step.observation = later_token;
    let step = changed
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == later_event)
        .unwrap()
        .evaluated
        .iter_mut()
        .find(|step| step.observation == later_token)
        .unwrap();
    step.observation = earlier_token;
    let failure = record_bound_validation::validate(&changed)
        .expect_err("joint retagging cannot move a later operand before its own Source boundary");
    assert!(
        failure
            .2
            .contains("application prefix changed its physical order or allocation epoch"),
        "coordinated metadata mutation must fail at the canonical physical upper bound: {failure:?}"
    );
}
