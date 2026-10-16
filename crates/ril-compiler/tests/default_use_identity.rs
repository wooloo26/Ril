use ril_compiler::sema::{
    copy_contract::CopyInvocationStatus,
    default_uses::{ArgumentSource, DefaultOrigin},
};
use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"))
}

#[test]
fn actual_defaults_have_callee_static_keys_and_an_exact_entered_call_event() {
    for source in [
        ril_test::case_source("tests/regressions/defaults.ril::scalars-and-order"),
        ril_test::case_source("tests/regressions/defaults.ril::local-handler"),
        ril_test::case_source("tests/regressions/defaults.ril::local-budget"),
    ] {
        let program = accepted(source);
        let facts = program.facts();
        let actual: Vec<_> = facts
            .default_uses
            .iter()
            .filter(|usage| matches!(usage.origin, DefaultOrigin::Call(_)))
            .collect();
        assert!(!actual.is_empty());
        for usage in actual {
            assert!(usage.evaluation_complete, "{usage:?}");
            assert_eq!(usage.status, CopyInvocationStatus::Completed, "{usage:?}");
            assert_eq!(usage.entered.len(), 1, "{usage:?}");
            let call = &facts.copy_invocations[usage.entered[0].0 as usize];
            let DefaultOrigin::Call(event) = usage.origin else {
                unreachable!()
            };
            assert_eq!(call.source_event, Some(event));
            assert_eq!(Some(call.target), usage.target);
            assert!(
                facts
                    .call_arguments
                    .iter()
                    .any(|arguments| arguments.source_event == event
                        && arguments.slots[usage.parameter as usize]
                            == ArgumentSource::Default(usage.id))
            );
            assert!(
                facts
                    .invocation_expressions
                    .iter()
                    .any(|fact| fact.context.default_use == Some(usage.id))
            );
        }
    }
}

#[test]
fn default_created_retained_closures_keep_their_actual_use_and_parameter_transfer() {
    let program = accepted(ril_test::case_source(
        "tests/regressions/defaults.ril::retained-closure",
    ));
    let facts = program.facts();
    let actual: Vec<_> = facts
        .closures
        .iter()
        .filter_map(|closure| {
            closure
                .creation_default
                .map(|id| (closure, &facts.default_uses[id.0 as usize]))
        })
        .filter(|(_, usage)| matches!(usage.origin, DefaultOrigin::Call(_)))
        .collect();
    assert_eq!(actual.len(), 3);
    for (_, usage) in actual {
        assert_eq!(usage.status, CopyInvocationStatus::Completed);
        assert_eq!(usage.entered.len(), 1);
    }
}

#[test]
fn a_callee_cannot_disguise_a_new_capture_as_a_forwarded_parameter() {
    let source = "type Reader=fn()->int &closure\nfn wrap(reader:Reader)->Reader{\\->reader()}\nfn example(){let value=wrap(\\->7);assert(value()==7)}";
    let Err(CompilationOutcome::Rejected { diagnostics }) =
        Session::new(source.as_bytes().to_vec()).verify()
    else {
        panic!("new capture accepted")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0510"),
        "{diagnostics:?}"
    );
}

#[test]
fn caller_generic_names_never_select_the_callee_default_binder() {
    accepted(
        "eff Read<T>{get()->T}\nfn selected<T>(w:T,value:T={with Read<T>::get()->resume w;Read<T>::get()})->T{value}\nfn caller<T>(w:T)->str{selected(\"seven\")}\nfn example(){assert(caller(7)==\"seven\")}",
    );
}

#[test]
fn a_stopping_default_does_not_evaluate_later_defaults_or_enter_the_body() {
    let program = accepted(
        "fn stopped(first:int=panic(\"default\"),second:int=9)->int{second}\nfn example(){stopped()}",
    );
    let facts = program.facts();
    let target = facts
        .functions
        .iter()
        .find(|info| info.syntax.name == "stopped")
        .unwrap()
        .definition;
    let actual: Vec<_> = facts
        .default_uses
        .iter()
        .filter(|usage| {
            matches!(usage.origin, DefaultOrigin::Call(_)) && usage.target == Some(target)
        })
        .collect();
    assert_eq!(actual.len(), 1);
    assert_eq!(actual[0].parameter, 0);
    assert!(!actual[0].evaluation_complete);
    assert!(actual[0].entered.is_empty());
    assert_ne!(actual[0].status, CopyInvocationStatus::Completed);
    let DefaultOrigin::Call(event) = actual[0].origin else {
        unreachable!()
    };
    assert!(
        !facts
            .copy_invocations
            .iter()
            .any(|call| call.source_event == Some(event))
    );
    assert!(
        facts
            .default_uses
            .iter()
            .any(|usage| usage.parameter == 1 && usage.origin == DefaultOrigin::DeclarationProbe)
    );
}

#[test]
fn result_producers_and_default_only_inspections_remain_application_specific() {
    accepted(
        "fn check(value:Result<int,str>,checked:bool=value is Ok(_)){assert(checked)}\nfn example(){let result:Result<int,str>=Ok(7);check(result)}",
    );
    for source in [
        "fn ignore(value:Result<int,str>=Ok(7)){}\nfn example(){ignore()}",
        "fn check(value:Result<int,str>,checked:bool=value is Ok(_)){assert(checked)}\nfn example(){let result:Result<int,str>=Ok(7);check(result,true)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).verify();
        let Err(CompilationOutcome::Rejected { diagnostics }) = outcome else {
            panic!("Result duty lost: {source}: {outcome:?}")
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{diagnostics:?}"
        );
    }
}

#[test]
fn universally_bad_defaults_are_checked_even_when_every_call_supplies_the_slot() {
    let source = "eff Read{get()->int}\nfn selected(value:int=Read::get())->int{value}\nfn example(){assert(selected(7)==7)}";
    let Err(CompilationOutcome::Rejected { diagnostics }) =
        Session::new(source.as_bytes().to_vec()).verify()
    else {
        panic!("universal default disappeared")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0409"),
        "{diagnostics:?}"
    );
}

#[test]
fn the_same_received_closure_can_arrive_through_multiple_parameter_paths() {
    accepted(
        "type Reader=fn()->int &closure\nfn pass(first:Reader,second:Reader)->(Reader,Reader){(first,second)}\nfn example(){let value=7;let reader=\\->value;let pair=pass(reader,reader);assert(pair.0()==7&&pair.1()==7)}",
    );
}

#[test]
fn a_result_prefix_survives_a_later_default_panic_without_claiming_inspection() {
    let program = accepted(
        "fn stopped(first:Result<int,str>=Ok(7),second:int=panic(\"default\")){assert(first is Ok(_))}\nfn example(){stopped()}",
    );
    let facts = program.facts();
    let actual: Vec<_> = facts
        .default_uses
        .iter()
        .filter(|usage| matches!(usage.origin, DefaultOrigin::Call(_)))
        .collect();
    assert_eq!(actual.len(), 2);
    assert!(actual.iter().all(|usage| usage.entered.is_empty()));
    let result = &actual[0].result.as_ref().unwrap().value;
    assert_eq!(result.results.len(), 1);
    for id in &result.results {
        let duty = &facts.result_duties[*id as usize];
        assert!(!duty.inspected);
        assert!(
            duty.abnormal,
            "producer must reach the caller's actual panic exit: {duty:?}"
        );
        assert!(!duty.returned);
    }
}

#[test]
fn budget_recovery_in_a_later_default_keeps_the_earlier_result_duty() {
    let prefix = "fn selected(first:Result<int,str>=Ok(7),second:int={with Div::exhausted()->0;Div::budget(0,\\->1)})";
    // The recovery exits only the second default's block. The first producer
    // must still reach the subsequent named invocation, which inspects it.
    let source = format!("{prefix}{{assert(first is Ok(_))}}\nfn example(){{selected()}}");
    accepted(&source);
    let inspected_prefix = "fn selected(first:Result<int,str>=Ok(7),checked:bool=first is Ok(_),second:int={with Div::exhausted()->0;Div::budget(0,\\->1)}){assert(checked)}\nfn example(){selected()}";
    accepted(inspected_prefix);
    let source = format!("{prefix}{{}}\nfn example(){{selected()}}");
    let Err(CompilationOutcome::Rejected { diagnostics }) =
        Session::new(source.into_bytes()).verify()
    else {
        panic!("budget recovery hid Result duty")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0720"),
        "{diagnostics:?}"
    );
}

#[test]
fn default_parameter_aliases_do_not_duplicate_or_inspect_the_original_result() {
    let prefix = "fn selected(first:Result<int,str>,second:Result<int,str>=first)";
    accepted(&format!(
        "{prefix}{{assert(second is Ok(_))}}\nfn example(){{let result:Result<int,str>=Ok(7);selected(result)}}"
    ));
    let source =
        format!("{prefix}{{}}\nfn example(){{let result:Result<int,str>=Ok(7);selected(result)}}");
    let Err(CompilationOutcome::Rejected { diagnostics }) =
        Session::new(source.into_bytes()).verify()
    else {
        panic!("default alias hid Result duty")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0720"),
        "{diagnostics:?}"
    );
}

#[test]
fn ambient_access_is_not_a_parameter_transfer_even_for_the_same_closure_object() {
    let source = "type Reader=fn()->int &closure\nfn example(){let value=7;let reader=\\->value;let returned=pass(reader);assert(returned()==7) where fn pass(input:Reader)->Reader{reader}}";
    let outcome = Session::new(source.as_bytes().to_vec()).verify();
    let Err(CompilationOutcome::Rejected { diagnostics }) = outcome else {
        panic!("ambient alias incorrectly hidden: {outcome:?}")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0510"),
        "{diagnostics:?}"
    );
}

#[test]
fn caller_generic_result_cannot_override_an_incompatible_callee_default() {
    let source = "fn selected<T>(w:T,value:T=w)->T{value}\nfn caller<T>(w:T)->T{selected(\"seven\")}\nfn example(){let value=caller(7)}";
    let Err(CompilationOutcome::Rejected { diagnostics }) =
        Session::new(source.as_bytes().to_vec()).verify()
    else {
        panic!("caller binder laundered incompatible str")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0301"),
        "{diagnostics:?}"
    );
}
