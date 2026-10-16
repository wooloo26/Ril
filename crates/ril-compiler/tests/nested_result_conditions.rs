use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"))
}
fn rejected(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).verify();
    assert!(
        matches!(&outcome,Err(CompilationOutcome::Rejected{diagnostics})if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{source}: {outcome:?}"
    );
}
fn source(tail: &str) -> String {
    format!(
        "fn example(flag:bool){{let value:Result<int,str>=Ok(1);let outer:Result<Result<int,str>,str>=if flag{{Ok(value)}}else{{Err(\"closed\")}};{tail}}}"
    )
}

#[test]
fn successful_nested_tests_restore_only_the_actual_required_inspections() {
    for tail in [
        "assert(outer is Ok(Ok(1)))",
        "let tested=outer is Ok(Ok(1));assert(tested)",
        "if outer is Ok(Ok(1)){}else{panic(\"not a match\")}",
        "assert(!!(outer is Ok(Ok(1))))",
        "assert(flag && outer is Ok(Ok(1)))",
        "assert(!(flag || !(outer is Ok(Ok(1)))))",
    ] {
        accepted(&source(tail));
    }
}

#[test]
fn an_unmatched_outer_tag_or_skipped_operand_leaves_the_original_inner_duty() {
    for tail in [
        "let tested=outer is Ok(Ok(1))",
        "assert(flag || outer is Ok(Ok(1)))",
        "let tested=flag && outer is Ok(Ok(1))",
        "assert(outer is Err(_))",
        "let tested=outer is Ok(Ok(1));let wrapped=Some(tested);assert(wrapped is Some(_))",
        "let tested=outer is Ok(Ok(1));let wrapped:Result<bool,str>=Ok(tested);assert(wrapped is Ok(_))",
    ] {
        rejected(&source(tail));
    }
}

#[test]
fn expected_pattern_expressions_execute_once() {
    accepted(
        "fn example(flag:bool){var calls=0;let value:Result<int,str>=Ok(1);let outer:Result<Result<int,str>,str>=if flag{Ok(value)}else{Err(\"closed\")};assert(outer is Ok(Ok({calls+=1;1})));assert(calls==1)}",
    );
}

#[test]
fn facts_and_core_keep_actual_evaluation_identity_and_success_inspections() {
    let program = accepted(&source("let tested=outer is Ok(Ok(1));assert(tested)"));
    let facts = program.facts();
    let evaluations: Vec<_> = facts
        .condition_evaluations
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                ril_compiler::sema::result_conditions::ConditionKind::Pattern
            )
        })
        .collect();
    assert!(!evaluations.is_empty());
    assert!(evaluations.iter().any(|event| {
        !event
            .inspections
            .when_true
            .is_subset(&event.inspections.when_false)
    }));
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    assert_eq!(
        core.provenance.condition_evaluations.len(),
        facts.condition_evaluations.len()
    );
    for (source, lowered) in facts
        .condition_evaluations
        .iter()
        .zip(&core.provenance.condition_evaluations)
    {
        assert_eq!(source.id.0, lowered.id.0);
        assert_eq!(source.cause, lowered.cause);
        assert_eq!(source.context.owner, lowered.owner);
        assert_eq!(
            source.context.invocation.map(|id| id.0),
            lowered.invocation.map(|id| id.0)
        );
        assert_eq!(
            source
                .inspections
                .when_true
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            lowered.inspections.when_true
        );
        assert_eq!(
            source
                .inspections
                .when_false
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            lowered.inspections.when_false
        );
    }
}

#[test]
fn each_iteration_checks_its_current_family_and_cached_bools_cannot_check_future_results() {
    let positive = "fn example(values:[]int){var previous=false;for values as item{let result:Result<int,str>=Ok(item);let outer:Result<Result<int,str>,str>=if item>=0{Ok(result)}else{Err(\"negative\")};let current=outer is Ok(Ok(_));assert(current);previous=current};let _=previous}";
    let program = accepted(positive);
    let previous = program
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "previous")
        .unwrap();
    assert!(previous.value.condition_inspections.when_true.is_empty());
    assert!(previous.value.condition_inspections.when_false.is_empty());
    assert!(
        program.facts().condition_evaluations.len() < 64,
        "loop evidence failed to stabilize"
    );
    rejected(
        "fn example(values:[]int){var previous=true;for values as item{let result:Result<int,str>=Ok(item);let checked=result is Ok(_);assert(checked);previous=checked};let later:Result<int,str>=Err(\"new producer\");assert(previous)}",
    );
}

#[test]
fn wrapper_and_comparison_truth_are_not_payload_truth() {
    for tail in [
        "let tested=outer is Ok(Ok(1));let wrapped=(tested,7);assert(wrapped is (_,7))",
        "let tested=outer is Ok(Ok(1));let wrapped:[]bool=[tested];assert(len(wrapped)==1)",
        "let tested=outer is Ok(Ok(1));assert(tested==tested)",
        "let tested=outer is Ok(Ok(1));assert(tested || !tested)",
    ] {
        rejected(&source(tail));
    }
}

#[test]
fn channel_nested_predicates_inspect_their_own_messages() {
    let source = include_str!("fixtures/nested_result_channel.ril");
    accepted(source);
    rejected(&source.replace(
        "assert((other_rx !> Channel::recv()) is Ok(Ok(2)))",
        "let other_received=other_rx !> Channel::recv();assert(other_received is Ok(_))",
    ));
}

#[test]
fn equal_diagnostic_spans_never_merge_actual_boolean_evaluations() {
    use ril_syntax::ast::{ExprKind, StmtKind};
    let source = "fn example(flag:bool){let first:Result<int,str>=Ok(1);let second:Result<int,str>=Ok(2);let a:Result<Result<int,str>,str>=if flag{Ok(first)}else{Err(\"a\")};let b:Result<Result<int,str>,str>=if flag{Ok(second)}else{Err(\"b\")};let pa=a is Ok(Ok(1));let pb=b is Ok(Ok(2));assert(pa);assert(pb)}";
    for inspect_second in [true, false] {
        let source = if inspect_second {
            source.to_owned()
        } else {
            source.replace("assert(pb)", "let ignored=pb")
        };
        let mut parsed = ril_syntax::parse(&source);
        assert!(parsed.is_ok());
        let StmtKind::Function(function) = &mut parsed.program.statements[0].kind else {
            unreachable!()
        };
        let mut shared = None;
        for statement in &mut function.body.as_mut().unwrap().statements {
            if let StmtKind::Binding(binding) = &mut statement.kind
                && let ExprKind::Is { value, .. } = &mut binding.value.kind
            {
                let span = *shared.get_or_insert(binding.value.span);
                binding.value.span = span;
                value.span = span;
            }
        }
        let outcome = Session::new(vec![]).verify_program(&parsed.program);
        if inspect_second {
            let verified = outcome.unwrap();
            let events: Vec<_> = verified
                .facts()
                .condition_evaluations
                .iter()
                .filter(|event| event.span == shared.unwrap())
                .collect();
            assert_eq!(events.len(), 2);
            assert_ne!(events[0].id, events[1].id);
            assert_ne!(
                events[0].inspections.when_true,
                events[1].inspections.when_true
            );
        } else {
            assert!(
                matches!(&outcome,Err(CompilationOutcome::Rejected{diagnostics})if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
                "{outcome:?}"
            );
        }
    }
}

#[test]
fn a_copied_result_needs_its_own_inspection_even_when_the_old_boolean_is_true() {
    rejected(
        "fn example(){let original:Result<int,str>=Ok(7);let checked=original is Ok(_);let copied=clone(original);assert(checked)}",
    );
    accepted(
        "fn example(){let original:Result<int,str>=Ok(7);let checked=original is Ok(_);let copied=clone(original);assert(checked);assert(copied is Ok(_))}",
    );
}

#[test]
fn budget_recovery_truth_cannot_reuse_the_abandoned_actions_boolean_proof() {
    let source = |recovery| {
        format!(
            "fn dummy(){{}}\nfn example(){{let original:Result<int,str>=Err(\"old\");let checked={{with Div::exhausted()->{recovery};Div::budget(1,\\->{{dummy();original is Err(_)}})}};assert(checked)}}"
        )
    };
    rejected(&source("true"));
    accepted(&source("false"));
}
