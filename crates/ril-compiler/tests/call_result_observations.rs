use ril_compiler::{
    Session,
    sema::{model::Ty, validate::solved_facts},
};

#[test]
fn actual_call_roots_keep_the_same_full_context_as_their_callee() {
    let verified = Session::new(
        ril_test::case_bytes(
            "tests/regressions/source-observations.ril::call-result-complete-roots",
        )
        .to_vec(),
    )
    .verify()
    .unwrap();
    let facts = verified.facts();
    assert!(!facts.copy_call_events.is_empty());
    for event in &facts.copy_call_events {
        let callee = event.callee_expression.unwrap();
        let result = event.result_expression.unwrap();
        assert!(callee < result);
        assert_eq!(facts.expressions[result].span, event.span);
        assert_eq!(
            facts.invocation_expressions[callee].context,
            facts.invocation_expressions[result].context
        );
    }
    for event in &facts.copy_call_events {
        let mut missing = facts.clone();
        missing.copy_call_events[event.id.0 as usize].result_expression = None;
        assert!(solved_facts(&missing).is_err());
        let mut retargeted = facts.clone();
        retargeted.copy_call_events[event.id.0 as usize].result_expression =
            event.callee_expression;
        assert!(solved_facts(&retargeted).is_err());
    }
}

#[test]
fn an_observed_never_root_does_not_claim_normal_argument_or_body_completion() {
    let verified = Session::new(
        ril_test::case_bytes("tests/regressions/source-observations.ril::call-result-never-root")
            .to_vec(),
    )
    .verify()
    .unwrap();
    let facts = verified.facts();
    assert!(facts.copy_call_events.iter().any(|event| {
        event
            .result_expression
            .is_some_and(|result| facts.expressions[result].value.ty == Ty::Never)
    }));
    solved_facts(facts).unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}
