use ril_compiler::{Session, sema::model::Ty};

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
    ril_compiler::lower::lower_core(&verified).unwrap();
}
