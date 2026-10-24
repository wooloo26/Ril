use ril_compiler::{CompilationOutcome, Session};

fn direct(call: &str) -> String {
    format!(
        "type Cell={{mut value:int}}\nfn example(){{let mut source=Cell.{{value:1}};source.value+=0;let mut other=Cell.{{value:2}};other.value+=0;let view action=\\mut target:Cell,padding:int->{{let observed=source.value;target.value+=1;observed}};{call}}}"
    )
}
#[test]
fn actual_closure_objects_prove_each_independent_argument_relation() {
    let source = direct("let result=action(mut other,0)");
    let verified = Session::new(source.into_bytes()).verify().unwrap();
    let facts = verified.facts();
    assert!(
        facts
            .closure_exclusivity_checks
            .iter()
            .any(|check| matches!(
                check.resolution,
                ril_compiler::sema::closure_exclusivity::Resolution::Discharged { .. }
            ))
    );
    let source = direct("let result=action(mut source,0)");
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0524")),
        "{outcome:?}"
    );
}
#[test]
fn typed_uninvoked_or_failed_closures_do_not_gain_actual_coverage() {
    for body in [
        "",
        "let first=action(mut other,0);let second=action(mut source,1)",
    ] {
        let outcome = Session::new(direct(body).into_bytes()).check();
        if body.is_empty() {
            assert!(
                matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.detail.contains("conditional closure exclusivity")),
                "{outcome:?}"
            );
        } else {
            assert!(
                matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0524")),
                "{outcome:?}"
            );
        }
    }
}

fn factory(public: bool, body: &str) -> String {
    format!(
        "type Cell={{mut value:int}}\ntype Reader=fn(mut Cell,int)->int &mut &closure\n{}fn make(source:Cell)->Reader &capture{{\\mut target:Cell,padding:int->{{let observed=source.value;target.value+=1;observed}}}}\nfn example(){{let mut shared=Cell.{{value:1}};shared.value+=0;let mut other=Cell.{{value:2}};other.value+=0;{body}}}",
        if public { "pub " } else { "" }
    )
}

#[test]
fn private_factory_templates_cover_each_real_created_closure() {
    let source = factory(
        false,
        "let view action=make(shared);let result=action(mut other,0)",
    );
    let verified = Session::new(source.into_bytes()).verify().unwrap();
    let certificate = verified
        .facts()
        .closure_exclusivity_certificate
        .as_ref()
        .unwrap();
    assert!(!certificate.templates.is_empty());
    assert!(
        certificate
            .templates
            .values()
            .all(|objects| !objects.is_empty())
    );
    let source = factory(
        false,
        "let view first=make(shared);let view second=make(shared);let a=first(mut other,0);let b=second(mut shared,1)",
    );
    let result = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&result,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0524")),
        "{result:?}"
    );
}

#[test]
fn public_uninvoked_and_uncovered_sibling_creations_keep_pending_requirements() {
    for (public, body) in [
        (
            true,
            "let view action=make(shared);let result=action(mut other,0)",
        ),
        (false, ""),
        (false, "let view action=make(shared)"),
        (
            false,
            "let view first=make(shared);let view second=make(shared);let result=first(mut other,0)",
        ),
        (
            false,
            "let create=make;let view action=create(shared);let result=action(mut other,0)",
        ),
    ] {
        let result = Session::new(factory(public, body).into_bytes()).check();
        assert!(
            matches!(&result,CompilationOutcome::NotImplemented{reason}if reason.detail.contains("conditional closure exclusivity")),
            "{public}/{body}: {result:?}"
        );
    }
}

#[test]
fn generic_factory_instances_cannot_exchange_successful_object_coverage() {
    let prefix = "type Cell={mut value:int}\ntype Reader=fn(mut Cell,int)->int &mut &closure\nfn make<T>(source:Cell,unused:T)->Reader &capture{\\mut target:Cell,padding:int->{let observed=source.value;target.value+=1;observed}}\n";
    for (second, accepted) in [("other", true), ("source", false)] {
        let source = format!(
            "{prefix}fn example(){{let mut source=Cell.{{value:1}};source.value+=0;let mut other=Cell.{{value:2}};let view first=make(source,1);let view second=make(source,\"two\");let a=first(mut other,0);let b=second(mut {second},1)}}"
        );
        let outcome = Session::new(source.into_bytes()).check();
        if accepted {
            assert!(
                matches!(outcome, CompilationOutcome::Accepted { .. }),
                "{outcome:?}"
            );
        } else {
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0524")),
                "{outcome:?}"
            );
        }
    }
}

#[test]
fn an_expression_statement_can_discard_only_its_own_unescaped_new_object() {
    use ril_compiler::sema::closure_exclusivity as domain;
    let source = factory(
        false,
        "make(shared);let view action=make(shared);let result=action(mut other,0)",
    );
    let verified = Session::new(source.into_bytes()).verify().unwrap();
    let facts = verified.facts();
    domain::validate(facts).unwrap();
    let certificate = facts.closure_exclusivity_certificate.as_ref().unwrap();
    assert!(!certificate.discarded.is_empty());
    assert!(
        certificate
            .discarded
            .keys()
            .all(|object| certificate.objects[object].is_empty())
    );
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
    let mut damaged = facts.clone();
    damaged.closure_discards.clear();
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.closure_discards[0].created_start = damaged.closure_discards[0].created_end;
    assert!(domain::validate(&damaged).is_err());

    // Referring to an existing binding is not its final ownership use.
    let source = factory(false, "let view action=make(shared);action;");
    let result = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&result, CompilationOutcome::NotImplemented { reason } if reason.detail.contains("conditional closure exclusivity")),
        "{result:?}"
    );
}

#[test]
fn storing_a_factory_result_before_discard_does_not_prove_no_future_call() {
    let source = r#"
type Cell={mut value:int}
type Reader=fn(mut Cell,int)->int &mut &closure
type Holder={mut callback:Reader}
fn idle(mut target:Cell,padding:int)->int &mut{target.value+=1;padding}
fn save(mut holder:Holder,source:Cell)->Reader &mut &capture{
    let view action=\mut target:Cell,padding:int->{let observed=source.value;target.value+=1;observed};
    holder.callback=action;
    action
}
fn example(){let mut shared=Cell.{value:0};shared.value+=0;let mut holder=Holder.{callback:idle};save(mut holder,shared);}
"#;
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::NotImplemented { reason } if reason.detail.contains("conditional closure exclusivity")),
        "{result:?}"
    );
}

#[test]
fn a_safe_local_call_cannot_authorize_later_public_or_stored_uses() {
    let prefix = "type Cell={mut value:int}\ntype Reader=fn(mut Cell,int)->int &mut &closure\n";
    for source in [
        format!(
            "{prefix}pub fn leaking(source:Cell)->Reader &capture{{let mut other=Cell.{{value:0}};let view action=\\mut target:Cell,padding:int->{{let observed=source.value;target.value+=1;observed}};let result=action(mut other,0);action}}"
        ),
        format!(
            "{prefix}pub fn leaking(source:Cell)->(Reader,int) &capture{{let mut other=Cell.{{value:0}};let view action=\\mut target:Cell,padding:int->{{let observed=source.value;target.value+=1;observed}};let result=action(mut other,0);(action,1)}}"
        ),
        format!(
            "{prefix}fn publish(mut holder:{{mut callback:Reader}},source:Cell) &mut &capture{{let mut other=Cell.{{value:0}};let view action=\\mut target:Cell,padding:int->{{let observed=source.value;target.value+=1;observed}};let result=action(mut other,0);holder.callback=action}}"
        ),
    ] {
        let result = Session::new(source.into_bytes()).check();
        assert!(
            matches!(&result,CompilationOutcome::NotImplemented{reason}if reason.detail.contains("conditional closure exclusivity")),
            "{result:?}"
        );
    }
}

#[test]
fn final_coverage_is_recomputed_and_core_keeps_conditional_probe_evidence() {
    use ril_compiler::sema::{closure_exclusivity as domain, copy_contract::CopyInvocationStatus};
    let source = factory(
        false,
        "let view first=make(shared);let view second=make(shared);let a=first(mut other,0);let b=second(mut other,1)",
    );
    let verified = Session::new(source.into_bytes()).verify().unwrap();
    let facts = verified.facts();
    domain::validate(facts).unwrap();
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
    let mut damaged = facts.clone();
    damaged.closure_exclusivity_certificate = None;
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    let call = *damaged
        .closure_exclusivity_certificate
        .as_ref()
        .unwrap()
        .objects
        .values()
        .next()
        .unwrap()
        .first()
        .unwrap();
    damaged.closure_invocations[call.0 as usize].status = CopyInvocationStatus::Unsupported;
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    let check = damaged
        .closure_exclusivity_checks
        .iter_mut()
        .find(|check| check.probe && !check.requirements.is_empty())
        .unwrap();
    check.requirements.clear();
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    let template = damaged
        .closure_exclusivity_certificate
        .as_mut()
        .unwrap()
        .templates
        .values_mut()
        .next()
        .unwrap();
    assert!(template.len() >= 2);
    template.pop_last();
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    let check = damaged
        .closure_exclusivity_checks
        .iter_mut()
        .find(|check| !check.probe)
        .unwrap();
    check.nodes.clear();
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.closure_exclusivity_checks.clear();
    damaged.closure_exclusivity_certificate = None;
    assert!(
        domain::validate(&damaged).is_err(),
        "missing probes cannot erase their obligations"
    );
    let mut damaged = facts.clone();
    let call = damaged
        .closure_invocations
        .iter_mut()
        .find(|call| !call.probe)
        .unwrap();
    call.parent_closure = Some(call.id);
    assert!(
        domain::validate(&damaged).is_err(),
        "cyclic dynamic ancestry cannot certify coverage"
    );
    let mut damaged = facts.clone();
    let access = damaged
        .closure_exclusivity_checks
        .iter_mut()
        .flat_map(|check| &mut check.accesses)
        .find(|access| !access.origins.nodes.is_empty())
        .unwrap();
    access.origin_owners.clear();
    assert!(
        domain::validate(&damaged).is_err(),
        "historical origin owners must cover the exact observed footprint"
    );
}
