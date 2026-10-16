use ril_compiler::{
    CompilationOutcome, Session,
    sema::{self, model::AnswerTransport},
};

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    sema::resumption::validate(verified.facts()).unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(
        core.provenance.resumption_steps.len(),
        verified.facts().resumption_steps.len()
    );
    assert_eq!(
        core.provenance.operation_loan_starts.len(),
        verified.facts().operation_loan_starts.len()
    );
    assert_eq!(
        core.provenance.allocation_history.len(),
        verified.facts().allocation_history.len()
    );
    verified
}
fn rejected(source: &str, codes: &[&str]) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|codes.contains(&diagnostic.code.as_str()))),
        "{source}: {outcome:?}"
    );
}

const RETAINED: &str = r#"
eff Read{get()->int}
type Reader=fn()->[]int &closure
fn make_reader()->Reader &capture{
    var reader:Reader=\->[0]
    {
        with Read::get()->{let answer=resume 7;assert(answer[0]>=0);clone(answer)}
        reader=\->[Read::get()]
        [0]
    }
    reader
}
fn example(){let reader=make_reader();let first=reader();let second=reader();assert(first[0]==7&&second[0]==7)}
"#;

#[test]
fn normal_reference_answers_run_the_suffix_against_the_actual_graph() {
    let verified = accepted(include_str!("fixtures/non_tail_reference_answer.ril"));
    assert!(
        verified
            .facts()
            .resumption_steps
            .iter()
            .any(|step| step.transport == AnswerTransport::OrdinaryChecked)
    );
    accepted(
        r#"
eff Read{get()->int}
fn example()->{left:[]int,right:[]int}{
    with Read::get()->{let answer=resume 7;let alias=answer;assert(alias.left[0]==7);alias}
    let shared=[Read::get()]
    .{left:shared,right:shared}
}
"#,
    );
    accepted(
        r#"
eff Read{get()->int}
fn example()->[]int{with Read::get()->{let mut answer=resume 7;answer[0]+=1;answer};[Read::get()]}
"#,
    );
}

#[test]
fn retained_reference_answers_require_each_fresh_invocations_own_steps() {
    let verified = accepted(RETAINED);
    let proofs: Vec<_> = verified
        .facts()
        .retained_handler_answers
        .iter()
        .filter(|proof| proof.transport == AnswerTransport::OrdinaryChecked)
        .collect();
    assert!(proofs.len() >= 2);
    for proof in &proofs {
        assert!(!proof.resumption_steps.is_empty());
    }
    assert!(
        proofs
            .windows(2)
            .any(|pair| pair[0].activation != pair[1].activation)
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        core.provenance
            .retained_handler_answers
            .iter()
            .any(|proof| proof.transport == ril_ir::provenance::AnswerTransport::OrdinaryChecked)
    );
}

#[test]
fn helper_recency_moves_transport_actual_answers_without_rewriting_snapshots() {
    let verified = accepted(
        r#"
eff Read{get()->int}
fn data(number:int)->[]int{[number]}
fn answer()->[]int{with Read::get()->{let answer=resume 7;let other=data(99);assert(other[0]==99&&answer[0]==7);clone(answer)};data(Read::get())}
fn example(){for [0,1] as index{let values=answer();assert(values[0]==7)}}
"#,
    );
    assert!(
        verified
            .facts()
            .resumption_steps
            .iter()
            .any(|step| step.completion_epoch > step.continuation_epoch)
    );
}

const OPERATION: &str = r#"
type Cell={mut count:int}
eff Edit{apply(mut Cell)->() &mut}
fn edited(mut cell:Cell)->[]int &mut{
    with Edit::apply(mut target)->{target.count+=1;let saved=target.count;let answer=resume();assert(answer[0]==saved+1);clone(answer)}
    Edit::apply(mut cell)
    cell.count+=1
    [cell.count]
}
fn example(){let mut cell=Cell.{count:0};let values=edited(mut cell);cell.count+=10;assert(values[0]==2&&cell.count==12)}
"#;

#[test]
fn operation_end_preserves_the_outer_loan_and_independent_retained_authority() {
    let verified = accepted(OPERATION);
    assert!(
        verified
            .facts()
            .resumption_steps
            .iter()
            .any(|step| !step.ended_operation_loans.is_empty())
    );
    accepted(
        r#"
type Cell={mut count:int}
eff Edit{apply(^mut Cell)->() &^mut}
fn edited(^mut cell:Cell)->[]int &mut{
    with Edit::apply(^mut target)->{target.count+=1;let answer=resume();target.count+=1;clone(answer)}
    Edit::apply(^mut cell)
    [cell.count]
}
fn example(){let mut cell=Cell.{count:0};let values=edited(^mut cell);assert(values[0]==1&&cell.count==2)}
"#,
    );
    for access in ["target.count+=1", "alias.count+=1"] {
        rejected(
            &format!(
                r#"
type Cell={{mut count:int}}
eff Edit{{apply(mut Cell)->() &mut}}
fn edited(mut cell:Cell)->[]int &mut{{with Edit::apply(mut target)->{{target.count+=1;let view alias=target;let answer=resume();{access};clone(answer)}};Edit::apply(mut cell);[cell.count]}}
fn example(){{let mut cell=Cell.{{count:0}};let values=edited(mut cell)}}
"#
            ),
            &["E0540"],
        );
    }
}

#[test]
fn readonly_reception_and_outer_capture_exclusivity_cannot_be_laundered() {
    rejected(
        r#"
eff Read{get()->int}
fn example()->[]int{let immutable=[7];with Read::get()->{let mut answer=resume 7;answer[0]=9;answer};Read::get();immutable}
"#,
        &["E0520", "E0528"],
    );
    rejected(
        r#"
eff Read{get()->int}
fn answer()->[]int{with Read::get()->{let answer=resume 7;let alias=answer;alias};[Read::get()]}
fn example(){let mut stolen=answer();stolen[0]=9}
"#,
        &["E0528"],
    );
    let prefix = r#"
type Cell={mut count:int}
type Action=fn()->() &mut &closure
eff Tick{tick()->()}
fn make(^mut cell:Cell)->Action &^mut &capture{\->{cell.count+=1}}
fn apply(mut target:Cell,mut action:Action)->[]int &mut{with Tick::tick()->{let answer=resume();action();clone(answer)};Tick::tick();target.count+=1;[target.count]}
"#;
    accepted(&format!(
        "{prefix}\nfn example(){{let mut target=Cell.{{count:0}};let mut other=Cell.{{count:0}};let mut action=make(^mut other);let values=apply(mut target,mut action)}}"
    ));
    rejected(
        &format!(
            "{prefix}\nfn example(){{let mut target=Cell.{{count:0}};let mut action=make(^mut target);let values=apply(mut target,mut action)}}"
        ),
        &["E0523"],
    );
    for aliases in [false, true] {
        let source = format!(
            r#"
type Cell={{mut count:int}}
eff Tick{{tick()->()}}
fn example(){{
    let mut ambient=Cell.{{count:0}}
    let mut other=Cell.{{count:0}}
    let mut apply=\mut target:Cell->{{with Tick::tick()->{{let answer=resume();ambient.count+=1;clone(answer)}};Tick::tick();target.count+=1;[target.count]}}
    let values=apply(mut {})
}}
"#,
            if aliases { "ambient" } else { "other" }
        );
        if aliases {
            rejected(&source, &["E0523"]);
        } else {
            accepted(&source);
        }
    }
}

#[test]
fn ordinary_transfer_does_not_expand_result_or_resource_proofs() {
    rejected(
        r#"
eff Read{get()->int}
fn answer()->[]int{with Read::get()->{let answer=resume 7;let pending:Result<int,str>=Ok(1);clone(answer)};[Read::get()]}
"#,
        &["E0720"],
    );
    for source in [
        "eff Read{get()->int}\nfn answer()->Result<[]int,str>{with Read::get()->{let answer=resume 7;assert(answer is Ok(_));answer};Ok([Read::get()])}",
        "eff Read{get()->int}\nfn answer()->{value:Result<[]int,str>}{with Read::get()->{let answer=resume 7;assert(answer.value is Ok(_));answer};.{value:Ok([Read::get()])}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.detail.contains("resumption")||reason.detail.contains("answer")),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn removing_graph_loan_or_invocation_evidence_fails_independent_validation() {
    let verified = accepted(OPERATION);
    let facts = verified.facts();
    let mut damaged = facts.clone();
    damaged.resumption_steps[0].continuation_value.nodes.clear();
    assert!(sema::resumption::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.resumption_steps.clear();
    assert!(
        sema::resumption::validate(&damaged).is_err(),
        "erasing every step cannot erase the actual non-tail resume expression events"
    );
    let mut damaged = facts.clone();
    damaged.operation_loan_starts.clear();
    damaged.operation_loan_ends.clear();
    for step in &mut damaged.resumption_steps {
        step.ended_operation_loans.clear();
    }
    assert!(
        sema::resumption::validate(&damaged).is_err(),
        "erasing every start and end cannot erase the actual operation's mut reception"
    );
    let mut damaged = facts.clone();
    damaged.resumption_steps[0].arm_value.value.permission = sema::facts::Permission::Write;
    if damaged.resumption_steps[0].arm_value.value.permission
        == facts.resumption_steps[0].arm_value.value.permission
    {
        damaged.resumption_steps[0].arm_value.value.permission = sema::facts::Permission::Read;
    }
    assert!(sema::resumption::validate(&damaged).is_err());
    let retained = accepted(RETAINED);
    let mut damaged = retained.facts().clone();
    let indices: Vec<_> = damaged
        .retained_handler_answers
        .iter()
        .enumerate()
        .filter_map(|(index, proof)| {
            (proof.transport == AnswerTransport::OrdinaryChecked).then_some(index)
        })
        .collect();
    let first = indices[0];
    let other = *indices
        .iter()
        .find(|index| {
            damaged.retained_handler_answers[**index].activation
                != damaged.retained_handler_answers[first].activation
        })
        .unwrap();
    damaged.retained_handler_answers[first].resumption_steps = damaged.retained_handler_answers
        [other]
        .resumption_steps
        .clone();
    assert!(
        sema::resumption::validate(&damaged).is_err(),
        "another call at the same span and answer type is not this call's proof"
    );
    let mut damaged = retained.facts().clone();
    damaged.retained_handler_answers[first]
        .resumption_steps
        .clear();
    assert!(sema::resumption::validate(&damaged).is_err());
}

#[test]
fn ended_continuation_locals_need_a_current_scope_exit_without_retiring_captures() {
    use sema::facts::{Permission, Publication};
    let verified = accepted(include_str!("fixtures/non_tail_private_local_answer.ril"));
    accepted(
        r#"
type Cell={mut value:int}
type Graph={mut count:int,child:Cell}
eff Read{get()->int}
fn answer(child:Immut<Cell>)->Graph{with Read::get()->{let answer=resume 7;assert(answer.count==8&&answer.child.value==3);clone(answer)};let mut graph=Graph.{count:Read::get(),child:child};graph.count+=1;graph}
fn example(){let child=Cell.{value:3};let result=answer(child);assert(result.child.value==3)}
"#,
    );
    rejected(
        r#"
type Cell={mut value:int}
type Graph={mut count:int,child:Cell}
eff Read{get()->int}
fn answer(child:Immut<Cell>)->Graph{with Read::get()->{let mut answer=resume 7;answer.child.value+=1;answer};let mut graph=Graph.{count:Read::get(),child:child};graph.count+=1;graph}
fn example(){let child=Cell.{value:3};let result=answer(child)}
"#,
        &["E0522", "E0520"],
    );
    let index = verified
        .facts()
        .resumption_steps
        .iter()
        .position(|step| step.scope_exit.is_some())
        .unwrap();
    let exit = verified.facts().resumption_steps[index]
        .scope_exit
        .as_ref()
        .unwrap();
    assert!(!exit.retired_bindings.is_empty());
    assert_eq!(exit.answer_before.value.permission, Permission::Write);
    assert!(!exit.answer_before.value.construction);
    assert_eq!(exit.answer_before.value.publication, Publication::Live);
    assert_eq!(exit.answer_received.value.permission, Permission::Write);
    assert!(exit.answer_received.value.construction);
    assert_eq!(
        exit.answer_received.value.publication,
        Publication::Unpublished
    );
    assert_eq!(
        exit.answer_before.value.origins,
        exit.answer_received.value.origins
    );
    assert_eq!(
        exit.answer_before.value.participants,
        exit.answer_received.value.participants
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        core.provenance
            .resumption_steps
            .iter()
            .any(|step| step.scope_exit.is_some())
    );
    let mut damaged = verified.facts().clone();
    damaged.resumption_steps[index].scope_exit = None;
    assert!(
        sema::resumption::validate(&damaged).is_err(),
        "the new private construction must retain its scope-exit proof"
    );
    let mut damaged = verified.facts().clone();
    damaged.resumption_steps[index]
        .scope_exit
        .as_mut()
        .unwrap()
        .protected_bindings
        .clear();
    assert!(
        sema::resumption::validate(&damaged).is_err(),
        "editing the protection set cannot replace independent root closure"
    );
    let mut damaged = verified.facts().clone();
    damaged.resumption_steps[index]
        .scope_exit
        .as_mut()
        .unwrap()
        .alive_bindings
        .clear();
    assert!(sema::resumption::validate(&damaged).is_err());
    let mut damaged = verified.facts().clone();
    damaged.resumption_steps[index]
        .scope_exit
        .as_mut()
        .unwrap()
        .epoch += 1;
    assert!(sema::resumption::validate(&damaged).is_err());
    let mut damaged = verified.facts().clone();
    damaged.resumption_steps[index]
        .scope_exit
        .as_mut()
        .unwrap()
        .answer_received
        .value
        .permission = Permission::Read;
    assert!(sema::resumption::validate(&damaged).is_err());
    rejected(
        r#"
eff Read{get()->int}
fn answer()->[]int{let mut ambient=[1];with Read::get()->{let answer=resume 7;clone(answer)};let mut alias=^mut ambient;alias[0]+=1;Read::get();alias}
"#,
        &["E0535"],
    );
    rejected(
        r#"
eff Read{get()->int}
fn answer()->[]int{with Read::get()->{let mut answer=resume 7;answer[0]+=1;answer};let mut values=[Read::get()];values[0]+=1;var alias=values;alias=alias;alias}
"#,
        &["E0520", "E0528"],
    );
    let captured = r#"
eff Read{get()->int}
type Action=fn()->() &mut &closure
type Holder={mut action:Action}
fn idle(){}
fn make(^mut values:[]int)->Action &capture &^mut{\->{values[0]+=1}}
fn example(){
    let mut holder=Holder.{action:idle}
    let result={with Read::get()->{let answer=resume 7;clone(answer)};let mut values=[Read::get()];holder.action=make(^mut values);values[0]+=1;values}
    holder.action()
}
"#;
    rejected(captured, &["E0535"]);
    accepted(&captured.replace("let answer=resume 7", "var answer=resume 7;answer=answer"));
}
