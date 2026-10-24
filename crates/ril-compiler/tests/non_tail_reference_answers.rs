use ril_compiler::{CompilationOutcome, Session, sema::model::AnswerTransport};

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
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
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
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
