use ril_compiler::{CompilationOutcome, Session};
use ril_ir::provenance::AnswerTransport;

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        core.provenance
            .retained_handler_answers
            .iter()
            .any(|proof| proof.parametric && proof.transport == AnswerTransport::Identity)
    );
    verified
}

const PRELUDE: &str = "eff Read{get()->int}\n";

#[test]
fn exact_identity_suffix_transports_fresh_and_immutable_ordinary_graphs() {
    for (answer, body, check) in [
        ("[]int", "[Read::get()]", "assert(value[0]==7)"),
        (
            "[]int",
            "{let values=[Read::get()];values}",
            "assert(value[0]==7)",
        ),
        (
            "{left:[]int,right:[]int}",
            "{let shared=[Read::get()];.{left:shared,right:shared}}",
            "assert(value.left[0]==7&&value.right[0]==7)",
        ),
    ] {
        accepted(&format!(
            "{PRELUDE}type Reader=fn()->{answer} &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->{body}}}\nfn example(){{let reader=make_reader();let value=reader();{check}}}"
        ));
    }
}

#[test]
fn forwarded_result_producers_require_the_callers_own_inspection() {
    let source = format!(
        "{PRELUDE}type Reader=fn()->Result<[]int,str> &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->Ok([Read::get()])}}\nfn example(){{let reader=make_reader();let value=reader();assert(value is Ok(_))}}"
    );
    accepted(&source);
    let outcome = Session::new(source.replace("assert(value is Ok(_))", "()").into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
}

#[test]
fn ordinary_let_reception_does_not_restore_write_authority() {
    let source = format!(
        "{PRELUDE}type Reader=fn()->[]int &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->[Read::get()]}}\nfn example(){{let reader=make_reader();let mut values=reader();values[0]=9}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|matches!(diagnostic.code.as_str(),"E0520"|"E0528"))),
        "{outcome:?}"
    );
}

#[test]
fn a_live_answer_requires_ordinary_immutable_reception() {
    let source = format!(
        "{PRELUDE}fn example(){{let mut values=[1];values[0]=2;var reader={{with Read::get()->{{let answer=resume 7;answer}};\\->{{Read::get();values}}}};reader=reader;let answer=reader();assert(answer[0]==2)}}"
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0535")),
        "{outcome:?}"
    );
    accepted(&source.replace("Read::get();values", "Read::get();clone_immut(values)"));
}

#[test]
fn result_identity_does_not_discharge_an_independent_copy() {
    let source = format!(
        "{PRELUDE}type Reader=fn()->Result<[]int,str> &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->Ok([Read::get()])}}\nfn example(){{let reader=make_reader();let original=reader();let copied=clone(original);assert(copied is Ok(_))}}"
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
    accepted(&source.replace(
        "assert(copied is Ok(_))",
        "assert(copied is Ok(_));assert(original is Ok(_))",
    ));
}

#[test]
fn identity_keeps_the_original_continuation_graph_and_producer_ids() {
    let source = format!(
        "{PRELUDE}type Reader=fn()->Result<[]int,str> &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->Ok([Read::get()])}}\nfn example(){{let reader=make_reader();let value=reader();assert(value is Ok(_))}}"
    );
    let verified = accepted(&source);
    let resume = source.find("resume 7").unwrap() as u32;
    let returned = (source.find(";answer}").unwrap() + 1) as u32;
    let inputs: Vec<_> = verified
        .facts()
        .expressions
        .iter()
        .filter(|fact| fact.span.start == resume && !fact.value.results.is_empty())
        .collect();
    assert!(!inputs.is_empty());
    for input in inputs {
        assert!(
            verified
                .facts()
                .expressions
                .iter()
                .any(|output| output.span.start == returned
                    && input.value.origins == output.value.origins
                    && input.value.results == output.value.results
                    && input.value.outer_results == output.value.outer_results
                    && input.value.pending_copies == output.value.pending_copies
                    && (input.value.participants.is_empty()
                        || input.value.participants == output.value.participants)),
            "the identity binder must transport the existing graph and duties"
        );
    }
}

#[test]
fn identity_does_not_publish_scoped_or_resource_answers() {
    let scoped = format!(
        "{PRELUDE}type Guard={{on_close:fn()->()}}\ntype Reader=fn()->Guard &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->{{let scoped guard=Guard.{{on_close:\\->()}};Read::get();guard}}}}"
    );
    let outcome = Session::new(scoped.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0604")),
        "{outcome:?}"
    );
    let resource = format!(
        "use ril/file\nuse ril/path\nuse ril/io\n{PRELUDE}type Reader=fn()->Result<File::Handle,Io::IoError> @Fiber &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\->{{Read::get();File::open_path(Path::from_string(\"example\"),File::OpenMode::Read)}}}}"
    );
    let outcome = Session::new(resource.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.to_string().contains("answer")),
        "{outcome:?}"
    );
}

#[test]
fn operation_loan_end_and_independent_caller_authority_survive_identity_transport() {
    let declarations = "type Cell={mut count:int}\neff Edit{apply(mut Cell)->() &mut}\ntype Reader=fn(mut Cell)->[]int &closure &mut\n";
    accepted(&format!(
        "{declarations}fn make_reader()->Reader &capture{{with Edit::apply(mut item)->{{item.count+=1;let answer=resume();answer}};\\mut cell:Cell->{{Edit::apply(mut cell);[cell.count]}}}}\nfn example(){{let reader=make_reader();let mut cell=Cell.{{count:0}};let answer=reader(mut cell);cell.count+=10;assert(answer[0]==1&&cell.count==11)}}"
    ));
    let source = format!(
        "{declarations}type Guard={{mut on_close:fn()->()}}\nfn make_reader()->Reader &capture{{with Edit::apply(mut item)->{{let scoped mut guard=Guard.{{on_close:\\->{{item.count+=1}}}};let answer=resume();answer}};\\mut cell:Cell->{{Edit::apply(mut cell);[cell.count]}}}}\nfn example(){{let reader=make_reader();let mut cell=Cell.{{count:0}};let answer=reader(mut cell);assert(answer[0]==1)}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0540")),
        "{outcome:?}"
    );
}

#[test]
fn identity_does_not_discharge_a_projected_symbolic_copy_dependency() {
    let source = format!(
        "{PRELUDE}fn unresolved<T>(value:(T,int))->int{{with Read::get()->{{let answer=resume 7;answer}};Read::get();clone(value).1}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.to_string().contains("copy")),
        "{outcome:?}"
    );
}

#[test]
fn both_result_tags_and_caller_owned_producers_keep_the_same_duty() {
    accepted(&format!(
        "{PRELUDE}type Reader=fn(bool)->Result<[]int,str> &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\success:bool->{{let number=Read::get();if success{{Ok([number])}}else{{Err(\"no\")}}}}}}\nfn example(){{let reader=make_reader();assert(reader(true) is Ok(_));assert(reader(false) is Err(\"no\"))}}"
    ));
    accepted(&format!(
        "{PRELUDE}type Reader=fn(Immut<Result<[]int,str>>)->Result<[]int,str> &closure\nfn make_reader()->Reader &capture{{with Read::get()->{{let answer=resume 7;answer}};\\value:Immut<Result<[]int,str>>->{{Read::get();value}}}}\nfn example(){{let reader=make_reader();let original:Result<[]int,str>=Ok([1]);let returned=reader(original);assert(returned is Ok(_))}}"
    ));
}
