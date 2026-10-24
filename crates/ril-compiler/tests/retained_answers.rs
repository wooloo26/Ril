use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"))
}
fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn identity_suffix_is_parametric_but_its_invocation_still_has_a_copy_answer() {
    let verified = accepted(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;answer};\\->Read::get()}\nfn example(){let reader=make_reader();assert(reader()==7)}",
    );
    assert!(
        verified
            .facts()
            .retained_handler_answers
            .iter()
            .any(|proof| proof.parametric)
    );
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn fixed_suffix_and_abort_require_the_original_copy_answer() {
    for arm in ["{let answer=resume 7;answer+1}", "7"] {
        let verified = accepted(&format!(
            "eff Read{{get()->int}}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{{var reader:Reader=\\->0;{{with Read::get()->{arm};reader=\\->Read::get()+1;0}};reader}}\nfn example(){{let reader=make_reader();let value=reader()}}"
        ));
        assert!(
            verified
                .facts()
                .retained_handler_answers
                .iter()
                .any(|proof| !proof.parametric)
        );
    }
}

#[test]
fn mismatched_fixed_answers_remain_a_retained_boundary_error() {
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->str &closure\nfn make_reader()->Reader &capture{var reader:Reader=\\->\"\";{with Read::get()->7;reader=\\->{Read::get();\"unreached\"};0};reader}",
        "E0614",
    );
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;answer+1};\\->Read::get()}",
        "E0614",
    );
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;\\->0};\\->Read::get()}",
        "E0614",
    );
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->7;\\->Read::get()}",
        "E0614",
    );
}

#[test]
fn a_general_suffix_still_needs_a_reference_transfer_proof() {
    let outcome = Session::new(b"eff Read{get()->int}\ntype Reader=fn()->[]int &closure\nfn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;let alias=answer;alias};\\->[Read::get()]}".to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn retained_prefixes_keep_their_result_inspection_duties() {
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->{let ignored=Ok(1);let answer=resume 7;answer};\\->Read::get()}",
        "E0720",
    );
}

#[test]
fn every_retained_arm_in_one_definition_must_fit_the_fresh_budget_callback_answer() {
    let prefix = "eff Read<T>{get()->T}\nfn read<T>(witness:T)->T @Read<T>{Read<T>::get()}\n";
    rejects(
        &format!(
            "{prefix}fn integer(limit:int)->?int{{with {{Read<int>::get()->resume 7,Div::exhausted()->None}};Some(Div::budget(limit,\\->read(0)))}}"
        ),
        "E0614",
    );
    accepted(&format!(
        "{prefix}fn integer(limit:int)->?int{{with {{Read<int>::get()->resume 7,Div::exhausted()->None}};Div::budget(limit,\\->Some(read(0)))}}"
    ));
    accepted(&format!(
        "{prefix}fn integer(limit:int)->?int{{with Read<int>::get()->resume 7;with Div::exhausted()->None;Some(Div::budget(limit,\\->read(0)))}}"
    ));
    accepted(&format!(
        "{prefix}fn integer(limit:int)->?int{{with {{Read<int>::get()->resume 7,Div::exhausted()->None}};Div::budget(limit,\\->Some(read(0)))}}\nfn example(){{assert(integer(0)==None);assert(integer(100)==Some(7))}}"
    ));
}
