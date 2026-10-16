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
fn retained_handlers_preserve_the_creation_selection() {
    let verified = accepted(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->resume 7;\\->Read::get()}\nfn example(){let reader=make_reader();with Read::get()->resume 99;assert(reader()==7&&reader()==7)}",
    );
    assert!(!verified.facts().retained_handlers.is_empty());
}
#[test]
fn retained_handler_answers_are_rechecked_for_the_callable() {
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->{let ignored=resume 7;\\->0};\\->Read::get()}",
        "E0614",
    );
}
#[test]
fn retained_handlers_keep_their_state_capability_obligation() {
    rejects(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->resume 7;\\->Read::get()}\nfn pure(action:fn()->int)->int &{}{action()}\nfn example(){let reader=make_reader();let _=pure(reader)}",
        "E0534",
    );
}
#[test]
fn unused_lexical_handlers_are_not_retained() {
    let verified = accepted(
        "eff Read{get()->int}\nfn make_reader()->fn()->int{with Read::get()->resume 7;\\->0}",
    );
    assert!(verified.facts().retained_handlers.is_empty());
}

#[test]
fn retained_handler_dependencies_follow_lexical_bindings_and_outer_handlers() {
    accepted(
        "eff Read{get()->int}\nfn ask()->int @Read{Read::get()}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{let value=7;with Read::get()->resume value;{let value=99;\\->ask()}}\nfn example(){let reader=make_reader();assert(reader()==7)}",
    );
    let verified = accepted(
        "eff Read{get()->int}\ntype Reader=fn()->int &closure\nfn make_reader()->Reader &capture{with Read::get()->resume 7;{with Read::get()->{let outer=Read::get();resume (outer+1)};\\->Read::get()}}\nfn example(){let reader=make_reader();assert(reader()==8)}",
    );
    assert!(
        verified
            .facts()
            .retained_handlers
            .iter()
            .any(|proof| proof.handlers.len() == 2)
    );
}

#[test]
fn parameterized_handlers_preserve_an_existing_selection() {
    accepted(
        "eff Read{get()->int}\nfn supply(value:int,action:fn()->int)->int{with Read::get()->resume value;action()}\nhalt fn configured()->int{with supply(7);Read::get()+1}\nhalt fn existing()->int{with Read::get()->resume 3;with supply(7);Read::get()}\nfn example(){assert(configured()==8&&existing()==3)}",
    );
}

#[test]
fn handler_application_finiteness_never_assumes_an_unknown_callback_is_finite() {
    rejects(
        "eff Read{get()->int}\nfn supply(value:int,action:fn()->int)->int{with Read::get()->resume value;action()}\nhalt fn diverging()->int{with supply(7);loop{}}",
        "E0820",
    );
    let outcome = Session::new(
        b"eff Read{get()->int}\nfn example()->int{with Read::get()->return 1;Read::get()}".to_vec(),
    )
    .check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}
