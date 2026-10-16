use ril_compiler::{CompilationOutcome, Session};

const BUDGET_CLEANUP: &str = r#"
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
fn read() -> int @Read { Read::get() }
halt fn clean() {
    let kept = [7]
    for 0..1200 as index { let unused = [index, index + 1] }
    with Read::get() -> resume kept[0]
    with Div::exhausted() -> panic("cleanup local budget was corrupted")
    assert(Div::budget(3, read) == 7)
}
"#;

#[test]
fn cleanup_reuses_actual_budget_and_handler_proofs_independently_of_definition_order() {
    let users = "fn returned()->[]int{let scoped guard=Guard.{on_close:clean};[42]}\nfn one()->int{let scoped guard=Guard.{on_close:clean};42}\nfn spin()->int{let scoped guard=Guard.{on_close:clean};loop{}}\nfn exact()->?int{with Div::exhausted()->None;Some(Div::budget(1,one))}\nfn exhausted()->?int{with Div::exhausted()->None;Some(Div::budget(2,spin))}";
    for source in [
        format!("{BUDGET_CLEANUP}\n{users}"),
        format!("{users}\n{BUDGET_CLEANUP}"),
    ] {
        let verified = Session::new(source.into_bytes()).verify().unwrap();
        assert!(verified.facts().budget_proofs.len() >= 3);
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn cleanup_aliases_use_the_actual_lexical_target_and_revalidate_callback_replacement() {
    let accepted = "type Guard={mut on_close:fn()->()}\nfn finite(){}\nfn another(){}\nfn entry(){let selected=finite;let scoped mut guard=Guard.{on_close:\\->selected()};guard.on_close=another}";
    Session::new(accepted.as_bytes().to_vec()).verify().unwrap();
    let rejected = accepted.replace("fn another(){}", "fn another(){loop{}}");
    let outcome = Session::new(rejected.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0617")),
        "{outcome:?}"
    );
}

#[test]
fn cleanup_finishes_only_with_actual_finite_selected_handlers() {
    let source = "eff Read{get()->int}\ntype Guard={on_close:fn()->()}\nfn clean() @Read{let value=Read::get()}\nfn entry(){with Read::get()->resume 7;let scoped guard=Guard.{on_close:clean}}";
    Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let outcome = Session::new(source.replace("resume 7", "loop{}").into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0617")),
        "{outcome:?}"
    );
}

#[test]
fn cleanup_query_never_substitutes_a_callers_same_named_alias_for_a_callee_capture() {
    let source = "type Guard={on_close:fn()->()}\nfn finite(){}\nfn infinite(){loop{}}\nfn entry(){let selected=infinite;{let selected=finite;let scoped guard=Guard.{on_close:\\->hidden()}} where fn hidden(){selected()}}";
    assert!(Session::new(source.as_bytes().to_vec()).verify().is_err());
}

#[test]
fn handler_parameters_cannot_borrow_an_outer_same_named_finite_callable_proof() {
    let source = "eff Run{run(callback:fn()->())->()}\ntype Guard={on_close:fn()->()}\nfn finite(){}\nfn infinite(){loop{}}\nfn clean() @Run{Run::run(infinite)}\nfn entry(){let callback=finite;with Run::run(callback)->{callback();resume ()};let scoped guard=Guard.{on_close:clean}}";
    assert!(
        Session::new(source.as_bytes().to_vec()).verify().is_err(),
        "the handler's actual callback can diverge despite a same-named finite outer binding"
    );
}

#[test]
fn protected_cleanup_and_arm_cleanup_use_their_own_handler_extents() {
    let declarations =
        "eff Close{run()->()}\ntype Guard={on_close:fn()->()}\nfn close() @Close{Close::run()}\n";
    for body in [
        "fn entry(){with Close::run()->resume ();let scoped guard=Guard.{on_close:close}}",
        "fn entry(){with Close::run()->();let scoped guard=Guard.{on_close:close};Close::run()}",
        "eff Stop{now()->int}\nfn entry()->int{with Close::run()->resume ();with Stop::now()->7;let scoped guard=Guard.{on_close:close};Stop::now()}",
        "fn entry(){with Close::run()->resume ();{with Close::run()->{let scoped guard=Guard.{on_close:close};()};Close::run()}}",
    ] {
        let source = format!("{declarations}{body}");
        let verified = Session::new(source.into_bytes()).verify().unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
    // The same handler is masked inside its own arm, including that arm's
    // scoped cleanup. Referencing an existing callable does not retain it.
    let source = format!(
        "{declarations}fn entry(){{with Close::run()->{{let scoped guard=Guard.{{on_close:close}};()}};Close::run()}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0616")),
        "{outcome:?}"
    );
}
