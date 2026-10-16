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
fn generic_effect_instances_have_distinct_operation_identities() {
    let verified = accepted(
        "eff State<T>{get()->T}\nfn example(){with {State<int>::get()->resume 7,State<str>::get()->resume \"seven\"};assert(State<int>::get()==7&&State<str>::get()==\"seven\")}",
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let operations: Vec<_> = core
        .operations
        .iter()
        .filter(|operation| operation.name.contains("State<"))
        .collect();
    assert_eq!(operations.len(), 2);
    assert_ne!(operations[0].identity, operations[1].identity);
}

#[test]
fn normalized_static_arguments_select_the_same_effect_instance() {
    rejects(
        "type Number=int\neff State<T>{get()->T}\nfn example(){with {State<int>::get()->resume 7,State<Number>::get()->resume 8};State<int>::get()}",
        "E0622",
    );
    accepted(
        "eff State<T=int>{get()->T}\nfn example()->int{with State<int>::get()->resume 7;State<>::get()}",
    );
}

#[test]
fn instance_operation_parameters_and_resumptions_are_checked() {
    rejects(
        "eff State<T>{get()->T}\nfn example(){with State<int>::get()->resume \"bad\";State<int>::get()}",
        "E0624",
    );
    rejects(
        "eff State<T>{put(T)}\nfn example(){with State<int>::put(value)->resume ();State<int>::put(\"bad\")}",
        "E0301",
    );
    rejects(
        "eff State<T>{get()->T}\nfn example(){with State<int>::get()->resume 7;State<str>::get()}",
        "E0612",
    );
}

#[test]
fn generic_effect_rows_and_local_instance_escape_keep_identity() {
    accepted("eff State<T>{get()->T}\nfn read()->int @State<int>{State<int>::get()}");
    accepted(
        "eff State<T>{get()->T}\neff ReadInt{State<int>}\nfn read()->int @ReadInt{State<int>::get()}",
    );
    rejects(
        "fn example()->fn()->int{\\->Local<int>::get() where eff Local<T>{get()->T}}",
        "E0618",
    );
}

#[test]
fn symbolic_effect_arguments_never_merge_same_spelled_enclosing_binders() {
    let source = "eff State<T>{get()->T}\nfn first<T>(){let operation=State<T>::get}\nfn second<T>(){let operation=State<T>::get}";
    let program = accepted(source);
    assert_eq!(program.facts().effect_instances.len(), 2);
    assert_ne!(
        program.facts().effect_instances[0].key,
        program.facts().effect_instances[1].key
    );
    assert!(ril_compiler::lower::lower_core(&program).is_err());
    let source = "fn example<T>(){let operation=Local<int>::get where eff Local<S>{get()->T}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
    let source = "fn example<T>(){let operation=Local<>::get where eff Local<S=T>{get()->S}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
    for source in [
        "fn example<T>(){let operation=Local<Alias>::get where type Alias=T;eff Local<S>{get()->int}}",
        "fn example<T>(){let operation=Local<Wrapper>::get where type Wrapper(T);eff Local<S>{get()->int}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::NotImplemented { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn unused_type_parameters_still_require_valid_static_arguments() {
    rejects(
        "eff Phantom<T>{get()->int}\nfn example()->int{with Phantom<Missing>::get()->resume 1;Phantom<Missing>::get()}",
        "E0204",
    );
    accepted("eff Read{get()->int}\nfn example()->int{with Read::get()->resume 1;Read<>::get()}");
}

#[test]
fn effect_sets_expand_to_member_identities_and_unique_operations() {
    accepted(
        "eff State<T>{get()->T}\neff App<T>{State<T>}\nfn example()->int{with App<int>::get()->resume 7;State<int>::get()}",
    );
    accepted(
        "eff State<T>{get()->T}\neff App<T>{State<T>}\neff ReadInt{App<int>}\nfn example()->int @ReadInt{State<int>::get()}",
    );
    rejects(
        "eff State<T>{get()->T}\neff App<T>{State<T>}\nfn example()->int{with {App<int>::get()->resume 7,State<int>::get()->resume 8};State<int>::get()}",
        "E0622",
    );
    rejects(
        "eff State<T>{get()->T}\neff Both{State<int>,State<str>}\nfn example(){let operation=Both::get}",
        "E0344",
    );
    rejects(
        "eff State<T>{get()->T}\neff App<T>{State<Missing>}\nfn example(){}",
        "E0204",
    );
    accepted(
        "eff Counter<n:int>{get()->int}\neff App<n:int>{Counter<n>}\nfn example()->int{with App<7>::get()->resume 7;Counter<7>::get()}",
    );
    rejects(
        "eff Counter<n:int>{get()->int}\neff App<T>{Counter<\"bad\">}\nfn example(){}",
        "E0323",
    );
}
