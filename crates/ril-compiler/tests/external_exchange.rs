use ril_compiler::{CheckOptions, CompilationOutcome, Session, session::ProjectSource};

fn check(declaration: &str, body: &str) -> CompilationOutcome {
    Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource {
                path: "virtual/main.ril".into(),
                bytes: format!("use external/api\n{body}").into_bytes(),
            },
            ProjectSource {
                path: "virtual/external/api.d.ril".into(),
                bytes: declaration.as_bytes().to_vec(),
            },
        ],
        CheckOptions::default(),
    )
    .unwrap()
    .check()
}
fn accepts(declaration: &str, body: &str) {
    let outcome = check(declaration, body);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{body}: {outcome:?}"
    );
}
fn rejects(declaration: &str, body: &str) {
    let outcome = check(declaration, body);
    assert!(
        !matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{body}: {outcome:?}"
    );
}

#[test]
fn callback_results_need_actual_immutable_publication() {
    let declaration = "pub fn consume(callback:fn()->[]int)";
    rejects(
        declaration,
        "fn entry(){let mut old=[1];old[0]=2;Api::consume(\\ -> old)}",
    );
    accepts(declaration, "fn entry(){Api::consume(\\ -> [1])}");
    accepts(
        declaration,
        "fn entry(){let mut old=[1];old[0]=2;Api::consume(\\ -> clone_immut(old))}",
    );
    accepts(
        declaration,
        "fn entry(){let old=[1];Api::consume(\\ -> old)}",
    );
    rejects(
        "pub fn consume(value:[]int)",
        "fn entry(){let mut old=[1];old[0]=2;Api::consume(old)}",
    );
    accepts(
        "pub fn consume(value:[]int)",
        "fn entry(){Api::consume([1])}",
    );
}

#[test]
fn callbacks_preserve_effects_and_environment_modes() {
    let declaration = "pub fn call(callback:fn()->int)";
    rejects(
        declaration,
        "effect Read{get()->int}\nfn entry(){Api::call(\\ -> Read::get())}",
    );
    accepts(declaration, "fn entry(){Api::call(\\ -> 1)}");
    rejects(
        declaration,
        "fn entry(){var count=0;let mut action=\\ -> {count+=1;count};Api::call(action)}",
    );
    accepts(
        "pub fn call(mut callback:fn()->int)",
        "fn entry(){var count=0;let mut action=\\ -> {count+=1;count};Api::call(mut action)}",
    );
}

#[test]
fn foreign_results_and_callback_results_keep_inspection_duties() {
    let declaration = "pub fn outcome()->Result<int,str>";
    rejects(declaration, "fn entry(){let ignored=Api::outcome()}");
    accepts(
        declaration,
        "fn entry(){let result=Api::outcome();assert(result is Ok(_))}",
    );
    rejects(
        "pub fn consume(callback:fn()->Result<int,str>)",
        "fn entry(){Api::consume(\\ -> Ok(1))}",
    );
    rejects(
        "pub fn consume(callback:fn()->())",
        "fn entry(){let pending:Result<int,str>=Ok(1);Api::consume(\\ -> {assert(pending is Ok(_))})}",
    );
    accepts(
        "pub fn consume(callback:fn()->())",
        "fn entry(){Api::consume(\\ -> {let result:Result<int,str>=Ok(1);assert(result is Ok(_))})}",
    );
    accepts(
        "pub fn consume(callback:fn(Result<int,str>)->())",
        "fn entry(){Api::consume(\\ result -> {assert(result is Ok(_))})}",
    );
    rejects(
        "pub fn consume(callback:fn(Result<int,str>)->())",
        "fn entry(){Api::consume(\\ result -> ())}",
    );
    rejects(
        "pub fn outcome()->{status:Result<int,str>}",
        "fn entry(){let output=Api::outcome()}",
    );
    accepts(
        "pub fn outcome()->{status:Result<int,str>}",
        "fn entry(){let output=Api::outcome();assert(output.status is Ok(_))}",
    );
}

#[test]
fn callback_immutable_inputs_do_not_establish_freshness_or_mutation() {
    accepts(
        "pub fn map(callback:fn([]int)->[]int)",
        "fn entry(){Api::map(\\ values -> values)}",
    );
    rejects(
        "pub fn map(callback:fn([]int)->())",
        "fn entry(){Api::map(\\ values -> {let mut stolen=values;stolen[0]=9})}",
    );
    accepts(
        "pub fn map(callback:fn([]int)->[]int)",
        "fn entry(){Api::map(\\ values -> {let mut copy=clone(values);copy[0]=9;clone_immut(copy)})}",
    );
}

#[test]
fn callback_input_modes_and_nested_callables_are_not_erased() {
    for declaration in [
        "pub fn consume(callback:fn(mut []int)->())",
        "pub type Action=fn(mut []int)->()\npub fn consume(callback:Action)",
        "pub fn consume(callback:fn(fn()->())->())",
        "pub fn consume(callback:fn()->fn()->())",
    ] {
        let outcome = check(declaration, "fn entry(){}");
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0908")),
            "{declaration}: {outcome:?}"
        );
    }
}

#[test]
fn conditional_nested_and_opaque_result_duties_are_not_invented_away() {
    for declaration in [
        "pub fn outcome()->Result<Result<int,str>,str>",
        "pub fn outcome()->[]Result<int,str>",
        "pub opaque type Hidden=Result<int,str>\npub fn outcome()->Hidden",
        "pub let OUTCOME:Result<int,str>\npub fn outcome()->int",
    ] {
        rejects(declaration, "fn entry(){let ignored=Api::outcome()}");
    }
    rejects(
        "pub fn outcome()->{a:Result<int,str>,b:Result<int,str>}",
        "fn entry(){let output=Api::outcome();assert(output.a is Ok(_))}",
    );
    accepts(
        "pub fn outcome()->{a:Result<int,str>,b:Result<int,str>}",
        "fn entry(){let output=Api::outcome();assert(output.a is Ok(_));assert(output.b is Ok(_))}",
    );
}
