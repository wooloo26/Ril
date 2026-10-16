use ril_compiler::{CheckOptions, Session, session::ProjectSource};
fn project(body: &str) -> Session {
    Session::with_project("virtual/main.ril".into(),vec![
        ProjectSource{path:"virtual/main.ril".into(),bytes:format!("use foreign\neff Stop{{now()->int}}\nfn stop(number:int)->int @Stop{{Stop::now();panic(\"abandoned continuation\")}}\n{body}").into_bytes()},
        ProjectSource{path:"virtual/foreign.d.ril".into(),bytes:b"pub fn apply(value:int,callback:fn(int)->int)->int".to_vec()},
    ],CheckOptions::default()).unwrap()
}

#[test]
fn callback_abort_retains_the_zero_invocation_continuation_and_outer_answer() {
    let source = project(
        "fn entry(){let answer={with Stop::now()->7;Foreign::apply(1,stop)+100};assert(answer==7)}",
    );
    let verified = source.verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "entry").unwrap();
    assert!(
        project("fn entry(){let answer={with Stop::now()->\"bad\";Foreign::apply(1,stop)+100}}")
            .verify()
            .is_err()
    );
}

#[test]
fn aborting_foreign_path_cannot_borrow_the_normal_paths_result_inspection() {
    assert!(project("fn entry(){let pending:Result<int,str>=Ok(1);let answer={with Stop::now()->7;Foreign::apply(1,stop);assert(pending is Ok(_));7};assert(answer==7)}").verify().is_err());
    project("fn entry(){let pending:Result<int,str>=Ok(1);let answer={with Stop::now()->7;Foreign::apply(1,stop);assert(pending is Ok(_));7};assert(pending is Ok(_));assert(answer==7)}").verify().unwrap();
    project("fn entry(){let answer:Result<int,str>={with Stop::now()->{let outcome:Result<int,str>=Ok(7);outcome};Foreign::apply(1,stop);let outcome:Result<int,str>=Ok(8);outcome};assert(answer is Ok(_))}").verify().unwrap();
    assert!(project("fn entry(){let answer:Result<int,str>={with Stop::now()->{let outcome:Result<int,str>=Ok(7);outcome};Foreign::apply(1,stop);let outcome:Result<int,str>=Ok(8);outcome}}").verify().is_err());
}

#[test]
fn distinct_abort_and_normal_heap_mutations_both_survive_the_join() {
    let verified=project("type Cell={mut value:int}\nfn entry(){let mut cell=Cell.{value:0};let answer={with Stop::now()->{cell.value=7;9};Foreign::apply(1,stop);cell.value=100;10};let observed=cell.value;assert(answer>=9);assert(observed>=7)}").verify().unwrap();
    let observed = verified
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "observed")
        .unwrap();
    assert!(
        observed.value.constant.is_none(),
        "the normal suffix cannot overwrite the abort path's value"
    );
}
