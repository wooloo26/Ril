use ril_compiler::{CheckOptions, Session, session::ProjectSource};

fn project(callback: &str, body: &str) -> Session {
    Session::with_project("virtual/main.ril".into(),vec![
        ProjectSource{path:"virtual/main.ril".into(),bytes:format!("use foreign\neff Stop{{now()->int}}\nfn mixed(number:int)->int @Stop{{{callback}}}\n{body}").into_bytes()},
        ProjectSource{path:"virtual/foreign.d.ril".into(),bytes:b"pub fn repeated(callback:fn(int)->int)->int".to_vec()},
    ],CheckOptions::default()).unwrap()
}

const SUFFIX: &str =
    "fn entry(){let answer={with Stop::now()->7;Foreign::repeated(mixed)+100};assert(answer>=7)}";
const MIXED: &str = "if number>=12{Stop::now();panic(\"abandoned\")}else{number+1}";

#[test]
fn mixed_if_match_short_circuit_and_early_return_keep_terminal_exits() {
    for callback in [
        MIXED,
        "if number<12{number+1}else{Stop::now();panic(\"abandoned\")}",
        "if number<12{return number+1}else{Stop::now();panic(\"abandoned\")}",
        "if number<12{return number+1};Stop::now();panic(\"abandoned\")",
        "match number{12->{Stop::now();panic(\"abandoned\")},_->number+1}",
        "let checked=number>=12&&{Stop::now();panic(\"abandoned\")};number+1",
        "if number<12{Stop::now();panic(\"left\")}else{Stop::now();panic(\"right\")}",
    ] {
        let verified = project(callback, SUFFIX)
            .verify()
            .unwrap_or_else(|error| panic!("{callback}: {error:?}"));
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "entry").unwrap();
    }
}

#[test]
fn normal_return_iterations_cannot_inspect_the_callers_result_on_an_abort_path() {
    let body = "fn entry(){let pending:Result<int,str>=Ok(1);let answer={with Stop::now()->7;Foreign::repeated(mixed);assert(pending is Ok(_));7};assert(answer==7)}";
    assert!(project(MIXED, body).verify().is_err());
    project(
        MIXED,
        &body.replace(
            "assert(answer==7)",
            "assert(pending is Ok(_));assert(answer==7)",
        ),
    )
    .verify()
    .unwrap();
}

#[test]
fn every_ordinary_iteration_closes_its_own_family_and_terminal_answer_keeps_its_duty() {
    let callback = "let outcome:Result<int,str>=Ok(number);if number>=12{Stop::now();panic(\"abandoned\")}else{assert(outcome is Ok(_));number+1}";
    let body = "fn entry(){let answer:Result<int,str>={with Stop::now()->{let terminal:Result<int,str>=Ok(7);terminal};Foreign::repeated(mixed);let normal:Result<int,str>=Ok(8);normal};assert(answer is Ok(_))}";
    project(callback, body).verify().unwrap();
    assert!(
        project(callback, &body.replace(";assert(answer is Ok(_))", ""))
            .verify()
            .is_err()
    );
    assert!(
        project(&callback.replace("assert(outcome is Ok(_));", ""), body)
            .verify()
            .is_err()
    );
}

#[test]
fn abort_only_reference_replacement_is_separate_from_the_repeatable_normal_graph() {
    let body = "type Cell={mut items:[]int}\nfn entry(){let mut cell=Cell.{items:[0]};let answer={with Stop::now()->{cell.items=[7];7};Foreign::repeated(mixed);cell.items=[100];100};let view selected=cell.items;assert(answer>=7);assert(selected[0]>=7)}";
    let verified = project(MIXED, body).verify().unwrap();
    let selected = verified
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "selected")
        .unwrap();
    assert!(
        selected.value.origins.nodes.len() >= 2,
        "both completed exits retain their distinct arrays"
    );
}

#[test]
fn nested_helper_returns_keep_their_actual_heap_and_result_exit_state() {
    let callback = "helper(number) where fn helper(number:int)->int @Stop{let outcome:Result<int,str>=Ok(number);if number<12{assert(outcome is Ok(_));return number+1};Stop::now();panic(\"abandoned\")}";
    project(callback, SUFFIX).verify().unwrap();
    assert!(
        project(&callback.replace("assert(outcome is Ok(_));", ""), SUFFIX)
            .verify()
            .is_err(),
        "retained activation abort cannot waive the normal-return producer"
    );
}

#[test]
fn alternate_callback_targets_do_not_overwrite_each_others_normal_states() {
    let body = "var state=true\nfn disable(number:int)->int &{mut state}{state=false;number}\nfn enable(number:int)->int &{mut state}{state=true;number}\nfn entry(flag:bool) &{mut state}{let callback=if flag{disable}else{enable};let output=Foreign::repeated(callback);let observed=state;assert(output>=0)}";
    let verified = project(MIXED, body).verify().unwrap();
    let observed = verified
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "observed")
        .unwrap();
    assert!(
        observed.value.constant.is_none(),
        "the second abstract callable cannot erase the first possible target"
    );
}

#[test]
fn normal_return_graph_changes_still_need_a_repeated_transfer_proof() {
    let source=Session::with_project("virtual/main.ril".into(),vec![
        ProjectSource{path:"virtual/main.ril".into(),bytes:b"use foreign\neff Stop{now()->int}\neff Step{change()->()}\nfn mixed(number:int)->int @{Stop,Step}{if number>=12{Stop::now();panic(\"abandoned\")}else{Step::change();number+1}}\ntype Cell={mut items:[]int}\nfn entry(){let mut cell=Cell.{items:[0]};let answer={with Stop::now()->7;with Step::change()->{cell.items=[2];resume ()};Foreign::repeated(mixed)+100};assert(answer>=7);assert(cell.items[0]>=0)}".to_vec()},
        ProjectSource{path:"virtual/foreign.d.ril".into(),bytes:b"pub fn repeated(callback:fn(int)->int)->int".to_vec()},
    ],CheckOptions::default()).unwrap();
    let outcome = source.verify();
    assert!(
        matches!(
            outcome,
            Err(ril_compiler::CompilationOutcome::NotImplemented { .. })
        ),
        "{outcome:?}"
    );
}

#[test]
fn mixed_mutable_callback_exits_end_their_loans_and_keep_independent_alias_conflicts() {
    let source = |conflict: bool| {
        Session::with_project("virtual/main.ril".into(),vec![
        ProjectSource{path:"virtual/main.ril".into(),bytes:format!("use foreign\neff Stop{{now()->int}}\ntype Cell={{mut value:int}}\nfn entry(){{let mut cell=Cell.{{value:0}};{}let mut callback=\\number:int->{{cell.value+=1;if number>=12{{Stop::now();panic(\"abandoned\")}}else{{number+1}}}};let answer={{with Stop::now()->{};Foreign::repeated(mut callback)+100}};cell.value=5;assert(cell.value==5);assert(answer>=7)}}",if conflict{"let mut other=^mut cell;other.value=1;"}else{""},if conflict{"other.value+7"}else{"7"}).into_bytes()},
        ProjectSource{path:"virtual/foreign.d.ril".into(),bytes:b"pub fn repeated(mut callback:fn(int)->int)->int".to_vec()},
    ],CheckOptions::default()).unwrap()
    };
    let verified = source(false).verify().unwrap();
    let cell = verified
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "cell")
        .unwrap();
    assert!(!cell.value.temporary);
    assert!(cell.value.participants.iter().all(|participant| !matches!(
        participant,
        ril_compiler::sema::facts::Participant::Loan(_)
    )));
    let outcome = source(true).verify();
    assert!(
        matches!(&outcome,Err(ril_compiler::CompilationOutcome::Rejected{diagnostics})if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0524")),
        "an independent alias cannot join the callback's temporary loan: {outcome:?}"
    );
}

#[test]
fn immutable_callback_input_records_keep_real_result_families() {
    let project = |inspect: bool| {
        Session::with_project(
            "virtual/main.ril".into(),
            vec![
                ProjectSource {
                    path: "virtual/main.ril".into(),
                    bytes: format!(
                        "use foreign\nfn entry(){{Foreign::visit(\\ input->{{{}}})}}",
                        if inspect {
                            "assert(input.status is Ok(_))"
                        } else {
                            "()"
                        }
                    )
                    .into_bytes(),
                },
                ProjectSource {
                    path: "virtual/foreign.d.ril".into(),
                    bytes: b"pub fn visit(callback:fn({status:Result<int,str>})->())".to_vec(),
                },
            ],
            CheckOptions::default(),
        )
        .unwrap()
    };
    project(true).verify().unwrap();
    assert!(project(false).verify().is_err());
}

#[test]
fn transitive_callable_choices_are_real_alternatives_inside_the_callback() {
    let project = |main: &str| {
        Session::with_project(
            "virtual/main.ril".into(),
            vec![
                ProjectSource {
                    path: "virtual/main.ril".into(),
                    bytes: format!("use foreign\n{main}").into_bytes(),
                },
                ProjectSource {
                    path: "virtual/foreign.d.ril".into(),
                    bytes: b"pub fn repeated(callback:fn(int)->int)->int".to_vec(),
                },
            ],
            CheckOptions::default(),
        )
        .unwrap()
    };
    let verified=project("var state=true\nfn disable(number:int)->int &{mut state}{state=false;number}\nfn enable(number:int)->int &{mut state}{state=true;number}\nfn dispatch(number:int)->int &{mut state}{let selected=if number==0{disable}else{enable};selected(number)}\nfn entry() &{mut state}{let value=Foreign::repeated(dispatch);let observed=state;assert(value>=0)}").verify().unwrap();
    let observed = verified
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "observed")
        .unwrap();
    assert!(observed.value.constant.is_none());
    project("eff Stop{now()->int}\nfn stopping(number:int)->int @Stop{Stop::now();panic(\"abandoned\")}\nfn ordinary(number:int)->int{number+1}\nfn dispatch(number:int)->int @Stop{let selected=if number>=12{stopping}else{ordinary};selected(number)}\nfn entry(){let value={with Stop::now()->7;Foreign::repeated(dispatch)+100};assert(value>=7)}").verify().unwrap();
}
