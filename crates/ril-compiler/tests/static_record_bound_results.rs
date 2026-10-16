use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn session(source: &str, target: &str) -> Session {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
}

#[test]
fn known_bound_fields_feed_real_result_producers_on_both_static_layouts() {
    let source = ril_test::case_source("tests/regressions/static.ril::static-bound-projection");
    for target in ["pointer32", "pointer64"] {
        let verified = session(source, target).verify().unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn a_reached_bound_member_inspection_discharges_the_actual_caller_producer() {
    let source =
        ril_test::case_source("tests/regressions/static.ril::static-bound-result-inspection");
    session(source, "pointer64").verify().unwrap();
}

#[test]
fn a_bound_projection_cannot_discard_a_result_hidden_in_the_open_remainder() {
    let source = r#"
meta fn read<T:{id:int,..R}>(value:T)->int{value.id}
meta let _={let hidden:Result<int,str>=Ok(1);read(.{id:7,hidden:hidden});()}
"#;
    let outcome = session(source, "pointer64").check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}

#[test]
fn universal_bound_definition_cannot_borrow_the_actual_calls_true_branch() {
    let source = r#"
meta fn read<T:{id:int,..R}>(value:T,flag:bool)->int{
    let pending:Result<int,str>=Ok(value.id)
    if flag{assert(pending is Ok(_))}
    value.id
}
meta let ANSWER=read(.{id:7},true)
"#;
    let outcome = session(source, "pointer64").check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}

#[test]
fn generic_receiving_transports_the_actual_callable_interface_and_defaults() {
    let source =
        ril_test::case_source("tests/regressions/static.ril::static-generic-callable-receiving");
    session(source, "pointer64").verify().unwrap();
}

#[test]
fn generic_alias_wrappers_keep_nested_actual_callable_interfaces() {
    let source =
        ril_test::case_source("tests/regressions/static.ril::static-generic-callable-wrapper");
    session(source, "pointer64").verify().unwrap();
}

#[test]
fn explicit_numeric_type_selection_does_not_retain_an_unrounded_branch_fact() {
    let source = r#"
meta fn identity<T>(value:T)->T{value}
meta let _={
    let pending:Result<int,str>=Ok(1)
    let selected=identity<f32>(16777217)
    if selected==16777216{}else{assert(pending is Ok(_))}
    ()
}
"#;
    let outcome = session(source, "pointer64").check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "the abstract proof must not use the unrounded integer: {outcome:?}"
    );
}

#[test]
fn explicit_type_arguments_select_the_real_result_flow_activation() {
    let source = r#"
meta fn identity<T>(value:T)->T{value}
meta let ANSWER={
    let pending:Result<int,str>=Ok(1)
    assert(pending is Ok(_))
    identity<int>(7)
}
meta let _=assert(ANSWER==7)
"#;
    session(source, "pointer64").verify().unwrap();
}

#[test]
fn editing_a_bound_application_cannot_reuse_the_previous_inspection() {
    let valid =
        ril_test::case_source("tests/regressions/static.ril::static-bound-result-inspection");
    let invalid = r#"
meta fn read<T:{id:int,..R}>(value:T)->int{value.id}
meta let _={let hidden:Result<int,str>=Ok(1);read(.{id:7,hidden:hidden});()}
"#;
    let mut edited = session(valid, "pointer64");
    edited.verify().unwrap();
    edited.update(invalid.as_bytes().to_vec());
    let incremental = edited.check();
    let fresh = session(invalid, "pointer64").check();
    let (
        CompilationOutcome::Rejected { diagnostics: left },
        CompilationOutcome::Rejected { diagnostics: right },
    ) = (incremental, fresh)
    else {
        panic!("both sessions must reject the uninspected actual caller producer");
    };
    assert!(left.iter().any(|diagnostic| diagnostic.code == "E0720"));
    assert_eq!(left, right);
    edited.update(valid.as_bytes().to_vec());
    edited.verify().unwrap();
}

#[test]
fn selecting_a_bound_numeric_field_keeps_other_fields_callable_defaults() {
    session(
        ril_test::case_source("tests/regressions/static.ril::static-bound-callable-construction"),
        "pointer64",
    )
    .verify()
    .unwrap();
}
