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
fn bounded_member_generic_arguments_are_selected_on_both_layouts_and_lower_to_core() {
    for target in ["pointer32", "pointer64"] {
        let verified = session(
            ril_test::case_source("tests/regressions/static.ril::static-bound-generic-members"),
            target,
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn bounded_member_constraints_reject_inconsistent_explicit_and_empty_array_types() {
    for source in [
        "meta fn pair<T:{item:U,..R},V:{item:U,..S},U>(left:T,right:V)->U{left.item}\nmeta let _=pair(.{item:7},.{item:\"different\"})",
        "meta fn member<T:{item:U,..R},U>(value:T)->U{value.item}\nmeta let _=member<{item:int},str>(.{item:7})",
        "meta fn pair<T:{item:U,..R},V:{item:U,..S},U>(left:T,right:V)->int{0}\nmeta let _={let left:[0][2]int=[];let right:[0][3]int=[];pair(.{item:left},.{item:right})}",
    ] {
        let outcome = session(source, "pointer64").check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn an_explicit_callable_view_still_renames_and_removes_defaults_after_member_inference() {
    for (ending, code) in [("callback(right:7)", "E0339"), ("callback()", "E0314")] {
        let source = format!(
            "meta fn second(right:int=2)->int{{right}}\nmeta fn member<T:{{item:U,..R}},U>(value:T)->U{{value.item}}\nmeta let _={{let callback:fn(renamed:int)->int=member(.{{item:second}});{ending}}}"
        );
        let outcome = session(&source, "pointer64").check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn selecting_member_types_cannot_use_actual_arguments_to_prove_a_universal_result_branch() {
    let source = "meta fn branch<T:{flag:bool,item:U,..R},U>(value:T)->int{if value.flag{1}else{let pending:Result<int,str>=Ok(7);0}}\nmeta let _=branch(.{flag:true,item:7})";
    let outcome = session(source, "pointer64").check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
        if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}

#[test]
fn a_selected_result_member_transfers_its_original_producer_to_the_returned_value() {
    let accepted = "meta fn member<T:{item:U,..R},U>(value:T)->U{value.item}\nmeta let _={let pending:Result<int,str>=Ok(7);let returned=member(.{item:pending});assert(returned is Ok(_))}";
    let verified = session(accepted, "pointer64").verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
    let rejected = "meta fn member<T:{item:U,..R},U>(value:T)->U{value.item}\nmeta let _={let pending:Result<int,str>=Ok(7);let returned=member(.{item:pending});()}";
    let outcome = session(rejected, "pointer64").check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
        if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}
