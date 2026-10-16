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
fn symbolic_alias_map_and_callable_members_check_both_layouts_and_lower_to_core() {
    for target in ["pointer32", "pointer64"] {
        let verified = session(
            include_str!("fixtures/static_bound_template_inference.ril"),
            target,
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn alias_and_map_inference_preserve_inconsistent_complete_member_types() {
    for source in [
        "type Packet<X>={value:X}\nmeta fn pair<T:{payload:Packet<U>,..R},V:{payload:Packet<U>,..S},U>(left:T,right:V)->T{left}\nmeta let _=pair(.{payload:.{value:7}},.{payload:.{value:\"different\"}})",
        "meta fn pair<T:{items:[str:U],..R},V:{items:[str:U],..S},U>(left:T,right:V)->T{left}\nmeta let _={let left:[str:[0][2]int]=[:];let right:[str:[0][3]int]=[:];pair(.{items:left},.{items:right})}",
        "meta let _=[\"a\":7][0]",
        "meta let _=[7,9][\"a\"]",
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
fn alias_projection_keeps_the_actual_result_producer_until_inspected() {
    let definitions = "type Packet<X>={value:X}\nmeta fn member<T:{payload:Packet<U>,..R},U>(value:T)->U{value.payload.value}\n";
    let accepted = format!(
        "{definitions}meta let _={{let pending:Result<int,str>=Ok(7);let returned=member(.{{payload:.{{value:pending}}}});assert(returned is Ok(_))}}"
    );
    let verified = session(&accepted, "pointer64").verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
    let rejected = format!(
        "{definitions}meta let _={{let pending:Result<int,str>=Ok(7);let returned=member(.{{payload:.{{value:pending}}}});()}}"
    );
    let outcome = session(&rejected, "pointer64").check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
        if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
}

#[test]
fn explicit_callable_views_still_control_labels_and_defaults_after_template_inference() {
    for (ending, code) in [("callback(right:7)", "E0339"), ("callback()", "E0314")] {
        let definitions = "meta fn second(right:int=2)->int{right}\nmeta fn pass<T:{handler:fn(input:U)->V,..R},U,V>(value:T)->T{value}\n";
        let source = format!(
            "{definitions}meta let _={{let callback:fn(renamed:int)->int=pass(.{{handler:second}}).handler;{ending}}}"
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
fn optional_fallback_preserves_lazy_execution_return_paths_and_declared_array_dimensions() {
    for source in [
        "meta let ANSWER=Some(7)??{assert(false);9}\nmeta let _=assert(ANSWER==7)",
        "meta fn fallback()->int{return 9}\nmeta fn choose(value:?int)->int{value??fallback()}\nmeta let ANSWER=choose(Some(7))+choose(None)\nmeta let _=assert(ANSWER==16)",
        "meta fn first<T>(value:[2]T)->T{value[0]}\nmeta let ANSWER={let missing:?[2]int=None;let selected=missing??[7,9];first(selected)}\nmeta let _=assert(ANSWER==7)",
    ] {
        let verified = session(source, "pointer64").verify().unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
    let source = "meta let _={let stored=[7,9];let missing:?[2]int=None;missing??stored}";
    let outcome = session(source, "pointer64").check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "{outcome:?}"
    );
}

#[test]
fn fallback_operator_boundaries_use_the_specified_diagnostics() {
    for (source, code) in [
        (
            "meta fn choose(value:?int)->int{value??{return 9}}\nmeta let ANSWER=choose(Some(7))+choose(None)",
            "E0710",
        ),
        (
            "meta fn choose(value:?int)->int{value??{if false{return 9};7}}",
            "E0710",
        ),
        (
            "meta fn choose(value:?int)->int{loop{value??{last 9}}}",
            "E0710",
        ),
        (
            "meta fn choose(value:?int)->int{loop{value??{next;9}}}",
            "E0710",
        ),
        ("meta fn choose(value:?int)->?int{value??Some(9)?}", "E0710"),
        ("meta let _=42??0", "E0714"),
        (
            "meta let _={let failed:Result<int,str>=Err(\"bad\");failed??0}",
            "E0711",
        ),
    ] {
        let outcome = session(source, "pointer64").check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
            "{source}\n{outcome:?}"
        );
    }
    let handler =
        "meta let _={let failed:Result<int,str>=Err(\"bad\");failed??\\error:str->len(error)}";
    let outcome = session(handler, "pointer64").check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn optional_fallback_transports_result_identity_without_inspecting_or_evaluating_unused_producers()
{
    let definitions =
        "meta fn transport(value:?Result<int,str>)->Result<int,str>{value??Err(\"fallback\")}\n";
    let accepted = format!(
        "{definitions}meta let _={{let pending:Result<int,str>=Ok(7);let returned=transport(Some(pending));assert(returned is Ok(_))}}"
    );
    let verified = session(&accepted, "pointer64").verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
    let rejected = format!(
        "{definitions}meta let _={{let pending:Result<int,str>=Ok(7);let returned=transport(Some(pending));()}}"
    );
    let outcome = session(&rejected, "pointer64").check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
}
