//! Source-level static loop contracts; no evaluator-private flags are witnesses.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use std::num::NonZeroU64;

fn check(source: &str, budget: u64) -> CompilationOutcome {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            static_budget: NonZeroU64::new(budget).unwrap(),
            ..Default::default()
        },
    )
    .check()
}
fn accepts(source: &str, budget: u64) {
    let result = check(source, budget);
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "budget={budget}: {source}\n{result:?}"
    );
}
fn rejects(source: &str, budget: u64, code: &str) {
    let result = check(source, budget);
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|item| item.code == code)),
        "budget={budget}: {source}\n{result:?}"
    );
}
fn core(source: &str) {
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .expect(source);
    ril_compiler::lower::lower_core(&verified).expect("static loop publication reaches Core");
}

#[test]
fn four_original_finite_immutable_loops_reach_session_and_core() {
    for source in [
        "meta fn once()->int{loop{last 7}}\nmeta let VALUE=once()\nmeta let _=assert(VALUE==7)\n",
        "meta fn first(values:[]int)->int{\n    for values as value{if value>0{return value};next}\n    0\n}\nmeta let VALUE=first([-1,7,9])\nmeta let _=assert(VALUE==7)\n",
        "meta fn none()->int{while false{};7}\nmeta let VALUE=none()\nmeta let _=assert(VALUE==7)\n",
        "type Pick=\\T->{loop{last type<T>}}\ntype Chosen=Pick<int>\nfn identity(value:Chosen)->Chosen{value}\n",
    ] {
        core(source);
    }
}

#[test]
fn every_condition_and_next_test_has_one_event_including_terminal_none() {
    for (source, quota) in [
        ("meta fn one()->int{loop{last 7}}\nmeta let VALUE=one()", 2),
        (
            "meta fn walk(){for [1,2] as value{next}}\nmeta let _=walk()",
            4,
        ),
        (
            "meta fn walk(){for [] as value{next}}\nmeta let _=walk()",
            2,
        ),
        ("meta fn walk(){while false{next}}\nmeta let _=walk()", 2),
        (
            "meta fn walk(){for [1,2] as value{last}}\nmeta let _=walk()",
            2,
        ),
        (
            "meta fn one()->int{1}\nmeta fn walk(){for [1,2] as value{assert(one()==1)}}\nmeta let _=walk()",
            6,
        ),
        (
            "type Pick=\\T->{loop{last type<T>}}\ntype Chosen=Pick<int>",
            2,
        ),
        (
            "meta fn walk(){for 254u8..=255u8 as value{assert(value>=254u8)}}\nmeta let _=walk()",
            4,
        ),
    ] {
        rejects(source, quota - 1, "E0811");
        accepts(source, quota);
    }
    accepts(
        "meta fn one()->int{loop{last 7}}\nmeta let FIRST=one()\nmeta let SECOND=one()",
        2,
    );
}

#[test]
fn infinite_unmarked_paths_exhaust_events_without_a_host_loop_limit() {
    for source in [
        "meta fn spin(){loop{next}}\nmeta let _=spin()",
        "meta fn spin(){while true{next}}\nmeta let _=spin()",
        "meta fn spin(){for 0.. as value{next}}\nmeta let _=spin()",
        "type Spin=\\T->{loop{next}}\ntype Selected=Spin<int>",
    ] {
        rejects(source, 10, "E0811");
    }
}

#[test]
fn nested_lexical_targets_and_call_boundaries_never_borrow_an_outer_loop() {
    for source in [
        "meta fn helper()->int{loop{last 9}}\nmeta fn outer()->int{loop{let value=helper();last value+1}}\nmeta let _=assert(outer()==10)",
        "meta fn outer()->int{loop{let value=(\\->loop{last 9})();last value+1}}\nmeta let _=assert(outer()==10)",
        "meta fn helper(value:int)->int{value}\nmeta fn outer()->int{loop{helper(last 7);last 9}}\nmeta let _=assert(outer()==7)",
        "meta fn outer()->int{loop{for [1,2] as value{if value==1{next};last};last 7}}\nmeta let _=assert(outer()==7)",
    ] {
        core(source);
    }
    for source in [
        "meta fn helper(){next}\nmeta fn outer(){loop{helper();last}}\nmeta let _=outer()",
        "meta fn outer()->int{loop{(\\->last 7)();last 9}}\nmeta let VALUE=outer()",
        "type Bad=\\T->{last type<T>}\ntype Outer=\\T->{loop{last Bad<T>}}\ntype Selected=Outer<int>",
        "meta fn helper(value:int={next})->int{value}\nmeta fn outer()->int{loop{last helper()}}\nmeta let VALUE=outer()",
    ] {
        rejects(source, 100, "E0707");
    }
}

#[test]
fn iteration_declaration_groups_capture_their_own_immutable_values() {
    core(
        r#"
meta fn make(values:[]int)->fn()->int{
    for values as value{return get where meta fn get()->int{value}}
    \->0
}
meta let FIRST=make([7])
meta let SECOND=make([9])
meta let _=assert(FIRST()==7 && SECOND()==9)
"#,
    );
}

#[test]
fn loop_last_and_callable_return_keep_distinct_numeric_contexts() {
    for source in [
        "meta fn byte()->u8{loop{last 255}}\nmeta let VALUE=byte()\nmeta let _=assert(VALUE==255u8)",
        "meta fn byte()->u8{let byte:u8=7;loop{last byte+1}}\nmeta let VALUE=byte()\nmeta let _=assert(VALUE==8u8)",
        "meta fn byte()->u8{let text:str=loop{return 255};1}\nmeta let VALUE=byte()\nmeta let _=assert(VALUE==255u8)",
        "meta fn text()->str{loop{false && {last 7};last `kept`}}\nmeta let _=assert(text()==`kept`)",
    ] {
        core(source);
    }
    for source in [
        "meta fn byte()->u8{let byte:u8=7;loop{last byte+1int}}\nmeta let VALUE=byte()",
        "meta fn bad(){while true{last 7}}",
        "meta fn bad(){for [1] as value{last 7}}",
    ] {
        rejects(source, 100, "E0301");
    }
    rejects("meta fn bad(){for [1,2] as 1{}}", 100, "E0345");
    rejects("meta fn bad(){for `text` as value{}}", 100, "E0355");
}

#[test]
fn immutable_iteration_order_and_shared_constant_origins_survive_last() {
    core(
        "meta fn first()->str{for [`b`:2,`a`:1] as (key,value){return key};``}\nmeta let _=assert(first()==`b`)",
    );
    core(
        "meta fn graph()->([2]int,[2]int){let shared:[2]int=[1,2];loop{last(shared,shared)}}\nmeta let GRAPH=graph()\nfn example() &{GRAPH}{assert(GRAPH.0[1]==2 && GRAPH.1[1]==2)}",
    );
}

#[test]
fn finite_halt_evidence_is_independent_of_actual_event_budget_success() {
    for source in [
        "halt type Once=\\T->{loop{last type<T>}}\ntype Selected=Once<int>",
        "meta fn once()->int{loop{last 7}}\nhalt type Via=\\T->{let value=once();assert(value==7);type<T>}\ntype Selected=Via<int>",
        "halt type Finite=\\T->{for [1,2] as value{next};type<T>}\ntype Selected=Finite<int>",
        "halt type Empty=\\T->{while false{next};type<T>}\ntype Selected=Empty<int>",
    ] {
        core(source);
    }
    for source in [
        "halt type Spin=\\T->{loop{next}}",
        "meta fn spin(){loop{false && {last};next}}\nhalt type Bad=\\T->{spin();type<T>}",
        "meta fn spin(){for 0.. as value{next}}\nhalt type Bad=\\T->{spin();type<T>}",
        "meta fn spin(){loop{let _=.{value:next};last}}\nhalt type Bad=\\T->{spin();type<T>}",
        "meta fn spin(){loop{let _=[0:next];last}}\nhalt type Bad=\\T->{spin();type<T>}",
    ] {
        rejects(source, 100, "E0820");
    }
}
