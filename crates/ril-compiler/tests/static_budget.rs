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
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
        "budget={budget}: {source}\n{result:?}"
    );
}

#[test]
fn entry_quota_counts_language_calls_and_permits_the_last_body() {
    let source = "meta fn one()->int{1}\nmeta fn two()->int{one()}\nmeta let _=assert(two()==1)";
    rejects(source, 1, "E0811");
    accepts(source, 2);
    let source = "meta fn fail(){assert(false)}\nmeta let _=fail()";
    rejects(source, 1, "E0830");
    let source = "meta fn fail(){assert(false)}\nmeta fn invoke(){fail()}\nmeta let _=invoke()";
    rejects(source, 1, "E0811");
    rejects(source, 2, "E0830");
}

#[test]
fn arithmetic_literal_spelling_and_type_shape_visits_are_not_events() {
    accepts(
        "meta fn compute()->int{let pair=(1+2,4+5);if pair.0==3{pair.1*2}else{0}}\nmeta let _=assert(compute()==18)",
        1,
    );
    let long = "7".repeat(2_000);
    accepts(
        &format!("meta let VALUE={long}bigint\nmeta let _=assert(len(`uncharged`)==9)"),
        1,
    );
    accepts(
        "meta fn fixed()->([2]int,[2]int){let a:[2]int=[1,2];(a,a)}\nmeta let VALUE=fixed()\nmeta let _=assert(VALUE.0[0]==1)",
        1,
    );
}

#[test]
fn independent_binding_roots_reset_but_nested_calls_never_reset() {
    accepts(
        "meta fn one()->int{1}\nmeta let FIRST=one()\nmeta let SECOND=one()\nmeta let _=assert(FIRST==SECOND)",
        1,
    );
    rejects(
        "meta fn one()->int{1}\nmeta let BOTH=(one(),one())",
        1,
        "E0811",
    );
    accepts("meta fn one()->int{1}\nmeta let BOTH=(one(),one())", 2);
}

#[test]
fn anonymous_parameter_type_computation_belongs_to_creation() {
    accepts(
        "meta fn shape()->[2]int{[0,0]}\nmeta let IDENTITY=\\value:[len(shape())]int->value\nmeta let FIRST=IDENTITY([1,2])\nmeta let SECOND=IDENTITY([3,4])\nmeta let _=assert(FIRST[0]==1 && SECOND[0]==3)",
        1,
    );
    rejects(
        "meta fn shape()->[2]int{[0,0]}\nmeta fn make()->fn([2]int)->[2]int{\\value:[len(shape())]int->value}\nmeta let IDENTITY=make()",
        1,
        "E0811",
    );
    accepts(
        "meta fn shape()->[2]int{[0,0]}\nmeta fn make()->fn([2]int)->[2]int{\\value:[len(shape())]int->value}\nmeta let IDENTITY=make()\nmeta let FIRST=IDENTITY([1,2])",
        2,
    );
}

#[test]
fn tail_calls_keep_every_source_entry_in_the_same_root() {
    let source =
        "meta fn count(n:int)->int{if n==0{7}else{count(n-1)}}\nmeta let _=assert(count(4)==7)";
    rejects(source, 4, "E0811");
    accepts(source, 5);
    let source = "meta fn apply()->int{(\\->7)()}\nmeta let _=assert(apply()==7)";
    rejects(source, 1, "E0811");
    accepts(source, 2);
}

#[test]
fn combinators_charge_iteration_tests_and_callback_entries() {
    let source = "meta let VALUES=Array::map([1,2],\\n->n+1)\nmeta let _=assert(VALUES==[2,3])";
    rejects(source, 4, "E0811");
    accepts(source, 5);
    let source = "meta fn inc(n:int)->int{n+1}\nmeta let VALUES=Array::map([1,2],\\n->inc(n))";
    rejects(source, 6, "E0811");
    accepts(source, 7);
    let source = "meta let FOUND=Array::any([1,2],\\n->n==1)\nmeta let _=assert(FOUND)";
    rejects(source, 1, "E0811");
    accepts(source, 2);
    let source = "meta let TOTAL=Array::fold([1,2],0,\\sum,n->sum+n)\nmeta let _=assert(TOTAL==3)";
    rejects(source, 4, "E0811");
    accepts(source, 5);
}

#[test]
fn type_function_entries_share_the_actual_type_evaluation_root() {
    accepts(
        "type Identity=\\T->type<T>\ntype First=Identity<int>\ntype Second=Identity<str>",
        1,
    );
    let source = "type Identity=\\T->type<T>\ntype Pair=(Identity<int>,Identity<str>)";
    rejects(source, 1, "E0811");
    accepts(source, 2);
    let source = "type Identity=\\T->type<T>\ntype Pair=\\T->Identity<T>\ntype Selected=Pair<int>";
    rejects(source, 1, "E0811");
    accepts(source, 2);
}
