use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use std::num::NonZeroU64;

fn outcome(source: &str, budget: u64) -> CompilationOutcome {
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
    let result = outcome(source, budget);
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "{source}\n{result:?}"
    );
}

#[test]
fn finite_type_tail_applications_use_an_explicit_driver() {
    for source in [
        "meta fn prior(n:int)->int{n-1}\ntype Count=\\n:int->if n==0{type<int>}else{Count<prior(n)>}\ntype Selected=Count<512>\nmeta let _=assert(type<Selected>==type<int>)",
        "meta fn prior(n:int)->int{n-1}\ntype Even=\\n:int->if n==0{type<int>}else{Odd<prior(n)>}\ntype Odd=\\n:int->if n==0{type<str>}else{Even<prior(n)>}\ntype Selected=Even<512>\nmeta let _=assert(type<Selected>==type<int>)",
        "meta fn prior(n:int)->int{n-1}\ntype Count=\\n:int->{if n==0{return type<int>};return Count<prior(n)>}\ntype Selected=Count<512>\nmeta let _=assert(type<Selected>==type<int>)",
        "meta fn prior(n:int)->int{n-1}\ntype Count=\\n:int->match n{0->type<int>,_->type<Count<prior(n)>>}\ntype Selected=Count<512>\nmeta let _=assert(type<Selected>==type<int>)",
    ] {
        accepts(source, 10_000);
    }
}

#[test]
fn type_tail_optimization_preserves_every_meta_and_type_entry() {
    let source = "meta fn prior(n:int)->int{n-1}\ntype Count=\\n:int->if n==0{type<int>}else{Count<prior(n)>}\ntype Selected=Count<512>";
    let result = outcome(source, 1_024);
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|d| d.code=="E0811")),
        "{result:?}"
    );
    accepts(source, 1_025);
}

#[test]
fn changing_argument_infinite_type_recursion_exhausts_the_language_budget() {
    let source =
        "meta fn advance(n:int)->int{n+1}\ntype Spin=\\n:int->Spin<advance(n)>\ntype Never=Spin<0>";
    let result = outcome(source, 20);
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|d| d.code=="E0811")),
        "{result:?}"
    );
}

#[test]
fn ordinary_meta_calls_do_not_inherit_type_return_control() {
    accepts(
        "type Select=\\T->(\\->type<T>)()\ntype Selected=Select<int>\nmeta let _=assert(type<Selected>==type<int>)",
        10,
    );
    let result = outcome(
        "meta fn illegal()->int{(\\->type<int>)()}\ntype Select=\\T->{illegal();type<T>}\ntype Selected=Select<int>",
        100,
    );
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|d| d.code=="E0812")),
        "{result:?}"
    );
}
