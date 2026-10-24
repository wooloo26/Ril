//! Defaults retain their original Source even when the function is never called.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn verified(source: &str, layout: &str) -> SemanticFacts {
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{layout}\n{source}\n{outcome:?}"));
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn unused_defaults_keep_original_dimensions_and_callable_parameters() {
    for source in [
        "fn dynamic()->[]int{[7,9]}\nfn unused(value:[2]int=dynamic()){}",
        "fn triple(values:[3]int)->int{0}\nfn unused(callback:fn([2]int)->int=triple){}",
        "type Holder={item:[0][2]int}\nfn old()->[0][3]int{[]}\nfn unused(value:Holder=.{item:old()}){}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected{diagnostics}
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{layout}\n{source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn unused_defaults_receive_real_literals_and_earlier_formals_without_body_entry() {
    for source in [
        "fn unused(value:[2]int=[7,9]){}",
        "fn unused(first:[2]int,second:[2]int=first){}",
        "fn direct(values:[2]int)->int{0}\nfn unused(callback:fn([2]int)->int=direct){}",
        "fn unused<T>(first:T,second:T=first){}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            verified(source, layout);
        }
    }
}

#[test]
fn actual_default_calls_keep_the_same_literal_source_across_repeated_evaluation() {
    for source in [
        "fn read(values:[2]int=[7,9])->int{values[0]}\nfn example(){assert(read()==7);assert(read()==7)}",
        "fn read(values:[2]int=[7,9])->int{values[0]}\nfn example(){var count=0;for [0,1] as step{assert(read()==7);count+=1};assert(count>=0)}",
        "fn read(value:f32=16777217)->f32{value}\nfn example(){assert(read()==16777216.0f32)}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            verified(source, layout);
        }
    }
}

#[test]
fn complete_tuple_record_and_nested_literal_defaults_keep_their_receiving_contexts() {
    for source in [
        "fn read(values:([2]int,[2]int)=([7,9],[11,13]))->int{values.0[0]+values.1[0]}\nfn example(){assert(read()==18)}",
        "type Holder={first:[2]int,second:[2]int}\nfn read(value:Holder=.{first:[7,9],second:[11,13]})->int{value.first[0]+value.second[0]}\nfn example(){assert(read()==18)}",
        "fn read(values:[2][2]int=[[7,9],[11,13]])->int{values[0][0]+values[1][0]}\nfn example(){assert(read()==18)}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            verified(source, layout);
        }
    }
}

#[test]
fn contextual_defaults_use_the_shared_expression_receiver() {
    let source =
        ril_test::case_source("tests/regressions/defaults.ril::contextual-values-pointer64");
    for layout in ["pointer32", "pointer64"] {
        verified(source, layout);
    }
}
