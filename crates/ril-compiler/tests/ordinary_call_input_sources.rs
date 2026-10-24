//! Original input schemas are obligations even when an application arena is
//! damaged; fresh receiving comes only from the actual operand syntax.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn verified(source: &str) -> SemanticFacts {
    let program = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

fn type_conflict(source: &str) {
    for target in ["pointer32", "pointer64"] {
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn a_stored_array_never_borrows_its_backing_count_for_receiving() {
    for source in [
        "fn exact(value:[2]int)->int{0}\nfn example()->int{let values:[]int=[7,9];exact(values)}",
        "fn exact<T>(value:[2]T)->int{0}\nfn example()->int{let values:[]int=[7,9];exact(values)}",
        "fn exact<T>(value:[2]T)->int{0}\nfn example()->int{let values:[]int=[7,9];exact<int>(values)}",
        "fn id<T>(value:T)->T{value}\nfn example(){let values:[]int=[7,9];let fixed=id<[2]int>(values)}",
        "fn exact<T>(value:[0][2]T)->int{0}\nfn example()->int{let values:[0][3]int=[];exact(values)}",
        "fn exact(value:[][]int)->int{0}\nfn example()->int{let values:[0][3]int=[];exact(values)}",
    ] {
        type_conflict(source);
    }
}

#[test]
fn callable_dimensions_are_checked_inside_the_original_signature() {
    type_conflict(
        "fn take(callback:fn([2]int)->int)->int{0}\nfn triple(values:[3]int)->int{0}\nfn example()->int{take(triple)}",
    );
}

#[test]
fn a_fresh_returned_shell_does_not_make_a_default_a_literal() {
    type_conflict(
        "fn dynamic()->[]int{[7,9]}\nfn take(value:[2]int=dynamic())->int{0}\nfn example()->int{take()}",
    );
}

#[test]
fn direct_literal_and_earlier_parameter_defaults_keep_their_real_receiving_context() {
    for source in [
        "fn take(value:[2]int)->int{value[0]}\nfn example()->int{take([7,9])}",
        "fn take(value:[2]int=[7,9])->int{value[0]}\nfn example()->int{take()}",
        "fn take(first:[2]int,second:[2]int=first)->int{second[0]}\nfn example()->int{take([7,9])}",
        "fn defaulted<T>(value:int=7)->int{value}\nfn example()->int{defaulted<str>()}",
        "fn id<T>(value:T)->T{value}\nfn example()->[2]int{id<[2]int>([7,9])}",
    ] {
        verified(source);
    }
}

#[test]
fn mutable_forwarding_keeps_its_source_type_and_its_original_loan_mode() {
    verified(
        "fn take(mut values:[2]int)&mut{values[0]=1}\nfn forward(mut values:[2]int)&mut{take(mut values)}\nfn example(){let mut values:[2]int=[7,9];forward(mut values)}",
    );
}

#[test]
fn a_symbolic_public_callable_cannot_receive_a_stored_dynamic_array_as_fixed() {
    type_conflict(
        "fn call(callback:fn([2]int)->int,values:[]int)->int{callback(values)}\nfn example(){}",
    );
}
