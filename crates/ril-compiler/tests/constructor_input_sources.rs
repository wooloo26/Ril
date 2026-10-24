//! Nominal payloads cannot replace the original operand's array coordinates.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn verified(source: &str, target: &str) -> SemanticFacts {
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{target}\n{source}\n{outcome:?}"));
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn stored_dynamic_and_empty_outer_dimensions_are_rejected_at_constructor_input() {
    for source in [
        "type Fixed([2]int)\nfn example(){let xs:[]int=[1,2];let wrapped=Fixed(xs)}",
        "type Fixed([0][2]int)\nfn example(){let xs:[0][3]int=[];let wrapped=Fixed(xs)}",
        "type Envelope{Item([0][2]int)}\nfn example(){let xs:[0][3]int=[];let wrapped=Envelope::Item(xs)}",
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
                matches!(&outcome,CompilationOutcome::Rejected{diagnostics}
                if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
                "{layout}\n{source}\n{outcome:?}"
            );
        }
    }
}
#[test]
fn written_literals_fixed_values_and_both_tuple_boundaries_keep_source_coordinates() {
    for source in [
        "type Fixed([2]int)\nfn example(){let wrapped=Fixed([1,2]);let xs:[2]int=inner(wrapped)}",
        "type Fixed([2]int)\nfn example(){let xs:[2]int=[1,2];let wrapped=Fixed(xs);let returned:[2]int=inner(wrapped)}",
        "type Fixed([0][2]int)\nfn example(){let wrapped=Fixed([]);let xs:[0][2]int=inner(wrapped)}",
        "type Envelope{Item([2]int,str)}\nfn example(){let first=Envelope::Item(([1,2],\"a\"));let second=Envelope::Item([3,4],\"b\")}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            verified(source, layout);
        }
    }
}
