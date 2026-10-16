//! Receiving source belongs only to actual match result positions.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn session(source: &str, target: &str) -> Session {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..CheckOptions::default()
        },
    )
}
#[test]
fn match_result_source_target_is_not_applied_to_subject_guard_or_nested_statement() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            "fn correct(flag:bool)->[0][2]int{let stored:[0][2]int=[];match flag{true->stored,false->[]}}",
            "fn correct(flag:bool)->[0][2]int{let choice:bool=match flag{true->true,false->false};match choice{true->[],false->[]}}",
            "fn correct(flag:bool)->[0][2]int{match flag{true if flag->[],true->[],false->[]}}",
        ] {
            let verified = session(source, target)
                .verify()
                .unwrap_or_else(|outcome| panic!("{target}: {source}\n{outcome:?}"));
            ril_compiler::lower::lower_core(&verified).unwrap();
        }
        let source = "fn wrong(flag:bool)->[0][2]int{let stored:[0][3]int=[];match flag{true->[],false->stored}}";
        let outcome = session(source, target).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{target}: {source}\n{outcome:?}"
        );
    }
}

#[test]
fn dynamic_array_destination_still_checks_invariant_stored_element_source() {
    for target in ["pointer32", "pointer64"] {
        let source = "fn example(){let stored:[0][3]int=[];let erased:[][]int=stored}";
        let outcome = session(source, target).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{target}: {source}\n{outcome:?}"
        );
        let source = "fn example(){let stored:[0][3]int=[];let dynamic:[][3]int=stored}";
        let verified = session(source, target)
            .verify()
            .unwrap_or_else(|outcome| panic!("{target}: {source}\n{outcome:?}"));
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}
