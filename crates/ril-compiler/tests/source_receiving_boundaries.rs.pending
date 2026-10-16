//! Real receiving boundaries, both static layouts. NI is never a completed
//! negative case; the four before inputs were accepted by the frozen v30 CLI.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

const BEFORE: [&str; 4] = [
    "fn example(){let stored:[0][3]int=[];let narrowed:[0][2]int=stored}",
    "fn wrong()->[0][2]int{let stored:[0][3]int=[];stored}",
    "fn triple(values:[3]int)->int{0}\nfn example(){let callback:fn([2]int)->int=triple}",
    "type Holder={item:[0][2]int}\nfn example(){let stored:[0][3]int=[];let holder:Holder=.{item:stored}}",
];

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
fn four_preserved_before_sources_are_real_dimension_rejections() {
    for target in ["pointer32", "pointer64"] {
        for source in BEFORE {
            let outcome = session(source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
                "{target}: {source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn fresh_literal_and_stored_matching_source_reach_core() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            "fn correct()->[0][2]int{let stored:[0][2]int=[];stored}",
            "fn example(){let stored:[0][3]int=[];let dynamic:[][3]int=stored}",
            "fn pair(values:[2]int)->int{0}\nfn example(){let callback:fn([2]int)->int=pair}",
            "type Holder={item:[0][2]int}\nfn example(){let holder:Holder=.{item:[]}}",
        ] {
            let verified = session(source, target)
                .verify()
                .unwrap_or_else(|outcome| panic!("{target}: {source}\n{outcome:?}"));
            ril_compiler::lower::lower_core(&verified).unwrap();
        }
    }
}

#[test]
fn explicit_and_branch_returns_do_not_reopen_stored_empty_arrays() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            "fn wrong()->[0][2]int{let stored:[0][3]int=[];return stored}",
            "fn wrong(flag:bool)->[0][2]int{let stored:[0][3]int=[];if flag{stored}else{[]}}",
            "fn wrong(flag:bool)->[0][2]int{let stored:[0][3]int=[];match flag{true->stored,false->[]}}",
        ] {
            let outcome = session(source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
                "{target}: {source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn dynamic_storage_and_typed_construction_cannot_borrow_literal_receiving() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            "fn example(){let stored:[]int=[1,2];let fixed:[2]int=stored}",
            "fn example(){let stored:[]int=[1,2];let fixed:[2]int=clone(stored)}",
            "type Holder={item:[]int}\nfn example(){let holder:{item:[2]int}=Holder.{item:[1,2]}}",
        ] {
            let outcome = session(source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
                "{target}: {source}\n{outcome:?}"
            );
        }
    }
}
