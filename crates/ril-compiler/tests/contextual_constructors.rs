//! Contextual constructors retain one original receiver and actual arguments.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn nested_literals_and_declared_constructor_payloads_use_the_same_receiving_rules() {
    for name in [
        "nested-receiving-contexts-pointer64",
        "declared-payload-contexts-pointer64",
    ] {
        let source = ril_test::case_bytes(&format!(
            "tests/regressions/contextual-constructors.ril::{name}"
        ));
        for target in ["pointer32", "pointer64"] {
            let snapshot = Session::with_options(
                source.to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .analyze();
            let diagnostics = format!("{:?}; {:?}", snapshot.diagnostics(), snapshot.unresolved());
            let program = snapshot
                .into_verified()
                .unwrap_or_else(|error| panic!("{name} {target}: {error:?}; {diagnostics}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
}

#[test]
fn constructor_contexts_never_retype_stored_dimensions_or_change_literal_cardinality() {
    for name in [
        "reject-stored-inner-dimension",
        "reject-stored-member-through-construction",
        "reject-construction-cardinality",
    ] {
        let source = ril_test::case_bytes(&format!(
            "tests/regressions/contextual-constructors.ril::{name}"
        ));
        for target in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                source.to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
                "{name} {target}: {outcome:?}"
            );
        }
    }
}
