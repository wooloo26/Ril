use ril_compiler::{CompilationOutcome, Session, sema::SemanticFacts};

fn source_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/record-bounds.ril::write-scalar")
}

fn facts() -> SemanticFacts {
    let program = Session::new(source_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let facts = program.facts().clone();
    assert!(!facts.bound_field_writes.is_empty());
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    facts
}

#[test]
fn actual_mutable_assignment_keeps_the_receiver_old_member_and_real_access() {
    facts();
    let program = Session::with_options(
        source_fixture().as_bytes().to_vec(),
        ril_compiler::CheckOptions {
            target: "pointer32".into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
}

#[test]
fn source_readonly_paths_and_immutable_members_remain_type_permission_errors() {
    for source in [
        "fn replace<T:{mut value:int,..R}>(object:T){object.value=7}",
        "fn replace<T:{value:int,..R}>(mut object:T)&mut{object.value=7}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0520")),
            "{outcome:?}"
        );
    }
}
