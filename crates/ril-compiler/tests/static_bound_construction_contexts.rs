use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn session(source: &str, target: &str) -> Session {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
}

#[test]
fn fresh_record_members_receive_known_numeric_and_slot_declarations_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let verified = session(
            include_str!("fixtures/static_bound_fresh_construction.ril"),
            target,
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn structural_context_does_not_reselect_stored_numbers_or_existing_slot_modes() {
    for (source, code) in [
        (
            "meta fn read<T:{mut id:i8,..R}>(value:T)->i8{value.id}\nmeta let STORED=.{id:7i8}\nmeta let _=read(STORED)",
            "E0301",
        ),
        (
            "meta fn read<T:{mut id:i8,..R}>(value:T)->i8{value.id}\nmeta let STORED=7\nmeta let _=read(.{id:STORED})",
            "E0301",
        ),
        (
            "meta fn read<T:{mut id:i8,..R}>(value:T)->i8{value.id}\nmeta let STORED=.{id:7}\nmeta let _=read(.{..STORED})",
            "E0301",
        ),
        (
            "meta fn read<T:{mut id:i8,..R}>(value:T)->i8{value.id}\nmeta let _=read(.{id:128})",
            "E0326",
        ),
    ] {
        let outcome = session(source, "pointer64").check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
            "{source}\n{outcome:?}"
        );
    }
}
