//! Nullary constructor reads have original declarations and receiving schemas.
use ril_compiler::{AnalysisStatus, CheckOptions, Session};

#[test]
fn nullary_constructors_cross_receiving_boundaries_without_inventing_payloads() {
    let source = ril_test::case_bytes(
        "tests/regressions/constructor-receiving.ril::none-receiving-pointer64",
    );
    for target in ["pointer32", "pointer64"] {
        let snapshot = Session::with_options(
            source.to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .analyze();
        assert_eq!(
            snapshot.status(),
            AnalysisStatus::Verified,
            "{target}: diagnostics={:?}; unresolved={:?}",
            snapshot.diagnostics(),
            snapshot.unresolved()
        );
        let program = snapshot.into_verified().unwrap();
        let facts = program.facts();
        let constructors: Vec<_> = facts
            .builtin_source_observations
            .iter()
            .filter(|row| {
                matches!(
                    row.full_header,
                    ril_compiler::sema::builtin_sources::BuiltinDeclaration::Nullary(_)
                )
            })
            .collect();
        assert!(!constructors.is_empty());
        for row in constructors {
            let value = &facts.expressions[row.expression].value;
            assert_eq!(value.option_tag, Some(false));
            assert!(value.option_payload.is_none());
            assert!(value.origins.nodes.is_empty());
        }
        let _core = ril_compiler::lower::lower_core(&program).unwrap();
        let _reads: std::collections::BTreeSet<_> = facts
            .builtin_source_observations
            .iter()
            .filter_map(|row| {
                matches!(
                    row.full_header,
                    ril_compiler::sema::builtin_sources::BuiltinDeclaration::Nullary(_)
                )
                .then_some(facts.expressions[row.expression].source_id.unwrap())
            })
            .collect();
    }
}

#[test]
fn absent_values_cannot_reselect_stored_coordinates_or_shadowed_declarations() {
    for name in [
        "reject-stored-none-dimension",
        "reject-shadowed-none-reinstantiation",
    ] {
        let source = ril_test::case_bytes(&format!(
            "tests/regressions/constructor-receiving.ril::{name}"
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
            assert_eq!(
                snapshot.status(),
                AnalysisStatus::Rejected,
                "{name} {target}: {:?}",
                snapshot.outcome()
            );
            assert!(
                snapshot
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{name} {target}: {:?}",
                snapshot.diagnostics()
            );
        }
    }
}
