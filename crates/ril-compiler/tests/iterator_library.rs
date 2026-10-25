//! Iterator adapters are ordinary declarations with latent closure bodies.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, Session};

fn indexed_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::generated-indexed-iterator")
}
fn pipeline_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::generated-map-filter-take")
}

fn verified(source: &str, target: &str) -> SemanticFacts {
    let snapshot = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .analyze();
    assert_eq!(
        snapshot.status(),
        ril_compiler::AnalysisStatus::Verified,
        "{target}\n{source}\n{:?}\n{:?}",
        snapshot.outcome(),
        snapshot.unresolved()
    );
    let program = snapshot.into_verified().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn ordinary_adapters_keep_declared_bodies_and_full_argument_types() {
    for source in [
        indexed_fixture(),
        pipeline_fixture(),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generated-iterator-nested-empty-extent",
        ),
    ] {
        for layout in ["pointer32", "pointer64"] {
            let facts = verified(source, layout);
            let library = facts
                .functions
                .iter()
                .filter(|function| function.syntax.span.file.0 != 0)
                .collect::<Vec<_>>();
            assert_eq!(library.len(), 8);
            for function in library {
                assert!(function.hir_id.is_some());
                assert!(function.syntax.body.is_some());
            }
        }
    }
}

#[test]
fn typed_adapter_creation_keeps_callbacks_latent() {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::generated-iterator-deferred-named-callback",
    );
    for layout in ["pointer32", "pointer64"] {
        let facts = verified(source, layout);
        let tick = facts
            .functions
            .iter()
            .find(|function| function.syntax.name == "tick")
            .unwrap()
            .definition;
        assert!(
            !facts
                .copy_invocations
                .iter()
                .any(|call| call.target == tick && !call.declaration_probe),
            "creating an adapter must not add a phantom callback invocation"
        );
    }
}

#[test]
fn imported_iterator_definitions_are_checked_without_specialized_calls() {
    for target in ["pointer32", "pointer64"] {
        verified(
            ril_test::case_source("tests/regressions/ordinary-iteration.ril::imported-definitions"),
            target,
        );
    }
}

#[test]
fn generic_aliases_substitute_complete_argument_identities_in_their_own_scope() {
    for target in ["pointer32", "pointer64"] {
        verified(
            ril_test::case_source("tests/regressions/ordinary-iteration.ril::generic-alias-scope"),
            target,
        );
    }
}

#[test]
fn opaque_callbacks_cannot_replace_private_state_without_its_cell() {
    for target in ["pointer32", "pointer64"] {
        verified(
            ril_test::case_source(
                "tests/regressions/ordinary-iteration.ril::private-callback-state",
            ),
            target,
        );
    }
}
