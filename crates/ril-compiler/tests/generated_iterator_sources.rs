//! Generated iterator syntax must remain connected to its true creation call.
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
fn actual_adapter_recipes_keep_real_sites_and_full_call_roots() {
    for source in [
        indexed_fixture(),
        pipeline_fixture(),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generated-iterator-nested-empty-extent",
        ),
    ] {
        for layout in ["pointer32", "pointer64"] {
            let facts = verified(source, layout);
            assert!(!facts.generated_sources.is_empty());
            for generated in &facts.generated_sources {
                assert_eq!(facts.closures[generated.closure].site, Some(generated.site));
                let event = &facts.copy_call_events[generated.origin_event.0 as usize];
                assert!(event.callee_expression.is_some() && event.result_expression.is_some());
                assert!(event.callee_expression < event.result_expression);
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
