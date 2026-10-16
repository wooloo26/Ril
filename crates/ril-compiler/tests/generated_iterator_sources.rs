//! Generated iterator syntax must remain connected to its true creation call.
use ril_compiler::sema::{SemanticFacts, validate::solved_facts};
use ril_compiler::{CheckOptions, Session};

fn indexed_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::generated-indexed-iterator")
}
fn pipeline_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::generated-map-filter-take")
}

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
fn actual_adapter_recipes_keep_real_sites_and_full_call_roots() {
    for source in [indexed_fixture(), pipeline_fixture()] {
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
fn joint_generated_arenas_deletion_cannot_remove_the_creation_obligation() {
    let mut facts = verified(indexed_fixture(), "pointer64");
    facts.generated_sources.clear();
    facts.iter_steps.clear();
    assert!(solved_facts(&facts).is_err());
}

#[test]
fn a_generated_capture_or_source_recipe_cannot_borrow_another_origin() {
    let facts = verified(pipeline_fixture(), "pointer64");
    assert!(facts.generated_sources.len() >= 4);
    for mutation in 0..5 {
        let mut changed = facts.clone();
        match mutation {
            0 => {
                changed.generated_sources[0].origin_event =
                    changed.generated_sources[1].origin_event
            }
            1 => changed.generated_sources[0].closure = changed.generated_sources[1].closure,
            2 => changed.generated_sources[1].captures.swap(0, 1),
            3 => changed.generated_sources[0].origin_context.owner = None,
            4 => changed.generated_sources[0].captures[0]
                .path
                .push(ril_compiler::sema::facts::Slot::AnyIndex),
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "mutation {mutation} was authorized"
        );
    }
}

#[test]
fn missing_result_root_and_changed_canonical_body_supply_no_generated_source_proof() {
    let facts = verified(indexed_fixture(), "pointer64");
    for mutation in 0..2 {
        let mut changed = facts.clone();
        let event = changed.generated_sources[0].origin_event;
        if mutation == 0 {
            changed.copy_call_events[event.0 as usize].result_expression = None;
        } else {
            let syntax = std::sync::Arc::make_mut(&mut changed.generated_sources[0].syntax);
            syntax.span.start += 1;
        }
        assert!(
            solved_facts(&changed).is_err(),
            "mutation {mutation} was authorized"
        );
    }
}

#[test]
fn captured_operand_transport_cannot_replace_the_graph_schema_or_permission() {
    let facts = verified(indexed_fixture(), "pointer64");
    for mutation in 0..4 {
        let mut changed = facts.clone();
        let id = changed.generated_sources[0].captures[0].binding;
        match mutation {
            0 => changed.bindings[id].value.origins.nodes.clear(),
            1 => changed.bindings[id].value.source_type_witness = None,
            2 => {
                changed.bindings[id].value.permission = ril_compiler::sema::facts::Permission::Write
            }
            3 => {
                let cause = changed.explanations.add(
                    ril_compiler::sema::facts::CauseKind::Source,
                    None,
                    "another operand",
                    [],
                );
                changed.bindings[id].value.cause = cause;
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "capture mutation {mutation} was authorized"
        );
    }
}
