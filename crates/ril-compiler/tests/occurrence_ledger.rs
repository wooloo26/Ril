use ril_compiler::{CheckOptions, Session, sema::SemanticFacts};
use ril_compiler_core::ids::EvaluationOccurrenceId;
use std::collections::{BTreeMap, BTreeSet};

fn facts(layout: &str) -> SemanticFacts {
    facts_for("application-repeated-ordinary-and-pipeline", layout)
}

fn facts_for(name: &str, layout: &str) -> SemanticFacts {
    let source = ril_test::case_source(&format!(
        "tests/regressions/evaluation-identity.ril::{name}"
    ));
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap();
    let _core = ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn repeated_nodes_have_distinct_occurrences_and_preserve_their_birth_epochs() {
    for layout in ["pointer32", "pointer64"] {
        let facts = facts(layout);
        let mut nodes = BTreeMap::<_, BTreeSet<_>>::new();
        for (index, record) in facts.evaluations.iter().enumerate() {
            assert_eq!(record.id, EvaluationOccurrenceId(index as u32));
            let identity = record.identity.unwrap();
            assert!(
                nodes
                    .entry(identity.source)
                    .or_default()
                    .insert(identity.activation)
            );
            assert_eq!(
                record.allocation_epoch,
                facts.expressions[index].allocation_epoch
            );
        }
        assert!(nodes.values().any(|activations| activations.len() > 1));
    }
}
