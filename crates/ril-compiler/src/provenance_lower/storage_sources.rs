//! Preserve original declarations and physical write coordinates in Core.
use super::*;
use crate::sema::storage_sources as source;

fn observation(value: source::StorageObservation) -> p::StorageObservation {
    p::StorageObservation {
        expression: value.expression,
        allocation_epoch: value.allocation_epoch,
    }
}

pub(super) fn lower(facts: &SemanticFacts, graph: &mut p::Graph) {
    graph.binding_sources = facts
        .binding_sources
        .iter()
        .map(|value| p::BindingSource {
            binding: value.binding as u32,
            context: resumption_context(value.context),
            activation: value.activation.0,
            declaration: value.declaration,
            declared: value.declared,
            initializer: observation(value.initializer),
            path: value.path.iter().map(projection).collect(),
            key: value.key.as_ref().map(record_bounds::key),
        })
        .collect();
    graph.storage_writes = facts
        .storage_writes
        .iter()
        .map(|value| p::StorageWrite {
            target: value.target,
            context: resumption_context(value.context),
            activation: value.activation.0,
            span: value.span,
            operator: value.operator.clone(),
            rhs: observation(value.rhs),
            destination: match &value.destination {
                source::StorageDestination::Binding(binding) => {
                    p::StorageDestination::Binding(*binding as u32)
                }
                source::StorageDestination::Projection {
                    receiver,
                    selector,
                    slot,
                } => p::StorageDestination::Projection {
                    receiver: observation(*receiver),
                    selector: selector.map(observation),
                    slot: projection(slot),
                },
            },
            expected: value.expected.as_ref().map(record_bounds::key),
            completed: value.completed,
        })
        .collect();
}
