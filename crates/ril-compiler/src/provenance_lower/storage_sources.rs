//! Preserve original declarations and physical write coordinates in Core.
use super::*;
use crate::sema::storage_sources as source;

fn observation(value: source::StorageObservation) -> p::StorageObservation {
    p::StorageObservation {
        expression: value.expression,
        allocation_epoch: value.allocation_epoch,
    }
}

pub(super) fn lower(
    facts: &SemanticFacts,
    graph: &mut p::Graph,
    contracts: &mut ReturnContracts,
) -> Result<(), NotImplemented> {
    let retained = contracts.source_query(|index, work| index.retained(work))?;
    contracts.source_query(|_, work| work.charge(facts.binding_sources.len()))?;
    graph.binding_sources = facts
        .binding_sources
        .iter()
        .map(|value| {
            Ok(p::BindingSource {
                receiver: value.receiver.map(|identity| p::OccurrenceIdentity {
                    source: identity.source,
                    activation: identity.activation,
                }),
                binding: value.binding as u32,
                context: resumption_context(value.context),
                activation: value.activation.0,
                declaration: value.declaration,
                declared: value.declared,
                initializer: observation(value.initializer),
                path: value.path.clone(),
                root: contracts
                    .source_query(|_, work| retained.binding_root(value.binding, work))?,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    contracts.source_query(|_, work| work.charge(facts.storage_writes.len()))?;
    graph.storage_writes = facts
        .storage_writes
        .iter()
        .map(|value| {
            let expected = value
                .expected
                .map(|view| {
                    let (root, environment) = contracts.source_query(|index, work| {
                        let (_, environment) = index.view_schema(view, None, work)?;
                        Ok((retained.view_root(view, work)?, environment))
                    })?;
                    Ok::<_, NotImplemented>(p::SourceView {
                        ty: root,
                        environment: contracts.environment(&mut graph.types, &environment),
                    })
                })
                .transpose()?;
            Ok(p::StorageWrite {
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
                expected,
                completed: value.completed,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    graph.source_types = retained.graph;
    Ok(())
}
