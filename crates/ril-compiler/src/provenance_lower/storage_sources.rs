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
    let mut work = crate::sema::source_types::WorkLimit::new(4_000_000);
    let retained = facts.source_types.retained(&mut work).map_err(|error| {
        NotImplemented::new(
            ril_compiler_core::phase::Stage::Lowering,
            format!("binding Source graph could not be retained: {error}"),
        )
    })?;
    work.charge(facts.binding_sources.len()).map_err(|error| {
        NotImplemented::new(
            ril_compiler_core::phase::Stage::Lowering,
            format!("binding Source receipts could not be retained: {error}"),
        )
    })?;
    graph.binding_sources = facts
        .binding_sources
        .iter()
        .map(|value| {
            Ok(p::BindingSource {
                binding: value.binding as u32,
                context: resumption_context(value.context),
                activation: value.activation.0,
                declaration: value.declaration,
                declared: value.declared,
                initializer: observation(value.initializer),
                path: value.path.clone(),
                root: retained
                    .binding_root(value.binding, &mut work)
                    .map_err(|error| {
                        NotImplemented::new(
                            ril_compiler_core::phase::Stage::Lowering,
                            format!("binding Source root could not be retained: {error}"),
                        )
                    })?,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    work.charge(facts.storage_writes.len()).map_err(|error| {
        NotImplemented::new(
            ril_compiler_core::phase::Stage::Lowering,
            format!("storage Source receipts could not be retained: {error}"),
        )
    })?;
    graph.storage_writes = facts
        .storage_writes
        .iter()
        .map(|value| {
            let expected = value
                .expected
                .map(|view| {
                    let (_, environment) = facts.source_types.view_schema(view, None, &mut work)?;
                    Ok::<_, crate::sema::source_types::SourceTypesError>(p::SourceView {
                        ty: retained.view_root(view, &mut work)?,
                        environment: contracts.environment(&mut graph.types, &environment),
                    })
                })
                .transpose()
                .map_err(|error| {
                    NotImplemented::new(
                        ril_compiler_core::phase::Stage::Lowering,
                        format!("storage Source view could not be retained: {error}"),
                    )
                })?;
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
