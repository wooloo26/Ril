//! Copy window recipes through the existing shared packet/heap exporter.
use super::*;

fn info(
    info: &crate::sema::WindowInfo,
    contracts: &mut ReturnContracts,
) -> Result<p::PatternWindowInfo, NotImplemented> {
    contracts.source_query(|_, work| {
        work.charge(5 + info.backing.nodes.len() + info.backing.choices.len())?;
        for alternatives in info.backing.choices.values() {
            work.charge(alternatives.len())?;
            for nodes in alternatives {
                work.charge(nodes.len())?;
            }
        }
        Ok(())
    })?;
    Ok(p::PatternWindowInfo {
        pattern: info.pattern,
        constant: info.constant,
        backing: info.backing.nodes.iter().copied().map(origin).collect(),
        choices: info
            .backing
            .choices
            .iter()
            .map(|(&branch, alternatives)| {
                (
                    branch,
                    alternatives
                        .iter()
                        .map(|nodes| nodes.iter().copied().map(origin).collect())
                        .collect(),
                )
            })
            .collect(),
        lower: info.lower,
        length: info.length,
        span: info.span,
        cause: info.cause,
    })
}

pub(super) fn lower(
    facts: &SemanticFacts,
    graph: &mut p::Graph,
    contracts: &mut ReturnContracts,
) -> Result<(), NotImplemented> {
    contracts
        .source_query(|_, work| work.charge(facts.windows.len() + facts.pattern_windows.len()))?;
    graph.windows = facts
        .windows
        .iter()
        .map(|(&node, window)| {
            let info = info(window, contracts)?;
            Ok(p::Window {
                pattern: info.pattern,
                constant: info.constant,
                origin: origin(node),
                backing: info.backing,
                choices: info.choices,
                lower: info.lower,
                length: info.length,
                span: info.span,
                cause: info.cause,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    graph.pattern_windows = facts
        .pattern_windows
        .iter()
        .map(|creation| {
            contracts.source_query(|_, work| work.charge(6 + creation.parents.len()))?;
            contracts.source_query(|_, work| {
                let node = &creation.output_node;
                work.charge(
                    1 + node.fact.fields.len() + node.fact.writable_roots.len() + node.fields.len(),
                )?;
                let slot = |slot: &f::Slot, work: &mut crate::sema::source_types::WorkLimit| {
                    work.charge(1)?;
                    match slot {
                        f::Slot::Field(name) => work.text(name),
                        f::Slot::RowTail(
                            m::rows::RowIdentity::Binder(name)
                            | m::rows::RowIdentity::Fresh { owner: name, .. },
                        ) => work.text(name),
                        _ => Ok(()),
                    }
                };
                for (key, origins) in &node.fact.fields {
                    slot(key, work)?;
                    work.charge(origins.len())?;
                }
                for (key, value) in &node.fields {
                    slot(key, work)?;
                    let mut remaining = work.remaining();
                    let admitted =
                        crate::sema::evaluated::charge_value_export(value, &mut remaining);
                    work.charge(work.remaining() - remaining)?;
                    admitted?;
                }
                Ok(())
            })?;
            let input = contracts.packet(&mut graph.types, &creation.input, creation.info.span)?;
            let output =
                contracts.packet(&mut graph.types, &creation.output, creation.info.span)?;
            let heap =
                contracts.packet_heap(&mut graph.types, &creation.heap, creation.info.span)?;
            let parents = creation
                .parents
                .iter()
                .map(|parent| {
                    Ok(p::PatternWindowInput {
                        node: origin(parent.node),
                        origin: match parent.origin {
                            crate::sema::pattern_windows::PatternWindowOrigin::Pattern(index) => {
                                p::PatternWindowOrigin::Pattern(index as u64)
                            }
                            crate::sema::pattern_windows::PatternWindowOrigin::Constant(
                                reference,
                            ) => p::PatternWindowOrigin::Constant(reference),
                        },
                        info: info(&parent.info, contracts)?,
                    })
                })
                .collect::<Result<_, NotImplemented>>()?;
            Ok(p::PatternWindowCreation {
                allocation: p::AllocationEventId(creation.allocation.0),
                root: creation.root,
                rest: creation.rest,
                anchor: creation.anchor,
                context: resumption_context(creation.context),
                owner: creation.owner.0,
                input,
                output,
                heap,
                parents,
                prefix: creation.prefix,
                suffix: creation.suffix,
                output_node: copy_node(
                    &creation.output_node,
                    creation.info.span,
                    &mut graph.types,
                    contracts,
                ),
                info: info(&creation.info, contracts)?,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    Ok(())
}
