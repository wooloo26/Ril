//! Export the sealed, checked arena without looking up expression facts by span.
use super::*;
use ril_compiler_core::ids::{ConstGraphId, ConstNodeId, ConstRef};
use ril_ir::constants::{ConstGraph, ConstNode};

pub(super) fn lower(facts: &crate::sema::SemanticFacts) -> Result<Vec<ConstGraph>, NotImplemented> {
    if facts.constant_pool.nodes.is_empty() {
        return Ok(vec![]);
    }
    let values: std::collections::BTreeMap<_, _> = facts
        .constant_values
        .iter()
        .map(|value| (value.reference, value))
        .collect();
    if values.len() != facts.constant_values.len() {
        return Err(unsupported("duplicate constant arena value"));
    }
    let mut nodes = Vec::with_capacity(facts.constant_pool.nodes.len());
    for (index, node) in facts.constant_pool.nodes.iter().enumerate() {
        let id = ConstNodeId(index as u32);
        let reference = ConstRef {
            graph: ConstGraphId(0),
            node: id,
        };
        let checked = values
            .get(&reference)
            .ok_or_else(|| unsupported("constant arena node was not analyzed"))?;
        let value = &checked.value;
        if !matches!(
            value.publication,
            crate::sema::facts::Publication::Immutable
        ) || !matches!(value.permission, crate::sema::facts::Permission::Read)
            || !value.callables.is_empty()
            || !value.scoped.is_empty()
            || !value.pending_copies.is_empty()
            || value.temporary
            || value.mutable_environment
            || value.observer_environment
        {
            return Err(unsupported(
                "constant arena contains data that is not immutable ordinary data",
            ));
        }
        nodes.push(ConstNode {
            id,
            kind: node.kind.clone(),
            span: checked.span,
            fixed_array_length: node.fixed_array_length,
        });
    }
    Ok(vec![ConstGraph {
        id: ConstGraphId(0),
        nodes,
    }])
}
