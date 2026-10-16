//! Export the sealed, checked arena without looking up expression facts by span.
use super::*;
use ril_compiler_core::ids::{ConstGraphId, ConstNodeId, ConstRef};
use ril_ir::constants::{ConstGraph, ConstNode};

pub(super) fn lower(
    facts: &crate::sema::SemanticFacts,
    provenance: &ril_ir::provenance::Graph,
) -> Result<Vec<ConstGraph>, NotImplemented> {
    if facts.constant_pool.nodes.is_empty() {
        return Ok(vec![]);
    }
    let witnesses: std::collections::BTreeMap<_, _> = provenance
        .constant_values
        .iter()
        .map(|(reference, value)| (*reference, value))
        .collect();
    if witnesses.len() != provenance.constant_values.len() {
        return Err(unsupported("duplicate constant arena semantic certificate"));
    }
    let mut nodes = Vec::with_capacity(facts.constant_pool.nodes.len());
    for (index, node) in facts.constant_pool.nodes.iter().enumerate() {
        let id = ConstNodeId(index as u32);
        let reference = ConstRef {
            graph: ConstGraphId(0),
            node: id,
        };
        let value = witnesses
            .get(&reference)
            .map(|value| (*value).clone())
            .ok_or_else(|| unsupported("constant arena node lacks its semantic certificate"))?;
        if !matches!(
            value.publication,
            ril_ir::provenance::Publication::Immutable
        ) || !matches!(value.permission, ril_ir::provenance::Permission::Read)
        {
            return Err(unsupported(
                "constant arena has an unpublished or writable node",
            ));
        }
        nodes.push(ConstNode {
            id,
            kind: node.kind.clone(),
            value,
            fixed_array_length: node.fixed_array_length,
        });
    }
    Ok(vec![ConstGraph {
        id: ConstGraphId(0),
        nodes,
    }])
}
