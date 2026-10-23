//! Declaration shape constraints for symbolic assumptions. This operation
//! reads complete Source; runtime Ty and current array cardinalities are not
//! inputs. It never changes authority or claims that a member family exists.
use super::{
    facts::{Heap, NodeId, OriginKind, Slot},
    model::Value,
    source_types::{
        SourceContainer, SourceLength, SourceNode, SourceSchema, SourceTypeId, SourceTypesError,
        WorkLimit,
    },
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn assumed_array_lengths(
    source: &SourceSchema,
    value: &Value,
    heap: &Heap,
    fields: &BTreeMap<(NodeId, Slot), Value>,
    work: &mut WorkLimit,
) -> Result<BTreeMap<NodeId, u64>, SourceTypesError> {
    // Completeness is checked in the source's own immutable snapshot.
    if !source.equivalent(source, work)? {
        return Err(SourceTypesError::InvalidEvidence(
            "a shape assumption needs a consistent declaration graph".into(),
        ));
    }
    let (types, root) = source.graph();
    work.charge(1)?;
    let mut pending = vec![(root, value)];
    let mut seen = BTreeSet::<(SourceTypeId, Vec<NodeId>)>::new();
    let mut lengths = BTreeMap::new();
    while let Some((source, value)) = pending.pop() {
        work.charge(2 + value.origins.nodes.len())?;
        if !seen.insert((source, value.origins.nodes.iter().copied().collect())) {
            continue;
        }
        match types.get(source)? {
            SourceNode::Alias { target, .. } => pending.push((*target, value)),
            SourceNode::Array { length, element } => {
                if let SourceLength::Fixed(length) = length {
                    for node in &value.origins.nodes {
                        work.charge(2)?;
                        if !heap
                            .nodes
                            .get(node.0 as usize)
                            .is_some_and(|node| matches!(node.kind, OriginKind::Formal(_)))
                        {
                            return Err(SourceTypesError::InvalidEvidence(
                                "a Source assumption cannot select the length of physical storage"
                                    .into(),
                            ));
                        }
                        if lengths
                            .insert(*node, *length)
                            .is_some_and(|prior| prior != *length)
                        {
                            return Err(SourceTypesError::InvalidEvidence(
                                "one symbolic array has conflicting declared dimensions".into(),
                            ));
                        }
                    }
                }
                for node in &value.origins.nodes {
                    for ((_, slot), child) in fields
                        .range((*node, Slot::Field(String::new()))..)
                        .take_while(|((parent, _), _)| parent == node)
                    {
                        work.charge(1)?;
                        if matches!(slot, Slot::Index(_) | Slot::AnyIndex) {
                            pending.push((*element, child));
                        }
                    }
                }
            }
            SourceNode::Tuple(items) => {
                work.charge(items.len().saturating_mul(value.origins.nodes.len()))?;
                for (index, ty) in items.iter().enumerate() {
                    let slot = Slot::Tuple(
                        u32::try_from(index).map_err(|_| SourceTypesError::IdentityExhausted)?,
                    );
                    for node in &value.origins.nodes {
                        if let Some(child) = fields.get(&(*node, slot.clone())) {
                            pending.push((*ty, child));
                        }
                    }
                }
            }
            SourceNode::Record {
                fields: members,
                row,
            } => {
                work.charge(members.len().saturating_mul(value.origins.nodes.len()))?;
                for member in members {
                    work.text(&member.label)?;
                    for node in &value.origins.nodes {
                        if let Some(child) = fields.get(&(*node, Slot::Field(member.label.clone())))
                        {
                            pending.push((member.value, child));
                        }
                    }
                }
                if let Some(row) = row {
                    pending.push((*row, value));
                }
            }
            SourceNode::Map {
                key,
                value: element,
            } => {
                for node in &value.origins.nodes {
                    for ((_, slot), child) in fields
                        .range((*node, Slot::Field(String::new()))..)
                        .take_while(|((parent, _), _)| parent == node)
                    {
                        work.charge(1)?;
                        if matches!(slot, Slot::Field(name) if name == "key") {
                            pending.push((*key, child));
                        } else if matches!(slot, Slot::Index(_) | Slot::AnyIndex) {
                            pending.push((*element, child));
                        }
                    }
                }
            }
            SourceNode::Container { kind, arguments } => match (kind, arguments.as_slice()) {
                (SourceContainer::Immutable, [inner]) => pending.push((*inner, value)),
                (SourceContainer::Option, [inner]) => {
                    if let Some(payload) = &value.option_payload {
                        pending.push((*inner, payload));
                    }
                }
                (SourceContainer::Result, [ok, error]) => {
                    if let Some(payload) = &value.result_success {
                        pending.push((*ok, payload));
                    }
                    if let Some(payload) = &value.result_error {
                        pending.push((*error, payload));
                    }
                    if let Some(payload) = &value.result_payload
                        && let Some(success) = value.result_tag
                    {
                        pending.push((if success { *ok } else { *error }, payload));
                    }
                }
                (
                    SourceContainer::Set
                    | SourceContainer::Range
                    | SourceContainer::Heap
                    | SourceContainer::Deque,
                    [inner],
                ) => {
                    for node in &value.origins.nodes {
                        for ((_, slot), child) in fields
                            .range((*node, Slot::Field(String::new()))..)
                            .take_while(|((parent, _), _)| parent == node)
                        {
                            work.charge(1)?;
                            if matches!(slot, Slot::Index(_) | Slot::AnyIndex) {
                                pending.push((*inner, child));
                            }
                        }
                    }
                }
                _ => return Err(SourceTypesError::InvalidContainer),
            },
            SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. } => {
                return Err(SourceTypesError::Unresolved);
            }
            _ => {}
        }
    }
    Ok(lengths)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        facts::{ScopeId, SiteId},
        model::Ty,
        relations::Pivot,
        source_types::{SourceBuilder, SourceField, SourceScalar},
    };
    use ril_compiler_core::diagnostic::CauseId;

    #[test]
    fn nested_source_dimensions_constrain_symbolic_members_without_runtime_types() {
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let int = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let inner = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: int,
                },
                &mut work,
            )
            .unwrap();
        let outer = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: inner,
                },
                &mut work,
            )
            .unwrap();
        let record = builder
            .insert(
                SourceNode::Record {
                    fields: vec![SourceField {
                        label: "items".into(),
                        mutable: false,
                        value: outer,
                    }],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let schema = SourceSchema::frozen_view(&types, record, None, &mut work).unwrap();
        let mut heap = Heap::default();
        let root = heap.symbolic(Pivot(0), ScopeId(0), CauseId(0));
        let outer_node = heap.symbolic(Pivot(1), ScopeId(0), CauseId(0));
        let inner_node = heap.symbolic(Pivot(2), ScopeId(0), CauseId(0));
        let value = Value::reference(Ty::Unknown, root, CauseId(0));
        let fields = [
            (
                (root, Slot::Field("items".into())),
                Value::reference(Ty::Unknown, outer_node, CauseId(0)),
            ),
            (
                (outer_node, Slot::AnyIndex),
                Value::reference(Ty::Unknown, inner_node, CauseId(0)),
            ),
        ]
        .into();
        assert_eq!(
            assumed_array_lengths(&schema, &value, &heap, &fields, &mut work).unwrap(),
            [(outer_node, 0), (inner_node, 2)].into()
        );
        assert!(
            assumed_array_lengths(&schema, &value, &heap, &fields, &mut WorkLimit::new(0)).is_err()
        );
        heap.nodes[inner_node.0 as usize].kind = OriginKind::Fresh(SiteId(0));
        assert!(
            assumed_array_lengths(&schema, &value, &heap, &fields, &mut work).is_err(),
            "a hypothetical type cannot reclassify physical storage"
        );
    }

    #[test]
    fn map_key_edges_and_shared_nodes_cannot_hide_conflicting_dimensions() {
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let int = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let two = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: int,
                },
                &mut work,
            )
            .unwrap();
        let three = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(3),
                    element: int,
                },
                &mut work,
            )
            .unwrap();
        let root = builder
            .insert(
                SourceNode::Map {
                    key: two,
                    value: three,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let schema = SourceSchema::frozen_view(&types, root, None, &mut work).unwrap();
        let mut heap = Heap::default();
        let root = heap.symbolic(Pivot(0), ScopeId(0), CauseId(0));
        let shared = heap.symbolic(Pivot(1), ScopeId(0), CauseId(0));
        let value = Value::reference(Ty::Unknown, root, CauseId(0));
        let child = Value::reference(Ty::Unknown, shared, CauseId(0));
        let fields = [
            ((root, Slot::Field("key".into())), child.clone()),
            ((root, Slot::AnyIndex), child),
        ]
        .into();
        assert!(assumed_array_lengths(&schema, &value, &heap, &fields, &mut work).is_err());
    }
}
