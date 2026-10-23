//! Transport a saved may-graph through actual allocation-recency transitions.
//! This module has no eligibility policy: the caller must establish ordinary
//! data before using its join at a loop or conditional boundary.
use super::*;

pub(super) fn reachable(
    fields: &BTreeMap<(NodeId, Slot), Value>,
    roots: impl IntoIterator<Item = NodeId>,
) -> BTreeSet<NodeId> {
    let mut nodes = BTreeSet::new();
    let mut pending: Vec<_> = roots.into_iter().collect();
    while let Some(node) = pending.pop() {
        if !nodes.insert(node) {
            continue;
        }
        for ((parent, _), value) in fields {
            if *parent == node {
                pending.extend(&value.origins.nodes);
            }
        }
    }
    nodes
}

pub(super) fn transport_values(
    values: &mut BTreeMap<BindingId, Value>,
    moves: &[(NodeId, NodeId)],
) {
    for &(recent, older) in moves {
        for value in values.values_mut() {
            copy::remap_value_origins(value, recent, older);
        }
    }
}

pub(super) fn transport_nodes(nodes: &mut BTreeSet<NodeId>, moves: &[(NodeId, NodeId)]) {
    for &(recent, older) in moves {
        if nodes.remove(&recent) {
            nodes.insert(older);
        }
    }
}

pub(super) fn transport_fields(
    fields: &mut BTreeMap<(NodeId, Slot), Value>,
    moves: &[(NodeId, NodeId)],
    branch: u32,
    cause: CauseId,
) {
    for &(recent, older) in moves {
        let previous = std::mem::take(fields);
        for ((parent, slot), mut value) in previous {
            copy::remap_value_origins(&mut value, recent, older);
            let key = (if parent == recent { older } else { parent }, slot);
            if let Some(existing) = fields.remove(&key) {
                value = existing.join(&value, branch, cause);
                forget_choices(&mut value);
            }
            fields.insert(key, value);
        }
    }
}

pub(super) use super::super::model::forget_choices;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recency_transport_contains_every_concrete_small_graph_path() {
        // The oracle is a separate concrete adjacency matrix. Exhaust graphs
        // on three objects, including self/back edges and shared descendants.
        for edges in 0u16..512 {
            let mut fields = BTreeMap::new();
            for a in 0..3u32 {
                for b in 0..3u32 {
                    if edges & (1 << (a * 3 + b)) != 0 {
                        let mut value = Value::scalar(Ty::Unit, None, CauseId(0));
                        value.origins = Origins::one(NodeId(b));
                        fields.insert((NodeId(a), Slot::Tuple(b)), value);
                    }
                }
            }
            let movement = [(NodeId(0), NodeId(3)), (NodeId(1), NodeId(3))];
            transport_fields(&mut fields, &movement, 0, CauseId(0));
            let map = |node: u32| if node < 2 { NodeId(3) } else { NodeId(node) };
            for root in 0..3u32 {
                let mut concrete = [false; 3];
                concrete[root as usize] = true;
                for _ in 0..3 {
                    for a in 0..3 {
                        for b in 0..3 {
                            if concrete[a] && edges & (1 << (a * 3 + b)) != 0 {
                                concrete[b] = true;
                            }
                        }
                    }
                }
                let mut abstract_nodes = BTreeSet::from([map(root)]);
                loop {
                    let previous = abstract_nodes.clone();
                    for ((parent, _), value) in &fields {
                        if previous.contains(parent) {
                            abstract_nodes.extend(&value.origins.nodes);
                        }
                    }
                    if previous == abstract_nodes {
                        break;
                    }
                }
                for (node, reachable) in concrete.into_iter().enumerate() {
                    assert!(!reachable || abstract_nodes.contains(&map(node as u32)));
                }
            }
        }
    }

    #[test]
    fn collision_join_keeps_aliases_and_only_restricts_permissions() {
        let mut writer = Value::scalar(Ty::Unit, None, CauseId(0));
        writer.origins = Origins::one(NodeId(2));
        writer.permission = Permission::Write;
        writer.publication = Publication::Live;
        let mut reader = writer.clone();
        reader.permission = Permission::Read;
        let mut fields = [
            ((NodeId(0), Slot::Tuple(0)), writer),
            ((NodeId(1), Slot::Tuple(0)), reader),
        ]
        .into();
        transport_fields(&mut fields, &[(NodeId(0), NodeId(1))], 0, CauseId(0));
        let merged = &fields[&(NodeId(1), Slot::Tuple(0))];
        assert_eq!(merged.permission, Permission::Read);
        assert_eq!(merged.publication, Publication::Live);
        assert_eq!(merged.origins.nodes, [NodeId(2)].into());
        assert!(merged.origins.choices.is_empty());
    }
}
