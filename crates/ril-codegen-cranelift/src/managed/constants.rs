//! A constant node is allocated once, then read through a program-owned cell.
use super::*;
use ril_compiler_core::{ids::ConstRef, source::Span};
use ril_ir::{constants::ConstNodeKind, provenance};
use std::collections::{BTreeMap, VecDeque};

pub(crate) struct Pool {
    pub names: HashMap<ConstRef, String>,
    nodes: Vec<Node>,
}
#[derive(Clone)]
struct Node {
    reference: ConstRef,
    kind: ConstNodeKind,
    span: Span,
}

fn edges(kind: &ConstNodeKind) -> Vec<ConstRef> {
    match kind {
        ConstNodeKind::Literal(_) => vec![],
        ConstNodeKind::Tuple(items) | ConstNodeKind::Array(items) => items.clone(),
        ConstNodeKind::Map(entries) => entries
            .iter()
            .flat_map(|(key, value)| [*key, *value])
            .collect(),
        ConstNodeKind::Record(fields) => fields.iter().map(|(_, value)| *value).collect(),
        ConstNodeKind::Variant { payload, .. } => payload.iter().copied().collect(),
    }
}

pub(super) fn prepare(input: &native::Module) -> Result<Pool, BackendError> {
    let mut graphs = HashSet::new();
    let mut nodes = BTreeMap::new();
    for graph in &input.constant_graphs {
        if !graphs.insert(graph.id) {
            return Err(BackendError::InvalidIr(
                "duplicate constant graph identity".into(),
            ));
        }
        for node in &graph.nodes {
            let reference = ConstRef {
                graph: graph.id,
                node: node.id,
            };
            if nodes.insert(reference, node).is_some() {
                return Err(BackendError::InvalidIr(
                    "duplicate constant node identity".into(),
                ));
            }
            if !matches!(node.value.permission, provenance::Permission::Read)
                || !matches!(node.value.publication, provenance::Publication::Immutable)
                || !node.value.callables.is_empty()
                || !node.value.scoped_bindings.is_empty()
                || !node.value.pending_copies.is_empty()
                || node.value.flags.temporary
                || node.value.flags.mutable_environment
                || node.value.flags.observer_environment
            {
                return Err(BackendError::InvalidIr(
                    "constant node lacks immutable ordinary-data evidence".into(),
                ));
            }
            if let Some(length) = node.fixed_array_length
                && !matches!(&node.kind, ConstNodeKind::Array(items) if items.len() as u64 == length)
            {
                return Err(BackendError::InvalidIr(
                    "constant fixed-array shape differs from its witness".into(),
                ));
            }
            if let ConstNodeKind::Record(fields) = &node.kind {
                let unique: HashSet<_> = fields.iter().map(|(name, _)| name).collect();
                if unique.len() != fields.len() {
                    return Err(BackendError::InvalidIr(
                        "duplicate constant record field".into(),
                    ));
                }
            }
        }
    }
    // Kahn's algorithm counts edges rather than unfolding shared subgraphs.
    // Repeated edges are retained: equal contents never merge node identities.
    let mut pending = HashMap::new();
    let mut parents: HashMap<ConstRef, Vec<ConstRef>> = HashMap::new();
    let mut ready = VecDeque::new();
    let mut names = HashMap::new();
    for (&reference, node) in &nodes {
        let name = format!("\0ril.const.{}.{}", reference.graph.0, reference.node.0);
        if input.global_bindings.contains(&name) {
            return Err(BackendError::InvalidIr(
                "constant pool cell conflicts with a global binding".into(),
            ));
        }
        names.insert(reference, name);
        let dependencies = edges(&node.kind);
        pending.insert(reference, dependencies.len());
        if dependencies.is_empty() {
            ready.push_back(reference);
        }
        for child in dependencies {
            if !nodes.contains_key(&child) {
                return Err(BackendError::InvalidIr(
                    "constant graph contains an unknown node reference".into(),
                ));
            }
            parents.entry(child).or_default().push(reference);
        }
    }
    let mut order = Vec::with_capacity(nodes.len());
    while let Some(reference) = ready.pop_front() {
        let node = nodes[&reference];
        order.push(Node {
            reference,
            kind: node.kind.clone(),
            span: node.value.span,
        });
        for parent in parents.get(&reference).into_iter().flatten() {
            let count = pending
                .get_mut(parent)
                .expect("validated constant dependency");
            *count -= 1;
            if *count == 0 {
                ready.push_back(*parent);
            }
        }
    }
    if order.len() != nodes.len() {
        return Err(unsupported(
            "cyclic constant graphs require shell initialization",
        ));
    }
    Ok(Pool {
        names,
        nodes: order,
    })
}

impl Emitter<'_, '_> {
    pub(super) fn constant_ref(&mut self, reference: ConstRef) -> Result<Value, BackendError> {
        let name = self
            .program
            .constants
            .names
            .get(&reference)
            .cloned()
            .ok_or_else(|| {
                BackendError::InvalidIr(
                    "constant expression references an unknown pool node".into(),
                )
            })?;
        self.name(&name)
    }

    pub(super) fn initialize_constants(&mut self) -> Result<(), BackendError> {
        for node in self.program.constants.nodes.clone() {
            self.locate(node.span)?;
            let value = self.constant_node(&node.kind)?;
            // Every allocation above goes through handle(), which roots its
            // result before the publishing cell or its key can allocate.
            let cell = self.handle("ril_rt_cell", &[value])?;
            let name = self.program.constants.names[&node.reference].clone();
            let key = self.string(&name)?;
            self.handle("ril_rt_global_set", &[key, cell])?;
        }
        Ok(())
    }

    fn constant_node(&mut self, kind: &ConstNodeKind) -> Result<Value, BackendError> {
        match kind {
            ConstNodeKind::Literal(literal) => self.literal(literal),
            ConstNodeKind::Tuple(items) | ConstNodeKind::Array(items) => {
                let values = items
                    .iter()
                    .map(|reference| self.constant_ref(*reference))
                    .collect::<Result<Vec<_>, _>>()?;
                self.sequence(
                    if matches!(kind, ConstNodeKind::Array(_)) {
                        0
                    } else {
                        1
                    },
                    &values,
                )
            }
            ConstNodeKind::Map(entries) => {
                let map = self.handle("ril_rt_map", &[])?;
                for (key, value) in entries {
                    let key = self.constant_ref(*key)?;
                    let value = self.constant_ref(*value)?;
                    self.handle("ril_rt_map_set", &[map, key, value])?;
                }
                Ok(map)
            }
            ConstNodeKind::Record(fields) => {
                let record = self.handle("ril_rt_record", &[])?;
                for (name, value) in fields {
                    let value = self.constant_ref(*value)?;
                    let key = self.string(name)?;
                    self.handle("ril_rt_set_field", &[record, key, value])?;
                }
                Ok(record)
            }
            ConstNodeKind::Variant { tag, payload } => {
                let tag = match tag.as_str() {
                    "Prelude::Some" => "Some",
                    "Prelude::None" => "None",
                    "Prelude::Ok" => "Ok",
                    "Prelude::Err" => "Err",
                    tag => tag,
                };
                let mut fields = Vec::new();
                if let Some(payload) = payload {
                    fields.push(self.constant_ref(*payload)?);
                }
                let fields = self.sequence(1, &fields)?;
                let tag = self.string(tag)?;
                self.handle("ril_rt_variant", &[tag, fields])
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::{
        diagnostic::CauseId,
        ids::{ConstGraphId, ConstNodeId, TypeId},
        source::FileId,
    };
    use ril_ir::constants::{ConstGraph, ConstNode};

    fn reference(graph: u32, node: u32) -> ConstRef {
        ConstRef {
            graph: ConstGraphId(graph),
            node: ConstNodeId(node),
        }
    }

    fn node(id: u32, kind: ConstNodeKind) -> ConstNode {
        ConstNode {
            id: ConstNodeId(id),
            kind,
            fixed_array_length: None,
            value: provenance::Value {
                source_type_witness: None,
                numeric: Default::default(),
                condition_inspections: Default::default(),
                span: Span {
                    file: FileId(0),
                    start: 1,
                    end: 2,
                },
                ty: TypeId(0),
                origins: vec![],
                choices: vec![],
                permission: provenance::Permission::Read,
                publication: provenance::Publication::Immutable,
                participants: vec![],
                sources: vec![],
                callback_parameters: vec![],
                results: vec![],
                outer_results: vec![],
                must_results: vec![],
                must_outer_results: vec![],
                scoped_bindings: vec![],
                result_payload: None,
                result_success: None,
                result_error: None,
                result_tag: None,
                option_payload: None,
                option_tag: None,
                variant_tag: None,
                variant_payload: None,
                variant_witnesses: BTreeMap::new(),
                abnormal: false,
                callables: vec![],
                callable_bounds: vec![],
                callable_returns: vec![],
                signature: None,
                constant: None,
                static_coordinate: None,
                pending_inference: vec![],
                pending_copies: vec![],
                flags: provenance::ValueFlags::default(),
                cause: CauseId(0),
            },
        }
    }

    fn module(nodes: Vec<ConstNode>) -> native::Module {
        native::Module {
            constant_graphs: vec![ConstGraph {
                id: ConstGraphId(7),
                nodes,
            }],
            ..Default::default()
        }
    }

    #[test]
    fn sparse_cross_graph_ids_and_repeated_edges_preserve_each_node_once() {
        let mut input = module(vec![node(
            99,
            ConstNodeKind::Tuple(vec![reference(2, 50); 2]),
        )]);
        input.constant_graphs.push(ConstGraph {
            id: ConstGraphId(2),
            nodes: vec![
                node(50, ConstNodeKind::Array(vec![])),
                node(60, ConstNodeKind::Array(vec![])),
            ],
        });
        let prepared = prepare(&input).unwrap();
        let order: Vec<_> = prepared.nodes.iter().map(|node| node.reference).collect();
        assert_eq!(
            order,
            [reference(2, 50), reference(2, 60), reference(7, 99)]
        );
        assert_ne!(
            prepared.names[&reference(2, 50)],
            prepared.names[&reference(2, 60)]
        );

        let mut nodes = vec![node(0, ConstNodeKind::Array(vec![]))];
        for id in 1..=64 {
            nodes.push(node(
                id,
                ConstNodeKind::Tuple(vec![reference(7, id - 1); 2]),
            ));
        }
        let prepared = prepare(&module(nodes)).unwrap();
        assert_eq!(prepared.nodes.len(), 65, "do not unfold the binary DAG");
    }

    #[test]
    fn malformed_identity_edges_publication_and_lengths_fail_closed() {
        let valid = module(vec![node(0, ConstNodeKind::Array(vec![]))]);
        for change in 0..7 {
            let mut input = valid.clone();
            match change {
                0 => input.constant_graphs.push(input.constant_graphs[0].clone()),
                1 => input.constant_graphs[0]
                    .nodes
                    .push(node(0, ConstNodeKind::Array(vec![]))),
                2 => {
                    input.constant_graphs[0].nodes[0].kind =
                        ConstNodeKind::Array(vec![reference(7, 9)])
                }
                3 => {
                    input.constant_graphs[0].nodes[0].value.permission =
                        provenance::Permission::Write
                }
                4 => {
                    input.constant_graphs[0].nodes[0].value.publication =
                        provenance::Publication::Live
                }
                5 => input.constant_graphs[0].nodes[0].fixed_array_length = Some(1),
                _ => {
                    input.global_bindings.insert("\0ril.const.7.0".into());
                }
            }
            assert!(
                matches!(prepare(&input), Err(BackendError::InvalidIr(_))),
                "case {change}"
            );
        }
        let cycle = module(vec![node(0, ConstNodeKind::Array(vec![reference(7, 0)]))]);
        assert!(
            prepare(&cycle).is_err(),
            "cycles require a separate shell-initialization contract"
        );
    }
}
