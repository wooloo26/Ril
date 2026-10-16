use super::*;
pub(super) fn remap_value_origins(value: &mut Value, recent: NodeId, older: NodeId) {
    value.origins.remap(recent, older);
    for payload in [
        &mut value.variant_payload,
        &mut value.option_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        remap_value_origins(payload, recent, older);
    }
}
pub(super) fn remap_summary(
    summary: &mut super::super::summary::InvocationSummary,
    recent: NodeId,
    older: NodeId,
) {
    summary.accesses = std::mem::take(&mut summary.accesses)
        .into_iter()
        .map(|mut access| {
            if access.origin == recent {
                access.origin = older;
            }
            access
        })
        .collect();
    for origins in [
        &mut summary.escaped_origins,
        &mut summary.retained_origins,
        &mut summary.new_environments,
    ] {
        if origins.remove(&recent) {
            origins.insert(older);
        }
    }
}
impl Checker {
    pub(super) fn graph_callables(&self, source: &Value) -> Vec<Callable> {
        fn visit(value: &Value, callables: &mut Vec<Callable>) {
            callables.extend(value.callables.iter().cloned());
            for payload in [
                &value.variant_payload,
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            {
                visit(payload, callables);
            }
        }
        let mut callables = Vec::new();
        visit(source, &mut callables);
        let reachable = self.heap.reachable(source.origins.nodes.iter().copied());
        for ((node, _), value) in &self.fields {
            if reachable.contains(node) {
                visit(value, &mut callables);
            }
        }
        let mut distinct = Vec::new();
        for callable in callables {
            if !distinct.contains(&callable) {
                distinct.push(callable);
            }
        }
        distinct
    }
    pub(super) fn clone_relations(&mut self, copies: &BTreeMap<NodeId, NodeId>) -> bool {
        let pairs: Vec<_> = copies
            .iter()
            .map(|(source, copy)| (*source, *copy))
            .collect();
        let mut aliases = false;
        for (index, (a, copy_a)) in pairs.iter().enumerate() {
            for (b, copy_b) in &pairs[index + 1..] {
                let relation = self.heap.relation(*a, *b);
                aliases |= relation.disjoint != Condition::TRUE;
                self.heap.set_relation(*copy_a, *copy_b, relation);
            }
        }
        aliases
    }
}
impl Checker {
    pub(super) fn immutable_clone_roots(
        &self,
        value: &Value,
        include_self: bool,
        roots: &mut BTreeSet<NodeId>,
    ) {
        if include_self && self.formal_is_immutable(&value.ty) {
            roots.extend(&value.origins.nodes);
        }
        for payload in [
            &value.variant_payload,
            &value.option_payload,
            &value.result_payload,
            &value.result_success,
            &value.result_error,
        ]
        .into_iter()
        .flatten()
        .chain(value.variant_witnesses.values())
        {
            self.immutable_clone_roots(payload, true, roots);
        }
    }
}
pub(super) fn rewrite_clone(
    value: &mut Value,
    copies: &BTreeMap<NodeId, NodeId>,
    frozen: &BTreeSet<NodeId>,
    immutable: bool,
) {
    value.scoped.clear();
    let old = value.origins.nodes.clone();
    value.origins.nodes = old
        .iter()
        .filter_map(|node| copies.get(node).copied())
        .collect();
    for branches in value.origins.choices.values_mut() {
        for branch in branches {
            *branch = branch
                .iter()
                .filter_map(|node| copies.get(node).copied())
                .collect();
        }
    }
    value.sources.clear();
    value.scoped.clear();
    value.participants.clear();
    value.unsuffixed_numeric = false;
    value.literal_number = false;
    value.temporary = false;
    value.marker = false;
    value.retention_result = false;
    value.through_return = false;
    let readonly = old.is_empty()
        || immutable
        || !old.is_disjoint(frozen)
        || value.ty.scalar()
        || !value.callables.is_empty();
    value.permission = if readonly {
        Permission::Read
    } else {
        Permission::Write
    };
    value.publication = if readonly {
        Publication::Immutable
    } else {
        Publication::Unpublished
    };
    value.construction = !readonly && !value.origins.nodes.is_empty();
    for payload in [
        &mut value.variant_payload,
        &mut value.option_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        rewrite_clone(payload, copies, frozen, immutable);
    }
}
