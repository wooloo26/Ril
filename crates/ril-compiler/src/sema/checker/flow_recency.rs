//! Conditional snapshots retain object identity when a fresh allocation site
//! is evaluated again. Replaying recency changes does not mint new authority.
use super::*;

impl Checker {
    pub(in crate::sema::checker) fn transport_value_since(&self, value: &mut Value, cursor: usize) {
        for &(recent, older) in &self.recency_moves[cursor..] {
            copy::remap_value_origins(value, recent, older);
        }
    }
    pub(in crate::sema::checker) fn access_owners(
        &self,
        origins: &Origins,
    ) -> BTreeMap<NodeId, AccessOwners> {
        origins
            .nodes
            .iter()
            .map(|node| {
                let owners = self
                    .heap
                    .nodes
                    .get(node.0 as usize)
                    .map(|node| AccessOwners::Known([node.owner].into()))
                    .unwrap_or(AccessOwners::Unknown);
                (*node, owners)
            })
            .collect()
    }
    pub(in crate::sema::checker) fn access_is_local(
        &self,
        access: &AccessFact,
        node: NodeId,
        owner: ScopeId,
    ) -> bool {
        matches!(access.origin_owners.get(&node), Some(AccessOwners::Known(owners))
            if !owners.is_empty() && owners.iter().all(|origin| self.scope_is_within(*origin, owner)))
    }
    pub(in crate::sema::checker) fn current_accesses(
        &self,
        accesses: &[AccessFact],
    ) -> Vec<AccessFact> {
        accesses
            .iter()
            .cloned()
            .map(|mut access| {
                access.transport(&self.recency_moves);
                if let Ok(participants) = super::super::super::invocation_loans::normalize(
                    &access.participants,
                    &self.ended_invocation_loans,
                ) {
                    access.participants = participants;
                }
                access
            })
            .collect()
    }
    pub(in crate::sema::checker) fn transport_frame_prefix(
        &self,
        frame: &mut Frame,
        cursor: usize,
        accesses: usize,
        returns: usize,
    ) {
        for access in frame.obligations.accesses.iter_mut().take(accesses) {
            access.transport(&self.recency_moves);
        }
        for &(recent, older) in &self.recency_moves[cursor..] {
            for returned in frame.returned.iter_mut().take(returns) {
                copy::remap_value_origins(returned, recent, older);
            }
        }
    }
    pub(in crate::sema::checker) fn rebase_flow_snapshot(
        &mut self,
        before: &FlowSnapshot,
        span: Span,
    ) -> Option<FlowSnapshot> {
        let moves = self.recency_moves[before.recency..].to_vec();
        let changed: BTreeSet<_> = moves.iter().map(|(recent, _)| *recent).collect();
        if before.live.is_disjoint(&changed) {
            return None;
        }
        let affected = |value: &Value| {
            !loop_graph::reachable(&before.fields, value.origins.nodes.iter().copied())
                .is_disjoint(&changed)
        };
        let eligible = before
            .bindings
            .iter()
            .zip(&before.uses)
            .all(|(value, (_, _, _, alive))| {
                !alive || !affected(value) || self.ordinary_loop_value(value, &before.fields)
            })
            && before.fields.iter().all(|((node, _), value)| {
                !before.live.contains(node)
                    || (!changed.contains(node) && !affected(value))
                    || self.ordinary_loop_value(value, &before.fields)
            });
        let mut rebased = before.clone();
        if !eligible
            || !rebased.control.remap_ordinary_origins(&moves, |value| {
                self.ordinary_loop_value(value, &before.fields)
            })
        {
            self.unsupported(span,"conditional recency transport requires a separate resource, Result or callable activation proof");
            return None;
        }
        for value in &mut rebased.bindings {
            for &(recent, older) in &moves {
                copy::remap_value_origins(value, recent, older);
            }
        }
        let cause = self.cause(
            CauseKind::BranchJoin,
            span,
            "transport saved ordinary graph through recent/older allocation history",
            [],
        );
        let branch = self.choice();
        loop_graph::transport_fields(&mut rebased.fields, &moves, branch, cause);
        loop_graph::transport_nodes(&mut rebased.live, &moves);
        loop_graph::transport_nodes(&mut rebased.fixed_arrays, &moves);
        for refinement in rebased.refinements.values_mut() {
            refinement.remap_origins(&moves);
        }
        for event in &mut rebased.writes {
            event.remap_origins(&moves);
        }
        for obligations in rebased.handler_obligations.values_mut() {
            for access in &mut obligations.accesses {
                access.transport(&self.recency_moves);
            }
        }
        for &(recent, older) in &moves {
            if let Some(length) = rebased.arrays.remove(&recent) {
                rebased
                    .arrays
                    .entry(older)
                    .and_modify(|existing| {
                        if *existing != length {
                            *existing = None;
                        }
                    })
                    .or_insert(length);
            }
            rebased.uncertain = rebased
                .uncertain
                .into_iter()
                .map(|(node, slot)| (if node == recent { older } else { node }, slot))
                .collect();
        }
        while rebased.kinds.len() < self.heap.nodes.len() {
            let node = &self.heap.nodes[rebased.kinds.len()];
            rebased.kinds.push((node.kind, node.cause));
        }
        for node in &rebased.live {
            let current = &self.heap.nodes[node.0 as usize];
            rebased.kinds[node.0 as usize] = (current.kind, current.cause);
        }
        rebased.recency = self.recency_moves.len();
        Some(rebased)
    }

    pub(in crate::sema::checker) fn transport_flow_value(
        &mut self,
        value: &Value,
        before: &FlowSnapshot,
        span: Span,
    ) -> Value {
        let mut value = value.clone();
        let moves = self.recency_moves[before.recency..].to_vec();
        let changed: BTreeSet<_> = moves.iter().map(|(recent, _)| *recent).collect();
        if loop_graph::reachable(&before.fields, value.origins.nodes.iter().copied())
            .is_disjoint(&changed)
        {
            return value;
        }
        if !self.ordinary_loop_value(&value, &before.fields) {
            self.unsupported(
                span,
                "conditional returned graph recency requires a separate nonordinary transfer proof",
            );
            return value;
        }
        for (recent, older) in moves {
            copy::remap_value_origins(&mut value, recent, older);
        }
        value
    }
}
