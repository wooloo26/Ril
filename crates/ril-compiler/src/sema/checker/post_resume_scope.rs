//! End only the ordinary continuation-local writers that reach this answer.
//! Lexical recipes and suspended control states keep their authority roots.
use super::*;

impl Checker {
    pub(super) fn retire_continuation_writers(
        &mut self,
        boundary: u32,
        caller: &Frame,
        ending_start: usize,
        arm: &Frame,
        registrations: &[BindingId],
        answer: &mut Value,
    ) -> Option<super::super::resumption::ContinuationScopeExit> {
        if !self.ordinary_handler_answer(answer)
            || !self.budget_recoveries.is_empty()
            || !self.foreign_abort_exits.is_empty()
            || !self.foreign_return_states.is_empty()
            || !self.resume_contexts.is_empty()
            || !self.cancellation_contexts.is_empty()
            || !self.suspended_cleanups.is_empty()
        {
            return None;
        }
        let answer_nodes = self.heap.reachable(answer.origins.nodes.iter().copied());
        let writers: BTreeSet<_> = answer_nodes
            .iter()
            .flat_map(|node| {
                self.heap.nodes[node.0 as usize]
                    .writable_roots
                    .iter()
                    .map(|root| root.0 as usize)
            })
            .collect();
        let ending: BTreeSet<_> = caller.locals[ending_start..].iter().copied().collect();
        let candidates: BTreeSet<_> = writers
            .iter()
            .copied()
            .filter(|id| {
                let binding = &self.bindings[*id];
                binding.alive
                    && ending.contains(id)
                    && !binding.parameter
                    && binding.owner == caller.owner
                    && binding.lexical_scope == boundary
                    && !matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
                    && self.ordinary_handler_answer(&binding.value)
            })
            .collect();
        if candidates.is_empty() {
            return None;
        }
        let mut protected = self.scope_exit_handler_bindings();
        protected.extend(arm.env.values().copied());
        protected.extend(arm.locals.iter().copied());
        protected.extend(registrations);
        for pending in self
            .deferred_arm_cleanups
            .iter()
            .filter(|pending| pending.boundary == boundary)
        {
            protected.extend(pending.frame.env.values().copied());
            protected.extend(pending.frame.locals.iter().copied());
            protected.extend(&pending.registrations);
        }
        protected.extend(self.closures.iter().flat_map(|closure| &closure.captures));
        protected.extend(
            self.functions
                .iter()
                .flat_map(|function| &function.captures),
        );
        // A hoisted named recipe may discover a free binding only when its
        // suffix call is checked. Its ended declaration environment survives.
        protected.extend(
            self.functions
                .iter()
                .filter(|function| function.owner.is_some())
                .flat_map(|function| function.lexical.values().copied()),
        );
        let mut visited_bindings = BTreeSet::new();
        let mut visited_nodes = BTreeSet::new();
        let mut visited_participants = BTreeSet::new();
        let mut participants = BTreeSet::new();
        let mut values: Vec<&Value> = caller
            .returned
            .iter()
            .chain(self.pending_abort.iter().map(|(_, value)| value))
            .chain(self.loop_breaks.iter().flat_map(|(_, values)| values))
            .collect();
        loop {
            let before = (protected.len(), visited_nodes.len(), participants.len());
            let pending: Vec<_> = protected
                .iter()
                .copied()
                .filter(|id| !visited_bindings.contains(id))
                .collect();
            for id in pending {
                visited_bindings.insert(id);
                let binding = &self.bindings[id];
                protected.extend(&binding.forwarded);
                values.push(&binding.value);
                if let Some(cell) = binding.cell
                    && visited_nodes.insert(cell)
                {
                    values.extend(
                        self.fields
                            .iter()
                            .filter_map(|((node, _), value)| (*node == cell).then_some(value)),
                    );
                }
            }
            while let Some(value) = values.pop() {
                if value
                    .callables
                    .iter()
                    .any(|callable| matches!(callable, Callable::Symbolic(..)))
                {
                    return None;
                }
                protected.extend(&value.sources);
                protected.extend(&value.scoped);
                protected.extend(&value.callback_parameters);
                for bound in &value.callable_bounds {
                    protected.extend(bound.typing_environment.contract_bindings.values().copied());
                }
                let mut returns: Vec<_> = value
                    .callable_returns
                    .iter()
                    .map(|bound| bound.as_ref())
                    .collect();
                while let Some(bound) = returns.pop() {
                    protected.extend(bound.typing_environment.contract_bindings.values().copied());
                    returns.extend(bound.predecessors.iter().map(|bound| bound.as_ref()));
                }
                participants.extend(&value.participants);
                for origin in &value.origins.nodes {
                    if visited_nodes.insert(*origin) {
                        values.extend(
                            self.fields
                                .iter()
                                .filter_map(|((node, _), value)| (node == origin).then_some(value)),
                        );
                    }
                }
                values.extend(
                    [
                        &value.option_payload,
                        &value.result_payload,
                        &value.result_success,
                        &value.result_error,
                        &value.variant_payload,
                    ]
                    .into_iter()
                    .flatten()
                    .map(Box::as_ref),
                );
                values.extend(value.variant_witnesses.values().map(Box::as_ref));
            }
            for participant in participants.clone() {
                if !visited_participants.insert(participant) {
                    continue;
                }
                match participant {
                    Participant::Root(root) => {
                        protected.insert(root.0 as usize);
                    }
                    Participant::Loan(loan) => {
                        participants.extend(self.loan_parents.get(&loan)?);
                    }
                }
            }
            if before == (protected.len(), visited_nodes.len(), participants.len())
                && values.is_empty()
            {
                break;
            }
        }
        let retired: BTreeSet<_> = candidates.difference(&protected).copied().collect();
        if retired.is_empty() {
            return None;
        }
        let before = self.copy_value_snapshot(answer);
        let frontier = self.bindings.len();
        let epoch = self.recency_moves.len();
        let observed: BTreeSet<_> = visited_bindings.union(&writers).copied().collect();
        let bindings = observed
            .iter()
            .map(|id| {
                let binding = &self.bindings[*id];
                super::super::resumption::ScopeBindingObservation {
                    binding: *id,
                    value: binding.value.clone(),
                    cell: binding.cell,
                    forwarded: binding.forwarded.clone(),
                    alive: binding.alive,
                }
            })
            .collect();
        let alive = observed
            .iter()
            .copied()
            .filter(|id| self.bindings[*id].alive)
            .collect();
        let nodes = visited_nodes
            .iter()
            .map(|node| super::super::copy_contract::CopyNode {
                origin: *node,
                fact: self.heap.nodes[node.0 as usize].clone(),
                fields: self
                    .fields
                    .iter()
                    .filter_map(|((parent, slot), value)| {
                        (parent == node).then_some((slot.clone(), value.clone()))
                    })
                    .collect(),
                length: self.array_lengths.get(node).copied(),
                fixed: self.fixed_arrays.contains(node),
            })
            .collect();
        for id in &retired {
            self.check_authority_use(*id);
            self.bindings[*id].alive = false;
        }
        if answer.permission == Permission::Write
            && answer.publication != Publication::Immutable
            && !self.has_writer(answer)
            && self.writable_nodes(answer).iter().all(|node| {
                matches!(
                    self.heap.nodes[node.0 as usize].kind,
                    OriginKind::Fresh(_) | OriginKind::Older(_)
                )
            })
        {
            answer.construction = true;
            answer.publication = Publication::Unpublished;
        }
        Some(super::super::resumption::ContinuationScopeExit {
            activation: caller.owner,
            boundary,
            epoch,
            binding_frontier: frontier,
            retired_bindings: retired,
            protected_bindings: protected,
            alive_bindings: alive,
            bindings,
            nodes,
            answer_before: before,
            answer_received: self.copy_value_snapshot(answer),
        })
    }
}
