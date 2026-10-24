//! Observable storage at a repeated-call boundary. A retired lexical binding
//! can still be captured; only unreachable historical bookkeeping is excluded.
use super::*;
use std::sync::Arc;

impl Checker {
    pub(super) fn repeated_observable_bindings(
        &self,
        invocation: &[(ParameterMode, Value, Span)],
        frame: &Frame,
    ) -> (BTreeSet<BindingId>, BTreeSet<NodeId>) {
        let mut bindings: BTreeSet<_> = self
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(id, binding)| binding.alive.then_some(id))
            .collect();
        // Existing saved control-flow snapshots contain additional return and
        // cleanup roots. Until those snapshots expose a common root visitor,
        // retain their complete historical binding set, as the old check did.
        if !self.budget_recoveries.is_empty()
            || !self.foreign_abort_exits.is_empty()
            || !self.foreign_return_states.is_empty()
            || !self.cancellation_contexts.is_empty()
            || !self.resume_contexts.is_empty()
            || !self.deferred_arm_cleanups.is_empty()
            || !self.suspended_cleanups.is_empty()
        {
            bindings.extend(0..self.bindings.len());
        }
        // A callable recipe may escape without an alive lexical binding. Keep
        // all known capture cells, including their ended creating frames.
        bindings.extend(
            self.closures
                .iter()
                .flat_map(|closure| closure.captures.iter().copied()),
        );
        bindings.extend(
            self.functions
                .iter()
                .flat_map(|function| function.captures.iter().copied()),
        );
        bindings.extend(self.repeated_handler_bindings());
        let mut nodes: BTreeSet<_> = self
            .closures
            .iter()
            .map(|closure| closure.node)
            .chain(
                self.functions
                    .iter()
                    .filter_map(|function| function.environment),
            )
            .collect();
        let mut values: Vec<&Value> = invocation
            .iter()
            .map(|(_, value, _)| value)
            .chain(frame.returned.iter().map(|packet| &packet.value))
            .chain(self.pending_abort.iter().map(|(_, value)| &value.value))
            .chain(self.loop_breaks.iter().flat_map(|(_, values)| values))
            .chain(self.repeated_handler_answers())
            .chain(self.concurrency.cancellation_retained_values())
            .collect();
        let mut participants = BTreeSet::<Participant>::new();
        let mut visited_bindings = BTreeSet::<BindingId>::new();
        let mut visited_nodes = BTreeSet::<NodeId>::new();
        let mut visited_participants = BTreeSet::<Participant>::new();
        loop {
            let prior = (bindings.len(), nodes.len(), participants.len());
            let mut forwarded = BTreeSet::<BindingId>::new();
            for &id in &bindings {
                if visited_bindings.insert(id) {
                    let binding = &self.bindings[id];
                    values.push(&binding.value);
                    nodes.extend(binding.cell);
                    forwarded.extend(&binding.forwarded);
                }
            }
            bindings.extend(forwarded);
            while let Some(value) = values.pop() {
                bindings.extend(&value.sources);
                bindings.extend(&value.scoped);
                bindings.extend(&value.callback_parameters);
                nodes.extend(&value.origins.nodes);
                participants.extend(&value.participants);
                for bound in &value.callable_bounds {
                    bindings.extend(
                        bound
                            .typing_environment
                            .contract_bindings()
                            .values()
                            .copied(),
                    );
                }
                let mut returns: Vec<_> = value.callable_returns.iter().map(Arc::as_ref).collect();
                while let Some(bound) = returns.pop() {
                    bindings.extend(
                        bound
                            .typing_environment
                            .contract_bindings()
                            .values()
                            .copied(),
                    );
                    returns.extend(bound.predecessors.iter().map(Arc::as_ref));
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
                    .filter_map(|value| value.as_deref()),
                );
                values.extend(value.variant_witnesses.values().map(Box::as_ref));
            }
            let pending: Vec<_> = participants.iter().copied().collect();
            for participant in pending {
                if !visited_participants.insert(participant) {
                    continue;
                }
                match participant {
                    Participant::Root(root) => bindings.extend(
                        self.bindings
                            .iter()
                            .enumerate()
                            .filter_map(|(id, binding)| (binding.root == root).then_some(id)),
                    ),
                    Participant::Loan(loan) => {
                        if let Some(parents) = self.loan_parents.get(&loan) {
                            participants.extend(parents);
                        }
                    }
                }
            }
            nodes = self.heap.reachable(nodes);
            for ((node, _), value) in &self.fields {
                if nodes.contains(node) && !visited_nodes.contains(node) {
                    values.push(value);
                }
            }
            visited_nodes.extend(&nodes);
            if prior == (bindings.len(), nodes.len(), participants.len()) && values.is_empty() {
                break;
            }
        }
        (bindings, nodes)
    }
}
