//! A repeated callback is analyzed with changing scalar inputs widened. Until
//! graph transfer has a regular fixed point, changing an existing reference
//! shape is an explicit incompleteness rather than a one-iteration certificate.
use super::*;
#[path = "repeated_bindings.rs"]
mod bindings;
pub(super) struct RepeatedCallbackState {
    channel_repetition: crate::sema::channel_messages::ChannelRepetitionId,
    foreign_exits: Vec<CauseId>,
    concurrency: concurrent::State,
    bindings: Vec<(BindingId, Value)>,
    fields: BTreeMap<(NodeId, Slot), Value>,
    live: BTreeSet<NodeId>,
    kinds: Vec<(OriginKind, CauseId)>,
    arrays: BTreeMap<NodeId, Option<u64>>,
    deferred: Vec<(u32, ScopeId)>,
    budgets: Vec<(u32, Span)>,
}
impl Checker {
    pub(super) fn begin_repeated_callback(
        &mut self,
        invocation: &mut [(ParameterMode, Value, Span)],
        frame: &Frame,
    ) -> RepeatedCallbackState {
        let channel_repetition = self.channel_begin_repetition(frame);
        let (observable, live) = self.repeated_observable_bindings(invocation, frame);
        for binding in &mut self.bindings {
            if binding.mode.is_reassignable() || binding.value.publication == Publication::Live {
                widen(&mut binding.value);
            }
        }
        for ((node, _), value) in &mut self.fields {
            if live.contains(node) {
                widen(value);
            }
        }
        for (_, value, _) in invocation {
            widen(value);
        }
        self.widen_repeated_refinements();
        RepeatedCallbackState {
            channel_repetition,
            foreign_exits: self
                .foreign_abort_exits
                .iter()
                .map(|exit| exit.identity)
                .collect(),
            concurrency: self.concurrency.clone(),
            budgets: self
                .budget_recoveries
                .iter()
                .map(|exit| (exit.boundary, exit.span))
                .collect(),
            bindings: observable
                .into_iter()
                .map(|id| (id, self.bindings[id].value.clone()))
                .collect(),
            fields: self.fields.clone(),
            live,
            kinds: self
                .heap
                .nodes
                .iter()
                .map(|node| (node.kind, node.cause))
                .collect(),
            arrays: self.array_lengths.clone(),
            deferred: self
                .deferred_arm_cleanups
                .iter()
                .map(|arm| (arm.boundary, arm.frame.owner))
                .collect(),
        }
    }
    pub(super) fn summarize_repeated_scalar_arrays(&mut self, live: &BTreeSet<NodeId>) {
        let mut arrays = BTreeMap::new();
        for value in self
            .bindings
            .iter()
            .filter(|binding| binding.alive)
            .map(|binding| &binding.value)
            .chain(
                self.fields
                    .iter()
                    .filter(|((node, _), _)| live.contains(node))
                    .map(|(_, value)| value),
            )
        {
            if value.permission == Permission::Read && value.publication == Publication::Immutable {
                continue;
            }
            let ty = self.collection_type(value);
            if let Ty::Array(element) = self.expanded(&ty, &mut BTreeSet::new())
                && !self.reference_bearing(&element)
            {
                for node in &value.origins.nodes {
                    if live.contains(node) && !self.fixed_arrays.contains(node) {
                        arrays.insert(*node, (*element.clone(), value.cause));
                    }
                }
            }
        }
        for (node, (element, cause)) in arrays {
            let existing: Vec<_> = self
                .fields
                .iter()
                .filter(|((parent, slot), _)| {
                    *parent == node && matches!(slot, Slot::Index(_) | Slot::AnyIndex)
                })
                .map(|(_, value)| value.clone())
                .collect();
            let mut summary = existing
                .first()
                .cloned()
                .unwrap_or_else(|| Value::scalar(element.clone(), None, cause));
            if !summary.origins.nodes.is_empty()
                || !summary.callables.is_empty()
                || !summary.results.is_empty()
                || !summary.scoped.is_empty()
            {
                continue;
            }
            for value in &existing[existing.len().min(1)..] {
                summary = summary.join(value, self.choice(), cause);
            }
            summary.ty = element;
            widen(&mut summary);
            self.fields.retain(|(parent, slot), _| {
                *parent != node || !matches!(slot, Slot::Index(_) | Slot::AnyIndex)
            });
            self.heap.nodes[node.0 as usize]
                .fields
                .retain(|slot, _| !matches!(slot, Slot::Index(_) | Slot::AnyIndex));
            self.array_lengths.insert(node, None);
            self.store_field(node, Slot::AnyIndex, summary);
        }
    }
    pub(super) fn finish_repeated_callback(&mut self, before: RepeatedCallbackState, span: Span) {
        self.finish_repeated_callback_with_exits(before, span, &BTreeSet::new());
    }
    pub(super) fn finish_aborted_repeated_callback(
        &mut self,
        before: RepeatedCallbackState,
        span: Span,
    ) {
        // The foreign abort path already applies its own exit/graph contract.
        // Its actual channel interval still has to close on that same path.
        self.channel_finish_repetition(before.channel_repetition, span);
    }
    pub(super) fn finish_repeated_callback_with_exits(
        &mut self,
        before: RepeatedCallbackState,
        span: Span,
        exits: &BTreeSet<u32>,
    ) {
        self.channel_finish_repetition(before.channel_repetition, span);
        if before.foreign_exits
            != self
                .foreign_abort_exits
                .iter()
                .filter(|exit| !exits.contains(&exit.identity.0))
                .map(|exit| exit.identity)
                .collect::<Vec<_>>()
        {
            self.unsupported(span,"repeated callback retains conditional foreign abort exits requiring an iteration-indexed summary");
        }
        if self.concurrent_iteration_changes_authority(&before.concurrency, &before.live) {
            self.unsupported(span, "repeated callback changes retained one-use resource authority or child-borrow multiplicity");
        }
        if before.budgets
            != self
                .budget_recoveries
                .iter()
                .map(|exit| (exit.boundary, exit.span))
                .collect::<Vec<_>>()
        {
            self.unsupported(
                span,
                "a repeated callback retains budget recovery activations requiring a fixed point",
            );
        }
        if before.deferred
            != self
                .deferred_arm_cleanups
                .iter()
                .map(|arm| (arm.boundary, arm.frame.owner))
                .collect::<Vec<_>>()
        {
            self.unsupported(
                span,
                "repeated callback creates pending resumed-arm cleanup activations",
            );
        }
        let changed = before.bindings.iter().any(|(id, old)| {
            self.bindings
                .get(*id)
                .is_none_or(|new| !same_graph(old, &new.value))
        }) || before.fields.iter().any(|((node, slot), old)| {
            before.live.contains(node)
                && self
                    .fields
                    .get(&(*node, slot.clone()))
                    .is_none_or(|new| !same_graph(old, new))
        }) || self
            .fields
            .keys()
            .any(|key| before.live.contains(&key.0) && !before.fields.contains_key(key))
            || before.live.iter().any(|node| {
                before.kinds[node.0 as usize]
                    != (
                        self.heap.nodes[node.0 as usize].kind,
                        self.heap.nodes[node.0 as usize].cause,
                    )
            })
            || before.arrays.iter().any(|(node, length)| {
                before.live.contains(node) && self.array_lengths.get(node) != Some(length)
            });
        if changed {
            self.unsupported(span,"repeated callback changes a retained reference or storage shape; a heap transfer fixed point is required");
        }
    }
}
fn widen(value: &mut Value) {
    value.origins.choices.clear();
    value.constant = None;
    value.option_tag = None;
    value.result_tag = None;
    value.variant_tag = None;
    for payload in [
        &mut value.option_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        widen(payload);
    }
}
fn same_graph(left: &Value, right: &Value) -> bool {
    if left.ty.scalar()
        && right.ty.scalar()
        && left.origins.nodes.is_empty()
        && right.origins.nodes.is_empty()
        && left.callables.is_empty()
        && right.callables.is_empty()
        && left.results.is_empty()
        && right.results.is_empty()
        && left.scoped.is_empty()
        && right.scoped.is_empty()
    {
        return left.ty == right.ty;
    }
    left.ty == right.ty
        && left.origins.nodes == right.origins.nodes
        && left.permission == right.permission
        && left.publication == right.publication
        && left.callables == right.callables
        && left.callable_bounds == right.callable_bounds
        && left.callable_returns == right.callable_returns
        && left.scoped == right.scoped
        && left.results == right.results
        && left.outer_results == right.outer_results
        && left.participants == right.participants
        && left.temporary == right.temporary
        && same_payload(&left.option_payload, &right.option_payload)
        && same_payload(&left.result_payload, &right.result_payload)
        && same_payload(&left.result_success, &right.result_success)
        && same_payload(&left.result_error, &right.result_error)
        && same_payload(&left.variant_payload, &right.variant_payload)
        && left.variant_witnesses.len() == right.variant_witnesses.len()
        && left.variant_witnesses.iter().all(|(tag, value)| {
            right
                .variant_witnesses
                .get(tag)
                .is_some_and(|other| same_graph(value, other))
        })
}
fn same_payload(left: &Option<Box<Value>>, right: &Option<Box<Value>>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => same_graph(left, right),
        (None, None) => true,
        _ => false,
    }
}

#[cfg(test)]
mod audit {
    #[test]
    fn checked_local_host_result_does_not_escape_a_repeated_callback() {
        let source = br#"
use ril/io
fn read_number(number:int)->int @Fiber {
    let result=Io::stdin_read(0)
    assert(result is Ok(_) | Err(_))
    number
}
fn example() @Fiber {let _=Array::map([1,2],read_number)}
"#;
        let result = crate::Session::new(source.to_vec()).check();
        assert!(
            matches!(result, crate::CompilationOutcome::Accepted { .. }),
            "{result:?}"
        );
    }
}
