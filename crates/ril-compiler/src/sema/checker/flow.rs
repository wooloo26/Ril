use super::*;
#[path = "flow_recency.rs"]
mod recency;

#[derive(Clone)]
pub(super) struct FlowSnapshot {
    recency: usize,
    allocation_frontier: usize,
    bindings: Vec<Value>,
    fields: BTreeMap<(NodeId, Slot), Value>,
    duties: Vec<ResultDuty>,
    kinds: Vec<(OriginKind, CauseId)>,
    live: BTreeSet<NodeId>,
    uses: Vec<(bool, bool, bool, bool)>,
    pub(super) handler_obligations: BTreeMap<ScopeId, Obligations>,
    refinements: BTreeMap<narrowing::Place, narrowing::Refinement>,
    writes: Vec<narrowing::WriteEvent>,
    reads: BTreeMap<(u32, u32, u32, u32), usize>,
    pub(super) control: effects::ControlState,
    uncertain: BTreeSet<(NodeId, Slot)>,
    arrays: BTreeMap<NodeId, Option<u64>>,
    fixed_arrays: BTreeSet<NodeId>,
}
impl FlowSnapshot {
    pub(super) fn channel_project(
        &mut self,
        guard: &super::super::channel_messages::ChannelGuard,
    ) -> bool {
        self.control.channel_flow_mut().select(guard)
    }
    pub(super) fn result_duties(&self) -> &[ResultDuty] {
        &self.duties
    }
    pub(super) fn cancellation_projection(
        &self,
        bindings: &[BindingId],
        nodes: &BTreeSet<NodeId>,
        duties: usize,
    ) -> cancellation::Projection {
        cancellation::Projection {
            recency: self.recency,
            concurrency: self.control.concurrent_state().clone(),
            bindings: bindings
                .iter()
                .map(|id| (*id, self.bindings[*id].clone()))
                .collect(),
            fields: self
                .fields
                .iter()
                .filter(|((node, _), _)| nodes.contains(node))
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect(),
            duties: self.duties[..duties.min(self.duties.len())].to_vec(),
            uncertain: self
                .uncertain
                .iter()
                .filter(|(node, _)| nodes.contains(node))
                .cloned()
                .collect(),
            arrays: self
                .arrays
                .iter()
                .filter(|(node, _)| nodes.contains(node))
                .map(|(node, length)| (*node, *length))
                .collect(),
            fixed_arrays: self.fixed_arrays.intersection(nodes).copied().collect(),
        }
    }
    pub(super) fn abandon_foreign_result_scope(
        &mut self,
        owner: ScopeId,
        preserved: &BTreeSet<u32>,
    ) {
        for duty in &mut self.duties {
            if duty.owner == owner && !preserved.contains(&duty.id) {
                duty.abnormal = true;
            }
        }
    }
    pub(super) fn ordinary_foreign_abort(&self, checker: &Checker) -> bool {
        self.control.ordinary_foreign_abort()
            && self
                .uses
                .iter()
                .zip(&checker.bindings)
                .all(|((_, _, _, alive), binding)| {
                    !alive || !matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
                })
    }
    pub(super) fn unwind_foreign_frame(
        &mut self,
        owner: ScopeId,
        locals: &[BindingId],
        loans: &BTreeMap<LoanId, BTreeSet<Participant>>,
    ) {
        // The handler already transferred its answer to the delimiter owner.
        // Only duties still owned by this abandoned activation receive its
        // abnormal-exit waiver; caller-owned producers keep their obligation.
        fn normalize(value: &mut Value, loans: &BTreeMap<LoanId, BTreeSet<Participant>>) {
            value.participants =
                super::recursive_calls::normalize_participants(&value.participants, loans);
            for nested in [
                &mut value.result_payload,
                &mut value.result_success,
                &mut value.result_error,
                &mut value.option_payload,
                &mut value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values_mut())
            {
                normalize(nested, loans);
            }
        }
        for value in self.bindings.iter_mut().chain(self.fields.values_mut()) {
            normalize(value, loans);
        }
        for id in locals {
            if let Some(usage) = self.uses.get_mut(*id) {
                usage.3 = false;
            }
        }
        for duty in &mut self.duties {
            if duty.owner == owner {
                duty.abnormal = true;
            }
        }
    }
    pub(super) fn restore_foreign_overlays(
        &mut self,
        overlay: &[(BindingId, BTreeSet<Participant>, bool)],
    ) {
        for (id, participants, temporary) in overlay {
            if let Some(value) = self.bindings.get_mut(*id) {
                value.participants = participants.clone();
                value.temporary = *temporary;
            }
        }
    }
}
impl Checker {
    fn foreign_abort_branch_flow(
        &mut self,
        before: &FlowSnapshot,
        left_state: &FlowSnapshot,
        left: &Value,
        right: &Value,
        span: Span,
    ) -> Option<Value> {
        // An abort does not reach the ordinary continuation. Keeping its heap
        // here would both corrupt the normal state and hide which transition
        // must satisfy the repeated-callback fixed point.
        if self.foreign_callback_depth == 0 {
            return None;
        }
        let left_abort = left.ty == Ty::Never && left_state.control.abort.is_some();
        let right_abort = right.ty == Ty::Never && self.pending_abort.is_some();
        let left_terminal = left_abort || (left.ty == Ty::Never && left.abnormal);
        let right_terminal = right_abort || (right.ty == Ty::Never && right.abnormal);
        if !left_terminal && !right_terminal {
            return None;
        }
        let right_state = self.snapshot_flow();
        if self.loop_depth > 0
            || (left_terminal && !left_state.ordinary_foreign_abort(self))
            || (right_terminal && !right_state.ordinary_foreign_abort(self))
        {
            return None;
        }
        let mut exits = Vec::new();
        if left_abort {
            exits.push(self.foreign_abort_snapshot(before, left_state.clone(), span)?);
        }
        if right_abort {
            exits.push(self.foreign_abort_snapshot(before, right_state.clone(), span)?);
        }
        let continuing = if !right_terminal {
            right.clone()
        } else if !left_terminal {
            self.restore_definition_state(left_state);
            left.clone()
        } else {
            self.restore_definition_state(before);
            let mut never = self.unit(span);
            never.ty = Ty::Never;
            never.abnormal = true;
            never
        };
        for state in [left_state, &right_state] {
            self.include_foreign_exit_states(&state.control.foreign_abort_exits);
            for (owner, obligations) in &state.handler_obligations {
                self.pending_handler_obligations
                    .entry(*owner)
                    .or_default()
                    .include(obligations, true);
            }
        }
        for exit in exits {
            self.include_foreign_abort_exit(exit);
        }
        Some(continuing)
    }
    pub(super) fn reset_foreign_abort_exits(&self, state: &mut FlowSnapshot) {
        state.control.foreign_abort_exits = self.foreign_abort_exits.clone();
    }
    pub(super) fn reset_budget_exits(&self, state: &mut FlowSnapshot) {
        state.control.budget_recoveries = self.budget_recoveries.clone();
    }
    pub(super) fn clear_budget_exits(&self, state: &mut FlowSnapshot) {
        state.control.budget_recoveries.clear();
    }
    pub(super) fn preview_expression(&mut self, expression: &Expr, frame: &mut Frame) -> Value {
        self.preview_expression_expected(expression, frame, None)
    }
    pub(super) fn preview_expression_expected(
        &mut self,
        expression: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
    ) -> Value {
        self.preview_expression_source(expression, frame, expected, None)
            .value
    }
    pub(super) fn preview_expression_source(
        &mut self,
        expression: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
        source: Option<&super::super::source_reception::Target>,
    ) -> super::expressions::SourceExpression {
        self.preview_evaluation(frame, |checker, frame| {
            checker.expression_expected_source(expression, frame, expected, source)
        })
    }

    /// A source block is already a collection of identified statements. A
    /// preview does not manufacture an expression occurrence around it.
    pub(super) fn preview_block_source(
        &mut self,
        block: &Block,
        frame: &mut Frame,
        expected: Option<&Ty>,
        source: Option<&super::super::source_reception::Target>,
    ) -> super::expressions::SourceExpression {
        // Block previews can recursively examine unreachable suffixes. They
        // still consume traversal work even though no wrapper is an expression.
        if self.analysis_depth >= 64 || self.analysis_visits >= 1_000_000 {
            self.unsupported(
                block.span,
                "semantic block preview traversal budget exhausted",
            );
            return super::expressions::SourceExpression {
                value: Value::scalar(
                    Ty::Unknown,
                    None,
                    self.cause(
                        CauseKind::MissingProof,
                        block.span,
                        "block preview stopped",
                        [],
                    ),
                ),
                observation: None,
                source_valid: false,
            };
        }
        self.analysis_depth += 1;
        self.analysis_visits += 1;
        let result = self.preview_evaluation(frame, |checker, frame| {
            checker.block_expected_source(block, frame, expected, source)
        });
        self.analysis_depth -= 1;
        result
    }

    fn preview_evaluation<T>(
        &mut self,
        frame: &mut Frame,
        evaluate: impl FnOnce(&mut Self, &mut Frame) -> T,
    ) -> T {
        let budget = std::mem::take(&mut self.budget_coverage);
        let before = self.snapshot_flow();
        self.channel_preview();
        let prior = frame.clone();
        let abort = self.pending_abort.clone();
        let resumes = self.resume_contexts.clone();
        let ended = self.ended_operation_loans.clone();
        let breaks = self.loop_breaks.clone();
        let result = evaluate(self, frame);
        self.restore_preview(&before);
        *frame = prior;
        self.pending_abort = abort;
        self.resume_contexts = resumes;
        self.ended_operation_loans = ended;
        self.loop_breaks = breaks;
        self.budget_coverage = budget;
        result
    }
    pub(super) fn branch_flow(
        &mut self,
        before: &FlowSnapshot,
        left_state: &FlowSnapshot,
        left: &Value,
        right: &Value,
        span: Span,
    ) -> Value {
        if let Some(value) = self.foreign_abort_branch_flow(before, left_state, left, right, span) {
            return value;
        }
        let left = self.transport_flow_value(left, left_state, span);
        let left = &left;
        let rebased_before = self.rebase_flow_snapshot(before, span);
        let before = rebased_before.as_ref().unwrap_or(before);
        let rebased_left = self.rebase_flow_snapshot(left_state, span);
        let left_state = rebased_left.as_ref().unwrap_or(left_state);
        self.check_flow_recency(before, span);
        self.merge_array_lengths(&left_state.arrays, &left_state.fixed_arrays);
        let right_refinements = self.refinements.clone();
        self.merge_refinements(
            &left_state.refinements,
            &right_refinements,
            left.ty == Ty::Never,
            right.ty == Ty::Never,
        );
        let current = self.snapshot_control_flow();
        self.merge_control_flow(&[left_state.control.clone(), current], span);
        self.uncertain_slots
            .extend(left_state.uncertain.iter().cloned());
        self.write_events.extend(
            left_state.writes[before.writes.len().min(left_state.writes.len())..]
                .iter()
                .cloned(),
        );
        for (owner, obligations) in &left_state.handler_obligations {
            self.pending_handler_obligations
                .entry(*owner)
                .or_default()
                .include(obligations, true);
        }
        let cause = self.cause(
            CauseKind::BranchJoin,
            span,
            "both source branches retain their state and per-producer inspection coverage",
            [left.cause, right.cause],
        );
        let choice = self.choice();
        for (index, _) in before.bindings.iter().enumerate() {
            let a = left_state.bindings[index].clone();
            let b = self.bindings[index].value.clone();
            let storage_cause = self.cause(
                CauseKind::BranchJoin,
                span,
                "conditional binding state keeps its own value alternatives",
                [a.cause, b.cause],
            );
            self.type_alternatives
                .insert(storage_cause.0, vec![a.clone(), b.clone()]);
            self.bindings[index].value = a.join(&b, choice, storage_cause);
        }
        for (key, a) in &left_state.fields {
            if let Some(b) = self.fields.get(key).cloned() {
                let storage_cause = self.cause(
                    CauseKind::BranchJoin,
                    span,
                    "conditional field state keeps its own value alternatives",
                    [a.cause, b.cause],
                );
                self.type_alternatives
                    .insert(storage_cause.0, vec![a.clone(), b.clone()]);
                self.fields
                    .insert(key.clone(), a.join(&b, choice, storage_cause));
            } else {
                self.fields.insert(key.clone(), a.clone());
            }
        }
        self.refresh_heap_fields();
        self.refresh_writable_roots();
        self.type_alternatives
            .insert(cause.0, vec![left.clone(), right.clone()]);
        let joined = if left.ty == Ty::Never {
            right.clone()
        } else if right.ty == Ty::Never {
            left.clone()
        } else {
            left.join(right, choice, cause)
        };
        self.merge_result_paths(&before.duties, &left_state.duties, left, right, joined)
    }
    pub(super) fn merge_array_lengths(
        &mut self,
        left: &BTreeMap<NodeId, Option<u64>>,
        fixed: &BTreeSet<NodeId>,
    ) {
        for (node, length) in left {
            let merged = match self.array_lengths.get(node) {
                Some(right) if right != length => None,
                _ => *length,
            };
            self.array_lengths.insert(*node, merged);
        }
        self.fixed_arrays.extend(fixed);
    }
    pub(super) fn snapshot_flow(&self) -> FlowSnapshot {
        let live = self.heap.reachable(
            self.bindings
                .iter()
                .filter(|binding| binding.alive)
                .flat_map(|binding| {
                    binding
                        .value
                        .origins
                        .nodes
                        .iter()
                        .copied()
                        .chain(binding.cell)
                }),
        );
        FlowSnapshot {
            recency: self.recency_moves.len(),
            allocation_frontier: self.heap.nodes.len(),
            bindings: self
                .bindings
                .iter()
                .map(|binding| binding.value.clone())
                .collect(),
            fields: self.fields.clone(),
            duties: self.result_duties.clone(),
            kinds: self
                .heap
                .nodes
                .iter()
                .map(|node| (node.kind, node.cause))
                .collect(),
            live,
            uses: self
                .bindings
                .iter()
                .map(|binding| {
                    (
                        binding.used,
                        binding.slot_used,
                        binding.write_used,
                        binding.alive,
                    )
                })
                .collect(),
            handler_obligations: self.pending_handler_obligations.clone(),
            refinements: self.refinements.clone(),
            writes: self.write_events.clone(),
            reads: self.read_epochs.clone(),
            control: self.snapshot_control_flow(),
            uncertain: self.uncertain_slots.clone(),
            arrays: self.array_lengths.clone(),
            fixed_arrays: self.fixed_arrays.clone(),
        }
    }
    pub(super) fn restore_preview(&mut self, before: &FlowSnapshot) {
        let span = before
            .live
            .first()
            .and_then(|node| {
                self.explanations
                    .causes
                    .get(before.kinds[node.0 as usize].1.0 as usize)
            })
            .and_then(|cause| cause.span)
            .unwrap_or(Span {
                file: self.file,
                start: 0,
                end: 0,
            });
        let rebased = self.rebase_flow_snapshot(before, span);
        let before = rebased.as_ref().unwrap_or(before);
        self.check_flow_recency(before, span);
        self.restore_control_flow(&before.control);
        self.uncertain_slots = before.uncertain.clone();
        self.array_lengths = before.arrays.clone();
        self.fixed_arrays = before.fixed_arrays.clone();
        self.write_events = before.writes.clone();
        self.read_epochs = before.reads.clone();
        self.refinements = before.refinements.clone();
        self.pending_handler_obligations = before.handler_obligations.clone();
        for (binding, old) in self.bindings.iter_mut().zip(&before.bindings) {
            binding.value = old.clone();
        }
        for (binding, (used, slot_used, write_used, alive)) in
            self.bindings.iter_mut().zip(&before.uses)
        {
            binding.alive = *alive;
            binding.used = *used;
            binding.slot_used = *slot_used;
            binding.write_used = *write_used;
        }
        for binding in &mut self.bindings[before.bindings.len()..] {
            binding.alive = false;
        }
        self.fields.retain(|key, _| {
            key.0.0 as usize >= before.allocation_frontier || before.fields.contains_key(key)
        });
        for (key, old) in &before.fields {
            self.fields.insert(key.clone(), old.clone());
        }
        for (duty, old) in self.result_duties.iter_mut().zip(&before.duties) {
            duty.inspected = old.inspected;
            duty.returned = old.returned;
            duty.abnormal = old.abnormal;
            duty.covered = old.covered;
        }
        for duty in &mut self.result_duties[before.duties.len()..] {
            duty.abnormal = true;
        }
        self.refresh_heap_fields();
        self.refresh_writable_roots();
    }
    pub(super) fn restore_definition_state(&mut self, before: &FlowSnapshot) {
        let uses: Vec<_> = self
            .bindings
            .iter()
            .map(|binding| (binding.used, binding.slot_used, binding.write_used))
            .collect();
        self.restore_preview(before);
        for (binding, (used, slot, write)) in self.bindings.iter_mut().zip(uses) {
            binding.used |= used;
            binding.slot_used |= slot;
            binding.write_used |= write;
        }
    }
    pub(super) fn conditional_flow(
        &mut self,
        before: &FlowSnapshot,
        skipped: &Value,
        executed: &Value,
        execute: Option<bool>,
        span: Span,
    ) -> Value {
        if execute == Some(true) {
            return executed.clone();
        }
        if execute.is_none()
            && (executed.ty == Ty::Never || executed.abnormal)
            && self.foreign_callback_depth > 0
            && self.pending_abort.is_some()
        {
            let state = self.snapshot_flow();
            if let Some(exit) = self.foreign_abort_snapshot(before, state, span) {
                self.restore_definition_state(before);
                self.include_foreign_abort_exit(exit);
                return skipped.clone();
            }
        }
        let skipped = self.transport_flow_value(skipped, before, span);
        let skipped = &skipped;
        let rebased = self.rebase_flow_snapshot(before, span);
        let before = rebased.as_ref().unwrap_or(before);
        self.check_flow_recency(before, span);
        let cause = self.cause(
            CauseKind::BranchJoin,
            span,
            "conditional execution retains the skipped and executed state",
            [skipped.cause, executed.cause],
        );
        let choice = self.choice();
        for index in 0..self.bindings.len().min(before.bindings.len()) {
            let old = &before.bindings[index];
            let current = self.bindings[index].value.clone();
            self.bindings[index].value = if execute == Some(false) {
                old.clone()
            } else {
                let storage_cause = self.cause(
                    CauseKind::BranchJoin,
                    span,
                    "conditional execution retains this binding's own value sources",
                    [old.cause, current.cause],
                );
                old.join(&current, choice, storage_cause)
            };
        }
        for (key, old) in &before.fields {
            let value = if execute == Some(false) {
                old.clone()
            } else {
                if let Some(current) = self.fields.get(key).cloned() {
                    let storage_cause = self.cause(
                        CauseKind::BranchJoin,
                        span,
                        "conditional execution retains this stored member's own value sources",
                        [old.cause, current.cause],
                    );
                    old.join(&current, choice, storage_cause)
                } else {
                    old.clone()
                }
            };
            self.fields.insert(key.clone(), value);
        }
        self.refresh_heap_fields();
        self.refresh_writable_roots();
        if execute == Some(false) {
            self.restore_control_flow(&before.control);
            self.uncertain_slots = before.uncertain.clone();
            self.array_lengths = before.arrays.clone();
            self.fixed_arrays = before.fixed_arrays.clone();
            self.write_events = before.writes.clone();
            self.read_epochs = before.reads.clone();
            self.refinements = before.refinements.clone();
            self.pending_handler_obligations = before.handler_obligations.clone();
            for (current, old) in self.result_duties.iter_mut().zip(&before.duties) {
                current.inspected = old.inspected;
                current.returned = old.returned;
                current.abnormal = old.abnormal;
                current.covered = old.covered;
            }
            for duty in &mut self.result_duties[before.duties.len()..] {
                duty.abnormal = true;
            }
            return skipped.clone();
        }
        let joined = if executed.ty == Ty::Never {
            skipped.clone()
        } else {
            skipped.join(executed, choice, cause)
        };
        self.merge_array_lengths(&before.arrays, &before.fixed_arrays);
        let current = self.refinements.clone();
        let control = self.snapshot_control_flow();
        self.merge_control_flow(&[before.control.clone(), control], span);
        self.uncertain_slots
            .extend(before.uncertain.iter().cloned());
        self.merge_refinements(
            &before.refinements,
            &current,
            skipped.ty == Ty::Never,
            executed.ty == Ty::Never,
        );
        self.merge_result_paths(&before.duties, &before.duties, skipped, executed, joined)
    }
    fn check_flow_recency(&mut self, before: &FlowSnapshot, span: Span) {
        if before.live.iter().any(|id| {
            before.kinds[id.0 as usize]
                != (
                    self.heap.nodes[id.0 as usize].kind,
                    self.heap.nodes[id.0 as usize].cause,
                )
        }) {
            self.unsupported(span,"conditional execution recycled a live allocation summary; relational recency transport is unresolved");
        }
    }
    pub(super) fn refresh_heap_fields(&mut self) {
        self.refresh_window_fields();
        for node in &mut self.heap.nodes {
            node.fields.clear();
        }
        for ((node, slot), value) in &self.fields {
            self.heap.nodes[node.0 as usize]
                .fields
                .insert(slot.clone(), value.origins.nodes.clone());
        }
    }
    pub(super) fn refresh_writable_roots(&mut self) {
        for node in &mut self.heap.nodes {
            node.writable_roots.clear();
        }
        for binding in self.bindings.iter().filter(|binding| binding.alive) {
            if let Some(cell) = binding.cell {
                self.heap.nodes[cell.0 as usize]
                    .writable_roots
                    .insert(binding.root);
            }
            if binding.mode.is_mutable() {
                let nodes = self.writable_nodes(&binding.value);
                for node in nodes {
                    self.heap.nodes[node.0 as usize]
                        .writable_roots
                        .insert(binding.root);
                }
            }
        }
    }
}

#[cfg(test)]
mod preview_tests {
    #[test]
    fn generated_unreachable_suffixes_keep_a_traversal_budget_without_wrapper_expressions() {
        let source = format!("fn example(){{ {} }}", "return;".repeat(192));
        let outcome = crate::Session::new(source.into_bytes()).check();
        assert!(
            matches!(&outcome, crate::CompilationOutcome::NotImplemented { reason }
                if reason.detail.contains("semantic") && reason.detail.contains("budget")),
            "{outcome:?}"
        );
    }
}
