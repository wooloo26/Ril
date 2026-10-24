//! Foreign callbacks have zero or more ordinary returns and at most one abort.
//! Normal and terminal exits retain separate heap, loan and Result-duty states.
use super::*;
use std::sync::Arc;

#[derive(Clone)]
pub(super) struct AbortExit {
    pub(super) identity: CauseId,
    boundary: u32,
    answer: EvaluatedValue,
    span: Span,
    before: Arc<flow::FlowSnapshot>,
    state: Arc<flow::FlowSnapshot>,
}
#[derive(Clone)]
pub(super) struct ReturnExit {
    owner: ScopeId,
    value: EvaluatedValue,
    state: Arc<flow::FlowSnapshot>,
}

impl Checker {
    pub(super) fn abandon_foreign_activation_results(&mut self, boundary: u32, owner: ScopeId) {
        let preserved: Vec<_> = self
            .foreign_abort_exits
            .iter()
            .filter(|exit| exit.boundary == boundary)
            .map(|exit| {
                (
                    exit.identity,
                    self.result_family_closure(exit.answer.value.results.iter().copied()),
                )
            })
            .collect();
        for (identity, preserved) in preserved {
            if let Some(exit) = self
                .foreign_abort_exits
                .iter_mut()
                .find(|exit| exit.identity == identity)
            {
                Arc::make_mut(&mut exit.state).abandon_foreign_result_scope(owner, &preserved);
            }
        }
    }
    pub(super) fn record_foreign_return(&mut self, value: &EvaluatedValue, frame: &mut Frame) {
        if self.foreign_callback_depth == 0 || value.value.ty == Ty::Never || self.loop_depth > 0 {
            return;
        }
        let state = self.snapshot_flow();
        if !state.ordinary_foreign_abort(self) {
            return;
        }
        frame
            .foreign_return_states
            .push(self.foreign_return_states.len());
        self.foreign_return_states.push(ReturnExit {
            owner: frame.owner,
            value: value.clone(),
            state: Arc::new(state),
        });
    }
    pub(super) fn finish_foreign_returns(
        &mut self,
        before: &flow::FlowSnapshot,
        frame: &mut Frame,
        result: &mut EvaluatedValue,
        span: Span,
        epoch: u32,
    ) {
        let returned: Vec<_> = frame
            .foreign_return_states
            .iter()
            .map(|id| self.foreign_return_states[*id].clone())
            .filter(|exit| exit.owner == frame.owner)
            .collect();
        let count = frame
            .returned
            .iter()
            .filter(|packet| packet.value.ty != Ty::Never)
            .count();
        if count == 0 {
            return;
        }
        if returned.len() != count {
            if self.pending_abort.is_some()
                || self
                    .foreign_abort_exits
                    .iter()
                    .any(|exit| exit.identity.0 >= epoch)
            {
                self.unsupported(
                    span,
                    "foreign callback early returns need complete scoped and per-exit Result state",
                );
            }
            return;
        }
        if self.pending_abort.is_some() {
            let Some(exit) = self.foreign_abort_snapshot(before, self.snapshot_flow(), span) else {
                return;
            };
            self.pending_abort = None;
            self.include_foreign_abort_exit(exit);
        }
        let exits = self.foreign_abort_exits.clone();
        let mut has_normal = result.value.ty != Ty::Never;
        for mut returned in returned {
            if has_normal {
                self.receive_boundary_type(&mut returned.value, result, span);
                self.transport_evaluation_packet(&mut returned.value, span);
                self.transport_evaluation_packet(result, span);
                let before = self
                    .rebase_flow_snapshot(before, span)
                    .unwrap_or_else(|| before.clone());
                let state = self
                    .rebase_flow_snapshot(&returned.state, span)
                    .unwrap_or_else(|| (*returned.state).clone());
                result.value =
                    self.branch_flow(&before, &state, &returned.value.value, &result.value, span);
            } else {
                self.restore_definition_state(&returned.state);
                *result = returned.value;
                has_normal = true;
            }
        }
        self.include_foreign_exit_states(&exits);
        frame.returned.clear();
        frame.foreign_return_states.clear();
    }
    pub(super) fn foreign_abort_snapshot(
        &mut self,
        before: &flow::FlowSnapshot,
        mut state: flow::FlowSnapshot,
        span: Span,
    ) -> Option<AbortExit> {
        if self.loop_depth > 0 || !state.ordinary_foreign_abort(self) {
            self.unsupported(span,"conditional foreign abort retains scoped cleanup, resumption, loop or resource ownership requiring a separate exit contract");
            return None;
        }
        let (boundary, answer) = state.control.abort.take()?;
        self.handler_boundary_owner(boundary)?;
        let identity=self.cause(CauseKind::Handler,span,"terminal foreign callback abort keeps its own state, apart from repeatable ordinary returns",[answer.value.cause]);
        Some(AbortExit {
            identity,
            boundary,
            answer,
            span,
            before: Arc::new(before.clone()),
            state: Arc::new(state),
        })
    }
    pub(super) fn include_foreign_exit_states(&mut self, exits: &[AbortExit]) {
        for exit in exits {
            if !self
                .foreign_abort_exits
                .iter()
                .any(|prior| prior.identity == exit.identity)
            {
                self.foreign_abort_exits.push(exit.clone());
            }
        }
    }
    pub(super) fn include_foreign_abort_exit(&mut self, exit: AbortExit) {
        for (owner, obligations) in &exit.state.handler_obligations {
            self.pending_handler_obligations
                .entry(*owner)
                .or_default()
                .include(obligations, true);
        }
        self.foreign_abort_exits.push(exit);
    }
    pub(super) fn unwind_foreign_abort_exits(
        &mut self,
        owner: ScopeId,
        locals: &[BindingId],
        loans: &BTreeMap<LoanId, BTreeSet<Participant>>,
        epoch: u32,
    ) {
        for exit in self
            .foreign_abort_exits
            .iter_mut()
            .filter(|exit| exit.identity.0 >= epoch)
        {
            Arc::make_mut(&mut exit.state).unwind_foreign_frame(owner, locals, loans);
            exit.answer.value.participants = super::recursive_calls::normalize_participants(
                &exit.answer.value.participants,
                loans,
            );
        }
    }
    pub(super) fn restore_foreign_exit_overlays(
        &mut self,
        overlay: &[(BindingId, BTreeSet<Participant>, bool)],
        epoch: u32,
    ) {
        for exit in self
            .foreign_abort_exits
            .iter_mut()
            .filter(|exit| exit.identity.0 >= epoch)
        {
            Arc::make_mut(&mut exit.state).restore_foreign_overlays(overlay);
        }
    }
    pub(super) fn finish_foreign_callback_exits(
        &mut self,
        epoch: u32,
        before: &flow::FlowSnapshot,
    ) -> BTreeSet<u32> {
        let mut ids = BTreeSet::new();
        for exit in self
            .foreign_abort_exits
            .iter_mut()
            .filter(|exit| exit.identity.0 >= epoch)
        {
            exit.before = Arc::new(before.clone());
            ids.insert(exit.identity.0);
        }
        ids
    }
    pub(super) fn can_record_foreign_abort(&mut self, span: Span) -> bool {
        if !self.resume_contexts.is_empty()
            || !self.deferred_arm_cleanups.is_empty()
            || !self.suspended_cleanups.is_empty()
            || !self.budget_recoveries.is_empty()
            || !self.loop_breaks.is_empty()
            || self.loop_depth > 0
            || self.concurrency.has_retained_authority()
            || self.bindings.iter().any(|binding| {
                binding.alive
                    && matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
            })
        {
            self.unsupported(span,"conditional foreign abort retains scoped cleanup, resumption, loop or resource ownership requiring a separate exit contract");
            return false;
        }
        true
    }

    pub(super) fn record_foreign_abort(
        &mut self,
        before: &flow::FlowSnapshot,
        frame: &Frame,
        span: Span,
    ) {
        let Some((boundary, answer)) = self.pending_abort.take() else {
            return;
        };
        let Some(owner) = self.handler_boundary_owner(boundary) else {
            self.unsupported(
                span,
                "foreign callback abort has no active checked delimiter owner",
            );
            return;
        };
        self.transfer_results(&answer.value, frame.owner, owner);
        let identity = self.cause(
            CauseKind::Handler,
            span,
            "foreign callback's at-most-once abort keeps a separate heap and Result-duty exit",
            [answer.value.cause],
        );
        let state = self.snapshot_flow();
        let obligations = self.pending_handler_obligations.clone();
        self.restore_definition_state(before);
        for (owner, obligations) in obligations {
            self.pending_handler_obligations
                .entry(owner)
                .or_default()
                .include(&obligations, true);
        }
        self.foreign_abort_exits.push(AbortExit {
            identity,
            boundary,
            answer,
            span,
            before: Arc::new(before.clone()),
            state: Arc::new(state),
        });
    }

    pub(super) fn finish_foreign_abort_exits(
        &mut self,
        boundary: u32,
        normal: &mut EvaluatedValue,
    ) -> bool {
        let (mut matching, remaining): (Vec<_>, Vec<_>) =
            std::mem::take(&mut self.foreign_abort_exits)
                .into_iter()
                .partition(|exit| exit.boundary == boundary);
        self.foreign_abort_exits = remaining;
        let replaced = !matching.is_empty();
        while let Some(mut exit) = matching.pop() {
            let mut before = (*exit.before).clone();
            let mut state = (*exit.state).clone();
            self.reset_foreign_abort_exits(&mut before);
            self.reset_foreign_abort_exits(&mut state);
            let no_normal = normal.value.ty == Ty::Never;
            if !no_normal {
                self.receive_boundary_type(&mut exit.answer, normal, exit.span);
            }
            self.transport_evaluation_packet(normal, exit.span);
            self.transport_evaluation_packet(&mut exit.answer, exit.span);
            let before = self
                .rebase_flow_snapshot(&before, exit.span)
                .unwrap_or(before);
            let state = self
                .rebase_flow_snapshot(&state, exit.span)
                .unwrap_or(state);
            let mut joined = self.branch_flow(
                &before,
                &state,
                &exit.answer.value,
                &normal.value,
                exit.span,
            );
            joined.cause=self.cause(CauseKind::BranchJoin,exit.span,"foreign callback abort and zero-callback continuation retain separate exit coverage",[joined.cause,exit.identity]);
            if no_normal {
                *normal = exit.answer;
            }
            normal.value = joined;
        }
        replaced
    }
}
