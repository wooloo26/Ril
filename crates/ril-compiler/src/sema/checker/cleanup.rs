use super::*;
#[derive(Clone)]
pub(super) struct DeferredArmCleanup {
    pub boundary: u32,
    pub target: ScopeId,
    pub frame: Frame,
    pub typing_environment: crate::sema::context::FrozenEnvironment,
    pub registrations: Vec<BindingId>,
    pub loans: BTreeMap<LoanId, BTreeSet<Participant>>,
    pub outer_handlers: Vec<usize>,
    pub suffix: Option<post_resume::ArmSuffix>,
}

impl Checker {
    pub(super) fn validate_cleanup(&mut self, binding: BindingId, frame: &mut Frame) {
        let preview = self.snapshot_flow();
        let value = self.bindings[binding].value.clone();
        let span = self.bindings[binding].span;
        let mut latent = self.frame(frame.env.clone(), true);
        self.cleanup_callback(&value, span, &mut latent, true);
        self.restore_preview(&preview);
    }
    fn cleanup_callback(&mut self, value: &Value, span: Span, frame: &mut Frame, validate: bool) {
        if self.is_file_handle(value) {
            if value.permission != Permission::Write {
                self.error(
                    "E0520",
                    span,
                    "implicit file release requires scoped mut operation authority",
                    [value.cause],
                );
            }
            if !validate {
                self.access(value, None, Mode::Write, span, frame);
            }
            return;
        }
        let Ty::Record(fields) = self.expanded(&value.ty, &mut BTreeSet::new()) else {
            self.error(
                "E0541",
                span,
                "scoped resource has no accessible structural cleanup contract",
                [value.cause],
            );
            return;
        };
        let Some((mutable, Ty::Callable(parameters, result))) = fields.get("on_close") else {
            self.error(
                "E0541",
                span,
                "scoped resource requires on_close: fn() -> ()",
                [value.cause],
            );
            return;
        };
        if !parameters.is_empty() || **result != Ty::Unit {
            self.error(
                "E0541",
                span,
                "scoped cleanup must take no arguments and return unit",
                [value.cause],
            );
            return;
        }
        let callback = self.project(value, Slot::Field("on_close".into()), span, frame, true);
        self.budget_cleanup(&callback, span);
        if callback.mutable_environment && (!*mutable || value.permission != Permission::Write) {
            self.error(
                "E0520",
                span,
                "mutable cleanup requires scoped mut and a mutable on_close field",
                [callback.cause],
            );
        }
        // Keep the invocation's own footprint separate: an effect already
        // present on the caller must not hide a residual cleanup effect.
        let mut invocation = frame.clone();
        invocation.obligations = Obligations::default();
        invocation.locals.clear();
        invocation.returned.clear();
        invocation.foreign_return_states.clear();
        let result = self.invoke_generated_values(&callback, Vec::new(), span, &mut invocation);
        self.require_type(&result, &Ty::Unit, span);
        let (mut judgment, handlers) =
            self.selected_handler_termination(&invocation.obligations.selected_handlers, span);
        let callback_judgment = self.callable_termination(&callback, span, &handlers);
        judgment.may_diverge |= callback_judgment.may_diverge;
        judgment.unresolved |= callback_judgment.unresolved;
        judgment
            .callable_parameters
            .extend(callback_judgment.callable_parameters);
        if judgment.may_diverge {
            self.error(
                "E0617",
                span,
                "scoped cleanup has no finite termination proof",
                [callback.cause],
            );
        }
        if judgment.unresolved || !judgment.callable_parameters.is_empty() {
            self.unsupported(
                span,
                "scoped cleanup finite proof contains an unresolved callable dependency",
            );
        }
        if !invocation.obligations.effects.is_empty() {
            self.error(
                "E0616",
                span,
                "scoped cleanup has residual effects",
                [callback.cause],
            );
        }
        frame.obligations.include(&invocation.obligations, true);
    }
    pub(super) fn exit_cleanups(
        &mut self,
        start: usize,
        value: &Value,
        span: Span,
        frame: &mut Frame,
    ) {
        let ending: BTreeSet<_> = frame.locals[start..].iter().copied().collect();
        let scoped: BTreeSet<_> = ending
            .iter()
            .copied()
            .filter(|id| {
                !self.completed_cleanups.contains(id)
                    && matches!(
                        self.bindings[*id].mode,
                        BindingMode::Scoped | BindingMode::ScopedMut
                    )
            })
            .collect();
        if scoped.is_empty() {
            return;
        }
        if self.carries_scoped(value, &scoped) {
            self.error(
                "E0604",
                span,
                "scoped authority escapes its registered lexical scope",
                [value.cause],
            );
        }
        let escaped: Vec<_> = self
            .bindings
            .iter()
            .enumerate()
            .filter(|(id, binding)| {
                binding.alive
                    && !ending.contains(id)
                    && self.carries_scoped(&binding.value, &scoped)
            })
            .map(|(_, binding)| (binding.span, binding.value.cause))
            .collect();
        for (span, cause) in escaped {
            self.error(
                "E0604",
                span,
                "outside storage carries authority from an ending scoped binding",
                [cause],
            );
        }
        let registrations = frame.locals[start..].to_vec();
        if self.resuming_arm(frame.owner) {
            self.suspended_cleanups
                .entry(frame.owner)
                .or_default()
                .extend(
                    registrations
                        .into_iter()
                        .rev()
                        .filter(|id| scoped.contains(id)),
                );
            return;
        }
        for id in registrations.into_iter().rev() {
            if scoped.contains(&id) {
                let value = self.bindings[id].value.clone();
                let span = self.bindings[id].span;
                if self.bindings[id].mode == BindingMode::ScopedMut {
                    self.use_binding(id, Mode::Write, frame);
                }
                self.cleanup_callback(&value, span, frame, false);
                self.completed_cleanups.insert(id);
                let cause = self.cause(
                    CauseKind::Cleanup,
                    span,
                    "registered cleanup runs once at the lexical exit",
                    [value.cause],
                );
                self.cleanup_events.push(super::super::CleanupEvent {
                    binding: id,
                    owner: frame.owner,
                    span,
                    resumed_boundary: None,
                    cause,
                });
            }
        }
    }
    pub(super) fn finish_deferred_cleanups(
        &mut self,
        boundary: u32,
        caller: &mut Frame,
        span: Span,
        answer: &mut Value,
        ending_start: usize,
    ) {
        while let Some(index) = self
            .deferred_arm_cleanups
            .iter()
            .rposition(|deferred| deferred.boundary == boundary)
        {
            let mut deferred = self.deferred_arm_cleanups.remove(index);
            let scoped: BTreeSet<_> = deferred.registrations.iter().copied().collect();
            let mut ending: BTreeSet<_> = caller.locals[ending_start..].iter().copied().collect();
            ending.extend(&deferred.frame.locals);
            if self.carries_scoped(answer, &scoped)
                || caller
                    .returned
                    .iter()
                    .any(|value| self.carries_scoped(value, &scoped))
            {
                self.error(
                    "E0604",
                    span,
                    "resumed-arm scoped authority escapes the protected continuation boundary",
                    [answer.cause],
                );
            }
            let escaped: Vec<_> = self
                .bindings
                .iter()
                .enumerate()
                .filter(|(id, binding)| {
                    binding.alive
                        && !ending.contains(id)
                        && self.carries_scoped(&binding.value, &scoped)
                })
                .map(|(_, binding)| (binding.span, binding.value.cause))
                .collect();
            for (source, cause) in escaped {
                self.error(
                    "E0604",
                    source,
                    "outside storage retains an ending resumed-arm scoped authority",
                    [cause],
                );
            }
            let active = std::mem::replace(&mut self.active_handlers, deferred.outer_handlers);
            let previous_typing = self.enter_typing_environment(&deferred.typing_environment);
            if let Some(suffix) = deferred.suffix.take() {
                let scope_exit = self.retire_continuation_writers(
                    boundary,
                    caller,
                    ending_start,
                    &deferred.frame,
                    &deferred.registrations,
                    answer,
                );
                *answer = self.run_arm_suffix(suffix, answer, &mut deferred.frame, scope_exit);
            }
            for binding in deferred.registrations {
                if self.completed_cleanups.contains(&binding) {
                    continue;
                }
                let value = self.bindings[binding].value.clone();
                let source = self.bindings[binding].span;
                if self.bindings[binding].mode == BindingMode::ScopedMut {
                    self.use_binding(binding, Mode::Write, &mut deferred.frame);
                }
                self.cleanup_callback(&value, source, &mut deferred.frame, false);
                self.completed_cleanups.insert(binding);
                let cause = self.cause(
                    CauseKind::Cleanup,
                    source,
                    "resumed-arm cleanup follows completion of its protected continuation",
                    [value.cause, answer.cause],
                );
                self.cleanup_events.push(super::super::CleanupEvent {
                    binding,
                    owner: deferred.frame.owner,
                    span: source,
                    resumed_boundary: Some(boundary),
                    cause,
                });
            }
            self.restore_typing_environment(previous_typing);
            self.active_handlers = active;
            let unit = self.unit(span);
            self.finish_results(deferred.frame.owner, &unit);
            for access in &mut deferred.frame.obligations.accesses {
                access.participants = super::recursive_calls::normalize_participants(
                    &access.participants,
                    &deferred.loans,
                );
            }
            self.check_exclusivity(&deferred.frame.obligations.accesses, span);
            if deferred.target == caller.owner {
                self.apply_handler_obligations(&deferred.frame.obligations, caller);
            } else {
                self.pending_handler_obligations
                    .entry(deferred.target)
                    .or_default()
                    .include(&deferred.frame.obligations, true);
            }
            caller
                .obligations
                .accesses
                .extend(deferred.frame.obligations.accesses);
            for binding in deferred.frame.locals {
                self.check_authority_use(binding);
                self.bindings[binding].alive = false;
            }
        }
    }
    pub(super) fn carries_scoped(&self, value: &Value, scoped: &BTreeSet<BindingId>) -> bool {
        if !value.scoped.is_disjoint(scoped) {
            return true;
        }
        if self
            .graph_callables(value)
            .iter()
            .any(|callable| match callable {
                Callable::Named(id) => self.functions[*id]
                    .captures
                    .iter()
                    .any(|binding| !self.bindings[*binding].value.scoped.is_disjoint(scoped)),
                Callable::Closure(id) => self.closures[*id]
                    .captures
                    .iter()
                    .any(|binding| !self.bindings[*binding].value.scoped.is_disjoint(scoped)),
                _ => false,
            })
        {
            return true;
        }
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        self.fields
            .iter()
            .any(|((node, _), field)| reachable.contains(node) && !field.scoped.is_disjoint(scoped))
    }
}
