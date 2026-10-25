//! Finite evaluation retains an explicit witness for every actual invocation.
//! Recovery is a separate path: its writes never guide the protected path.
use super::*;
#[path = "budget_results.rs"]
mod result_exits;

#[derive(Clone)]
pub(super) struct Coverage {
    owner: ScopeId,
    callees: Vec<CauseId>,
    cleanups: Vec<CauseId>,
    complete: bool,
}

#[derive(Clone)]
pub(super) struct Recovery {
    pub boundary: u32,
    pub answer: EvaluatedValue,
    pub span: Span,
    before: Box<flow::FlowSnapshot>,
    state: Box<flow::FlowSnapshot>,
    result_causes: BTreeMap<u32, CauseId>,
}

impl Checker {
    pub(super) fn budget_invoke(&mut self, callable: &Callable, span: Span) {
        if self.budget_coverage.is_empty() {
            return;
        }
        // Sifts are finite only after checking the actual receiver's retained
        // comparator. Their standard-operation hook records that evidence.
        if matches!(callable, Callable::Builtin(name) if matches!(name.as_str(), "Heap::push" | "Heap::pop"))
        {
            return;
        }
        let (description, covered) = match callable {
            Callable::Named(id, _) => (
                "ordinary Ril function entry",
                self.functions[*id].syntax.body.is_some(),
            ),
            Callable::Closure(_) => ("ordinary Ril anonymous callable entry", true),
            Callable::Constructor(_) => ("finite data constructor", true),
            Callable::Symbolic(..) => ("unresolved actual callable coverage", false),
            Callable::Builtin(name) if self.operations.contains_key(name) => (
                "effect request and its selected handler",
                !matches!(
                    self.operations[name].effect.as_str(),
                    "Fiber" | "Concurrent"
                ),
            ),
            Callable::Builtin(name) => (
                "finite language primitive",
                finite_primitive(name) || name.starts_with("Heap::__new_"),
            ),
        };
        let cause = self.cause(
            if covered {
                CauseKind::Call
            } else {
                CauseKind::MissingProof
            },
            span,
            description,
            [],
        );
        for coverage in &mut self.budget_coverage {
            coverage.callees.push(cause);
            coverage.complete &= covered;
        }
        if !covered {
            if matches!(callable, Callable::Symbolic(..))
                || matches!(callable, Callable::Builtin(name) if !self.operations.contains_key(name))
            {
                self.unsupported(
                    span,
                    "finite-evaluation coverage of this actual callable or primitive is unresolved",
                );
            } else {
                self.error(
                    "E0822",
                    span,
                    "finite evaluation reaches excluded or uncovered computation",
                    [cause],
                );
            }
        }
    }

    pub(super) fn budget_handler(
        &mut self,
        _name: &str,
        selected: Option<(usize, Span)>,
        _span: Span,
    ) {
        if self.budget_coverage.is_empty() {
            return;
        }
        // Installation time does not determine charging: every selected arm
        // has paired ordinary/metered entries matched by definition+operation.
        // Native lowering rejects a missing pair, including foreign defaults.
        // The actual arm invocation still contributes all semantic obligations.
        if let Some((_, arm_span)) = selected {
            let cause = self.cause(
                CauseKind::Handler,
                arm_span,
                "actual selected handler entry participates in the protected charging graph",
                [],
            );
            for scope in &mut self.budget_coverage {
                scope.callees.push(cause);
            }
        }
    }

    pub(super) fn budget_resume(&mut self, span: Span) {
        if self.budget_coverage.is_empty() {
            return;
        }
        let cause = self.cause(
            CauseKind::Handler,
            span,
            "actual affine resumption participates in the protected charging graph",
            [],
        );
        for scope in &mut self.budget_coverage {
            scope.callees.push(cause);
        }
    }

    pub(super) fn budget_cleanup(&mut self, callback: &Value, span: Span) {
        if self.budget_coverage.is_empty() {
            return;
        }
        let cause = self.cause(
            CauseKind::Cleanup,
            span,
            "cleanup has its independently checked finite invocation contract",
            [callback.cause],
        );
        for scope in &mut self.budget_coverage {
            scope.cleanups.push(cause);
        }
    }

    pub(super) fn finite_budget(
        &mut self,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        caller: &mut Frame,
    ) -> Value {
        if args.len() != 2 {
            self.error(
                "E0314",
                span,
                "Div::budget requires a limit and a nullary action",
                [],
            );
            return self.unit(span);
        }
        for (mode, value, argument_span) in args {
            if *mode != ParameterMode::Read {
                self.error(
                    "E0405",
                    *argument_span,
                    "Div::budget uses read reception",
                    [value.cause],
                );
            }
        }
        self.require_type(&args[0].1, &Ty::Int("int".into()), args[0].2);
        let mut action = args[1].1.clone();
        action.permission = Permission::Read;
        if action
            .signature
            .as_ref()
            .is_some_and(|signature| !signature.parameters.is_empty())
            || matches!(&action.ty, Ty::Callable(parameters, _) if !parameters.is_empty())
        {
            self.error(
                "E0404",
                args[1].2,
                "budget action must take no arguments",
                [action.cause],
            );
        }
        let errors = self.diagnostics.len();
        let unsupported = self.unsupported.len();
        if self.loop_depth > 0 {
            self.unsupported(
                span,
                "a repeated budget recovery requires iteration-indexed exit ownership",
            );
        }
        let pending_full = self.budget_recoveries.len() >= 64;
        if pending_full {
            self.unsupported(span, "bounded recovery-shape domain requires a summarized block exit before another budget");
        }
        let mut before = self.snapshot_flow();
        let mut protected = self.frame(caller.env.clone(), true);
        self.scopes.set_parent(protected.owner, caller.owner);
        self.budget_coverage.push(Coverage {
            owner: protected.owner,
            callees: Vec::new(),
            cleanups: Vec::new(),
            complete: true,
        });
        let limit = match args[0].1.constant {
            Some(Constant::Integer(value)) => Some(value),
            _ => None,
        };
        let validation_only = self.effect_answer_probe || limit.is_some_and(|value| value <= 0);
        if validation_only {
            self.budget_validation_depth += 1;
        }
        let result = self.invoke_generated_values(&action, Vec::new(), span, &mut protected);
        if validation_only {
            self.budget_validation_depth -= 1;
        }
        self.flush_handler_obligations(&mut protected);
        let mut coverage = self.budget_coverage.pop().unwrap();
        let actual_owner = self
            .completed_summary()
            .and_then(|summary| summary.activation)
            .unwrap_or(protected.owner);
        if protected.obligations.symbolic {
            coverage.complete = false;
            self.unsupported(
                span,
                "finite evaluation retains an unresolved callable dependency",
            );
        }
        if !protected.obligations.effects.is_empty() {
            coverage.complete = false;
            self.error(
                "E0822",
                span,
                "protected action has residual effects",
                [action.cause],
            );
        }
        if protected.obligations.retention || protected.obligations.capture {
            coverage.complete = false;
            self.error(
                "E0822",
                span,
                "protected action exports a retained authority or captured environment",
                [action.cause],
            );
        }
        for (&binding, &mode) in &protected.obligations.named {
            let info = &self.bindings[binding];
            let confined = self.scope_is_within(info.owner, actual_owner)
                || self.scope_is_within(info.owner, coverage.owner);
            let readonly_input = mode == Mode::Read
                && !info.mode.is_reassignable()
                && !info.mode.is_mutable()
                && self.resource_free(&info.value)
                && (info.parameter || info.value.publication == Publication::Immutable);
            if !confined && !readonly_input {
                coverage.complete = false;
                self.error(
                    "E0822",
                    span,
                    "protected invocation retains an outward capability root",
                    [info.value.cause],
                );
            }
        }
        if !result.scoped.is_empty()
            || (!result.results.is_empty() && !self.identity_handler_answer(&result))
        {
            coverage.complete = false;
            self.unsupported(
                span,
                "budget return membership requires path-indexed Result and scoped ownership",
            );
        }
        // The delimited answer's type comes from the protected computation's
        // ordinary type, even when the actual allowance cannot enter it. This
        // visit is isolated by probe_handler_answer's complete flow snapshot.
        if self.effect_answer_probe {
            return result;
        }
        if self.pending_abort.is_some() {
            coverage.complete = false;
            self.unsupported(
                span,
                "protected outward abort requires a budget-specific exit ownership summary",
            );
        }
        // Even the zero/negative cases validate ordinary typing and coverage,
        // but none of the protected state is executed on those paths.
        if limit.is_some_and(|value| value <= 0) {
            self.restore_preview(&before);
        }
        if limit.is_some_and(|value| value < 0) {
            let mut never = self.unit(span);
            never.ty = Ty::Never;
            never.abnormal = true;
            never.cause = self.cause(
                CauseKind::Call,
                span,
                "negative allowance panics before action entry; validation supplies no inspection",
                [args[0].1.cause, action.cause],
            );
            if coverage.complete
                && self.diagnostics.len() == errors
                && self.unsupported.len() == unsupported
            {
                self.save_budget_proof(span, coverage);
            }
            return never;
        }
        self.transfer_results(&result, protected.owner, caller.owner);
        let normal_state = self.snapshot_flow();
        let previous_completed = self.completed_invocation.clone();
        // Exhaustion can occur at the first charged entry. The completed
        // action's inspections, refinements and heap are not a prefix proof.
        // Entry is a conservative state for all admitted readonly outer roots;
        // abandoned action-local producers are absent on this recovery path.
        self.restore_preview(&before);
        let mut recovery_frame = caller.clone();
        recovery_frame.obligations = Obligations::default();
        recovery_frame.returned.clear();
        let origin = self
            .application_effect
            .current_activation()
            .zip(
                self.application_effect
                    .current_call_event()
                    .and_then(|id| self.copy_call_events.get(id.0 as usize)?.callee_expression),
            )
            .map(
                |(anchor, callee)| crate::sema::application_effect::EntryOrigin::Generated {
                    anchor,
                    callee: ril_compiler_core::ids::EvaluationOccurrenceId(callee as u32),
                    inputs: vec![],
                },
            )
            .unwrap_or(crate::sema::application_effect::EntryOrigin::Unresolved);
        let recovery =
            self.perform_operation_from("Div::exhausted", &[], span, &mut recovery_frame, origin);
        let recovery_pending = self.pending_handler_obligations.clone();
        let transfer = self.pending_abort.take();
        let answer = transfer.as_ref().map(|(_, answer)| answer.value.clone());
        let mut recovery_state = self.snapshot_flow();
        let result_causes = self.budget_result_exit_causes(
            &before,
            &normal_state,
            &recovery_state,
            [&result, answer.as_ref().unwrap_or(&recovery)],
            limit != Some(0) && result.ty != Ty::Never,
            span,
        );
        coverage.callees.extend(result_causes.values().copied());
        let recovery_writes = recovery_frame
            .obligations
            .accesses
            .iter()
            .any(|access| access.mode != Mode::Read);
        if recovery_writes
            || answer.as_ref().is_some_and(|value| {
                !value.scoped.is_empty()
                    || (!value.origins.nodes.is_empty() && value.results.is_empty())
                    || (!value.results.is_empty() && !self.identity_handler_answer(value))
            })
        {
            coverage.complete = false;
            self.unsupported(
                span,
                "budget recovery writes or reference ownership require per-exit heap summaries",
            );
        }
        self.restore_preview(&normal_state);
        for (owner, obligations) in recovery_pending {
            self.pending_handler_obligations
                .entry(owner)
                .or_default()
                .include(&obligations, true);
        }
        self.completed_invocation = previous_completed;
        self.include_budget_obligations(&protected.obligations, caller);
        self.include_budget_obligations(&recovery_frame.obligations, caller);
        if coverage.complete
            && self.diagnostics.len() == errors
            && self.unsupported.len() == unsupported
        {
            self.save_budget_proof(span, coverage);
        }
        if limit == Some(0) || result.ty == Ty::Never {
            // There is no continuing normal action on this path. Restore the
            // actual recovery state, including its own producers/inspection,
            // instead of gifting it the discarded validation/action state.
            self.restore_definition_state(&recovery_state);
            self.apply_budget_result_causes(&result_causes);
            self.pending_abort = transfer;
            return recovery;
        }
        if let Some((boundary, answer)) = transfer
            && !pending_full
        {
            // Pending siblings are represented by the outer work list, never
            // recursively copied into each stored exit's baseline.
            self.clear_budget_exits(&mut before);
            self.clear_budget_exits(&mut recovery_state);
            self.budget_recoveries.push(Recovery {
                boundary,
                answer,
                span,
                before: Box::new(before),
                state: Box::new(recovery_state),
                result_causes,
            });
        }
        self.transport_flow_value(&result, &normal_state, span)
    }

    fn save_budget_proof(&mut self, span: Span, coverage: Coverage) {
        let invocation_cause = self.cause(
            CauseKind::Call,
            span,
            "this protected invocation and its finite cleanup have complete budget coverage",
            coverage
                .callees
                .iter()
                .chain(coverage.cleanups.iter())
                .copied(),
        );
        self.expression_witness(
            span,
            super::super::effect_identity::InvocationWitnessKind::Budget(
                super::super::BudgetProof {
                    span,
                    exhaustion_operation: self.operations["Div::exhausted"].identity,
                    callee_coverage: coverage.callees.clone(),
                    cleanup_coverage: coverage.cleanups.clone(),
                    cause: invocation_cause,
                },
            ),
        );
        let mut callees = coverage.callees;
        let mut cleanups = coverage.cleanups;
        let mut previous_proofs = Vec::new();
        if let Some(index) = self
            .budget_proofs
            .iter()
            .position(|proof| proof.span == span)
        {
            let previous = self.budget_proofs.remove(index);
            previous_proofs.push(previous.cause);
            callees.extend(previous.callee_coverage);
            cleanups.extend(previous.cleanup_coverage);
        }
        callees.sort_by_key(|cause| cause.0);
        callees.dedup();
        cleanups.sort_by_key(|cause| cause.0);
        cleanups.dedup();
        let cause = self.cause(CauseKind::Call, span,
            "every actual protected entry and finite cleanup has complete budget coverage; recovery is outside the allowance",
            callees.iter().chain(cleanups.iter()).chain(previous_proofs.iter()).copied());
        self.budget_proofs.push(super::super::BudgetProof {
            span,
            exhaustion_operation: self.operations["Div::exhausted"].identity,
            callee_coverage: callees.into_iter().collect(),
            cleanup_coverage: cleanups.into_iter().collect(),
            cause,
        });
    }

    fn include_budget_obligations(&self, obligations: &Obligations, caller: &mut Frame) {
        // Names local to the receiving frame are already its own authority.
        // The accesses themselves still participate in borrow/alias checking.
        let mut outward = obligations.clone();
        for (&binding, &mode) in &obligations.named {
            let info = &self.bindings[binding];
            if info.owner == caller.owner && info.parameter && mode != Mode::Read {
                outward.parameter_write = true;
            }
        }
        for map in [
            &mut outward.named,
            &mut outward.concrete,
            &mut outward.direct,
        ] {
            map.retain(|binding, _| self.bindings[*binding].owner != caller.owner);
        }
        caller.obligations.include(&outward, true);
    }

    pub(super) fn finish_budget_recoveries(
        &mut self,
        boundary: u32,
        normal: &mut EvaluatedValue,
    ) -> bool {
        let mut retained = Vec::new();
        let recoveries = std::mem::take(&mut self.budget_recoveries);
        let (mut matching, other): (Vec<_>, Vec<_>) = recoveries
            .into_iter()
            .partition(|exit| exit.boundary == boundary);
        retained.extend(other);
        self.budget_recoveries = retained;
        let replaced = !matching.is_empty();
        while let Some(mut recovery) = matching.pop() {
            self.reset_budget_exits(&mut recovery.before);
            self.reset_budget_exits(&mut recovery.state);
            let no_normal = normal.value.ty == Ty::Never;
            if !no_normal {
                self.receive_boundary_type(&mut recovery.answer, normal, recovery.span);
            }
            self.transport_evaluation_packet(normal, recovery.span);
            self.transport_evaluation_packet(&mut recovery.answer, recovery.span);
            let before = self
                .rebase_flow_snapshot(&recovery.before, recovery.span)
                .unwrap_or_else(|| (*recovery.before).clone());
            let state = self
                .rebase_flow_snapshot(&recovery.state, recovery.span)
                .unwrap_or_else(|| (*recovery.state).clone());
            let cause = self.cause(
                CauseKind::BranchJoin,
                recovery.span,
                "budget recovery aborts the remaining delimited continuation",
                [normal.value.cause, recovery.answer.value.cause],
            );
            let mut joined = self.branch_flow(
                &before,
                &state,
                &recovery.answer.value,
                &normal.value,
                recovery.span,
            );
            joined.cause = cause;
            self.apply_budget_result_causes(&recovery.result_causes);
            if no_normal {
                *normal = recovery.answer;
            }
            normal.value = joined;
        }
        replaced
    }
}

fn finite_primitive(name: &str) -> bool {
    matches!(
        name,
        "assert"
            | "panic"
            | "len"
            | "clone"
            | "clone_immut"
            | "inner"
            | "Some"
            | "Ok"
            | "Err"
            | "Div::budget"
            // Buffer maintenance is finite language work. io_buffered/io_all
            // separately invoke and certify the actual stream callback; this
            // entry never covers a file wait or unresolved operation table.
            | "Io::read_buffer"
            | "Io::read_position"
            | "Io::guard_read"
            | "Io::guard_seek"
            | "Io::write_buffer"
            | "Io::read_buffered"
            | "Io::read_buffered_at"
            | "Io::write_buffered"
            | "Io::flush"
            | "Array::push"
            | "Array::insert"
            | "Array::truncate"
            | "Array::get"
            | "Array::first"
            | "Array::last"
            | "Array::pop"
            | "Array::remove"
            | "Array::reverse"
            | "Array::concat"
            | "Array::contains"
            | "Array::map"
            | "Array::filter"
            | "Array::fold"
            | "Array::find"
            | "Array::any"
            | "Array::all"
            | "Array::for_each"
            | "Options::map"
            | "Options::and_then"
            | "Options::filter"
            | "Options::or_else"
            | "Results::map"
            | "Results::map_err"
            | "Results::and_then"
            | "Results::or_else"
            | "Bytes::slice"
            | "Bytes::len"
            | "Bytes::from_array"
            | "Bytes::to_array"
            | "String::len"
            | "String::byte_len"
            | "String::slice"
            | "StringBuilder::new"
            | "StringBuilder::append"
            | "StringBuilder::append_scalar"
            | "StringBuilder::clear"
            | "StringBuilder::to_string"
            | "Order::compare_int"
            | "Order::compare_str"
            | "Order::compare_bytes"
            | "Order::total_f64"
            | "Heap::new"
            | "Heap::len"
            | "Heap::peek"
    )
}
