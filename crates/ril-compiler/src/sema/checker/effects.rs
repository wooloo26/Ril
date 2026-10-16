use super::*;

#[derive(Clone)]
pub(super) struct HandlerDefinition {
    site: Option<HandlerSiteId>,
    callable_owner: Option<CallableOwner>,
    boundary: u32,
    arms: BTreeMap<String, HandlerArm>,
    lexical: Env,
    span: Span,
    answer: Option<Ty>,
    owner: ScopeId,
    abort_answers: Vec<Value>,
    post_checked: BTreeSet<String>,
    retained_post_checks: BTreeMap<String, Vec<Ty>>,
    outer: Vec<usize>,
}
pub(super) struct RetainedActivation {
    definitions: Vec<(usize, HandlerDefinition)>,
    active: Vec<usize>,
    boundary: u32,
    diagnostics: usize,
}
#[derive(Clone)]
pub(super) struct ResumeContext {
    owner: ScopeId,
    result: Ty,
    supplied: Option<Value>,
    pub(super) loans: BTreeSet<LoanId>,
    abortive: bool,
    pub(super) receptions: Vec<super::super::resumption::OperationReception>,
}
#[derive(Clone)]
pub(super) struct ControlState {
    pub(super) foreign_abort_exits: Vec<external_exits::AbortExit>,
    concurrency: concurrent::State,
    pub(super) budget_recoveries: Vec<budget::Recovery>,
    resumes: Vec<ResumeContext>,
    ended: BTreeSet<LoanId>,
    pub(super) abort: Option<(u32, Value)>,
    breaks: Vec<(ScopeId, Vec<Value>)>,
    continuations: Vec<(ScopeId, bool)>,
    completed_cleanups: BTreeSet<BindingId>,
    suspended_cleanups: BTreeMap<ScopeId, Vec<BindingId>>,
    deferred_cleanups: Vec<cleanup::DeferredArmCleanup>,
    result_exits: BTreeMap<(u32, u32, u32, u32), bool>,
    result_returns: BTreeMap<(u32, u32), bool>,
}
impl ControlState {
    pub(super) fn channel_flow_mut(&mut self) -> &mut concurrent::messages::Flow {
        &mut self.concurrency.message_flow
    }
    pub(super) fn concurrent_state(&self) -> &concurrent::State {
        &self.concurrency
    }
    pub(super) fn ordinary_foreign_abort(&self) -> bool {
        self.resumes.is_empty()
            && self.deferred_cleanups.is_empty()
            && self.suspended_cleanups.is_empty()
            && self.budget_recoveries.is_empty()
            && self.breaks.is_empty()
            && !self.concurrency.has_retained_authority()
    }
    pub(super) fn remap_ordinary_origins(
        &mut self,
        moves: &[(NodeId, NodeId)],
        ordinary: impl Fn(&Value) -> bool,
    ) -> bool {
        if !self.foreign_abort_exits.is_empty()
            || self.concurrency.has_retained_authority()
            || !self.budget_recoveries.is_empty()
            || !self.resumes.is_empty()
            || self.abort.is_some()
            || !self.deferred_cleanups.is_empty()
            || self
                .breaks
                .iter()
                .flat_map(|(_, values)| values)
                .any(|value| !ordinary(value))
        {
            return false;
        }
        for (_, values) in &mut self.breaks {
            for value in values {
                for &(recent, older) in moves {
                    copy::remap_value_origins(value, recent, older);
                }
            }
        }
        true
    }
}
impl Checker {
    pub(super) fn finish_retained_answer_contracts(&mut self) {
        for pending in self.retained_answer_uses.clone() {
            let definition = self.handler_definitions[pending.handler].clone();
            let Some(declaration) = definition.answer else {
                self.unsupported(
                    pending.span,
                    "retained handler declaration has no completed answer constraint",
                );
                continue;
            };
            let declaration = self.expanded(&declaration, &mut BTreeSet::new());
            let invocation = self.expanded(&pending.invocation, &mut BTreeSet::new());
            if !pending.copy && !pending.identity_transport && !pending.ordinary_transport {
                self.unsupported(pending.span, "retained handler answer has no completed copy, identity or ordinary continuation transfer proof");
                continue;
            }
            if !pending.copy
                && !pending.identity_transport
                && pending.ordinary_transport
                && !pending.resumed
            {
                self.unsupported(pending.span,"retained abort reference answers require a separate terminal-exit ownership proof");
                continue;
            }
            if !pending.parametric && declaration != invocation {
                self.error(
                    "E0614",
                    pending.span,
                    format!("fixed retained handler answer {invocation:?} differs from the declaration boundary answer {declaration:?}"),
                    [pending.cause],
                );
                continue;
            }
            if !pending.parametric
                && !self.copy_handler_answer_type(&declaration)
                && !(pending.ordinary_transport
                    && self.ordinary_loop_type(&declaration, &mut BTreeSet::new()))
            {
                self.unsupported(
                    pending.span,
                    "fixed retained handler declaration answer has unresolved ownership",
                );
                continue;
            }
            if pending.resumed
                && (pending.resumption_steps.is_empty()
                    || pending.resumption_steps.iter().any(|index| {
                        self.resumption_steps.get(*index).is_none_or(|step| {
                            step.handler != pending.handler
                                || step.operation != self.operations[&pending.operation].identity
                                || self.scope_parents.get(&step.owner) != Some(&pending.activation)
                                || self.expanded(&step.arm_answer, &mut BTreeSet::new())
                                    != invocation
                        })
                    }))
            {
                self.unsupported(
                    pending.span,
                    "retained handler suffix has no completed invocation answer proof",
                );
                continue;
            }
            let transport = if pending.identity_transport {
                AnswerTransport::Identity
            } else if !pending.copy && pending.ordinary_transport {
                AnswerTransport::OrdinaryChecked
            } else {
                AnswerTransport::CopyChecked
            };
            let cause = self.cause(CauseKind::Handler, pending.span, if pending.parametric { "the resume answer binder forwards the same checked value under its fresh boundary" } else { "the original and fresh copy-answer constraints agree" }, [pending.cause]);
            self.retained_handler_answers
                .push(RetainedHandlerAnswerFact {
                    handler: pending.handler,
                    operation: self.operations[&pending.operation].identity,
                    declaration,
                    invocation,
                    parametric: pending.parametric,
                    transport,
                    span: pending.span,
                    cause,
                    activation: pending.activation,
                    resumption_steps: pending.resumption_steps,
                });
        }
    }
    pub(super) fn has_retained_handlers(&self, callable: &Callable) -> bool {
        self.retained_handlers
            .iter()
            .any(|proof| &proof.callable == callable && !proof.handlers.is_empty())
    }
    pub(super) fn begin_retained_handlers(
        &mut self,
        callable: &Callable,
        context: &[usize],
        frame: &Frame,
    ) -> Option<RetainedActivation> {
        let selected = self
            .retained_handlers
            .iter()
            .find(|proof| &proof.callable == callable)
            .map(|proof| proof.handlers.clone())
            .unwrap_or_else(|| context.to_vec());
        let selected: Vec<_> = selected
            .into_iter()
            .filter(|id| {
                self.handler_definitions[*id]
                    .arms
                    .keys()
                    .any(|name| name != "Div::exhausted")
            })
            .collect();
        if selected.is_empty() {
            return None;
        }
        let boundary = self.next_boundary;
        self.next_boundary += 1;
        let active = self.active_handlers.clone();
        self.active_handlers.retain(|id| !selected.contains(id));
        self.active_handlers.extend(&selected);
        let definitions = selected
            .into_iter()
            .map(|id| {
                let previous = self.handler_definitions[id].clone();
                let fresh = &mut self.handler_definitions[id];
                fresh.boundary = boundary;
                fresh.owner = frame.owner;
                fresh.answer = None;
                fresh.abort_answers.clear();
                fresh.post_checked.clear();
                (id, previous)
            })
            .collect();
        self.block_boundaries.push(boundary);
        Some(RetainedActivation {
            definitions,
            active,
            boundary,
            diagnostics: self.diagnostics.len(),
        })
    }
    pub(super) fn finish_retained_handlers(
        &mut self,
        activation: Option<RetainedActivation>,
        frame: &mut Frame,
        answer: &mut Value,
        span: Span,
    ) {
        let Some(activation) = activation else {
            return;
        };
        // A lexical candidate that the body never selects has no fresh answer
        // obligation in this invocation, including a non-tail outer arm.
        for (id, previous) in &activation.definitions {
            if !frame.obligations.selected_handlers.contains(id) {
                self.handler_definitions[*id] = previous.clone();
            }
        }
        self.finish_deferred_cleanups(activation.boundary, frame, span, answer, 0);
        self.abandon_foreign_activation_results(activation.boundary, frame.owner);
        self.finish_foreign_abort_exits(activation.boundary, answer);
        if self
            .pending_abort
            .as_ref()
            .is_some_and(|(boundary, _)| *boundary == activation.boundary)
        {
            *answer = self.pending_abort.take().unwrap().1;
        }
        self.record_handler_answer(activation.boundary, &answer.ty);
        for diagnostic in &mut self.diagnostics[activation.diagnostics..] {
            if diagnostic.code == "E0625" {
                diagnostic.code = "E0614".into();
                diagnostic.message =
                    "retained handler answer is incompatible with its fresh invocation boundary"
                        .into();
            }
        }
        for (id, mut previous) in activation.definitions {
            for operation in &self.handler_definitions[id].post_checked {
                let answers = previous
                    .retained_post_checks
                    .entry(operation.clone())
                    .or_default();
                if !answers.contains(&answer.ty) {
                    answers.push(answer.ty.clone());
                }
            }
            self.handler_definitions[id] = previous;
        }
        self.active_handlers = activation.active;
        self.block_boundaries.pop();
    }
    pub(super) fn record_retained_handlers(
        &mut self,
        callable: Callable,
        context: &[usize],
        selected: &BTreeSet<usize>,
        answer: &Value,
        activation: ScopeId,
        span: Span,
    ) {
        let handlers: Vec<_> = context
            .iter()
            .copied()
            .filter(|id| {
                selected.contains(id)
                    && self.handler_definitions[*id]
                        .arms
                        .keys()
                        .any(|name| name != "Div::exhausted")
            })
            .collect();
        if handlers.is_empty() {
            return;
        }
        for id in &handlers {
            let definition = self.handler_definitions[*id].clone();
            for (operation, arm) in &definition.arms {
                if !tail_resume(&arm.body) {
                    self.retained_answer_uses
                        .push(retained_answers::PendingUse {
                            handler: *id,
                            operation: operation.clone(),
                            invocation: answer.ty.clone(),
                            copy: self.copy_handler_answer(answer),
                            identity_transport: retained_answers::identity_suffix(&arm.body)
                                && self.identity_handler_answer(answer),
                            parametric: retained_answers::identity_suffix(&arm.body),
                            resumed: audit_resumes(&arm.body, false).count != 0,
                            span,
                            cause: answer.cause,
                            ordinary_transport: self.ordinary_handler_answer(answer),
                            activation,
                            resumption_steps: self
                                .resumption_steps
                                .iter()
                                .enumerate()
                                .filter_map(|(index, step)| {
                                    (step.handler == *id
                                        && step.operation == self.operations[operation].identity
                                        && self.scope_parents.get(&step.owner) == Some(&activation))
                                    .then_some(index)
                                })
                                .collect(),
                        });
                }
                let mut names = BTreeSet::new();
                expressions::collect_names(&arm.body, &mut names);
                for parameter in &arm.parameters {
                    for name in environments::pattern_names(&parameter.pattern) {
                        names.remove(&name);
                    }
                }
                for binding in names.iter().filter_map(|name| definition.lexical.get(name)) {
                    let value = &self.bindings[*binding].value;
                    if value.temporary || !value.scoped.is_empty() || self.contains_resource(value)
                    {
                        self.error("E0614", span, "persistent handler cannot retain scoped resources or a temporary operation loan", [value.cause]);
                    }
                }
            }
        }
        let cause = self.cause(
            CauseKind::Handler,
            span,
            "selected lexical handler definitions have a fresh invocation answer boundary",
            [answer.cause],
        );
        let owner = match &callable {
            Callable::Named(id) => Some(CallableOwner::Function(self.functions[*id].definition)),
            Callable::Closure(id) => self.closures[*id].site.map(CallableOwner::Lambda),
            _ => None,
        };
        self.invocation_witness(
            owner,
            span,
            super::super::effect_identity::InvocationWitnessKind::RetainedHandler(
                RetainedHandlerFact {
                    callable: callable.clone(),
                    span,
                    handlers: handlers.clone(),
                    answer: answer.ty.clone(),
                    cause,
                },
            ),
        );
        if let Some(proof) = self
            .retained_handlers
            .iter_mut()
            .find(|proof| proof.callable == callable)
        {
            for id in handlers {
                if !proof.handlers.contains(&id) {
                    proof.handlers.push(id);
                }
            }
            proof
                .handlers
                .sort_by_key(|id| context.iter().position(|candidate| candidate == id));
        } else {
            let span = match &callable {
                Callable::Closure(id) => self
                    .lambda_contracts
                    .get(id)
                    .map_or(span, |contract| contract.span),
                Callable::Named(id) => self.functions[*id].syntax.span,
                _ => span,
            };
            self.retained_handlers.push(RetainedHandlerFact {
                callable,
                span,
                handlers,
                answer: answer.ty.clone(),
                cause,
            });
        }
    }
    pub(super) fn selected_handler_bodies(&self, selected: &BTreeSet<usize>) -> Vec<(Env, Expr)> {
        selected
            .iter()
            .flat_map(|id| {
                let definition = &self.handler_definitions[*id];
                definition
                    .arms
                    .values()
                    .map(|arm| (definition.lexical.clone(), arm.body.clone()))
            })
            .collect()
    }
    pub(super) fn selected_handler_arms(
        &self,
        selected: &BTreeSet<usize>,
    ) -> Vec<(Env, Vec<HandlerArm>)> {
        selected
            .iter()
            .map(|id| {
                let definition = &self.handler_definitions[*id];
                (
                    definition.lexical.clone(),
                    definition.arms.values().cloned().collect(),
                )
            })
            .collect()
    }
    pub(super) fn value_local_effects(&self, value: &Value) -> BTreeSet<String> {
        let mut residual = BTreeSet::new();
        if self.local_effects.is_empty() {
            return residual;
        }
        for callable in self.graph_callables(value) {
            let stored = match &callable {
                Callable::Named(id) => self.callable_local_effects.get(&(false, *id)),
                Callable::Closure(id) => self.callable_local_effects.get(&(true, *id)),
                Callable::Builtin(name) => {
                    if let Some(operation) = self.operations.get(name)
                        && self.local_effects.contains(&operation.effect)
                    {
                        residual.insert(operation.effect.clone());
                    }
                    None
                }
                _ => None,
            };
            if let Some(stored) = stored {
                residual.extend(stored.iter().cloned());
            }
        }
        residual
    }
    pub(super) fn record_callable_local_effects(
        &mut self,
        closure: bool,
        id: usize,
        frame: &Frame,
        result: &Value,
    ) {
        self.callable_dependencies
            .entry((closure, id))
            .or_default()
            .include(&frame.obligations, false);
        if self.local_effects.is_empty() {
            return;
        }
        let mut residual = self.value_local_effects(result);
        residual.extend(
            frame
                .obligations
                .effects
                .intersection(&self.local_effects)
                .cloned(),
        );
        self.callable_local_effects
            .entry((closure, id))
            .or_default()
            .extend(residual);
    }
    pub(super) fn check_local_effect_boundary(
        &mut self,
        block: &Block,
        outer: &Env,
        result: &Value,
        frame: &Frame,
    ) {
        let local: BTreeSet<_> = block
            .statements
            .iter()
            .chain(&block.where_items)
            .filter_map(|statement| match &statement.kind {
                StmtKind::Effect(effect) => Some(effect.name.clone()),
                _ => None,
            })
            .collect();
        if local.is_empty() {
            return;
        }
        let mut escaped = self.value_local_effects(result);
        for binding in outer.values() {
            if self.bindings[*binding].alive {
                escaped.extend(self.value_local_effects(&self.bindings[*binding].value));
            }
        }
        escaped.extend(frame.obligations.effects.iter().cloned());
        for effect in &escaped {
            if !local.contains(effect)
                && !local.iter().any(|family| {
                    self.effects
                        .get(family)
                        .zip(self.effects.get(effect))
                        .is_some_and(|(family, instance)| family.span == instance.span)
                })
            {
                continue;
            }
            let declaration = &self.effects[effect];
            self.error(
                "E0618",
                declaration.span,
                "local effect remains residual in the block answer or surviving storage",
                [],
            );
        }
    }
    pub(super) fn active_handler_window_bindings(&self) -> BTreeSet<BindingId> {
        let mut bindings = BTreeSet::new();
        for handler in &self.active_handlers {
            let definition = &self.handler_definitions[*handler];
            let mut names = BTreeSet::new();
            for arm in definition.arms.values() {
                expressions::collect_names(&arm.body, &mut names);
            }
            bindings.extend(
                names
                    .iter()
                    .filter_map(|name| definition.lexical.get(name).copied()),
            );
        }
        bindings
    }
    /// Repetition can reach a retained recipe after its creating lexical frame
    /// has ended. Keep its entire declaration environment conservatively; a
    /// current `alive` flag alone cannot establish that those bindings are dead.
    pub(super) fn repeated_handler_bindings(&self) -> BTreeSet<BindingId> {
        let mut handlers: BTreeSet<_> = self.active_handlers.iter().copied().collect();
        handlers.extend(
            self.closures
                .iter()
                .flat_map(|closure| closure.handler_context.iter().copied()),
        );
        handlers.extend(
            self.functions
                .iter()
                .flat_map(|function| function.handler_context.iter().copied()),
        );
        let mut pending: Vec<_> = handlers.iter().copied().collect();
        let mut bindings = BTreeSet::new();
        while let Some(id) = pending.pop() {
            let definition = &self.handler_definitions[id];
            bindings.extend(definition.lexical.values().copied());
            for outer in &definition.outer {
                if handlers.insert(*outer) {
                    pending.push(*outer);
                }
            }
        }
        bindings
    }
    pub(super) fn repeated_handler_answers(&self) -> impl Iterator<Item = &Value> {
        self.handler_definitions
            .iter()
            .flat_map(|definition| &definition.abort_answers)
    }
    pub(super) fn scope_exit_handler_bindings(&self) -> BTreeSet<BindingId> {
        self.handler_definitions
            .iter()
            .flat_map(|handler| handler.lexical.values().copied())
            .collect()
    }
    pub(super) fn snapshot_control_flow(&self) -> ControlState {
        ControlState {
            foreign_abort_exits: self.foreign_abort_exits.clone(),
            concurrency: self.concurrency.clone(),
            budget_recoveries: self.budget_recoveries.clone(),
            resumes: self.resume_contexts.clone(),
            ended: self.ended_operation_loans.clone(),
            abort: self.pending_abort.clone(),
            breaks: self.loop_breaks.clone(),
            continuations: self.loop_continuations.clone(),
            completed_cleanups: self.completed_cleanups.clone(),
            suspended_cleanups: self.suspended_cleanups.clone(),
            deferred_cleanups: self.deferred_arm_cleanups.clone(),
            result_exits: self.result_exit_checks.clone(),
            result_returns: self.result_return_checks.clone(),
        }
    }
    pub(super) fn restore_control_flow(&mut self, state: &ControlState) {
        self.foreign_abort_exits = state.foreign_abort_exits.clone();
        self.concurrency = state.concurrency.clone();
        self.budget_recoveries = state.budget_recoveries.clone();
        self.resume_contexts = state.resumes.clone();
        self.ended_operation_loans = state.ended.clone();
        self.pending_abort = state.abort.clone();
        self.loop_breaks = state.breaks.clone();
        self.loop_continuations = state.continuations.clone();
        self.completed_cleanups = state.completed_cleanups.clone();
        self.suspended_cleanups = state.suspended_cleanups.clone();
        self.deferred_arm_cleanups = state.deferred_cleanups.clone();
        self.result_exit_checks = state.result_exits.clone();
        self.result_return_checks = state.result_returns.clone();
    }
    pub(super) fn merge_control_flow(&mut self, states: &[ControlState], span: Span) {
        let Some(first) = states.first() else {
            return;
        };
        self.foreign_abort_exits.clear();
        let mut seen_foreign_exits = BTreeSet::new();
        for exit in states.iter().flat_map(|state| &state.foreign_abort_exits) {
            if seen_foreign_exits.insert(exit.identity.0) {
                self.foreign_abort_exits.push(exit.clone());
            }
        }
        self.loop_continuations = first.continuations.clone();
        for state in &states[1..] {
            for (target, source) in self.loop_continuations.iter_mut().zip(&state.continuations) {
                if target.0 == source.0 {
                    target.1 |= source.1;
                } else {
                    self.unsupported(
                        span,
                        "conditional control flow changes the target loop activation",
                    );
                    break;
                }
            }
        }
        self.merge_concurrent_states(
            &states
                .iter()
                .map(|state| state.concurrency.clone())
                .collect::<Vec<_>>(),
        );
        self.result_exit_checks.clear();
        self.result_return_checks.clear();
        for state in states {
            for (exit, covered) in &state.result_exits {
                self.result_exit_checks
                    .entry(*exit)
                    .and_modify(|old| *old &= covered)
                    .or_insert(*covered);
            }
            for (exit, covered) in &state.result_returns {
                self.result_return_checks
                    .entry(*exit)
                    .and_modify(|old| *old &= covered)
                    .or_insert(*covered);
            }
        }
        let baseline: Vec<_> = first
            .budget_recoveries
            .iter()
            .map(|exit| (exit.boundary, exit.span))
            .collect();
        if states.iter().any(|state| {
            state
                .budget_recoveries
                .iter()
                .map(|exit| (exit.boundary, exit.span))
                .collect::<Vec<_>>()
                != baseline
        }) {
            self.unsupported(
                span,
                "conditional budget ownership requires path-indexed recovery stacks",
            );
        }
        self.budget_recoveries = first.budget_recoveries.clone();
        self.completed_cleanups = first.completed_cleanups.clone();
        self.completed_cleanups.retain(|binding| {
            states
                .iter()
                .all(|state| state.completed_cleanups.contains(binding))
        });
        let baseline: Vec<_> = first
            .deferred_cleanups
            .iter()
            .map(|arm| (arm.boundary, arm.frame.owner))
            .collect();
        if states.iter().any(|state| {
            state
                .deferred_cleanups
                .iter()
                .map(|arm| (arm.boundary, arm.frame.owner))
                .collect::<Vec<_>>()
                != baseline
                || state.suspended_cleanups != first.suspended_cleanups
        }) {
            self.unsupported(
                span,
                "conditional resumed-arm cleanup requires path-indexed pending activations",
            );
        }
        self.deferred_arm_cleanups = first.deferred_cleanups.clone();
        self.suspended_cleanups = first.suspended_cleanups.clone();
        if states.iter().any(|state| state.abort.is_some()) {
            self.unsupported(
                span,
                "conditional delimited abort requires per-exit heap and Result-duty summaries",
            );
            self.pending_abort = None;
        }
        self.resume_contexts = first.resumes.clone();
        for index in 0..self.resume_contexts.len() {
            let alternatives: Vec<_> = states
                .iter()
                .filter_map(|state| state.resumes.get(index))
                .collect();
            if alternatives.len() != states.len() {
                self.unsupported(span, "resumption activation shapes differ across branches");
                continue;
            }
            let supplied: Vec<_> = alternatives
                .iter()
                .filter_map(|context| context.supplied.clone())
                .collect();
            if !supplied.is_empty() && supplied.len() != alternatives.len() {
                self.unsupported(span,"mixed resumed and non-resumed handler paths require continuation-answer summaries");
            }
            if supplied.iter().any(|value| !value.results.is_empty()) && supplied.len() > 1 {
                self.unsupported(span,"conditional resumption carries Result duties requiring a continuation transfer summary");
            }
            let mut values = supplied.into_iter();
            if let Some(mut value) = values.next() {
                for other in values {
                    let cause = self.cause(
                        CauseKind::BranchJoin,
                        span,
                        "alternative affine resumptions preserve their whole operand relations",
                        [value.cause, other.cause],
                    );
                    value = value.join(&other, self.choice(), cause);
                }
                self.resume_contexts[index].supplied = Some(value);
            }
        }
        self.ended_operation_loans = states
            .iter()
            .flat_map(|state| state.ended.iter().copied())
            .collect();
        self.loop_breaks = first.breaks.clone();
        for state in &states[1..] {
            for (index, (owner, values)) in state.breaks.iter().enumerate() {
                if let Some((current_owner, current)) = self.loop_breaks.get_mut(index) {
                    if current_owner != owner {
                        continue;
                    }
                    for value in values {
                        if !current.iter().any(|old| old.same_abstract_value(value)) {
                            current.push(value.clone());
                        }
                    }
                }
            }
        }
    }
    pub(super) fn resuming_arm(&self, owner: ScopeId) -> bool {
        self.resume_contexts
            .last()
            .is_some_and(|context| context.owner == owner && context.supplied.is_some())
    }
    pub(super) fn effect_row(&mut self, annotation: &Annotation) -> BTreeSet<String> {
        let mut resolved = BTreeSet::new();
        for name in effect_row_members(
            annotation
                .text
                .trim()
                .trim_start_matches('@')
                .trim_matches(['{', '}']),
        )
        .into_iter()
        .map(str::trim)
        .filter(|name| !name.is_empty())
        {
            self.resolve_effect_member(name, annotation.span, &mut BTreeSet::new(), &mut resolved);
        }
        resolved
    }
    fn resolve_effect_member(
        &mut self,
        name: &str,
        span: Span,
        visiting: &mut BTreeSet<String>,
        resolved: &mut BTreeSet<String>,
    ) {
        if visiting.len() >= 64 {
            self.unsupported(
                span,
                "effect-set instance expansion exceeds the finite normalization budget",
            );
            return;
        }
        if name.contains('<') && !self.effects.contains_key(name) {
            let source = format!("{name}()");
            let mut parsed = ril_syntax::parse_expression(&source, span.file);
            // Annotation names have already passed source-role validation and
            // lexical resolution. Only the resolver's reserved names may skip
            // the spelling diagnostic when reparsing static arguments.
            parsed.diagnostics.retain(|diagnostic| {
                diagnostic.code != "E0102"
                    || !diagnostic.labels.iter().all(|label| {
                        source
                            .get(label.span.start as usize..label.span.end as usize)
                            .is_some_and(|name| name.starts_with("Ril__"))
                    })
            });
            if parsed.diagnostics.is_empty()
                && let ExprKind::Call { callee, .. } = parsed.expression.kind
                && let ExprKind::Generic { base, arguments } = callee.kind
                && let Some(family) = operation_name(&base)
                && let Some(instance) = self.effect_instance(&family, &arguments, span)
            {
                self.resolve_effect_member(&instance, span, visiting, resolved);
            } else if parsed.diagnostics.is_empty() {
                self.unsupported(span, "effect row instance has unresolved static arguments");
            } else {
                self.error("E0204", span, "invalid effect instance in effect row", []);
            }
            return;
        }
        if !visiting.insert(name.into()) {
            self.unsupported(
                span,
                "cyclic effect-set expansion requires an instance fixed point",
            );
            return;
        }
        match name {
            "Async" => {
                resolved.extend(["Fiber".into(), "Concurrent".into()]);
            }
            "Fiber" | "Concurrent" | "Div" => {
                resolved.insert(name.into());
            }
            _ => {
                if let Some(declaration) = self.effects.get(name).cloned() {
                    if !declaration.generics.is_empty() {
                        self.unsupported(
                            span,
                            "generic effect rows require explicit instance identity and inference",
                        );
                    } else if declaration.members.is_empty() {
                        resolved.insert(name.into());
                    } else {
                        for member in &declaration.members {
                            if let TypeKind::Name { path, arguments } = &member.kind {
                                if arguments.is_empty() {
                                    self.resolve_effect_member(
                                        &path.join("::"),
                                        member.span,
                                        visiting,
                                        resolved,
                                    );
                                } else if let Some(instance) =
                                    self.effect_instance(&path.join("::"), arguments, member.span)
                                {
                                    self.resolve_effect_member(
                                        &instance,
                                        member.span,
                                        visiting,
                                        resolved,
                                    );
                                }
                            } else {
                                self.error(
                                    "E0204",
                                    member.span,
                                    "effect-set members must resolve to effect declarations",
                                    [],
                                );
                            }
                        }
                    }
                } else if self.generic_context.contains_key(name) || name.contains('<') {
                    self.unsupported(
                        span,
                        "symbolic effect row requires an instantiated effect identity",
                    );
                } else {
                    self.error(
                        "E0204",
                        span,
                        format!("unknown effect declaration {name}"),
                        [],
                    );
                }
            }
        }
        visiting.remove(name);
    }
    pub(super) fn declare_system_operations(&mut self) {
        let name = "Fiber::yield".to_owned();
        self.operations.insert(
            name.clone(),
            OperationFact {
                identity: u64::MAX,
                name,
                effect: "Fiber".into(),
                span: Span {
                    file: FileId(u32::MAX),
                    start: 0,
                    end: 0,
                },
                parameters: Vec::new(),
                result: Ty::Unit,
            },
        );
        let name = "Div::exhausted".to_owned();
        self.operations.insert(
            name.clone(),
            OperationFact {
                identity: u64::MAX - 1,
                name,
                effect: "Div".into(),
                span: Span {
                    file: FileId(u32::MAX),
                    start: 0,
                    end: 1,
                },
                parameters: Vec::new(),
                result: Ty::Never,
            },
        );
    }
    pub(super) fn declare_operations(&mut self, effect: &EffectDeclaration) {
        if !effect.generics.is_empty() {
            // A generic family has no operation until a single instance is
            // selected. Never let its declaration stand for all instances.
            let previous = self.generic_context.clone();
            for (index, parameter) in effect.generics.iter().enumerate() {
                self.generic_context.insert(
                    parameter.name.clone(),
                    format!(
                        "{}:{}:effect:{index}:{}",
                        effect.span.file.0, effect.span.start, parameter.name
                    ),
                );
            }
            for operation in &effect.operations {
                for parameter in &operation.parameters {
                    if let Some(ty) = &parameter.ty {
                        let _ = self.ty(ty);
                    }
                }
                if let Some(ty) = &operation.return_type {
                    let _ = self.ty(ty);
                }
            }
            for member in &effect.members {
                let TypeKind::Name { path, arguments } = &member.kind else {
                    self.error(
                        "E0204",
                        member.span,
                        "effect-set members must name an effect declaration",
                        [],
                    );
                    continue;
                };
                if let Some(target) = self.effects.get(&path.join("::")).cloned() {
                    if arguments.len() > target.generics.len()
                        || arguments.len()
                            < target
                                .generics
                                .iter()
                                .filter(|parameter| parameter.default.is_none())
                                .count()
                    {
                        self.error(
                            "E0340",
                            member.span,
                            "effect-set member has the wrong static argument count",
                            [],
                        );
                    }
                    for (argument, parameter) in arguments.iter().zip(&target.generics) {
                        if parameter
                            .name
                            .chars()
                            .next()
                            .is_some_and(char::is_uppercase)
                            && !matches!(
                                parameter.bound.as_ref().map(|bound| &bound.kind),
                                Some(TypeKind::KindArrow { .. } | TypeKind::KeyOf(_))
                            )
                        {
                            let _ = self.ty(argument);
                        }
                    }
                    if !crate::static_eval::effects::mentions_enclosing_binders(
                        &target,
                        arguments,
                        &self.types,
                        &self.generic_context,
                    ) {
                        let _ = self.effect_instance(&target.name, arguments, member.span);
                    }
                } else if self.generic_context.contains_key(&path.join("::")) {
                    self.unsupported(
                        member.span,
                        "effect-valued generic members require an effect-kind substitution proof",
                    );
                } else {
                    self.error(
                        "E0204",
                        member.span,
                        "unknown effect-set member declaration",
                        [],
                    );
                }
            }
            self.generic_context = previous;
            return;
        }
        for operation in &effect.operations {
            let name = format!("{}::{}", effect.name, operation.name);
            let identity = self.operations.get(&name).map_or_else(
                || self.operations.len() as u64,
                |operation| operation.identity,
            );
            let parameters = operation
                .parameters
                .iter()
                .map(|parameter| {
                    (
                        parameter.mode,
                        parameter
                            .ty
                            .as_ref()
                            .map(|ty| self.ty(ty))
                            .unwrap_or(Ty::Unknown),
                    )
                })
                .collect();
            let result = operation
                .return_type
                .as_ref()
                .map(|ty| self.ty(ty))
                .unwrap_or(Ty::Unit);
            self.operations.insert(
                name.clone(),
                OperationFact {
                    identity,
                    name,
                    effect: effect.name.clone(),
                    span: operation.span,
                    parameters,
                    result,
                },
            );
        }
    }
    pub(super) fn explicit_effect_operation(&mut self, expression: &Expr) -> Option<String> {
        let ExprKind::Field {
            base,
            field,
            safe: false,
        } = &expression.kind
        else {
            return None;
        };
        let ExprKind::Generic { base, arguments } = &base.kind else {
            return None;
        };
        let family = operation_name(base)?;
        if !self.effects.contains_key(&family) {
            return None;
        }
        let Some(instance) = self.effect_instance(&family, arguments, expression.span) else {
            return Some(String::new());
        };
        let name = format!("{instance}::{field}");
        if let Some(selected) = self.effect_alias_operation(&name, expression.span) {
            return Some(selected);
        }
        if !self.operations.contains_key(&name) {
            self.error("E0209", expression.span, "effect has no such operation", []);
            return Some(String::new());
        }
        Some(name)
    }
    pub(super) fn effect_alias_operation(&mut self, name: &str, span: Span) -> Option<String> {
        let (family, member) = name.rsplit_once("::")?;
        if !self
            .effects
            .get(family)
            .is_some_and(|effect| !effect.members.is_empty())
        {
            return None;
        }
        let mut instances = BTreeSet::new();
        self.resolve_effect_member(family, span, &mut BTreeSet::new(), &mut instances);
        let candidates: BTreeSet<_> = instances
            .into_iter()
            .map(|instance| format!("{instance}::{member}"))
            .filter(|name| self.operations.contains_key(name))
            .collect();
        if candidates.len() == 1 {
            return candidates.into_iter().next();
        }
        self.error(
            if candidates.is_empty() {
                "E0209"
            } else {
                "E0344"
            },
            span,
            if candidates.is_empty() {
                "no member effect supplies this operation"
            } else {
                "more than one effect instance supplies this operation"
            },
            [],
        );
        Some(String::new())
    }
    fn effect_instance(
        &mut self,
        family: &str,
        arguments: &[TypeExpr],
        span: Span,
    ) -> Option<String> {
        let Some(declaration) = self.effects.get(family).cloned() else {
            self.error(
                "E0204",
                span,
                format!("unknown effect declaration {family}"),
                [],
            );
            return None;
        };
        if crate::static_eval::effects::mentions_enclosing_binders(
            &declaration,
            &[],
            &self.types,
            &self.generic_context,
        ) {
            self.unsupported(
                span,
                "local effect captures an enclosing binder without its declaration environment",
            );
            return None;
        }
        let arguments = match arguments
            .iter()
            .map(|argument| self.effect_argument_syntax(argument))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(message) => {
                self.unsupported(span, message);
                return None;
            }
        };
        let instance = match crate::static_eval::effects::instantiate(
            &declaration,
            &arguments,
            &self.types,
            self.layout,
        ) {
            Ok(instance) => instance,
            Err(crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message)) => {
                self.error(code, span, message, []);
                return None;
            }
            Err(crate::static_eval::ArgumentNormalizationError::Unsupported(message)) => {
                self.unsupported(span, message);
                return None;
            }
        };
        if crate::static_eval::effects::mentions_enclosing_binders(
            &instance.declaration,
            &instance.arguments,
            &self.types,
            &self.generic_context,
        ) {
            self.unsupported(
                span,
                "normalized effect instance still depends on an enclosing static binder",
            );
            return None;
        }
        for (parameter, argument) in declaration.generics.iter().zip(&instance.arguments) {
            if let Err(message) = self.effect_argument_syntax(argument) {
                self.unsupported(span, message);
                return None;
            }
            if parameter
                .name
                .chars()
                .next()
                .is_some_and(char::is_uppercase)
                && !matches!(
                    parameter.bound.as_ref().map(|bound| &bound.kind),
                    Some(TypeKind::KindArrow { .. } | TypeKind::KeyOf(_))
                )
            {
                // Even an erased/phantom type argument must name a lawful type.
                let _ = self.ty(argument);
            }
        }
        let key = super::super::effect_identity::EffectInstanceKey {
            declaration: declaration.span,
            name: declaration.name.clone(),
            arguments: instance
                .arguments
                .iter()
                .map(|argument| {
                    crate::static_eval::effects::argument_key(argument, &self.effect_type_binders)
                })
                .collect(),
        };
        if let Some(existing) = self
            .effect_instances
            .iter_mut()
            .find(|existing| existing.key == key)
        {
            existing.sites.insert((span.file.0, span.start, span.end));
            return Some(existing.name.clone());
        }
        let instance = instance.declaration;
        let name = instance.name.clone();
        if self.local_effects.contains(family) {
            self.local_effects.insert(instance.name.clone());
        }
        self.declare_operations(&instance);
        self.effect_instances
            .push(super::super::effect_identity::EffectInstance {
                key,
                name: name.clone(),
                operations: self
                    .operations
                    .values()
                    .filter(|operation| operation.effect == name)
                    .map(|operation| operation.identity)
                    .collect(),
                sites: [(span.file.0, span.start, span.end)].into(),
            });
        self.effects
            .entry(instance.name.clone())
            .or_insert(instance);
        Some(name)
    }
    pub(super) fn register_handler(&mut self, arms: &[HandlerArm], span: Span, frame: &mut Frame) {
        let Some(boundary) = self.block_boundaries.last().copied() else {
            self.unsupported(
                span,
                "top-level handler extent requires an executable activation boundary",
            );
            return;
        };
        let mut resolved = BTreeMap::new();
        for arm in arms {
            let Some(name) = self
                .explicit_effect_operation(&arm.operation)
                .or_else(|| operation_name(&arm.operation))
            else {
                self.error(
                    "E0621",
                    arm.span,
                    "handler target is not an effect operation",
                    [],
                );
                continue;
            };
            if name.is_empty() {
                continue;
            }
            let name = self
                .effect_alias_operation(&name, arm.operation.span)
                .unwrap_or(name);
            if name.is_empty() {
                continue;
            }
            if name == "Div::budget" {
                self.error(
                    "E0621",
                    arm.span,
                    "Div::budget is an ordinary callable, not an effect operation",
                    [],
                );
                continue;
            }
            let Some(operation) = self.operations.get(&name).cloned() else {
                if let Some((family, _)) = name.split_once("::") {
                    if self.effects.contains_key(family) {
                        self.error("E0209", arm.span, "effect has no such operation", []);
                    } else {
                        self.error("E0204", arm.span, "unknown effect operation", []);
                    }
                } else if frame.env.contains_key(&name) {
                    self.error(
                        "E0621",
                        arm.span,
                        "handler target resolves to an ordinary value",
                        [],
                    );
                } else {
                    self.error("E0204", arm.span, "unknown handler target", []);
                }
                continue;
            };
            let cause = self.cause(
                CauseKind::Source,
                arm.operation.span,
                "selected effect operation instance",
                [],
            );
            let mut target = Value::scalar(
                Ty::Callable(
                    operation
                        .parameters
                        .iter()
                        .map(|(_, ty)| ty.clone())
                        .collect(),
                    Box::new(operation.result.clone()),
                ),
                None,
                cause,
            );
            target.callables.push(Callable::Builtin(name.clone()));
            self.invocation_expressions
                .push(super::super::effect_identity::InvocationExpression {
                    context: self.invocation_context(frame.callable_owner),
                    expression: self.expression_facts.len(),
                    argument_of: None,
                });
            self.expression_facts.push(super::super::ExpressionFact {
                source_id: arm.operation.hir_id,
                span: arm.operation.span,
                value: target,
            });
            if resolved.insert(name.clone(), arm.clone()).is_some() {
                self.error(
                    "E0622",
                    arm.span,
                    "duplicate operation in one handler definition",
                    [],
                );
            }
            if arm.parameters.len() != operation.parameters.len() {
                self.error(
                    "E0404",
                    arm.span,
                    "handler parameter count does not match the operation",
                    [],
                );
            }
            for (parameter, (mode, _)) in arm.parameters.iter().zip(&operation.parameters) {
                if parameter.mode != *mode {
                    self.error(
                        "E0406",
                        parameter.span,
                        "handler parameter mode must exactly match the operation",
                        [],
                    );
                }
                match parameter.pattern.kind {
                    PatternKind::Name(_)
                    | PatternKind::Wildcard
                    | PatternKind::Tuple(_)
                    | PatternKind::Record { .. } => {}
                    PatternKind::Mode {
                        mode: BindingMode::Var | BindingMode::VarMut,
                        ..
                    } => self.error(
                        "E0403",
                        parameter.span,
                        "handler binders cannot be reassignable",
                        [],
                    ),
                    PatternKind::Mode { .. } => self.error(
                        "E0406",
                        parameter.span,
                        "nested handler binder modes are prohibited",
                        [],
                    ),
                    _ => self.error(
                        "E0345",
                        parameter.span,
                        "handler parameters require irrefutable patterns",
                        [],
                    ),
                }
            }
            let audit = audit_resumes(&arm.body, false);
            if audit.count > 1 {
                self.error(
                    "E0610",
                    arm.span,
                    "one operation arm can resume more than once",
                    [],
                );
            }
            if audit.captured {
                self.error(
                    "E0611",
                    arm.span,
                    "resumption cannot cross a nested callable boundary",
                    [],
                );
            }
            if audit.outward {
                self.unsupported(arm.span,"outward control targets in handler arms require activation-aware continuation transfer");
            }
            if audit.count > 0
                && !tail_resume(&arm.body)
                && post_resume::linear_resume(&arm.body).is_none()
            {
                self.unsupported(
                    arm.span,
                    "post-resumption handler answers require continuation-answer analysis",
                );
            }
        }
        let id = self.handler_definitions.len();
        self.invocation_witness(
            frame.callable_owner,
            span,
            super::super::effect_identity::InvocationWitnessKind::Handler(id),
        );
        let site = frame.callable_owner.map(|owner| {
            self.handler_definitions
                .iter()
                .find(|definition| {
                    definition.callable_owner == Some(owner) && definition.span == span
                })
                .and_then(|definition| definition.site)
                .unwrap_or(HandlerSiteId(id as u32))
        });
        self.handler_definitions.push(HandlerDefinition {
            site,
            callable_owner: frame.callable_owner,
            boundary,
            arms: resolved,
            lexical: frame.env.clone(),
            span,
            answer: None,
            owner: frame.owner,
            abort_answers: Vec::new(),
            post_checked: BTreeSet::new(),
            retained_post_checks: BTreeMap::new(),
            outer: self.active_handlers.clone(),
        });
        self.active_handlers.push(id);
        let names: Vec<_> = self.handler_definitions[id].arms.keys().cloned().collect();
        let budget = std::mem::take(&mut self.budget_coverage);
        for name in names {
            let before = self.snapshot_flow();
            let abort = self.pending_abort.clone();
            let breaks = self.loop_breaks.clone();
            let operation = self.operations[&name].clone();
            let existing = self.heap.nodes.len();
            let mut arguments = Vec::new();
            for (index, (mode, ty)) in operation.parameters.iter().enumerate() {
                let mut value =
                    self.formal_value(ty.clone(), index as u32, span, &mut BTreeSet::new());
                if *mode != ParameterMode::Read && !self.formal_is_immutable(&value.ty) {
                    value.permission = Permission::Write;
                    for node in self.heap.reachable(value.origins.nodes.iter().copied()) {
                        for previous in 0..existing {
                            self.heap.set_relation(
                                node,
                                NodeId(previous as u32),
                                Relation::DISJOINT,
                            );
                        }
                    }
                }
                arguments.push((*mode, value, span));
            }
            let mut context = frame.clone();
            let _ = self.perform_operation(&name, &arguments, span, &mut context);
            self.restore_preview(&before);
            self.pending_abort = abort;
            self.loop_breaks = breaks;
        }
        self.budget_coverage = budget;
    }
    pub(super) fn perform_operation(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        caller: &mut Frame,
    ) -> Value {
        let operation = self.operations[name].clone();
        caller
            .obligations
            .performed_operations
            .insert(operation.identity);
        if operation.parameters.len() != args.len() {
            self.error(
                "E0404",
                span,
                "effect operation argument count mismatch",
                [],
            );
        }
        for ((mode, value, arg_span), (expected, ty)) in args.iter().zip(&operation.parameters) {
            if mode != expected {
                self.error(
                    "E0405",
                    *arg_span,
                    "effect operation argument mode mismatch",
                    [value.cause],
                );
            }
            self.require_type(value, ty, *arg_span);
            if *mode != ParameterMode::Read && value.permission != Permission::Write {
                self.error(
                    "E0520",
                    *arg_span,
                    "effect operation argument has no write authority",
                    [value.cause],
                );
            }
            if *mode != ParameterMode::Read {
                for source in &value.sources {
                    self.use_binding(
                        *source,
                        if *mode == ParameterMode::SharedMut {
                            Mode::Retain
                        } else {
                            Mode::Write
                        },
                        caller,
                    );
                }
            }
        }
        let selected = self
            .active_handlers
            .iter()
            .enumerate()
            .rev()
            .find_map(|(position, id)| {
                self.handler_definitions[*id]
                    .arms
                    .get(name)
                    .cloned()
                    .map(|arm| (position, *id, arm))
            });
        self.budget_handler(
            name,
            selected.as_ref().map(|(_, id, arm)| (*id, arm.span)),
            span,
        );
        if self.effect_answer_probe {
            if selected.is_none() {
                caller.obligations.effects.insert(operation.effect.clone());
                if !caller.callback_call {
                    caller.obligations.concrete_effects.insert(operation.effect);
                }
            }
            return self.formal_value(operation.result, span.start, span, &mut BTreeSet::new());
        }
        let Some((position, id, arm)) = selected else {
            let mutated: Vec<_> = args
                .iter()
                .filter(|(mode, _, _)| *mode != ParameterMode::Read)
                .map(|(_, value, _)| value.clone())
                .collect();
            self.mark_heap_uncertain(&mutated);
            caller.obligations.effects.insert(operation.effect.clone());
            if !caller.callback_call {
                caller.obligations.concrete_effects.insert(operation.effect);
            }
            for (mode, value, arg_span) in args {
                if *mode == ParameterMode::Read {
                    self.deep_read(value, *arg_span, caller);
                } else {
                    for node in self.heap.reachable(value.origins.nodes.iter().copied()) {
                        let mut reached = value.clone();
                        reached.origins = Origins::one(node);
                        self.access(&reached, None, Mode::Write, *arg_span, caller);
                    }
                }
            }
            let mut value =
                self.formal_value(operation.result, span.start, span, &mut BTreeSet::new());
            value.permission = Permission::Read;
            value.construction = false;
            self.produced_symbolic_results(&mut value, span, caller.owner);
            return value;
        };
        caller.obligations.selected_handlers.insert(id);
        let definition = self.handler_definitions[id].clone();
        let active = self.active_handlers.clone();
        self.active_handlers.truncate(position);
        let mut frame = self.frame(definition.lexical.clone(), true);
        frame.callable_owner = definition.callable_owner;
        self.scope_parents.insert(frame.owner, definition.owner);
        let mut loans = BTreeMap::new();
        let mut temporary_loans = BTreeSet::new();
        let mut receptions = Vec::new();
        for (index, (parameter, ((mode, mut value, arg_span), (_, ty)))) in arm
            .parameters
            .iter()
            .zip(args.iter().cloned().zip(&operation.parameters))
            .enumerate()
        {
            value.ty = ty.clone();
            let sources = value.sources.clone();
            if mode == ParameterMode::Read {
                receptions.push(super::super::resumption::OperationReception {
                    parameter: index as u32,
                    mode,
                    loan: None,
                });
                value.permission = Permission::Read;
                value.construction = false;
            } else {
                let loan = LoanId(self.next_loan);
                self.next_loan += 1;
                self.loan_parents.insert(loan, value.participants.clone());
                let cause = self.cause(
                    CauseKind::Loan,
                    arg_span,
                    "operation parameter receives its actual borrowing participant",
                    [value.cause],
                );
                self.operation_loan_starts
                    .push(super::super::resumption::OperationLoanStart {
                        loan,
                        activation: frame.owner,
                        boundary: definition.boundary,
                        handler: id,
                        operation: operation.identity,
                        parameter: index as u32,
                        temporary: mode == ParameterMode::Mut,
                        context: self.invocation_context(frame.callable_owner),
                        source: self.copy_value_snapshot(&value),
                        allocation_epoch: self.recency_moves.len(),
                        span: arg_span,
                        cause,
                    });
                receptions.push(super::super::resumption::OperationReception {
                    parameter: index as u32,
                    mode,
                    loan: Some(loan),
                });
                loans.insert(loan, value.participants.clone());
                if mode == ParameterMode::Mut {
                    temporary_loans.insert(loan);
                }
                value.participants = [Participant::Loan(loan)].into();
                value.temporary |= mode == ParameterMode::Mut;
            }
            let start = frame.locals.len();
            self.bind_pattern(
                &parameter.pattern,
                if mode == ParameterMode::Read {
                    BindingMode::Let
                } else {
                    BindingMode::LetMut
                },
                value,
                &mut frame,
                true,
            );
            for binding in &frame.locals[start..] {
                self.bindings[*binding].forwarded = sources.clone();
            }
            let _ = arg_span;
        }
        self.resume_contexts.push(ResumeContext {
            owner: frame.owner,
            result: operation.result.clone(),
            supplied: None,
            loans: temporary_loans,
            abortive: name == "Div::exhausted",
            receptions,
        });
        let (answer, suffix) = if !tail_resume(&arm.body)
            && let Some((answer, suffix)) = self.arm_prefix(&arm.body, id, name, &mut frame)
        {
            (answer, Some(suffix))
        } else {
            (self.expression(&arm.body, &mut frame), None)
        };
        let context = self.resume_contexts.pop().unwrap();
        let exported = context.supplied.as_ref().unwrap_or(&answer);
        let delayed = if context.supplied.is_some() {
            self.suspended_cleanups
                .remove(&frame.owner)
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let suspended = !delayed.is_empty() || suffix.is_some();
        if !suspended {
            self.finish_results(frame.owner, exported);
        } else {
            self.return_results(exported);
        }
        self.transfer_results(
            exported,
            frame.owner,
            if context.supplied.is_some() {
                caller.owner
            } else {
                definition.owner
            },
        );
        if !suspended {
            for binding in &frame.locals {
                self.check_authority_use(*binding);
                self.bindings[*binding].alive = false;
            }
        }
        self.check_exclusivity(&frame.obligations.accesses, span);
        for access in &mut frame.obligations.accesses {
            access.participants =
                super::recursive_calls::normalize_participants(&access.participants, &loans);
        }
        caller
            .obligations
            .performed_operations
            .extend(&frame.obligations.performed_operations);
        caller
            .obligations
            .selected_handlers
            .extend(&frame.obligations.selected_handlers);
        caller
            .obligations
            .accesses
            .extend(frame.obligations.accesses.iter().cloned());
        if definition.owner == caller.owner {
            self.apply_handler_obligations(&frame.obligations, caller);
        } else {
            self.pending_handler_obligations
                .entry(definition.owner)
                .or_default()
                .include(&frame.obligations, true);
        }
        if suspended {
            let mut continuation_frame = frame.clone();
            continuation_frame.obligations = Obligations::default();
            self.deferred_arm_cleanups
                .push(cleanup::DeferredArmCleanup {
                    boundary: definition.boundary,
                    target: definition.owner,
                    frame: continuation_frame,
                    registrations: delayed,
                    loans: loans.clone(),
                    outer_handlers: active[..position].to_vec(),
                    suffix,
                });
        }
        self.active_handlers = active;
        if let Some(mut supplied) = context.supplied {
            supplied.participants =
                super::recursive_calls::normalize_participants(&supplied.participants, &loans);
            if supplied.temporary {
                supplied.permission = Permission::Read;
                supplied.construction = false;
            }
            supplied
        } else {
            let mut answer = answer;
            answer.participants =
                super::recursive_calls::normalize_participants(&answer.participants, &loans);
            if answer.temporary {
                answer.permission = Permission::Read;
                answer.construction = false;
            }
            answer.cause = self.cause(
                CauseKind::Handler,
                arm.span,
                "abort answer must fit its delimited block continuation",
                [answer.cause],
            );
            self.handler_definitions[id]
                .abort_answers
                .push(answer.clone());
            self.pending_abort = Some((definition.boundary, answer.clone()));
            let mut never = answer;
            never.ty = Ty::Never;
            never.abnormal = true;
            never
        }
    }
    pub(super) fn flush_handler_obligations(&mut self, frame: &mut Frame) {
        if let Some(obligations) = self.pending_handler_obligations.remove(&frame.owner) {
            self.apply_handler_obligations(&obligations, frame);
        }
    }
    pub(super) fn handler_boundary_owner(&self, boundary: u32) -> Option<ScopeId> {
        self.handler_definitions
            .iter()
            .find(|definition| definition.boundary == boundary)
            .map(|definition| definition.owner)
    }
    pub(super) fn handler_answer_boundary(&self, handler: usize) -> u32 {
        self.handler_definitions[handler].boundary
    }
    pub(super) fn apply_handler_obligations(&self, obligations: &Obligations, frame: &mut Frame) {
        frame
            .obligations
            .copy_boundaries
            .extend(&obligations.copy_boundaries);
        frame.obligations.handler_environment |= obligations.handler_environment;
        frame
            .obligations
            .effects
            .extend(obligations.effects.iter().cloned());
        frame
            .obligations
            .concrete_effects
            .extend(obligations.concrete_effects.iter().cloned());
        frame
            .obligations
            .performed_operations
            .extend(&obligations.performed_operations);
        frame
            .obligations
            .selected_handlers
            .extend(&obligations.selected_handlers);
        frame.obligations.retention |= obligations.retention;
        frame.obligations.capture |= obligations.capture;
        frame.obligations.symbolic |= obligations.symbolic;
        for (&binding, &mode) in &obligations.named {
            if self.bindings[binding].owner != frame.owner {
                for map in [
                    &mut frame.obligations.named,
                    &mut frame.obligations.concrete,
                    &mut frame.obligations.direct,
                ] {
                    map.entry(binding)
                        .and_modify(|old| *old = (*old).max(mode))
                        .or_insert(mode);
                }
            } else if self.bindings[binding].parameter && mode != Mode::Read {
                frame.obligations.parameter_write = true;
            }
        }
    }
    pub(super) fn probe_handler_answer(
        &mut self,
        before: &flow::FlowSnapshot,
        prior: &Frame,
        remaining: &[Stmt],
        frame: &mut Frame,
        span: Span,
    ) {
        let pending = self.pending_abort.take().unwrap();
        let actual = self.snapshot_flow();
        let actual_frame = frame.clone();
        self.restore_definition_state(before);
        *frame = prior.clone();
        self.effect_answer_probe = true;
        let mut normal = self.unit(span);
        for statement in remaining {
            normal = self.statement(statement, frame);
            if normal.ty == Ty::Never {
                break;
            }
        }
        if normal.ty != Ty::Never {
            self.require_type(&pending.1, &normal.ty, span);
        }
        self.effect_answer_probe = false;
        self.restore_preview(&actual);
        *frame = actual_frame;
        self.pending_abort = Some(pending);
    }
    pub(super) fn resume_operation(
        &mut self,
        value: Value,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let Some(context) = self.resume_contexts.last().cloned() else {
            self.error(
                "E0623",
                span,
                "resume is outside an operation arm",
                [value.cause],
            );
            return self.unit(span);
        };
        if context.owner != frame.owner {
            self.error(
                "E0611",
                span,
                "resumption crosses a callable boundary",
                [value.cause],
            );
            return self.unit(span);
        }
        if context.abortive {
            self.error(
                "E0822",
                span,
                "budget exhaustion has no returning continuation",
                [value.cause],
            );
            let mut value = value;
            value.ty = Ty::Never;
            return value;
        }
        self.budget_resume(span);
        if context.supplied.is_some() {
            self.error(
                "E0610",
                span,
                "resumption is affine and was already used",
                [value.cause],
            );
        }
        let result = context.result.clone();
        let loans = context.loans.clone();
        let numeric = value.unsuffixed_numeric
            && matches!(
                (&value.ty, &result),
                (Ty::Int(_), Ty::Int(_)) | (Ty::Float(_), Ty::Float(_))
            );
        if !self.compatible(&value.ty, &result) && !numeric {
            self.error(
                "E0624",
                span,
                "resume operand does not match the operation result",
                [value.cause],
            );
        }
        self.require_type(&value, &result, span);
        self.resume_contexts.last_mut().unwrap().supplied = Some(value);
        for loan in &loans {
            let cause = self.cause(
                CauseKind::Loan,
                span,
                "operation loan ends before the continuation starts",
                [],
            );
            let cause = if let Some(previous) = self.operation_loan_ends.get(loan).copied() {
                self.cause(
                    CauseKind::BranchJoin,
                    span,
                    "operation loan ends in every resumed alternative",
                    [previous, cause],
                )
            } else {
                cause
            };
            self.operation_loan_ends.insert(*loan, cause);
        }
        self.ended_operation_loans.extend(loans);
        self.unit(span)
    }
    pub(super) fn check_operation_loan(&mut self, value: &Value, span: Span) {
        if value.participants.iter().any(|participant|matches!(participant,Participant::Loan(id)if self.ended_operation_loans.contains(id))){self.error("E0540",span,"the operation loan ended when resumption started",[value.cause]);}
    }
    pub(super) fn record_handler_answer(&mut self, boundary: u32, answer: &Ty) {
        let mut checks = Vec::new();
        for definition in &mut self.handler_definitions {
            if definition.boundary == boundary {
                definition.answer = Some(answer.clone());
                checks.extend(
                    definition
                        .abort_answers
                        .iter()
                        .cloned()
                        .map(|value| (definition.span, value)),
                );
            }
        }
        let unchecked: Vec<_> =
            self.handler_definitions
                .iter()
                .filter(|definition| definition.boundary == boundary)
                .flat_map(|definition| {
                    definition
                        .arms
                        .iter()
                        .filter(|(name, arm)| {
                            !tail_resume(&arm.body)
                                && post_resume::linear_resume(&arm.body).is_some()
                                && !definition.post_checked.contains(*name)
                                && !retained_answers::identity_suffix(&arm.body)
                                && !definition.retained_post_checks.get(*name).is_some_and(
                                    |answers| {
                                        answers.iter().any(|checked| {
                                            self.expanded(checked, &mut BTreeSet::new())
                                                == self.expanded(answer, &mut BTreeSet::new())
                                        })
                                    },
                                )
                        })
                        .map(|(_, arm)| arm.span)
                })
                .collect();
        for span in unchecked {
            self.unsupported(
                span,
                "unused non-tail handler suffix requires a checked continuation-answer context",
            );
        }
        if *answer != Ty::Never {
            for (span, value) in checks {
                self.require_type(&value, answer, span);
            }
        }
    }
    pub(super) fn mark_post_resume_checked(&mut self, handler: usize, operation: &str) {
        self.handler_definitions[handler]
            .post_checked
            .insert(operation.into());
    }
    pub(super) fn handler_facts(&self) -> Vec<HandlerFact> {
        self.handler_definitions
            .iter()
            .enumerate()
            .map(|(id, definition)| HandlerFact {
                site: definition.site,
                callable_owner: definition.callable_owner,
                id,
                boundary: definition.boundary,
                span: definition.span,
                operations: definition
                    .arms
                    .keys()
                    .filter_map(|name| {
                        self.operations
                            .get(name)
                            .map(|operation| operation.identity)
                    })
                    .collect(),
                arm_spans: definition.arms.values().map(|arm| arm.span).collect(),
                lexical: definition.lexical.clone(),
                answer: definition.answer.clone(),
                arms: definition.arms.values().cloned().collect(),
                outer: definition.outer.clone(),
            })
            .collect()
    }
}
fn effect_row_members(text: &str) -> Vec<&str> {
    let mut members = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (index, token) in text.char_indices() {
        match token {
            '<' | '(' | '[' | '{' => depth += 1,
            '>' | ')' | ']' | '}' => depth = depth.saturating_sub(1),
            '+' | ',' if depth == 0 => {
                members.push(&text[start..index]);
                start = index + 1;
            }
            _ => {}
        }
    }
    members.push(&text[start..]);
    members
}
fn operation_name(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Name(name) => Some(name.clone()),
        ExprKind::Path(path) => Some(path.join("::")),
        ExprKind::Call { callee, .. } => operation_name(callee),
        _ => None,
    }
}
#[derive(Default)]
struct ResumeAudit {
    count: usize,
    captured: bool,
    outward: bool,
}
fn audit_resumes(expr: &Expr, nested: bool) -> ResumeAudit {
    fn include(result: &mut ResumeAudit, other: ResumeAudit) {
        result.count = result.count.saturating_add(other.count);
        result.captured |= other.captured;
        result.outward |= other.outward;
    }
    let mut result = ResumeAudit::default();
    match &expr.kind {
        ExprKind::Control {
            operation: ControlOperation::Resume,
            value,
        } => {
            result.count = 1;
            result.captured = nested;
            if let Some(value) = value {
                include(&mut result, audit_resumes(value, nested));
            }
        }
        ExprKind::Control {
            operation: ControlOperation::Return | ControlOperation::Last | ControlOperation::Next,
            value,
        } => {
            result.outward = !nested;
            if let Some(value) = value {
                include(&mut result, audit_resumes(value, nested));
            }
        }
        ExprKind::Lambda { body, .. } => {
            let audit = audit_resumes(body, true);
            result.captured = audit.captured || audit.count > 0;
        }
        ExprKind::Block(block) | ExprKind::Loop(block) => {
            for statement in &block.statements {
                match &statement.kind {
                    StmtKind::Expr { expression, .. }
                    | StmtKind::HandlerApplication(expression) => {
                        include(&mut result, audit_resumes(expression, nested))
                    }
                    StmtKind::Binding(binding) => {
                        include(&mut result, audit_resumes(&binding.value, nested))
                    }
                    StmtKind::Assignment { target, value, .. } => {
                        include(&mut result, audit_resumes(target, nested));
                        include(&mut result, audit_resumes(value, nested));
                    }
                    StmtKind::Function(function) => {
                        if let Some(body) = &function.body {
                            let audit = audit_resumes(
                                &Expr {
                                    hir_id: None,
                                    kind: ExprKind::Block(body.clone()),
                                    span: body.span,
                                },
                                true,
                            );
                            result.captured |= audit.captured || audit.count > 0;
                        }
                    }
                    _ => {}
                }
            }
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            include(&mut result, audit_resumes(condition, nested));
            let left = audit_resumes(then_branch, nested);
            let right = else_branch
                .as_ref()
                .map(|value| audit_resumes(value, nested))
                .unwrap_or_default();
            result.count += left.count.max(right.count);
            result.captured |= left.captured || right.captured;
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Field { base: operand, .. }
        | ExprKind::Generic { base: operand, .. } => {
            include(&mut result, audit_resumes(operand, nested))
        }
        ExprKind::Binary { left, right, .. }
        | ExprKind::Index {
            base: left,
            index: right,
            ..
        }
        | ExprKind::ComputedField {
            base: left,
            key: right,
        } => {
            include(&mut result, audit_resumes(left, nested));
            include(&mut result, audit_resumes(right, nested));
        }
        ExprKind::Call { callee, arguments } => {
            include(&mut result, audit_resumes(callee, nested));
            for argument in arguments {
                include(&mut result, audit_resumes(&argument.value, nested));
            }
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                include(&mut result, audit_resumes(item, nested));
            }
        }
        ExprKind::Match { value, arms, .. } => {
            include(&mut result, audit_resumes(value, nested));
            let mut maximum = 0;
            for arm in arms {
                let mut audit = audit_resumes(&arm.body, nested);
                if let Some(guard) = &arm.guard {
                    include(&mut audit, audit_resumes(guard, nested));
                }
                maximum = maximum.max(audit.count);
                result.captured |= audit.captured;
                result.outward |= audit.outward;
            }
            result.count = result.count.saturating_add(maximum);
        }
        ExprKind::Map(entries) => {
            for (key, value) in entries {
                include(&mut result, audit_resumes(key, nested));
                include(&mut result, audit_resumes(value, nested));
            }
        }
        ExprKind::Record { members, .. } => {
            for member in members {
                let value = match member {
                    RecordMember::Field(field) => &field.value,
                    RecordMember::Spread(value) => value,
                };
                include(&mut result, audit_resumes(value, nested));
            }
        }
        ExprKind::While { condition, body } => {
            include(&mut result, audit_resumes(condition, nested));
            let mut body = audit_resumes(
                &Expr {
                    hir_id: None,
                    kind: ExprKind::Block(body.clone()),
                    span: body.span,
                },
                nested,
            );
            if body.count > 0 {
                body.count = 2;
            }
            include(&mut result, body);
        }
        ExprKind::For { iterable, body, .. } => {
            include(&mut result, audit_resumes(iterable, nested));
            let mut body = audit_resumes(
                &Expr {
                    hir_id: None,
                    kind: ExprKind::Block(body.clone()),
                    span: body.span,
                },
                nested,
            );
            if body.count > 0 {
                body.count = 2;
            }
            include(&mut result, body);
        }
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation { expression, .. } = part {
                    include(&mut result, audit_resumes(expression, nested));
                }
            }
        }
        ExprKind::Range { start, end, .. } => {
            for value in start.iter().chain(end) {
                include(&mut result, audit_resumes(value, nested));
            }
        }
        ExprKind::Derive { base, recipe } => {
            if let Some(base) = base {
                include(&mut result, audit_resumes(base, nested));
            }
            include(&mut result, audit_resumes(recipe, nested));
        }
        _ => {}
    }
    result
}
fn tail_resume(expr: &Expr) -> bool {
    match &expr.kind{ExprKind::Control{operation:ControlOperation::Resume,..}=>true,ExprKind::Block(block)=>block.statements.last().is_some_and(|statement|matches!(&statement.kind,StmtKind::Expr{expression,..}if tail_resume(expression))),ExprKind::If{then_branch,else_branch:Some(other),..}=>tail_resume(then_branch)&&tail_resume(other),ExprKind::Match{arms,..}=>!arms.is_empty()&&arms.iter().all(|arm|tail_resume(&arm.body)),_=>false}
}
