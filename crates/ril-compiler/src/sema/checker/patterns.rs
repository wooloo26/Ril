//! Binding match patterns and nonbinding value tests have different authority rules.
use super::expressions::{SourceContext, SourceExpression};
use super::*;

#[derive(Clone)]
struct PatternState {
    bindings: Vec<Value>,
    fields: BTreeMap<(NodeId, Slot), Value>,
    allocations: Vec<CauseId>,
    duties: Vec<ResultDuty>,
    refinements: BTreeMap<narrowing::Place, narrowing::Refinement>,
    handler_obligations: BTreeMap<ScopeId, Obligations>,
    writes: Vec<narrowing::WriteEvent>,
    reads: BTreeMap<(u32, u32, u32, u32), usize>,
    uncertain: BTreeSet<(NodeId, Slot)>,
    arrays: BTreeMap<NodeId, Option<u64>>,
    fixed_arrays: BTreeSet<NodeId>,
    control: effects::ControlState,
    abnormal: bool,
    never: bool,
}

enum PatternOutcome {
    Normal(PatternDecision),
    Exit(Box<Value>),
}

struct PatternDecision {
    matched: Option<bool>,
    inspections: super::super::result_conditions::ConditionInspections,
}

impl Checker {
    fn pattern_outcome(&self, matched: Option<bool>) -> PatternOutcome {
        PatternOutcome::Normal(PatternDecision {
            matched,
            inspections: self.current_condition_inspections(),
        })
    }
    pub(super) fn bind_iteration_pattern(
        &mut self,
        value: Value,
        pattern: &Pattern,
        _span: Span,
        frame: &mut Frame,
    ) {
        self.check_pattern_binder_uniqueness(pattern);
        if !self.patterns_exhaustive(
            &value.ty,
            std::slice::from_ref(pattern),
            &mut BTreeSet::new(),
        ) {
            self.error(
                "E0345",
                pattern.span,
                "iteration element pattern must be irrefutable",
                [value.cause],
            );
            return;
        }
        let bindings = self.checked_pattern_bindings(pattern, &value, None, frame);
        for (name, (mode, value, binding_span)) in bindings {
            self.bind_pattern_alias(&name, mode, value, binding_span, frame);
        }
    }

    pub(super) fn check_pattern_binder_uniqueness(&mut self, pattern: &Pattern) -> bool {
        fn collect(checker: &mut Checker, pattern: &Pattern, valid: &mut bool) -> BTreeSet<String> {
            let mut names = BTreeSet::new();
            let groups: Vec<_> = match &pattern.kind {
                PatternKind::Name(name) => {
                    names.insert(name.clone());
                    vec![]
                }
                PatternKind::Tuple(patterns)
                | PatternKind::Constructor {
                    arguments: patterns,
                    ..
                } => patterns
                    .iter()
                    .map(|pattern| collect(checker, pattern, valid))
                    .collect(),
                PatternKind::Record {
                    fields,
                    rest_binding,
                    ..
                } => {
                    if let Some(name) = rest_binding {
                        names.insert(name.clone());
                    }
                    fields
                        .iter()
                        .map(|field| collect(checker, &field.pattern, valid))
                        .collect()
                }
                PatternKind::Alternative(patterns) => {
                    for pattern in patterns {
                        names.extend(collect(checker, pattern, valid));
                    }
                    vec![]
                }
                PatternKind::Mode { pattern, .. } => return collect(checker, pattern, valid),
                PatternKind::Type { binder, .. } => {
                    names.extend(binder.iter().cloned());
                    vec![]
                }
                _ => vec![],
            };
            for group in groups {
                for name in group {
                    if !names.insert(name.clone()) {
                        *valid = false;
                        checker.error(
                            "E0347",
                            pattern.span,
                            format!("duplicate pattern binding {name}"),
                            [],
                        );
                    }
                }
            }
            names
        }
        let mut valid = true;
        collect(self, pattern, &mut valid);
        valid
    }

    fn pattern_state(&self) -> PatternState {
        PatternState {
            bindings: self
                .bindings
                .iter()
                .map(|binding| binding.value.clone())
                .collect(),
            fields: self.fields.clone(),
            allocations: self.heap.nodes.iter().map(|node| node.cause).collect(),
            duties: self.result_duties.clone(),
            refinements: self.refinements.clone(),
            handler_obligations: self.pending_handler_obligations.clone(),
            writes: self.write_events.clone(),
            reads: self.read_epochs.clone(),
            uncertain: self.uncertain_slots.clone(),
            arrays: self.array_lengths.clone(),
            fixed_arrays: self.fixed_arrays.clone(),
            control: self.snapshot_control_flow(),
            abnormal: false,
            never: false,
        }
    }
    fn restore_pattern_state(&mut self, state: &PatternState) {
        self.refinements = state.refinements.clone();
        self.pending_handler_obligations = state.handler_obligations.clone();
        self.write_events = state.writes.clone();
        self.read_epochs = state.reads.clone();
        self.uncertain_slots = state.uncertain.clone();
        self.array_lengths = state.arrays.clone();
        self.fixed_arrays = state.fixed_arrays.clone();
        self.restore_control_flow(&state.control);
        for (duty, original) in self.result_duties.iter_mut().zip(&state.duties) {
            *duty = original.clone();
        }
        for (binding, value) in self.bindings.iter_mut().zip(&state.bindings) {
            binding.value = value.clone();
        }
        let old_nodes: BTreeSet<_> = state.fields.keys().map(|(node, _)| *node).collect();
        let remove: Vec<_> = self
            .fields
            .keys()
            .filter(|key| old_nodes.contains(&key.0) && !state.fields.contains_key(key))
            .cloned()
            .collect();
        for (node, slot) in remove {
            self.fields.remove(&(node, slot.clone()));
            self.heap.nodes[node.0 as usize].fields.remove(&slot);
        }
        for ((node, slot), value) in &state.fields {
            self.store_field(*node, slot.clone(), value.clone());
        }
        self.refresh_heap_fields();
        self.refresh_writable_roots();
    }
    fn merge_pattern_states(
        &mut self,
        states: &[PatternState],
        baseline: &PatternState,
        span: Span,
    ) {
        self.pending_handler_obligations = baseline.handler_obligations.clone();
        self.write_events = baseline.writes.clone();
        self.read_epochs = baseline.reads.clone();
        self.uncertain_slots = baseline.uncertain.clone();
        if let Some(first) = states.first() {
            self.array_lengths = first.arrays.clone();
            self.fixed_arrays = first.fixed_arrays.clone();
            for state in states.iter().skip(1) {
                self.merge_array_lengths(&state.arrays, &state.fixed_arrays);
            }
        } else {
            self.array_lengths = baseline.arrays.clone();
            self.fixed_arrays = baseline.fixed_arrays.clone();
        }
        for state in states {
            self.uncertain_slots.extend(state.uncertain.iter().cloned());
            let prefix = baseline.writes.len().min(state.writes.len());
            let offset = self.write_events.len();
            self.write_events
                .extend(state.writes[prefix..].iter().cloned());
            for (key, epoch) in &state.reads {
                let remapped = if *epoch < prefix {
                    *epoch
                } else {
                    offset + epoch.saturating_sub(prefix)
                };
                self.read_epochs
                    .entry(*key)
                    .and_modify(|old| *old = (*old).min(remapped))
                    .or_insert(remapped);
            }
            for (owner, obligations) in &state.handler_obligations {
                self.pending_handler_obligations
                    .entry(*owner)
                    .or_default()
                    .include(obligations, true);
            }
        }
        let continuing: Vec<_> = states.iter().filter(|state| !state.never).collect();
        self.refinements = continuing
            .first()
            .map(|state| state.refinements.clone())
            .unwrap_or_default();
        for state in continuing.iter().skip(1) {
            let previous = self.refinements.clone();
            self.merge_refinements(&previous, &state.refinements, false, false);
        }
        let controls = states
            .iter()
            .map(|state| state.control.clone())
            .collect::<Vec<_>>();
        self.merge_control_flow(&controls, span);
        for index in 0..baseline.duties.len() {
            let normal: Vec<_> = states.iter().filter(|state| !state.abnormal).collect();
            if normal.is_empty() {
                self.result_duties[index].abnormal = true;
            } else {
                self.result_duties[index].inspected =
                    normal.iter().all(|state| state.duties[index].inspected);
                self.result_duties[index].returned =
                    normal.iter().all(|state| state.duties[index].returned);
                self.result_duties[index].abnormal =
                    normal.iter().all(|state| state.duties[index].abnormal);
                self.result_duties[index].covered =
                    normal.iter().all(|state| state.duties[index].covered);
            }
        }
        let choice = self.choice();
        for index in 0..baseline.bindings.len() {
            let values = continuing
                .iter()
                .filter_map(|state| state.bindings.get(index))
                .collect::<Vec<_>>();
            let cause = self.cause(
                CauseKind::BranchJoin,
                span,
                "pattern alternatives retain this binding's own value sources",
                values.iter().map(|value| value.cause).collect::<Vec<_>>(),
            );
            let mut values = values.into_iter();
            if let Some(first) = values.next() {
                let value = values.fold(first.clone(), |joined, value| {
                    joined.join(value, choice, cause)
                });
                self.bindings[index].value = value;
            }
        }
        let keys: BTreeSet<_> = continuing
            .iter()
            .flat_map(|state| state.fields.keys().cloned())
            .collect();
        for key in keys {
            let values = continuing
                .iter()
                .filter_map(|state| state.fields.get(&key))
                .collect::<Vec<_>>();
            let cause = self.cause(
                CauseKind::BranchJoin,
                span,
                "pattern alternatives retain this stored member's own value sources",
                values.iter().map(|value| value.cause).collect::<Vec<_>>(),
            );
            let mut values = values.into_iter();
            if let Some(first) = values.next() {
                let value = values.fold(first.clone(), |joined, value| {
                    joined.join(value, choice, cause)
                });
                self.store_field(key.0, key.1, value);
            }
        }
        if states.iter().any(|state| {
            baseline
                .allocations
                .iter()
                .zip(&state.allocations)
                .any(|(old, new)| old != new)
        }) {
            self.unsupported(span,"pattern branches with recycled allocation sites require allocation-version remapping");
        }
        self.refresh_heap_fields();
        self.refresh_writable_roots();
    }

    pub(super) fn check_match(
        &mut self,
        expression: &Expr,
        arms: &[MatchArm],
        type_match: bool,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        self.check_match_expected_source(
            expression,
            arms,
            type_match,
            span,
            frame,
            SourceContext {
                ordinary: None,
                source: None,
            },
        )
        .value
    }

    pub(super) fn check_match_expected_source(
        &mut self,
        expression: &Expr,
        arms: &[MatchArm],
        type_match: bool,
        span: Span,
        frame: &mut Frame,
        context: SourceContext<'_>,
    ) -> SourceExpression {
        if type_match {
            self.unsupported(span, "static type-match pattern checking");
            return SourceExpression {
                value: Value::scalar(
                    Ty::Unknown,
                    None,
                    self.cause(CauseKind::MissingProof, span, "unresolved type match", []),
                ),
                observation: None,
                source_valid: false,
            };
        }
        // Subject and guards are not result positions. An explicit Return
        // inside them still receives its own fixed Frame return target.
        let subject = self.expression(expression, frame);
        let mut source_valid = true;
        if subject.ty == Ty::Never {
            for arm in arms {
                if matches!(arm.pattern.kind, PatternKind::Wildcard) {
                    if let Some(guard) = &arm.guard {
                        let value = self.preview_expression(guard, frame);
                        self.require_type(&value, &Ty::Bool, guard.span);
                    }
                    let checked = self.preview_expression_source(
                        &arm.body,
                        frame,
                        context.ordinary,
                        context.source,
                    );
                    source_valid &= checked.source_valid;
                } else {
                    self.unsupported(
                        arm.pattern.span,
                        "unreachable match arm binding needs a bottom-subject typing context",
                    );
                }
            }
            return SourceExpression {
                value: subject,
                observation: None,
                source_valid,
            };
        }
        if let Some(first) = arms.first() {
            self.inspect_guaranteed_pattern_head(&subject, &first.pattern, span, frame);
        }
        let baseline = self.pattern_state();
        let baseline_recency = self.recency_moves.len();
        let foreign_baseline = (self.foreign_callback_depth > 0).then(|| self.snapshot_flow());
        let old_env = frame.env.clone();
        let local_count = frame.locals.len();
        let mut states = Vec::new();
        let mut result: Option<Value> = None;
        let mut result_state: Option<Vec<ResultDuty>> = None;
        let mut previous = Vec::<Pattern>::new();
        for arm in arms {
            self.restore_pattern_state(&baseline);
            frame.env = old_env.clone();
            if let PatternKind::Constructor { path, .. } = &arm.pattern.kind
                && self.constructor_pattern_excluded(&path.join("::"), &subject)
            {
                if self.universal || self.call_stack.is_empty() {
                    self.error(
                        "E0304",
                        arm.pattern.span,
                        "constructor result equation excludes this concrete match subject",
                        [subject.cause],
                    );
                }
                // An excluded equation has no compatible payload schema. Do
                // not invent origins, execute its body, or count it as coverage.
                // A specialized invocation may exclude an arm that was already
                // checked under the definition's rigid generic parameters.
                continue;
            }
            let possible = pattern_tag_possible(&arm.pattern, &subject, frame);
            let preview = (!possible).then(|| (self.snapshot_flow(), frame.clone()));
            let typed_subject = if possible {
                subject.clone()
            } else {
                // A constructor excluded by a known tag still needs ordinary
                // payload typing. Its invented formal shape exists only in a
                // fully restored preview, never in an executable path's state.
                self.formal_value(
                    subject.ty.clone(),
                    u32::MAX,
                    arm.pattern.span,
                    &mut BTreeSet::new(),
                )
            };
            let unreachable = previous
                .iter()
                .any(|pattern| pattern_subsumes(pattern, &arm.pattern))
                || self.patterns_exhaustive(&subject.ty, &previous, &mut BTreeSet::new());
            if unreachable {
                self.error(
                    "E0304",
                    arm.pattern.span,
                    "match arm is unreachable after an earlier covering pattern",
                    [subject.cause],
                );
            }
            let bindings = self.checked_pattern_bindings(&arm.pattern, &typed_subject, None, frame);
            for (name, (mode, value, binding_span)) in bindings {
                self.bind_pattern_alias(&name, mode, value, binding_span, frame);
            }
            if let Some(guard) = &arm.guard {
                let guard = self.expression(guard, frame);
                self.require_type(&guard, &Ty::Bool, arm.span);
            }
            let returned_before = frame.returned.len();
            let constructor_tag = if let PatternKind::Constructor { path, .. } = &arm.pattern.kind {
                self.resolved_pattern_tag(path, &subject, frame)
            } else {
                None
            };
            let arm_source = constructor_tag.as_ref().and_then(|tag| {
                context
                    .source
                    .and_then(|target| self.constructor_arm_source_target(&subject, tag, target))
            });
            let original_return_source = frame.expected_return_source.clone();
            if let Some(target) = constructor_tag.as_ref().and_then(|tag| {
                original_return_source
                    .as_ref()
                    .and_then(|target| self.constructor_arm_source_target(&subject, tag, target))
            }) {
                frame.expected_return_source = Some(target);
            }
            // Check each actual result before constructor transport or
            // branch join can replace or coarsen its source descriptor.
            let checked = self.expression_expected_source(
                &arm.body,
                frame,
                context.ordinary,
                arm_source.as_ref().or(context.source),
            );
            frame.expected_return_source = original_return_source;
            source_valid &= checked.source_valid;
            let mut value = checked.value;
            if let PatternKind::Constructor { path, .. } = &arm.pattern.kind
                && let Some(tag) = self.resolved_pattern_tag(path, &subject, frame)
            {
                self.transport_constructor_arm_result(
                    &subject,
                    &tag,
                    &mut value,
                    frame.expected_return.as_ref(),
                );
            }
            if frame.returned.len() != returned_before
                && self
                    .result_duties
                    .iter()
                    .any(|duty| duty.owner == frame.owner)
                && frame.returned[returned_before..]
                    .iter()
                    .any(|value| !self.result_return_covered(frame.owner, value))
            {
                self.unsupported(
                    arm.body.span,
                    "Result match with control-flow returns requires exit-path duty coverage",
                );
            }
            let abnormal = value.abnormal;
            if !unreachable && possible {
                if let Some(previous) = &result
                    && !self.compatible(&value.ty, &previous.ty)
                    && !matches!(previous.ty, Ty::Never)
                {
                    self.error(
                        "E0351",
                        arm.body.span,
                        "reachable match arms return incompatible types",
                        [previous.cause, value.cause],
                    );
                }
                if !matches!(value.ty, Ty::Never) {
                    result = Some(if let Some(previous) = result {
                        let cause = self.cause(
                            CauseKind::BranchJoin,
                            span,
                            "match results preserve aligned branch alternatives",
                            [previous.cause, value.cause],
                        );
                        let joined = previous.join(&value, self.choice(), cause);
                        self.merge_result_paths(
                            &baseline.duties,
                            result_state.as_ref().expect("prior result state"),
                            &previous,
                            &value,
                            joined,
                        )
                    } else {
                        value.clone()
                    });
                    result_state = Some(self.result_duties.clone());
                }
                if value.ty == Ty::Never
                    && self.pending_abort.is_some()
                    && let Some(before) = &foreign_baseline
                    && let Some(exit) =
                        self.foreign_abort_snapshot(before, self.snapshot_flow(), arm.body.span)
                {
                    self.pending_abort = None;
                    self.include_foreign_abort_exit(exit);
                }
                let mut state = self.pattern_state();
                state.abnormal = abnormal;
                state.never = matches!(value.ty, Ty::Never);
                states.push(state);
            }
            if arm.guard.is_none() {
                previous.push(arm.pattern.clone());
            }
            for binding in frame.locals.drain(local_count..).collect::<Vec<_>>() {
                if possible {
                    self.check_authority_use(binding);
                }
                self.bindings[binding].alive = false;
            }
            if let Some((before, original)) = preview {
                self.restore_preview(&before);
                *frame = original;
            }
        }
        frame.env = old_env;
        if self.recency_moves.len() != baseline_recency {
            // This older snapshot protocol cannot yet transport every arm and
            // subject. Include preview/exiting arms: their graph identities
            // also advance the same monotonic allocation history.
            self.unsupported(span,"pattern branches with recycled allocation sites require allocation-version remapping");
        }
        if !states.is_empty() {
            self.merge_pattern_states(&states, &baseline, span);
        }
        if !self.patterns_exhaustive(&subject.ty, &previous, &mut BTreeSet::new()) {
            self.error(
                "E0303",
                span,
                "match patterns do not cover every value of the subject type",
                [subject.cause],
            );
        }
        SourceExpression {
            value: result.unwrap_or_else(|| {
                let mut value = self.unit(span);
                value.ty = Ty::Never;
                value
            }),
            // The enclosing expression emitter mints the real match token.
            // Arm tokens must not masquerade as this expression's result.
            observation: None,
            source_valid,
        }
    }

    pub(super) fn check_is(
        &mut self,
        expression: &Expr,
        pattern: &Pattern,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let (subject, subject_expression) = self.expression_observed(expression, frame);
        if subject.ty == Ty::Never {
            self.preview_value_pattern(frame, |checker, frame| {
                checker.check_value_pattern(pattern, &subject, frame)
            });
            return subject;
        }
        self.inspect_guaranteed_pattern_head(&subject, pattern, span, frame);
        let decision = match self.check_value_pattern(pattern, &subject, frame) {
            PatternOutcome::Normal(decision) => decision,
            PatternOutcome::Exit(value) => return *value,
        };
        let cause=self.cause(CauseKind::Projection,span,"nonbinding value test preserves subject provenance and expected-expression obligations",[subject.cause]);
        let mut value = Value::scalar(Ty::Bool, decision.matched.map(Constant::Bool), cause);
        value.condition_inspections = decision.inspections;
        let evaluation = self.record_condition_evaluation(
            &mut value,
            super::super::result_conditions::ConditionKind::Pattern,
            span,
            frame,
        );
        if let Some(subject_expression) = subject_expression {
            self.channel_condition_evaluated(
                evaluation,
                subject_expression,
                &subject,
                span,
                value.cause,
                frame,
            );
        }
        value
    }

    pub(super) fn check_guarded_binding(
        &mut self,
        binding: &Binding,
        value: Value,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        self.inspect_guaranteed_pattern_head(&value, &binding.pattern, span, frame);
        let bindings = self.checked_pattern_bindings(&binding.pattern, &value, None, frame);
        if binding.fallback.is_some() && bindings.is_empty() {
            self.error(
                "E0309",
                binding.pattern.span,
                "a guarded binding must introduce at least one variable",
                [value.cause],
            );
        }
        if matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
            && !matches!(binding.pattern.kind, PatternKind::Name(_))
        {
            self.unsupported(
                span,
                "scoped destructuring registration requires one cleanup per bound resource",
            );
        }
        let guaranteed = self.guarded_pattern_irrefutable(&binding.pattern, &value, frame);
        let possible = pattern_tag_possible(&binding.pattern, &value, frame);
        if let Some(fallback) = &binding.fallback {
            let baseline = self.pattern_state();
            let returned_before = frame.returned.len();
            let failure = if guaranteed {
                self.preview_expression(fallback, frame)
            } else {
                self.expression(fallback, frame)
            };
            if failure.ty != Ty::Never {
                self.error(
                    "E0321",
                    fallback.span,
                    "the failure branch of a guarded binding must diverge",
                    [failure.cause],
                );
            }
            if !possible {
                return failure;
            }
            if !guaranteed {
                let failed = self.pattern_state();
                if !failure.abnormal && failed.writes.len() > baseline.writes.len() {
                    self.unsupported(span,"guarded failure writes require a heap and binding state summary for early exits");
                }
                if !failure.abnormal
                    && baseline
                        .duties
                        .iter()
                        .any(|duty| duty.owner == frame.owner && !duty.covered && !duty.abnormal)
                {
                    self.unsupported(span,"guarded conditional returns require per-exit coverage of existing Result duties");
                }
                if frame.returned[returned_before..]
                    .iter()
                    .any(|value| !value.origins.nodes.is_empty())
                {
                    self.unsupported(
                        span,
                        "guarded failure reference returns require a retained heap exit summary",
                    );
                }
                if baseline
                    .allocations
                    .iter()
                    .zip(&failed.allocations)
                    .any(|(old, new)| old != new)
                {
                    self.unsupported(
                        span,
                        "guarded failure recycled an existing allocation summary",
                    );
                }
                self.restore_pattern_state(&baseline);
                for (owner, obligations) in failed.handler_obligations {
                    self.pending_handler_obligations
                        .entry(owner)
                        .or_default()
                        .include(&obligations, true);
                }
            }
            let test = Expr {
                kind: ExprKind::Is {
                    value: Box::new(binding.value.clone()),
                    pattern: binding.pattern.clone(),
                },
                span,
            };
            self.refine_condition(&test, true, value.cause, frame);
        } else if !guaranteed {
            self.error(
                "E0345",
                binding.pattern.span,
                "a refutable binding pattern requires a diverging else branch",
                [value.cause],
            );
        }
        for (name, (mode, value, binding_span)) in bindings {
            self.bind_name(
                &name,
                mode.unwrap_or(binding.mode),
                value,
                binding_span,
                frame,
                false,
            );
        }
        self.unit(span)
    }
    fn guarded_pattern_irrefutable(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        frame: &mut Frame,
    ) -> bool {
        if irrefutable(pattern) || structurally_irrefutable(pattern) {
            return true;
        }
        if self.patterns_exhaustive(
            &value.ty,
            std::slice::from_ref(pattern),
            &mut BTreeSet::new(),
        ) {
            return true;
        }
        match &pattern.kind {
            PatternKind::Mode { pattern, .. } => {
                self.guarded_pattern_irrefutable(pattern, value, frame)
            }
            PatternKind::Alternative(patterns) => patterns
                .iter()
                .any(|pattern| self.guarded_pattern_irrefutable(pattern, value, frame)),
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                let Some(tag) = self.resolved_pattern_tag(path, value, frame) else {
                    return false;
                };
                if self.constructor_tag_match(value, &tag) != Some(true) {
                    return false;
                }
                if arguments.is_empty() {
                    return true;
                }
                let Some(payload) = self.pattern_payload(value, &tag, pattern.span, frame) else {
                    return false;
                };
                self.guarded_pattern_irrefutable(
                    &constructor_payload_pattern(arguments, pattern.span),
                    &payload,
                    frame,
                )
            }
            _ => false,
        }
    }

    fn bind_pattern_alias(
        &mut self,
        name: &str,
        mode: Option<BindingMode>,
        mut value: Value,
        span: Span,
        frame: &mut Frame,
    ) {
        // An arm is a lexical binding scope, not a new callable environment layer.
        frame.env.remove(name);
        if let Some(mode) = mode {
            self.bind_name(name, mode, value, span, frame, false);
            return;
        }
        value.permission = Permission::Read;
        value.construction = false;
        value.marker = false;
        value.retention_result = false;
        let forwarded = value.sources.clone();
        let id = self.bindings.len();
        let root = RootId(id as u32);
        value.sources = [id].into();
        if value.participants.is_empty() {
            value.participants.insert(Participant::Root(root));
        }
        self.bindings.push(BindingInfo {
            name: name.into(),
            value,
            mode: BindingMode::Let,
            owner: frame.owner,
            lexical_scope: self.block_boundaries.last().copied().unwrap_or(u32::MAX),
            span,
            root,
            cell: None,
            alive: true,
            slot_used: false,
            write_used: false,
            used: false,
            forwarded,
            parameter: false,
        });
        frame.env.insert(name.into(), id);
        frame.locals.push(id);
    }

    fn checked_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        mode: Option<BindingMode>,
        frame: &mut Frame,
    ) -> BTreeMap<String, (Option<BindingMode>, Value, Span)> {
        let mut result = BTreeMap::new();
        match &pattern.kind {
            PatternKind::Name(name) => {
                result.insert(name.clone(), (mode, value.clone(), pattern.span));
            }
            PatternKind::Wildcard => {}
            PatternKind::Mode { mode, pattern } => {
                return self.checked_pattern_bindings(pattern, value, Some(*mode), frame);
            }
            PatternKind::Literal(literal) => {
                let expected = self.literal(literal, pattern.span, frame);
                self.require_type(&expected, &value.ty, pattern.span);
            }
            PatternKind::Value(expression) => {
                if !self.check_pattern_range(expression, value, pattern.span, frame) {
                    self.error(
                        "E0349",
                        pattern.span,
                        "computed expressions are not binding match patterns",
                        [value.cause],
                    );
                }
            }
            PatternKind::Tuple(patterns) => {
                if let Ty::Tuple(items) = self.expanded(&value.ty, &mut BTreeSet::new()) {
                    if items.len() != patterns.len() {
                        self.error(
                            "E0305",
                            pattern.span,
                            "tuple pattern arity differs from its subject",
                            [value.cause],
                        );
                    }
                    for (index, pattern) in patterns.iter().enumerate() {
                        let child = self.project(
                            value,
                            Slot::Tuple(index as u32),
                            pattern.span,
                            frame,
                            true,
                        );
                        let bindings = self.checked_pattern_bindings(pattern, &child, mode, frame);
                        self.extend_pattern_bindings(&mut result, bindings, pattern.span);
                    }
                } else {
                    self.error(
                        "E0301",
                        pattern.span,
                        "tuple pattern requires a tuple subject",
                        [value.cause],
                    );
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                if matches!(
                    self.expanded(&value.ty, &mut BTreeSet::new()),
                    Ty::Record(_)
                ) {
                    for field in fields {
                        let child = self.project(
                            value,
                            Slot::Field(field.name.clone()),
                            field.span,
                            frame,
                            true,
                        );
                        let bindings =
                            self.checked_pattern_bindings(&field.pattern, &child, mode, frame);
                        self.extend_pattern_bindings(&mut result, bindings, field.span);
                    }
                    if rest_binding.is_some() {
                        self.unsupported(pattern.span, "record-rest binding provenance");
                    }
                } else {
                    self.error(
                        "E0301",
                        pattern.span,
                        "record pattern requires a record subject",
                        [value.cause],
                    );
                }
            }
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } => {
                if super::standard::constant_ty(&path.join("::")).is_some() {
                    if *parenthesized {
                        self.error(
                            "E0353",
                            pattern.span,
                            "a nullary variant tag cannot have argument parentheses",
                            [value.cause],
                        );
                    }
                    let expected = Expr {
                        kind: ExprKind::Path(path.clone()),
                        span: pattern.span,
                    };
                    let expected = self.expression(&expected, frame);
                    self.require_type(&expected, &value.ty, pattern.span);
                    return result;
                }
                let Some(name) = self.resolved_pattern_tag(path, value, frame) else {
                    if *parenthesized
                        && frame.env.get(&path.join("::")).is_some_and(|binding| {
                            !self.bindings[*binding].value.callables.is_empty()
                        })
                    {
                        self.error(
                            "E0349",
                            pattern.span,
                            "match patterns cannot contain computed expected expressions",
                            [value.cause],
                        );
                    } else {
                        self.unsupported(pattern.span, "nonstandard constructor pattern identity");
                    }
                    return result;
                };
                if (name == "None"
                    || self
                        .constructor_pattern_info(&name, value)
                        .is_some_and(|info| !info.has_payload))
                    && *parenthesized
                {
                    self.error(
                        "E0353",
                        pattern.span,
                        "a nullary variant tag cannot have argument parentheses",
                        [value.cause],
                    );
                }
                if name == "None" {
                    self.discharge_absent_results(value, pattern.span);
                }
                if matches!(name.as_str(), "Ok" | "Err") {
                    self.channel_assume_result(value, name == "Ok", pattern.span, frame);
                } else if matches!(name.as_str(), "Some" | "None")
                    && matches!(
                        self.expanded(&value.ty, &mut BTreeSet::new()),
                        Ty::Optional(_)
                    )
                {
                    self.channel_assume_optional(value, name == "Some", pattern.span, frame);
                }
                if let Some(payload) = self.pattern_payload(value, &name, pattern.span, frame) {
                    self.validate_constructor_pattern_arity(
                        arguments,
                        *parenthesized,
                        &payload,
                        pattern.span,
                    );
                    if !self.pattern_contains_result(&payload.ty, &mut BTreeSet::new()) {
                        self.discharge_absent_results(value, pattern.span);
                    }
                    if arguments.len() == 1 {
                        return self.checked_pattern_bindings(&arguments[0], &payload, mode, frame);
                    }
                    if !arguments.is_empty() {
                        if let Ty::Tuple(items) = self.expanded(&payload.ty, &mut BTreeSet::new()) {
                            if items.len() != arguments.len() {
                                self.error(
                                    "E0314",
                                    pattern.span,
                                    "constructor tuple payload arity mismatch",
                                    [value.cause],
                                );
                            }
                            for (index, pattern) in arguments.iter().enumerate() {
                                let child = self.project(
                                    &payload,
                                    Slot::Tuple(index as u32),
                                    pattern.span,
                                    frame,
                                    true,
                                );
                                let bindings =
                                    self.checked_pattern_bindings(pattern, &child, mode, frame);
                                self.extend_pattern_bindings(&mut result, bindings, pattern.span);
                            }
                        } else {
                            self.error(
                                "E0314",
                                pattern.span,
                                "constructor payload has a different arity",
                                [value.cause],
                            );
                        }
                    }
                }
            }
            PatternKind::Alternative(patterns) => {
                let baseline = self.pattern_state();
                let original_frame = frame.clone();
                let mut choices = Vec::new();
                let mut states = Vec::new();
                let mut obligations = original_frame.obligations.clone();
                for pattern in patterns {
                    self.restore_pattern_state(&baseline);
                    *frame = original_frame.clone();
                    let possible = pattern_tag_possible(pattern, value, frame);
                    let preview = (!possible).then(|| self.snapshot_flow());
                    let subject = if possible {
                        value.clone()
                    } else {
                        // An inactive tag has a payload schema, but no actual
                        // origin or permission in this invocation. Its formal
                        // witness is used only for or-pattern compatibility.
                        self.formal_value(
                            value.ty.clone(),
                            u32::MAX,
                            pattern.span,
                            &mut BTreeSet::new(),
                        )
                    };
                    let bindings = self.checked_pattern_bindings(pattern, &subject, mode, frame);
                    choices.push((possible, bindings));
                    if let Some(preview) = preview {
                        self.restore_preview(&preview);
                    } else {
                        states.push(self.pattern_state());
                        obligations.include(&frame.obligations, true);
                    }
                }
                *frame = original_frame;
                frame.obligations = obligations;
                if states.is_empty() {
                    self.restore_pattern_state(&baseline);
                } else {
                    self.merge_pattern_states(&states, &baseline, pattern.span);
                }
                let choice = self.choice();
                if let Some((_, first)) = choices.first() {
                    let keys: BTreeSet<_> = first.keys().cloned().collect();
                    for (_, alternative) in &choices[1..] {
                        if keys != alternative.keys().cloned().collect() {
                            self.error(
                                "E0346",
                                pattern.span,
                                "or-pattern alternatives bind different names",
                                [value.cause],
                            );
                        }
                    }
                    for (name, (mode, first, binding_span)) in first {
                        for (_, alternative) in &choices[1..] {
                            if let Some((other_mode, other, _)) = alternative.get(name)
                                && (mode != other_mode || !self.compatible(&first.ty, &other.ty))
                            {
                                self.error(
                                    "E0346",
                                    pattern.span,
                                    "or-pattern binding types or modes differ",
                                    [first.cause, other.cause],
                                );
                            }
                        }
                        let mut actual =
                            choices.iter().filter(|(possible, _)| *possible).filter_map(
                                |(_, alternative)| alternative.get(name).map(|(_, value, _)| value),
                            );
                        let mut joined = actual.next().cloned().unwrap_or_else(|| first.clone());
                        for other in actual {
                            let cause = self.cause(
                                CauseKind::BranchJoin,
                                pattern.span,
                                "or-pattern binding preserves alternative payload origins",
                                [joined.cause, other.cause],
                            );
                            joined = joined.join(other, choice, cause);
                        }
                        result.insert(name.clone(), (*mode, joined, *binding_span));
                    }
                }
            }
            PatternKind::Type { .. } | PatternKind::Error => {
                self.unsupported(pattern.span, "static or invalid binding pattern")
            }
        }
        result
    }
    fn extend_pattern_bindings(
        &mut self,
        target: &mut BTreeMap<String, (Option<BindingMode>, Value, Span)>,
        values: BTreeMap<String, (Option<BindingMode>, Value, Span)>,
        span: Span,
    ) {
        for (name, value) in values {
            if target.insert(name.clone(), value).is_some() {
                self.error(
                    "E0347",
                    span,
                    format!("duplicate pattern binding {name}"),
                    [],
                );
            }
        }
    }

    fn pattern_payload(
        &mut self,
        value: &Value,
        tag: &str,
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        match (self.expanded(&value.ty, &mut BTreeSet::new()), tag) {
            (Ty::Optional(inner), "Some") => {
                let mut payload = value
                    .option_payload
                    .as_ref()
                    .map(|payload| *payload.clone())
                    .unwrap_or_else(|| value.clone());
                payload.ty = *inner;
                payload.permission = payload.permission.meet(value.permission);
                payload.construction &= value.construction;
                payload.retention_result =
                    value.retention_result || (value.construction && payload.retention_result);
                payload.through_return |= value.through_return;
                payload.publication = if payload.publication == Publication::Immutable
                    || value.publication == Publication::Immutable
                {
                    Publication::Immutable
                } else if value.publication == Publication::Live {
                    Publication::Live
                } else {
                    payload.publication
                };
                if payload.ty.scalar() {
                    payload.origins = Origins::default();
                    payload.participants.clear();
                    payload.temporary = false;
                    payload.marker = false;
                } else {
                    payload.participants = value.participants.clone();
                    payload.temporary |= value.temporary;
                    payload.marker = value.marker || (value.construction && payload.marker);
                }
                Some(payload)
            }
            (Ty::Optional(_), "None") => None,
            (_, "Some" | "None") => {
                self.error(
                    "E0301",
                    span,
                    "Option constructor pattern requires an optional subject",
                    [value.cause],
                );
                None
            }
            (Ty::Result(..), "Ok" | "Err") => {
                self.inspect_result(value);
                Some(self.result_payload(value, tag == "Ok", span, frame))
            }
            (_, "Ok" | "Err") => {
                self.error(
                    "E0301",
                    span,
                    "Result constructor pattern requires a Result subject",
                    [value.cause],
                );
                None
            }
            _ if self
                .constructors
                .iter()
                .any(|(identity, info)| identity == tag || info.tag == tag) =>
            {
                if self.constructor_pattern_info(tag, value).is_none() {
                    if self.constructor_pattern_unresolved(tag, value) {
                        self.unsupported(
                            span,
                            "symbolic constructor equations require additional arm-local proof",
                        );
                    } else {
                        self.error(
                            "E0301",
                            span,
                            "constructor pattern belongs to another instantiated subject type",
                            [value.cause],
                        );
                    }
                    None
                } else {
                    self.constructor_pattern_payload(value, tag, span, frame)
                }
            }
            _ => {
                self.unsupported(span, "named sum constructor pattern checking");
                None
            }
        }
    }
    fn resolved_pattern_tag(
        &self,
        path: &[String],
        value: &Value,
        frame: &Frame,
    ) -> Option<String> {
        let name = path.join("::");
        if !(path.len() == 1 && frame.env.contains_key(&name)) {
            if let Some(info) = self.constructor_pattern_info(&name, value) {
                return Some(info.tag);
            }
            // A known constructor with the wrong owner still needs a type
            // error, rather than an inferred tag test that grants an unwrap.
            if self
                .constructors
                .iter()
                .any(|(identity, info)| identity == &name || info.tag == name)
            {
                return Some(name);
            }
        }
        standard_pattern_tag(path, frame).map(str::to_owned)
    }
    fn constructor_tag_match(&self, value: &Value, tag: &str) -> Option<bool> {
        match tag {
            "Some" => value.option_tag,
            "None" => value.option_tag.map(|some| !some),
            "Ok" => value.result_tag,
            "Err" => value.result_tag.map(|ok| !ok),
            _ => value.variant_tag.as_ref().map(|found| found == tag),
        }
    }

    fn validate_constructor_pattern_arity(
        &mut self,
        arguments: &[Pattern],
        parenthesized: bool,
        payload: &Value,
        span: Span,
    ) {
        if !parenthesized {
            return;
        }
        let ty = self.expanded(&payload.ty, &mut BTreeSet::new());
        let valid = match arguments.len() {
            0 => matches!(ty, Ty::Unit),
            1 => true,
            count => matches!(ty,Ty::Tuple(ref items)if items.len()==count),
        };
        if !valid {
            self.error(
                "E0314",
                span,
                "constructor pattern arity differs from its payload type",
                [payload.cause],
            );
        }
    }

    fn pattern_contains_result(&self, ty: &Ty, seen: &mut BTreeSet<String>) -> bool {
        if let Ty::Named(name) = ty
            && !seen.insert(name.clone())
        {
            return false;
        }
        let constructors: Vec<_> = self
            .constructors
            .values()
            .filter(|constructor| &constructor.owner == ty)
            .collect();
        if !constructors.is_empty() {
            return constructors
                .iter()
                .any(|constructor| self.pattern_contains_result(&constructor.payload, seen));
        }
        match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Result(..)
            | Ty::Unknown
            | Ty::Generic(_)
            | Ty::OpenRecord { .. }
            | Ty::Applied { .. }
            | Ty::Projection { .. } => true,
            Ty::Optional(inner) | Ty::Immutable(inner) | Ty::Array(inner) | Ty::Set(inner) => {
                self.pattern_contains_result(&inner, seen)
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|ty| self.pattern_contains_result(ty, seen)),
            Ty::Record(fields) => fields
                .values()
                .any(|(_, ty)| self.pattern_contains_result(ty, seen)),
            Ty::Map(key, value) => {
                self.pattern_contains_result(&key, seen)
                    || self.pattern_contains_result(&value, seen)
            }
            _ => false,
        }
    }

    fn inspect_guaranteed_pattern_head(
        &mut self,
        value: &Value,
        pattern: &Pattern,
        span: Span,
        frame: &mut Frame,
    ) {
        match &pattern.kind {
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                let Some(tag) = self.resolved_pattern_tag(path, value, frame) else {
                    return;
                };
                if matches!(tag.as_str(), "Ok" | "Err")
                    && matches!(
                        self.expanded(&value.ty, &mut BTreeSet::new()),
                        Ty::Result(..)
                    )
                {
                    self.inspect_result(value);
                    if value.result_tag == Some(tag == "Ok")
                        && let Some(pattern) = arguments.first()
                    {
                        let payload = self.result_payload(value, tag == "Ok", span, frame);
                        self.inspect_guaranteed_pattern_head(&payload, pattern, span, frame);
                    }
                } else if tag == "Some"
                    && value.option_tag == Some(true)
                    && let Some(pattern) = arguments.first()
                    && let Some(payload) = self.pattern_payload(value, "Some", span, frame)
                {
                    self.inspect_guaranteed_pattern_head(&payload, pattern, span, frame);
                } else if value.variant_tag.as_deref() == Some(tag.as_str())
                    && let Some(pattern) = arguments.first()
                    && let Some(payload) =
                        self.constructor_pattern_payload(value, &tag, span, frame)
                {
                    self.inspect_guaranteed_pattern_head(&payload, pattern, span, frame);
                }
            }
            PatternKind::Alternative(patterns) => {
                if let Some(pattern) = patterns.first() {
                    self.inspect_guaranteed_pattern_head(value, pattern, span, frame)
                }
            }
            PatternKind::Tuple(patterns) => {
                if let Some(pattern) = patterns.first() {
                    let child = self.project(value, Slot::Tuple(0), span, frame, true);
                    self.inspect_guaranteed_pattern_head(&child, pattern, span, frame)
                }
            }
            PatternKind::Record { fields, .. } => {
                if let Some(field) = fields.first() {
                    let child =
                        self.project(value, Slot::Field(field.name.clone()), span, frame, true);
                    self.inspect_guaranteed_pattern_head(&child, &field.pattern, span, frame)
                }
            }
            _ => {}
        }
    }

    fn check_value_pattern(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        frame: &mut Frame,
    ) -> PatternOutcome {
        match &pattern.kind {
            PatternKind::Wildcard => self.pattern_outcome(Some(true)),
            PatternKind::Name(name) => {
                let expected = Expr {
                    kind: ExprKind::Name(name.clone()),
                    span: pattern.span,
                };
                self.compare_expected(value, &expected, frame)
            }
            PatternKind::Literal(literal) => {
                let expected = Expr {
                    kind: ExprKind::Literal(literal.clone()),
                    span: pattern.span,
                };
                self.compare_expected(value, &expected, frame)
            }
            PatternKind::Value(expected) => {
                if self.check_pattern_range(expected, value, pattern.span, frame) {
                    let matched = if let (
                        ExprKind::Range {
                            start: Some(start),
                            end: Some(end),
                            inclusive,
                        },
                        Some(Constant::Integer(value)),
                    ) = (&expected.kind, &value.constant)
                    {
                        pattern_integer(start)
                            .zip(pattern_integer(end))
                            .map(|(lower, upper)| {
                                *value >= lower
                                    && if *inclusive {
                                        *value <= upper
                                    } else {
                                        *value < upper
                                    }
                            })
                    } else {
                        None
                    };
                    self.pattern_outcome(matched)
                } else {
                    self.compare_expected(value, expected, frame)
                }
            }
            PatternKind::Mode { .. } => {
                self.error(
                    "E0120",
                    pattern.span,
                    "is value tests cannot introduce binding modifiers",
                    [value.cause],
                );
                self.pattern_outcome(None)
            }
            PatternKind::Tuple(patterns) => {
                let Ty::Tuple(items) = self.expanded(&value.ty, &mut BTreeSet::new()) else {
                    self.error(
                        "E0301",
                        pattern.span,
                        "tuple value test requires a tuple",
                        [value.cause],
                    );
                    return self.pattern_outcome(None);
                };
                if items.len() != patterns.len() {
                    self.error(
                        "E0305",
                        pattern.span,
                        "tuple value-test arity mismatch",
                        [value.cause],
                    );
                }
                let mut matched = self.pattern_outcome(Some(true));
                for (index, pattern) in patterns.iter().enumerate() {
                    let component = |checker: &mut Checker, frame: &mut Frame| {
                        let child = checker.project(
                            value,
                            Slot::Tuple(index as u32),
                            pattern.span,
                            frame,
                            true,
                        );
                        checker.check_value_pattern(pattern, &child, frame)
                    };
                    matched = self.pattern_sequence(matched, true, pattern.span, frame, component);
                }
                matched
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                if rest_binding.is_some() {
                    self.error(
                        "E0120",
                        pattern.span,
                        "is record tests do not bind a rest value",
                        [value.cause],
                    );
                }
                let mut matched = self.pattern_outcome(Some(true));
                for field in fields {
                    let component = |checker: &mut Checker, frame: &mut Frame| {
                        let child = checker.project(
                            value,
                            Slot::Field(field.name.clone()),
                            field.span,
                            frame,
                            true,
                        );
                        checker.check_value_pattern(&field.pattern, &child, frame)
                    };
                    matched = self.pattern_sequence(matched, true, field.span, frame, component);
                }
                matched
            }
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } => {
                if super::standard::constant_ty(&path.join("::")).is_some() {
                    if *parenthesized {
                        self.error(
                            "E0353",
                            pattern.span,
                            "a nullary variant tag cannot have argument parentheses",
                            [value.cause],
                        );
                    }
                    let expected = Expr {
                        kind: ExprKind::Path(path.clone()),
                        span: pattern.span,
                    };
                    return self.compare_expected(value, &expected, frame);
                }
                let Some(tag) = self.resolved_pattern_tag(path, value, frame) else {
                    self.unsupported(pattern.span, "nonstandard constructor value-test identity");
                    return self.pattern_outcome(None);
                };
                if (tag == "None"
                    || self
                        .constructor_pattern_info(&tag, value)
                        .is_some_and(|info| !info.has_payload))
                    && *parenthesized
                {
                    self.error(
                        "E0353",
                        pattern.span,
                        "a nullary variant tag cannot have argument parentheses",
                        [value.cause],
                    );
                }
                let tag_match = self.constructor_tag_match(value, &tag);
                let mut head = self.pattern_outcome(tag_match);
                if matches!(tag.as_str(), "Ok" | "Err") {
                    self.channel_tag_test(value, tag == "Ok", pattern.span, frame);
                    if let PatternOutcome::Normal(head) = &mut head {
                        head.inspections.channel_when_true =
                            self.channel_result_outcome(value, tag == "Ok");
                        head.inspections.channel_when_false =
                            self.channel_result_outcome(value, tag != "Ok");
                    }
                } else if matches!(tag.as_str(), "Some" | "None")
                    && matches!(
                        self.expanded(&value.ty, &mut BTreeSet::new()),
                        Ty::Optional(_)
                    )
                {
                    self.channel_optional_tag_test(value, tag == "Some", pattern.span, frame);
                    if let PatternOutcome::Normal(head) = &mut head {
                        head.inspections.channel_when_true =
                            self.channel_optional_outcome(value, tag == "Some");
                        head.inspections.channel_when_false =
                            self.channel_optional_outcome(value, tag != "Some");
                    }
                }
                let payload = self.pattern_payload(value, &tag, pattern.span, frame);
                let component = |checker: &mut Checker, frame: &mut Frame| {
                    if let Some(payload) = payload {
                        checker.validate_constructor_pattern_arity(
                            arguments,
                            *parenthesized,
                            &payload,
                            pattern.span,
                        );
                        if arguments.len() == 1 {
                            checker.check_value_pattern(&arguments[0], &payload, frame)
                        } else if arguments.is_empty() {
                            checker.pattern_outcome(Some(true))
                        } else {
                            let mut matched = checker.pattern_outcome(Some(true));
                            for (index, pattern) in arguments.iter().enumerate() {
                                let child_component = |checker: &mut Checker, frame: &mut Frame| {
                                    let child = checker.project(
                                        &payload,
                                        Slot::Tuple(index as u32),
                                        pattern.span,
                                        frame,
                                        true,
                                    );
                                    checker.check_value_pattern(pattern, &child, frame)
                                };
                                matched = checker.pattern_sequence(
                                    matched,
                                    true,
                                    pattern.span,
                                    frame,
                                    child_component,
                                );
                            }
                            matched
                        }
                    } else {
                        checker.pattern_outcome(Some(true))
                    }
                };
                self.pattern_sequence(head, true, pattern.span, frame, component)
            }
            PatternKind::Alternative(patterns) => {
                let mut matched = self.pattern_outcome(Some(false));
                for pattern in patterns {
                    let component = |checker: &mut Checker, frame: &mut Frame| {
                        checker.check_value_pattern(pattern, value, frame)
                    };
                    matched = self.pattern_sequence(matched, false, pattern.span, frame, component);
                }
                matched
            }
            _ => {
                self.unsupported(pattern.span, "static value-test pattern");
                self.pattern_outcome(None)
            }
        }
    }
    fn pattern_sequence(
        &mut self,
        prior: PatternOutcome,
        conjunction: bool,
        span: Span,
        frame: &mut Frame,
        check: impl FnOnce(&mut Checker, &mut Frame) -> PatternOutcome,
    ) -> PatternOutcome {
        let prior = match prior {
            PatternOutcome::Exit(value) => {
                self.preview_value_pattern(frame, check);
                return PatternOutcome::Exit(value);
            }
            PatternOutcome::Normal(matched) => matched,
        };
        if prior.matched == Some(!conjunction) {
            self.preview_value_pattern(frame, check);
            return PatternOutcome::Normal(prior);
        }
        if prior.matched.is_some() {
            return check(self, frame);
        }
        let baseline = self.pattern_state();
        let parents = prior
            .inspections
            .outcome(conjunction)
            .iter()
            .filter_map(|id| self.result_duties.get(*id as usize).map(|duty| duty.cause))
            .collect::<Vec<_>>();
        let path_cause = self.cause(
            CauseKind::Projection,
            span,
            "pattern component executes only after its required prefix outcome",
            parents,
        );
        self.apply_condition_inspections(&prior.inspections, conjunction, span, path_cause);
        let tested = check(self, frame);
        let mut after = self.pattern_state();
        let decision = match tested {
            PatternOutcome::Normal(tested) => PatternDecision {
                matched: if conjunction {
                    and_match(prior.matched, tested.matched)
                } else {
                    or_match(prior.matched, tested.matched)
                },
                inspections: prior.inspections.sequence(
                    prior.matched,
                    &tested.inspections,
                    tested.matched,
                    conjunction,
                ),
            },
            PatternOutcome::Exit(value) => {
                self.unsupported(
                    span,
                    "conditional value-test exit requires a per-exit heap and Result summary",
                );
                after.abnormal = value.abnormal;
                after.never = true;
                PatternDecision {
                    matched: Some(!conjunction),
                    inspections: prior.inspections,
                }
            }
        };
        self.merge_pattern_states(&[baseline.clone(), after], &baseline, span);
        PatternOutcome::Normal(decision)
    }
    fn preview_value_pattern(
        &mut self,
        frame: &mut Frame,
        check: impl FnOnce(&mut Checker, &mut Frame) -> PatternOutcome,
    ) -> PatternOutcome {
        let before = self.snapshot_flow();
        let original = frame.clone();
        let result = check(self, frame);
        self.restore_preview(&before);
        *frame = original;
        result
    }
    fn compare_expected(
        &mut self,
        subject: &Value,
        expected: &Expr,
        frame: &mut Frame,
    ) -> PatternOutcome {
        let value = self.expression(expected, frame);
        self.require_type(&value, &subject.ty, expected.span);
        if self.equality_has_generic(&subject.ty) || self.equality_has_generic(&value.ty) {
            self.unsupported(
                expected.span,
                "value-test equality requires a proved constraint for every generic constituent",
            );
        }
        if self.contains_resource(subject)
            || self.contains_resource(&value)
            || !self.pattern_equality(&subject.ty, &mut BTreeSet::new())
        {
            self.error(
                "E0327",
                expected.span,
                "value-test equality is unavailable for a resource, callable, or unsupported constituent",
                [subject.cause, value.cause],
            );
        }
        if value.ty == Ty::Never {
            return PatternOutcome::Exit(Box::new(value));
        }
        self.access(subject, None, Mode::Read, expected.span, frame);
        self.access(&value, None, Mode::Read, expected.span, frame);
        self.pattern_outcome(match (&subject.constant, &value.constant) {
            (Some(a), Some(b)) => Some(a == b),
            _ => None,
        })
    }
    fn pattern_equality(&self, ty: &Ty, seen: &mut BTreeSet<String>) -> bool {
        if let Ty::Named(name) = ty
            && !seen.insert(name.clone())
        {
            return true;
        }
        let constructors: Vec<_> = self
            .constructors
            .values()
            .filter(|constructor| &constructor.owner == ty)
            .collect();
        if !constructors.is_empty() {
            return constructors
                .iter()
                .all(|constructor| self.pattern_equality(&constructor.payload, seen));
        }
        match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Callable(..)
            | Ty::Applied { .. }
            | Ty::Projection { .. }
            | Ty::OpenRecord { .. } => false,
            Ty::Result(ok, error) => {
                self.pattern_equality(&ok, seen) && self.pattern_equality(&error, seen)
            }
            Ty::Optional(inner) | Ty::Array(inner) | Ty::Immutable(inner) | Ty::Set(inner) => {
                self.pattern_equality(&inner, seen)
            }
            Ty::Map(key, value) => {
                self.pattern_equality(&key, seen) && self.pattern_equality(&value, seen)
            }
            Ty::Tuple(items) => items.iter().all(|ty| self.pattern_equality(ty, seen)),
            Ty::Record(fields) => fields
                .values()
                .all(|(_, ty)| self.pattern_equality(ty, seen)),
            _ => true,
        }
    }
    fn check_pattern_range(
        &mut self,
        expr: &Expr,
        value: &Value,
        span: Span,
        frame: &mut Frame,
    ) -> bool {
        let ExprKind::Range {
            start,
            end,
            inclusive,
        } = &expr.kind
        else {
            return false;
        };
        let _ = inclusive;
        let bounds = start
            .as_ref()
            .zip(end.as_ref())
            .and_then(|(a, b)| pattern_integer(a).zip(pattern_integer(b)));
        let literal_bounds = start
            .as_ref()
            .zip(end.as_ref())
            .is_some_and(|(a, b)| pattern_integer_syntax(a) && pattern_integer_syntax(b));
        if !literal_bounds
            || bounds.is_some_and(|(a, b)| a > b)
            || !matches!(self.expanded(&value.ty, &mut BTreeSet::new()), Ty::Int(_))
        {
            self.error(
                "E0348",
                span,
                "range pattern requires ordered literal integer bounds and an integer subject",
                [value.cause],
            );
        }
        if literal_bounds && bounds.is_none() {
            self.unsupported(
                span,
                "range bounds beyond the fixed integer comparison domain",
            );
        }
        if let Some(start) = start {
            let bound = self.expression(start, frame);
            self.require_type(&bound, &value.ty, start.span);
        }
        if let Some(end) = end {
            let bound = self.expression(end, frame);
            self.require_type(&bound, &value.ty, end.span);
        }
        true
    }

    fn patterns_exhaustive(
        &self,
        ty: &Ty,
        patterns: &[Pattern],
        seen: &mut BTreeSet<String>,
    ) -> bool {
        let patterns: Vec<_> = patterns.iter().flat_map(flat_patterns).collect();
        if patterns.iter().any(|pattern| irrefutable(pattern)) {
            return true;
        }
        if let Ty::Named(name) = ty
            && !seen.insert(name.clone())
        {
            return false;
        }
        match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Bool => [true,false].iter().all(|value| patterns.iter().any(|pattern| matches!(&pattern.kind,PatternKind::Literal(Literal::Bool(found))if found==value))),
            Ty::Optional(inner) => {
                let none=patterns.iter().any(|pattern| matches!(&pattern.kind,PatternKind::Constructor{path,..}if static_standard_tag(path)==Some("None")));
                let some = constructor_payload_patterns(&patterns,"Some");
                none && self.patterns_exhaustive(&inner,&some,seen)
            }
            Ty::Result(ok,error) => [(&*ok,"Ok"),(&*error,"Err")].into_iter().all(|(payload,tag)| {
                let values=constructor_payload_patterns(&patterns,tag);
                self.patterns_exhaustive(payload,&values,&mut seen.clone())
            }),
            Ty::Tuple(_) | Ty::Record(_) => patterns.iter().any(|pattern|structurally_irrefutable(pattern)),
            owner @ (Ty::Named(_) | Ty::Applied{..})=>{
                let variants = if let Some(tags) = self.constructor_possible_tags(&owner) {
                    tags.into_iter().map(|tag| {
                        self.constructors.values().find(|info| info.tag==tag && self.expanded(&info.owner,&mut BTreeSet::new())==owner).cloned()
                            .or_else(|| self.conditional_constructor_info(&tag,&owner))
                    }).collect::<Option<Vec<_>>>()
                } else {
                    Some(self.constructors.values().filter(|constructor|self.expanded(&constructor.owner,&mut BTreeSet::new())==owner).cloned().collect::<Vec<_>>())
                };
                let Some(variants) = variants else {return false;};
                !variants.is_empty()&&variants.into_iter().all(|constructor|{
                    let payloads=constructor_payload_patterns(&patterns,&constructor.tag);
                    if constructor.has_payload{self.patterns_exhaustive(&constructor.payload,&payloads,&mut seen.clone())}else{!payloads.is_empty()}
                })
            }
            _ => false,
        }
    }
}

fn flat_patterns(pattern: &Pattern) -> Vec<&Pattern> {
    match &pattern.kind {
        PatternKind::Alternative(patterns) => patterns.iter().flat_map(flat_patterns).collect(),
        PatternKind::Mode { pattern, .. } => flat_patterns(pattern),
        _ => vec![pattern],
    }
}
fn irrefutable(pattern: &Pattern) -> bool {
    matches!(pattern.kind, PatternKind::Name(_) | PatternKind::Wildcard)
        || matches!(&pattern.kind,PatternKind::Mode{pattern,..}if irrefutable(pattern))
}
fn structurally_irrefutable(pattern: &Pattern) -> bool {
    if irrefutable(pattern) {
        return true;
    }
    match &pattern.kind {
        PatternKind::Tuple(items) => items.iter().all(structurally_irrefutable),
        PatternKind::Record { fields, .. } => fields
            .iter()
            .all(|field| structurally_irrefutable(&field.pattern)),
        _ => false,
    }
}
fn pattern_subsumes(first: &Pattern, second: &Pattern) -> bool {
    if irrefutable(first) {
        return true;
    }
    if first.kind == second.kind {
        return true;
    }
    match (&first.kind, &second.kind) {
        (
            PatternKind::Constructor {
                path: a,
                arguments: x,
                ..
            },
            PatternKind::Constructor {
                path: b,
                arguments: y,
                ..
            },
        ) => {
            a == b
                && (x.is_empty()
                    || pattern_subsumes(
                        &constructor_payload_pattern(x, first.span),
                        &constructor_payload_pattern(y, second.span),
                    ))
        }
        (PatternKind::Tuple(a), PatternKind::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| pattern_subsumes(a, b))
        }
        (PatternKind::Alternative(patterns), _) => patterns
            .iter()
            .any(|pattern| pattern_subsumes(pattern, second)),
        _ => false,
    }
}
fn standard_pattern_tag<'a>(path: &'a [String], frame: &Frame) -> Option<&'a str> {
    if let [name] = path
        && frame.env.contains_key(name)
    {
        return None;
    }
    static_standard_tag(path)
}
fn static_standard_tag(path: &[String]) -> Option<&str> {
    let tag = match path {
        [name] => name.strip_prefix("Prelude::").unwrap_or(name),
        [module, name] if module == "Prelude" => name,
        _ => return None,
    };
    matches!(tag, "Some" | "None" | "Ok" | "Err").then_some(tag)
}
fn constructor_payload_patterns(patterns: &[&Pattern], tag: &str) -> Vec<Pattern> {
    patterns
        .iter()
        .filter_map(|pattern| {
            if let PatternKind::Constructor {
                path, arguments, ..
            } = &pattern.kind
                && (static_standard_tag(path) == Some(tag) || path.join("::") == tag)
            {
                return Some(constructor_payload_pattern(arguments, pattern.span));
            }
            None
        })
        .collect()
}
fn constructor_payload_pattern(arguments: &[Pattern], span: Span) -> Pattern {
    let kind = match arguments {
        [] => PatternKind::Wildcard,
        [one] => return one.clone(),
        _ => PatternKind::Tuple(arguments.to_vec()),
    };
    Pattern { kind, span }
}
fn pattern_tag_possible(pattern: &Pattern, value: &Value, frame: &Frame) -> bool {
    match &pattern.kind {
        PatternKind::Constructor { path, .. } => match standard_pattern_tag(path, frame) {
            Some("Ok") => value.result_tag != Some(false),
            Some("Err") => value.result_tag != Some(true),
            Some("Some") => value.option_tag != Some(false),
            Some("None") => value.option_tag != Some(true),
            _ => value
                .variant_tag
                .as_ref()
                .is_none_or(|found| found == &path.join("::")),
        },
        PatternKind::Literal(Literal::Bool(found)) => value
            .constant
            .as_ref()
            .is_none_or(|value| value != &Constant::Bool(!found)),
        PatternKind::Alternative(patterns) => patterns
            .iter()
            .any(|pattern| pattern_tag_possible(pattern, value, frame)),
        PatternKind::Mode { pattern, .. } => pattern_tag_possible(pattern, value, frame),
        _ => true,
    }
}
fn and_match(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}
fn or_match(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}
fn pattern_integer(expr: &Expr) -> Option<i128> {
    match &expr.kind {
        ExprKind::Literal(Literal::Integer(text)) => {
            let text = text.replace('_', "");
            let text = [
                "bigint", "int", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64",
            ]
            .iter()
            .find_map(|suffix| text.strip_suffix(suffix))
            .unwrap_or(&text);
            let (digits, radix) = if let Some(digits) =
                text.strip_prefix("0x").or_else(|| text.strip_prefix("0X"))
            {
                (digits, 16)
            } else if let Some(digits) = text.strip_prefix("0o").or_else(|| text.strip_prefix("0O"))
            {
                (digits, 8)
            } else if let Some(digits) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B"))
            {
                (digits, 2)
            } else {
                (text, 10)
            };
            i128::from_str_radix(digits, radix).ok()
        }
        ExprKind::Unary { operator, operand } if operator == "-" => {
            pattern_integer(operand)?.checked_neg()
        }
        _ => None,
    }
}
fn pattern_integer_syntax(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Literal(Literal::Integer(_)) => true,
        ExprKind::Unary { operator, operand } if operator == "-" => {
            matches!(operand.kind, ExprKind::Literal(Literal::Integer(_)))
        }
        _ => false,
    }
}
