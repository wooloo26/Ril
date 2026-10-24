//! Iteration-local Result families. A closed family carries a proof for one
//! arbitrary iteration; it cannot discharge obligations from before the loop.
use super::*;

pub(super) struct LoopResultState {
    start: usize,
    depth: usize,
    baseline: Vec<ResultDuty>,
    outside: Vec<BindingId>,
}

impl Checker {
    pub(super) fn begin_loop_results(&mut self, _owner: ScopeId) -> LoopResultState {
        let state = LoopResultState {
            start: self.result_duties.len(),
            depth: self.result_loop_starts.len(),
            baseline: self.result_duties.clone(),
            outside: self
                .bindings
                .iter()
                .enumerate()
                .filter_map(|(id, binding)| binding.alive.then_some(id))
                .collect(),
        };
        self.result_loop_starts.push(state.start);
        state
    }

    pub(super) fn loop_result_inspection_allowed(&self, value: &Value) -> bool {
        let Some(&start) = self.result_loop_starts.last() else {
            return self.loop_depth == 0;
        };
        value.outer_results.iter().all(|&id| {
            (id as usize) >= start
                || self
                    .result_duties
                    .get(id as usize)
                    .is_some_and(|duty| duty.inspected)
        })
    }

    pub(super) fn loop_result_site_can_repeat(&self, id: u32) -> bool {
        !self.result_loop_starts.is_empty()
            && self
                .result_duties
                .get(id as usize)
                .is_some_and(|duty| duty.inspected)
    }

    pub(super) fn finish_single_callback_results(&mut self, state: LoopResultState, span: Span) {
        if self.result_loop_starts.len() != state.depth + 1
            || self.result_loop_starts.last() != Some(&state.start)
        {
            self.unsupported(
                span,
                "single aborting callback Result activation boundaries are inconsistent",
            );
        }
        self.result_loop_starts.truncate(state.depth);
    }

    pub(super) fn finish_loop_results(
        &mut self,
        state: LoopResultState,
        iteration: &mut Value,
        frame: &mut Frame,
        span: Span,
        body: &Block,
    ) {
        if self.result_loop_starts.len() != state.depth + 1
            || self.result_loop_starts.last() != Some(&state.start)
        {
            self.unsupported(span, "Result loop activation boundaries are inconsistent");
        }
        self.result_loop_starts.truncate(state.depth);
        // The body may execute zero times. An old producer cannot acquire an
        // inspection, return, or abnormal-path waiver from its first iteration.
        for (duty, before) in self.result_duties.iter_mut().zip(&state.baseline) {
            duty.inspected = before.inspected;
            duty.returned = before.returned;
            duty.abnormal = before.abnormal;
            duty.covered = before.covered;
        }
        let new = &self.result_duties[state.start..];
        // Control certificates belong to the actual invocation, are merged
        // across live branches and restored after previews. An unreachable
        // expression contributes no exit; every reached exit contributes its
        // contemporaneous coverage, including an explicit unproved resumption.
        let uncovered: BTreeSet<_> = self
            .result_exit_checks
            .iter()
            .filter_map(|(&(owner, file, start, end), covered)| {
                (owner == frame.owner.0 && !covered).then_some((file, start, end))
            })
            .collect();
        if !new.is_empty() && has_control_block(body, &uncovered) {
            self.unsupported(
                span,
                "Result-producing loop has an early exit without per-exit inspection coverage",
            );
            return;
        }
        if new.iter().any(|duty| !duty.inspected && !duty.abnormal) {
            self.unsupported(span,"loop Result family is not inspected on every iteration exit; returned or outstanding families need an exit summary");
            return;
        }
        let closed: BTreeSet<_> = new.iter().map(|duty| duty.id).collect();
        if closed.is_empty() {
            return;
        }
        let mut roots: BTreeSet<_> = state
            .outside
            .iter()
            .flat_map(|id| {
                self.bindings[*id]
                    .value
                    .origins
                    .nodes
                    .iter()
                    .copied()
                    .chain(self.bindings[*id].cell)
            })
            .collect();
        roots.extend(iteration.origins.nodes.iter().copied());
        let reachable = self.heap.reachable(roots);
        let accumulates = state
            .outside
            .iter()
            .any(|id| carries_family(&self.bindings[*id].value, &closed))
            || self.fields.iter().any(|((node, _), value)| {
                reachable.contains(node) && carries_family(value, &closed)
            })
            || (iteration.ty != Ty::Never && carries_family(iteration, &closed));
        if accumulates {
            self.unsupported(span,"loop Result family escapes its iteration; copies and later projections require a multiplicity-aware obligation");
            return;
        }
        // A return or last selects one terminal iteration. Its inspected
        // wrappers are alternatives, not an aggregate of all loop instances.
        // Preserve those carrier IDs so later copies still reproduce duties.
        let terminal: BTreeSet<_> = frame
            .returned
            .iter()
            .map(|packet| &packet.value)
            .chain(
                self.loop_breaks
                    .iter()
                    .flat_map(|(_, values)| values.iter()),
            )
            .flat_map(|value| value.results.iter().copied())
            .filter(|id| closed.contains(id))
            .collect();
        let removable: BTreeSet<_> = closed.difference(&terminal).copied().collect();
        // Keep ResultDuty evidence and IDs valid in recorded expression facts.
        // Only live carriers forget obligations that are already inspected.
        for binding in &mut self.bindings {
            strip_closed(&mut binding.value, &removable);
        }
        for value in self.fields.values_mut() {
            strip_closed(value, &removable);
        }
        strip_closed(iteration, &removable);
        for value in &mut frame.returned {
            strip_closed(&mut value.value, &removable);
        }
        for (_, values) in &mut self.loop_breaks {
            for value in values {
                strip_closed(value, &removable);
            }
        }
        self.result_sites.retain(|_, id| !closed.contains(id));
    }

    /// A normal read_all/write_all return has entered the operation at least
    /// once, including an empty write. Only reached inspections of old duties
    /// survive; a callback return or abnormal flag does not waive caller debt.
    pub(super) fn finish_guaranteed_callback_results(
        &mut self,
        state: LoopResultState,
        iteration: &mut Value,
        frame: &mut Frame,
        span: Span,
        body: &Block,
    ) {
        let inspected: BTreeSet<_> = self.result_duties[..state.start]
            .iter()
            .filter_map(|duty| duty.inspected.then_some(duty.id))
            .collect();
        self.finish_loop_results(state, iteration, frame, span, body);
        for id in inspected {
            let duty = &mut self.result_duties[id as usize];
            duty.inspected = true;
            duty.covered = true;
        }
    }
}

fn strip_closed(value: &mut Value, closed: &BTreeSet<u32>) {
    value.condition_inspections.strip(closed);
    value.results.retain(|id| !closed.contains(id));
    value.must_results.retain(|id| !closed.contains(id));
    value.outer_results.retain(|id| !closed.contains(id));
    value.must_outer_results.retain(|id| !closed.contains(id));
    for nested in [
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.option_payload,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    {
        strip_closed(nested, closed);
    }
    for nested in value.variant_witnesses.values_mut() {
        strip_closed(nested, closed);
    }
}

fn carries_family(value: &Value, family: &BTreeSet<u32>) -> bool {
    !value.results.is_disjoint(family)
        || [
            &value.result_payload,
            &value.result_success,
            &value.result_error,
            &value.option_payload,
            &value.variant_payload,
        ]
        .into_iter()
        .flatten()
        .any(|nested| carries_family(nested, family))
        || value
            .variant_witnesses
            .values()
            .any(|nested| carries_family(nested, family))
}

fn has_control_block(block: &Block, checked: &BTreeSet<(u32, u32, u32)>) -> bool {
    block
        .where_items
        .iter()
        .chain(&block.statements)
        .any(|statement| match &statement.kind {
            StmtKind::Binding(binding) => {
                has_control(&binding.value, checked)
                    || binding
                        .fallback
                        .as_ref()
                        .is_some_and(|value| has_control(value, checked))
                    || pattern_control(&binding.pattern, checked)
            }
            StmtKind::Assignment { target, value, .. } => {
                has_control(target, checked) || has_control(value, checked)
            }
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                has_control(expression, checked)
            }
            StmtKind::Handler(arms) => arms.iter().any(|arm| has_control(&arm.body, checked)),
            StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_) | StmtKind::Use(_) => {
                false
            }
        })
}
fn has_control(expression: &Expr, checked: &BTreeSet<(u32, u32, u32)>) -> bool {
    let visit = |value: &Expr| has_control(value, checked);
    let block = |block: &Block| has_control_block(block, checked);
    let pattern = |pattern: &Pattern| pattern_control(pattern, checked);
    match &expression.kind {
        ExprKind::Control { value, .. } => {
            checked.contains(&(
                expression.span.file.0,
                expression.span.start,
                expression.span.end,
            )) || value.as_ref().is_some_and(|value| visit(value))
        }
        ExprKind::Lambda { .. } => false,
        ExprKind::Block(body) | ExprKind::Loop(body) => block(body),
        ExprKind::While { condition, body } => visit(condition) || block(body),
        ExprKind::WhileLet {
            pattern: binder,
            value,
            body,
        } => visit(value) || pattern(binder) || block(body),
        ExprKind::For {
            iterable,
            pattern: binder,
            body,
        } => visit(iterable) || pattern(binder) || block(body),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visit(condition)
                || visit(then_branch)
                || else_branch.as_ref().is_some_and(|value| visit(value))
        }
        ExprKind::IfLet {
            pattern: binder,
            value,
            then_branch,
            else_branch,
        } => {
            visit(value)
                || pattern(binder)
                || visit(then_branch)
                || else_branch.as_ref().is_some_and(|value| visit(value))
        }
        ExprKind::Match { value, arms, .. } => {
            visit(value)
                || arms.iter().any(|arm| {
                    pattern(&arm.pattern)
                        || arm.guard.as_ref().is_some_and(visit)
                        || visit(&arm.body)
                })
        }
        ExprKind::Is {
            value,
            pattern: binder,
        } => visit(value) || pattern(binder),
        ExprKind::Tuple(values) | ExprKind::Array(values) => values.iter().any(visit),
        ExprKind::Map(values) => values.iter().any(|(key, value)| visit(key) || visit(value)),
        ExprKind::Record { members, .. } => members.iter().any(|member| match member {
            RecordMember::Field(field) => visit(&field.value),
            RecordMember::Spread(value) => visit(value),
        }),
        ExprKind::Generic { base, .. }
        | ExprKind::Unary { operand: base, .. }
        | ExprKind::Field { base, .. } => visit(base),
        ExprKind::Binary { left, right, .. }
        | ExprKind::Index {
            base: left,
            index: right,
            ..
        }
        | ExprKind::ComputedField {
            base: left,
            key: right,
        } => visit(left) || visit(right),
        ExprKind::Call { callee, arguments } => {
            visit(callee) || arguments.iter().any(|argument| visit(&argument.value))
        }
        ExprKind::Derive { base, recipe } => {
            base.as_ref().is_some_and(|value| visit(value)) || visit(recipe)
        }
        ExprKind::Range { start, end, .. } => {
            start.as_ref().is_some_and(|value| visit(value))
                || end.as_ref().is_some_and(|value| visit(value))
        }
        ExprKind::Interpolated(parts) => parts.iter().any(
            |part| matches!(part,StringPart::Interpolation{expression,..}if visit(expression)),
        ),
        ExprKind::Literal(_)
        | ExprKind::Name(_)
        | ExprKind::Path(_)
        | ExprKind::Accessor(_)
        | ExprKind::TypeValue(_)
        | ExprKind::KeyOf(_)
        | ExprKind::Ambient => false,
        ExprKind::Error => true,
    }
}
fn pattern_control(pattern: &Pattern, checked: &BTreeSet<(u32, u32, u32)>) -> bool {
    match &pattern.kind {
        PatternKind::Value(value) => has_control(value, checked),
        PatternKind::Tuple(patterns)
        | PatternKind::Array(patterns)
        | PatternKind::Alternative(patterns)
        | PatternKind::Constructor {
            arguments: patterns,
            ..
        } => patterns
            .iter()
            .any(|pattern| pattern_control(pattern, checked)),
        PatternKind::Record { fields, .. } => fields
            .iter()
            .any(|field| pattern_control(&field.pattern, checked)),
        PatternKind::Mode { pattern, .. } => pattern_control(pattern, checked),
        PatternKind::Name(_)
        | PatternKind::Rest(_)
        | PatternKind::Wildcard
        | PatternKind::Literal(_)
        | PatternKind::Type { .. } => false,
        PatternKind::Error => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn propagated_terminal_iterations_keep_inspected_result_alternatives() {
        let source = "fn produce(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err(\"error\")}}\nfn example(flag:bool)->Result<(),str>{loop{let value=produce(flag)?;if value==1{last}};Ok()}";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let source = "fn produce(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err(\"error\")}}\nfn example(flag:bool)->Result<(),str>{loop{let pending=produce(flag);if flag{last};assert(pending is Ok(_))};Ok()}";
        let parsed = ril_syntax::parse(source);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result.program.is_none(),
            "an uninspected terminal iteration cannot close its family"
        );
        for source in [
            "fn produce()->Result<int,str>{Ok(1)}\nfn example(flag:bool)->Result<(),str>{let outside=produce();loop{let value=produce()?;if flag{last}};Ok()}",
            "fn example(flag:bool){for [1,2] as index{let result:Result<int,str>=Ok(index);let copied=clone(result);assert(result is Ok(_));if flag{last}}}",
            "fn example(flag:bool){for [1,2] as index{let result:Result<Result<int,str>,str>=Ok(Err(\"nested\"));assert(result is Ok(_));if flag{last}}}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let checked = crate::sema::analyze(&parsed.program, FileId(0));
            assert!(
                checked.program.is_none(),
                "an outside, copied or nested duty must survive terminal coverage"
            );
        }
    }

    #[test]
    fn a_tagged_payload_carries_its_own_result_family_and_only_closed_ids_are_removed() {
        let mut payload = Value::scalar(Ty::Unit, None, CauseId(0));
        payload.results = [3, 7].into();
        payload.must_results = [3, 7].into();
        payload.outer_results = [3, 7].into();
        payload.must_outer_results = [3, 7].into();
        let mut value = Value::scalar(Ty::Unit, None, CauseId(0));
        value
            .variant_witnesses
            .insert("Choice::Item".into(), Box::new(payload));
        assert!(carries_family(&value, &[3].into()));
        strip_closed(&mut value, &[3].into());
        assert!(!carries_family(&value, &[3].into()));
        assert!(carries_family(&value, &[7].into()));
        let payload = &value.variant_witnesses["Choice::Item"];
        assert_eq!(payload.results, [7].into());
        assert_eq!(payload.must_results, [7].into());
        assert_eq!(payload.outer_results, [7].into());
        assert_eq!(payload.must_outer_results, [7].into());
    }
}
