//! Complete-evaluation truth from frozen Source and physical observations.
//! Missing premises supply no truth. No final inspection bit is consumed.
use super::*;
use crate::hir::application::AstApplication;
use crate::sema::{
    copy_contract::{CopyInvocation, CopyInvocationStatus},
    model::{Callable, ClosureInfo, Mode, Ty},
    result_conditions::ConditionKind,
};
use ril_compiler_core::ids::CallableOwner;
use ril_syntax::ast::{ExprKind, Function, StmtKind};
#[path = "channel_condition_source.rs"]
mod source;

pub(super) struct Analysis<'a> {
    facts: &'a SemanticFacts,
    work: usize,
}

#[cfg(test)]
#[path = "channel_condition_business_tests.rs"]
mod business_tests;
#[cfg(test)]
#[path = "channel_condition_validation_tests.rs"]
mod tests;

struct Owners<'a> {
    header: &'a Function,
    invocation: &'a CopyInvocation,
    lambdas: Vec<source::LambdaHeader<'a>>,
    objects: Vec<&'a ClosureInfo>,
    current_span: Span,
}

impl<'a> Analysis<'a> {
    pub(super) fn new(facts: &'a SemanticFacts) -> Self {
        Self {
            facts,
            work: 65_536,
        }
    }

    fn charge(&mut self) -> Check {
        self.work = self
            .work
            .checked_sub(1)
            .ok_or("complete condition Source analysis exceeds its work bound")?;
        Ok(())
    }

    fn owners(&mut self, context: InvocationContext) -> Check<Option<Owners<'a>>> {
        let facts = self.facts;
        if context.budget_validation || context.default_use.is_some() {
            return Ok(None);
        }
        let Some(mut owner) = context.owner else {
            return Ok(None);
        };
        let mut object = context.closure;
        let mut named = context.invocation;
        let mut lambdas = Vec::new();
        let mut objects = Vec::new();
        let mut seen = BTreeSet::new();
        if matches!(owner, CallableOwner::Lambda(_)) {
            let Some(actual) = context.closure_invocation.and_then(|id| {
                facts
                    .closure_invocations
                    .get(id.0 as usize)
                    .filter(|row| row.id == id)
            }) else {
                return Ok(None);
            };
            // A real incoming occurrence, not a mutable probe selector, is
            // required before any callback can constrain a replay case.
            if Some(actual.closure) != object
                || actual.source_event.is_none()
                || actual.status != CopyInvocationStatus::Completed
            {
                return Ok(None);
            }
        }
        loop {
            self.charge()?;
            if !seen.insert(owner) || seen.len() > 128 {
                return Ok(None);
            }
            match owner {
                CallableOwner::Global => return Ok(None),
                CallableOwner::Lambda(id) => {
                    let Some(site) = facts
                        .closure_sites
                        .get(id.0 as usize)
                        .filter(|site| site.id == id)
                    else {
                        return Ok(None);
                    };
                    let Some(closure) = object
                        .and_then(|index| facts.closures.get(index))
                        .filter(|closure| closure.site == Some(id))
                    else {
                        return Ok(None);
                    };
                    if closure.creation_default.is_some() {
                        return Ok(None);
                    }
                    lambdas.push(source::LambdaHeader {
                        span: site.span,
                        parameters: &closure.parameters,
                        body: &closure.body,
                    });
                    objects.push(closure);
                    owner = site.owner;
                    if matches!(owner, CallableOwner::Lambda(_)) {
                        let Some(parent) = closure.creation_closure.and_then(|id| {
                            facts
                                .closure_invocations
                                .get(id.0 as usize)
                                .filter(|row| row.id == id)
                        }) else {
                            return Ok(None);
                        };
                        if parent.status != CopyInvocationStatus::Completed
                            || parent.source_event.is_none()
                        {
                            return Ok(None);
                        }
                        object = Some(parent.closure);
                    } else {
                        named = closure.creation_invocation;
                    }
                }
                CallableOwner::Function(id) => {
                    let mut header = None;
                    for function in &facts.functions {
                        self.charge()?;
                        if function.definition != id {
                            continue;
                        }
                        if header.is_some_and(|header: &Function| header != &function.syntax) {
                            return Ok(None);
                        }
                        header = Some(&function.syntax);
                    }
                    let Some(header) = header else {
                        return Ok(None);
                    };
                    let Some(invocation) = named.and_then(|id| {
                        facts
                            .copy_invocations
                            .get(id.0 as usize)
                            .filter(|row| row.id == id)
                    }) else {
                        return Ok(None);
                    };
                    // Initial admission is relative to an independent real
                    // header entry. Caller-prefix reconstruction for ordinary
                    // incoming calls remains unknown, never a flag-based skip.
                    if invocation.target != id
                        || invocation.status != CopyInvocationStatus::Completed
                        || invocation.span != header.span
                        || invocation.parent.is_some()
                        || invocation.caller.is_some()
                        || invocation.caller_owner.is_some()
                        || invocation.caller_activation.is_some()
                        || invocation.source_event.is_some()
                        || invocation.arguments.len() != header.parameters.len()
                    {
                        return Ok(None);
                    }
                    let current_span = lambdas.first().map_or(header.span, |lambda| lambda.span);
                    if !lambdas.is_empty() {
                        // Initial actual callback admission is a single direct
                        // scope call in the header's first statement. Creation
                        // under this owner cannot prove a conditional cb() call.
                        if lambdas.len() != 1 {
                            return Ok(None);
                        }
                        let Some(actual) = context.closure_invocation.and_then(|id| {
                            facts
                                .closure_invocations
                                .get(id.0 as usize)
                                .filter(|row| row.id == id)
                        }) else {
                            return Ok(None);
                        };
                        let Some(application) = actual.source_event.and_then(|id| {
                            facts
                                .copy_call_events
                                .get(id.0 as usize)
                                .filter(|row| row.id == id)
                        }) else {
                            return Ok(None);
                        };
                        let Some(StmtKind::Expr { expression, .. }) = header
                            .body
                            .as_ref()
                            .and_then(|body| body.statements.first())
                            .map(|statement| &statement.kind)
                        else {
                            return Ok(None);
                        };
                        let Some(scope) = AstApplication::from_ast(expression) else {
                            return Ok(None);
                        };
                        let Some(program) = facts.source_program.as_deref() else {
                            return Ok(None);
                        };
                        if !source::canonical_scope_callee(
                            program,
                            header,
                            scope.callee,
                            &mut self.work,
                        )
                        .map_err(str::to_owned)?
                        {
                            return Ok(None);
                        }
                        if scope.operands.len() != 1
                            || scope.operands[0].expression.hir_id.is_none()
                            || scope.operands[0].expression.hir_id != objects[0].hir_id
                            || scope.operands[0].expression.span != lambdas[0].span
                            || !matches!(scope.operands[0].expression.kind, ExprKind::Lambda { .. })
                            || application.source_id.is_none()
                            || application.source_id != expression.hir_id
                            || application.span != expression.span
                            || application.owner != Some(owner)
                            || application.parent != Some(invocation.id)
                            || actual.parent_named != Some(invocation.id)
                            || actual.parent_closure.is_some()
                            || actual.caller_owner != Some(owner)
                        {
                            return Ok(None);
                        }
                        let Some(index) = application.callee_expression else {
                            return Ok(None);
                        };
                        let Some(callee_value) = facts.expressions.get(index) else {
                            return Ok(None);
                        };
                        let mut callee_rows = 0;
                        for row in &facts.invocation_expressions {
                            self.charge()?;
                            if row.expression == index
                                && row.context.owner == Some(owner)
                                && row.context.invocation == Some(invocation.id)
                                && row.context.closure.is_none()
                                && row.context.closure_invocation.is_none()
                                && row.context.default_use.is_none()
                                && !row.context.budget_validation
                            {
                                callee_rows += 1;
                            }
                        }
                        if callee_value.source_id.is_none()
                            || callee_value.source_id != scope.callee.hir_id
                            || !matches!(callee_value.value.callables.as_slice(), [Callable::Builtin(name)] if name == "Concurrent::scope")
                            || callee_rows != 1
                        {
                            return Ok(None);
                        }
                    }
                    if lambdas.is_empty()
                        && (context.closure.is_some() || context.closure_invocation.is_some())
                    {
                        return Ok(None);
                    }
                    lambdas.reverse();
                    objects.reverse();
                    return Ok(Some(Owners {
                        header,
                        invocation,
                        lambdas,
                        objects,
                        current_span,
                    }));
                }
            }
        }
    }

    fn reaches(&mut self, from: CauseId, target: CauseId) -> Check<bool> {
        let facts = self.facts;
        let mut pending = vec![from];
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            self.charge()?;
            if id == target {
                return Ok(true);
            }
            if !seen.insert(id.0) {
                continue;
            }
            let Some(cause) = facts
                .explanations
                .causes
                .get(id.0 as usize)
                .filter(|cause| cause.id == id)
            else {
                return Ok(false);
            };
            pending.extend(cause.parents.iter().copied());
        }
        Ok(false)
    }

    fn root_value(
        &mut self,
        owners: &Owners<'a>,
        root: &source::FormalRoot,
        steps: &[source::SourceStep],
    ) -> Check<Option<&'a Value>> {
        let facts = self.facts;
        if root.callable != owners.header.span {
            return Ok(None);
        }
        let Some(parameter) = owners.header.parameters.get(root.parameter) else {
            return Ok(None);
        };
        let Some((Mode::Read, snapshot)) = owners.invocation.arguments.get(root.parameter) else {
            return Ok(None);
        };
        if parameter.span != root.parameter_span || parameter.pattern.span != root.binder {
            return Ok(None);
        }
        let mut value = &snapshot.value;
        for step in steps {
            self.charge()?;
            match step {
                source::SourceStep::Alias { .. } => {}
                source::SourceStep::Capture { lambda, name } => {
                    let Some(index) = owners
                        .lambdas
                        .iter()
                        .position(|header| header.span == *lambda)
                    else {
                        return Ok(None);
                    };
                    let object = owners.objects[index];
                    let Some(binding) = object
                        .lexical
                        .get(name)
                        .filter(|id| object.captures.contains(id))
                        .and_then(|id| facts.bindings.get(*id))
                    else {
                        return Ok(None);
                    };
                    let within = |span: Span| {
                        span.file == binding.span.file
                            && span.start <= binding.span.start
                            && span.end >= binding.span.end
                    };
                    if !within(root.binder)
                        && !within(root.parameter_span)
                        && !steps.iter().any(|step| match step {
                            source::SourceStep::Alias { binding } => within(*binding),
                            source::SourceStep::OptionPayload { pattern } => within(*pattern),
                            _ => false,
                        })
                    {
                        return Ok(None);
                    }
                }
                source::SourceStep::OptionPayload { .. } => {
                    let Some(payload) = value.option_payload.as_deref() else {
                        return Ok(None);
                    };
                    value = payload;
                }
                source::SourceStep::Field { field, .. } => {
                    let slot = field
                        .parse()
                        .map(crate::sema::facts::Slot::Tuple)
                        .unwrap_or_else(|_| crate::sema::facts::Slot::Field(field.clone()));
                    let mut selected = None;
                    for origin in &value.origins.nodes {
                        self.charge()?;
                        let Some(node) = snapshot.nodes.iter().find(|node| node.origin == *origin)
                        else {
                            return Ok(None);
                        };
                        for (actual, child) in &node.fields {
                            self.charge()?;
                            if actual == &slot {
                                if selected.is_some() {
                                    return Ok(None);
                                }
                                selected = Some(child);
                            }
                        }
                    }
                    let Some(child) = selected else {
                        return Ok(None);
                    };
                    value = child;
                }
            }
        }
        // Do not consult the final global heap, binding values or duty flags.
        Ok(Some(value))
    }

    fn same_identity(
        &mut self,
        original: &Value,
        observed: &Value,
        from: usize,
        to: usize,
        depth: usize,
    ) -> Check<bool> {
        self.charge()?;
        if depth > 128 || from > to || to > self.facts.allocation_history.len() {
            return Ok(false);
        }
        // Read reception may restrict permissions and change borrow participants.
        // It cannot substitute another Result producer or reachable graph. The
        // complete received authority itself is checked against the exact actual
        // operand observation above; this theorem grants no access authority.
        if original.results != observed.results
            || original.outer_results != observed.outer_results
            || original.must_results != observed.must_results
            || original.must_outer_results != observed.must_outer_results
            || original.option_identity != observed.option_identity
            || original.result_tag != observed.result_tag
            || original.option_tag != observed.option_tag
            || original.variant_tag != observed.variant_tag
        {
            return Ok(false);
        }
        let mut origins = original.origins.clone();
        for &(recent, older) in &self.facts.allocation_history[from..to] {
            self.charge()?;
            if origins.nodes.remove(&recent) {
                origins.nodes.insert(older);
            }
            for alternatives in origins.choices.values_mut() {
                for alternative in alternatives {
                    self.charge()?;
                    if alternative.remove(&recent) {
                        alternative.insert(older);
                    }
                }
            }
        }
        if origins != observed.origins {
            return Ok(false);
        }
        for (left, right) in [
            (&original.option_payload, &observed.option_payload),
            (&original.result_payload, &observed.result_payload),
            (&original.result_success, &observed.result_success),
            (&original.result_error, &observed.result_error),
            (&original.variant_payload, &observed.variant_payload),
        ] {
            match (left, right) {
                (Some(left), Some(right))
                    if self.same_identity(left, right, from, to, depth + 1)? => {}
                (None, None) => {}
                _ => return Ok(false),
            }
        }
        if !original
            .variant_witnesses
            .keys()
            .eq(observed.variant_witnesses.keys())
        {
            return Ok(false);
        }
        for (tag, value) in &original.variant_witnesses {
            if !self.same_identity(value, &observed.variant_witnesses[tag], from, to, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn scalar_carrier(&mut self, value: &Value, depth: usize) -> Check<bool> {
        self.charge()?;
        if depth > 128 || !value.origins.nodes.is_empty() || !value.origins.choices.is_empty() {
            return Ok(false);
        }
        for child in [
            &value.option_payload,
            &value.result_payload,
            &value.result_success,
            &value.result_error,
            &value.variant_payload,
        ]
        .into_iter()
        .flatten()
        .chain(value.variant_witnesses.values())
        {
            if !self.scalar_carrier(child, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn assertion(
        &mut self,
        context: InvocationContext,
        call: Span,
        callee: Span,
        condition: Span,
    ) -> Check<Option<GuardLiteral>> {
        let facts = self.facts;
        let mut evaluated = None;
        for (index, evaluation) in facts.condition_evaluations.iter().enumerate() {
            self.charge()?;
            if evaluation.context != context
                || evaluation.span != condition
                || evaluation.kind != ConditionKind::Pattern
            {
                continue;
            }
            if evaluation.id.0 as usize != index {
                return Ok(None);
            }
            let mut whole = 0;
            for row in &facts.invocation_expressions {
                self.charge()?;
                if row.context == context
                    && facts.expressions.get(row.expression).is_some_and(|value| {
                        value.span == condition
                            && value
                                .value
                                .condition_inspections
                                .evaluations
                                .contains(&evaluation.id)
                    })
                {
                    whole += 1;
                }
            }
            if whole != 1 || evaluated.replace(evaluation.id).is_some() {
                return Ok(None);
            }
        }
        let Some(evaluation) = evaluated else {
            return Ok(None);
        };
        let mut actual = 0;
        for application in &facts.copy_call_events {
            self.charge()?;
            if application.span != call
                || application.owner != context.owner
                || application.parent != context.invocation
            {
                continue;
            }
            let Some(index) = application.callee_expression else {
                continue;
            };
            let Some(value) = facts.expressions.get(index) else {
                continue;
            };
            if value.span == callee
                && matches!(value.value.callables.as_slice(), [Callable::Builtin(name)] if matches!(name.as_str(), "assert" | "Prelude::assert"))
            {
                let mut rows = 0;
                for row in &facts.invocation_expressions {
                    self.charge()?;
                    if row.expression == index && row.context == context {
                        rows += 1;
                    }
                }
                if rows == 1 {
                    actual += 1;
                }
            }
        }
        Ok((actual == 1).then_some(GuardLiteral::Boolean {
            evaluation,
            truth: true,
        }))
    }

    pub(super) fn truth(&mut self, event: &ChannelMessageFact) -> Check<Option<bool>> {
        let ChannelAction::ConditionEvaluated {
            evaluation,
            subject_expression,
            subject,
        } = &event.action
        else {
            return Ok(None);
        };
        let facts = self.facts;
        let Some(program) = facts.source_program.as_deref() else {
            return Ok(None);
        };
        let Some(owners) = self.owners(event.context)? else {
            return Ok(None);
        };
        let Some(source) = source::observed_result_source(
            program,
            owners.header,
            &owners.lambdas,
            event.span,
            &mut self.work,
        )
        .map_err(str::to_owned)?
        else {
            return Ok(None);
        };
        if source
            .controls
            .iter()
            .any(|control| matches!(control, source::SourceControl::UnprovedPrefix))
        {
            return Ok(None);
        }
        let Some(proof) = facts
            .condition_evaluations
            .get(evaluation.0 as usize)
            .filter(|proof| proof.id == *evaluation)
        else {
            return Ok(None);
        };
        if proof.context != event.context || proof.span != event.span || proof.cause != event.cause || proof.kind != ConditionKind::Pattern
            || event.guard.terms.iter().flatten().any(|literal| matches!(literal, GuardLiteral::Boolean { evaluation: own, .. } if own == evaluation)) { return Ok(None); }
        let Some(operand) = facts.expressions.get(*subject_expression) else {
            return Ok(None);
        };
        // Initial admission has a fully scalar reachable carrier. Heap-bearing
        // Result snapshots need independently replayed historical field reads;
        // their graph/epoch cannot be manufactured from this receipt itself.
        if !subject.nodes.is_empty()
            || !subject.relations.is_empty()
            || !self.scalar_carrier(&subject.value, 0)?
        {
            return Ok(None);
        }
        if operand.value != subject.value
            || operand.value.condition_inspections.evaluations
                != subject.value.condition_inspections.evaluations
        {
            return Ok(None);
        }
        let mut operand_rows = 0;
        let mut whole = None;
        for row in &facts.invocation_expressions {
            self.charge()?;
            if row.context != event.context {
                continue;
            }
            if row.expression == *subject_expression {
                operand_rows += 1;
            }
            if let Some(expression) = facts.expressions.get(row.expression)
                && expression.span == event.span
                && expression
                    .value
                    .condition_inspections
                    .evaluations
                    .contains(evaluation)
                && (row.expression <= *subject_expression || whole.replace(expression).is_some())
            {
                return Ok(None);
            }
        }
        let Some(whole) = whole else {
            return Ok(None);
        };
        if operand_rows != 1
            || !self.reaches(whole.value.cause, event.cause)?
            || !self.reaches(event.cause, subject.value.cause)?
        {
            return Ok(None);
        }
        if source.subject != operand.span {
            return Ok(None);
        }
        let Some(original) = self.root_value(&owners, &source.root, &source.steps)? else {
            return Ok(None);
        };
        if !matches!(original.ty, Ty::Result(..))
            || !self.reaches(subject.value.cause, original.cause)?
            || !self.same_identity(
                original,
                &subject.value,
                owners.invocation.entry_allocation_epoch,
                event.allocation_epoch,
                0,
            )?
        {
            return Ok(None);
        }
        for control in &source.controls {
            self.charge()?;
            let literal = match control {
                source::SourceControl::Some { root, steps, .. } => {
                    let Some(value) = self.root_value(&owners, root, steps)? else {
                        return Ok(None);
                    };
                    let Some(identity) = value.option_identity else {
                        return Ok(None);
                    };
                    GuardLiteral::Optional {
                        identity,
                        present: true,
                    }
                }
                source::SourceControl::Assertion {
                    owner,
                    call,
                    callee,
                    condition,
                } => {
                    if owner != &owners.current_span {
                        return Ok(None);
                    }
                    let Some(literal) =
                        self.assertion(event.context, *call, *callee, *condition)?
                    else {
                        return Ok(None);
                    };
                    literal
                }
                source::SourceControl::UnprovedPrefix => return Ok(None),
            };
            // Unknown overlap/guard arithmetic supplies no execution proof.
            let Some(opposite) = ChannelGuard::literal(literal).not() else {
                return Ok(None);
            };
            if event
                .guard
                .and(&opposite)
                .is_none_or(|intersection| !intersection.is_never())
            {
                return Ok(None);
            }
        }
        // The first tag record is an additional temporal/physical consistency
        // check. Complete Source coverage and parent controls above supply the
        // theorem; this record never substitutes for them.
        let mut head = None;
        for prior in &facts.channel_messages {
            self.charge()?;
            if prior.sequence >= event.sequence
                || prior.context != event.context
                || prior.span != source.first_head
                || prior.activation != event.activation
                || prior.task != event.task
            {
                continue;
            }
            if let ChannelAction::TagTest {
                subject: tested,
                success,
                ..
            } = &prior.action
                && tested.value == subject.value
                && *success == source.first_success
                && head.replace(prior).is_some()
            {
                return Ok(None);
            }
        }
        let Some(head) = head else {
            return Ok(None);
        };
        if head.allocation_epoch != event.allocation_epoch {
            return Ok(None);
        }
        if event
            .guard
            .and(
                &head
                    .guard
                    .not()
                    .ok_or("complete condition prefix guard complement is unavailable")?,
            )
            .is_none_or(|intersection| !intersection.is_never())
        {
            return Ok(None);
        }
        if proof.constant == Some(false) {
            return Err(
                "complete canonical Result predicate contradicts its recorded Boolean".into(),
            );
        }
        Ok(Some(true))
    }
}
