//! Physical entry bounds reconstructed from actual application identities.
//! Source spans locate syntax only after the dynamic call/closure ancestry has
//! selected its callable. A representative body never proves event count.
use crate::sema::{
    SemanticFacts, channel_messages::*, copy_contract::CopyCallEventId,
    effect_identity::InvocationContext, model::Callable,
};
use ril_compiler_core::{ids::CallableOwner, source::Span};
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};
#[path = "channel_source_index.rs"]
mod source_index;

type Check<T = ()> = Result<T, String>;

#[derive(Clone, Copy)]
struct Bounds {
    once: bool,
    entered: bool,
    repeated: bool,
}
impl Default for Bounds {
    fn default() -> Self {
        Self {
            once: true,
            entered: true,
            repeated: false,
        }
    }
}
impl Bounds {
    fn and(self, other: Self) -> Self {
        Self {
            once: self.once && other.once,
            entered: self.entered && other.entered,
            repeated: self.repeated || other.repeated,
        }
    }
    fn count(count: Option<u64>) -> Self {
        Self {
            once: count.is_some_and(|count| count <= 1),
            entered: count.is_some_and(|count| count > 0),
            repeated: count.is_none_or(|count| count > 1),
        }
    }
}

pub(super) struct Analysis<'a> {
    facts: &'a SemanticFacts,
    work: usize,
    calls: BTreeMap<CopyCallEventId, Bounds>,
    source_index: source_index::Index<'a>,
}
impl<'a> Analysis<'a> {
    pub(super) fn new(facts: &'a SemanticFacts) -> Self {
        Self {
            facts,
            work: 65_536,
            calls: BTreeMap::new(),
            source_index: source_index::Index::new(facts),
        }
    }

    fn charge(&mut self) -> Check {
        self.work = self
            .work
            .checked_sub(1)
            .ok_or("channel execution-bound analysis exceeds its work bound")?;
        Ok(())
    }

    /// An actual named call needs its own source occurrence and evaluated
    /// callee. Merely naming a real surrounding callback application is not
    /// evidence that its input aliases replace a declaration's formal slots.
    pub(super) fn named_entry_source(
        &mut self,
        invocation: &crate::sema::copy_contract::CopyInvocation,
    ) -> Check {
        self.charge()?;
        let facts = self.facts;
        let id = invocation
            .source_event
            .ok_or("optional input call lacks its actual named source application")?;
        let call = self.source_index.application(id, &mut self.work)?;
        if call.span != invocation.span
            || call.owner != invocation.caller_owner
            || call.parent != invocation.parent
            || call.target != Some(invocation.target)
        {
            return Err("optional input call borrowed another source occurrence".into());
        }
        self.call(id)?;
        let expression = call
            .callee_expression
            .and_then(|index| facts.expressions.get(index))
            .ok_or("optional input call lacks its evaluated named callee")?;
        let [Callable::Named(index)] = expression.value.callables.as_slice() else {
            return Err("optional input call source is not its named callee".into());
        };
        if facts
            .functions
            .get(*index)
            .is_none_or(|function| function.definition != invocation.target)
        {
            return Err("optional input call selected another named callee".into());
        }
        let callers = self
            .source_index
            .caller_links(invocation.id, &mut self.work)?;
        let [caller] = callers.as_slice() else {
            return Err("optional input call lacks a unique actual caller observation".into());
        };
        if caller.caller_owner != call.owner
            || !facts.invocation_expressions.iter().any(|observation| {
                Some(observation.expression) == call.callee_expression
                    && observation.context.owner == call.owner
                    && observation.context.invocation == call.parent
                    && observation.context.closure == caller.caller_closure
                    && observation.context.closure_invocation == caller.caller_closure_invocation
                    && observation.context.default_use == caller.default_use
            })
        {
            return Err("optional input call callee belongs to another execution context".into());
        }
        Ok(())
    }

    pub(super) fn metadata(&mut self) -> Check {
        let facts = self.facts;
        let mut business_regions = BTreeSet::new();
        for event in &facts.channel_messages {
            self.charge()?;
            if matches!(&event.action, ChannelAction::Send { payload, .. } | ChannelAction::Receive { payload, .. } if !payload.value.results.is_empty())
            {
                business_regions.insert(super::region(facts, event.context)?);
            }
        }
        for (index, repeat) in facts.channel_repetitions.iter().enumerate() {
            self.charge()?;
            let end = repeat
                .end_sequence
                .ok_or("channel repetition has no completed actual boundary")?;
            if repeat.id.0 as usize != index
                || repeat.start_sequence > end
                || end > facts.channel_message_sequence
                || !facts.allocated_scopes.contains(&repeat.activation)
            {
                return Err("channel repetition identity/activation/interval is incomplete".into());
            }
            if let Some(parent) = repeat.parent {
                let parent = facts
                    .channel_repetitions
                    .get(parent.0 as usize)
                    .filter(|parent| parent.id.0 < repeat.id.0)
                    .ok_or("channel repetition parent is not an earlier actual boundary")?;
                if parent.start_sequence > repeat.start_sequence
                    || parent
                        .end_sequence
                        .is_none_or(|parent_end| parent_end < end)
                {
                    return Err(
                        "nested channel repetition escapes its actual parent interval".into(),
                    );
                }
            }
            if let Some(call) = repeat.call
                && facts
                    .copy_call_events
                    .get(call.0 as usize)
                    .is_none_or(|event| event.id != call)
            {
                return Err("channel repetition names a missing application".into());
            }
        }
        for event in &facts.channel_messages {
            self.charge()?;
            let mut interval = None;
            for repeat in &facts.channel_repetitions {
                self.charge()?;
                if repeat.start_sequence <= event.sequence
                    && repeat.end_sequence.is_some_and(|end| event.sequence < end)
                    && interval.is_none_or(|old: &ChannelRepetition| old.id < repeat.id)
                {
                    interval = Some(repeat);
                }
            }
            if event.repetition != interval.map(|repeat| repeat.id) {
                return Err("channel event does not name its innermost actual repetition".into());
            }
            if physical(&event.action)
                && business_regions.contains(&super::region(facts, event.context)?)
            {
                if interval.is_some() {
                    return Err("repeated channel operations lack iteration-indexed physical event coverage".into());
                }
                // This check survives erasing every repetition and reference:
                // the real application/callback ancestry is independent.
                let bounds = self
                    .execution(event.context, event.source_event, true)?
                    .and(self.syntax(event.context.owner, event.span, false)?.1);
                if !bounds.once {
                    return Err("channel operation belongs to a source loop or callback without a physical event-count proof".into());
                }
            }
        }
        Ok(())
    }

    pub(super) fn inspection_entered(&mut self, event: &ChannelMessageFact) -> Check<bool> {
        let mut bounds = self.execution(event.context, event.source_event, false)?;
        if let ChannelAction::Select { evaluation, .. }
        | ChannelAction::ConditionEvaluated { evaluation, .. } = event.action
        {
            let proof = self
                .facts
                .condition_evaluations
                .get(evaluation.0 as usize)
                .ok_or("inspection selection lacks its actual evaluation")?;
            bounds = bounds.and(self.syntax(proof.context.owner, proof.span, false)?.1);
        }
        if !bounds.entered {
            return Ok(false);
        }
        let mut repeat = event.repetition;
        while let Some(id) = repeat {
            self.charge()?;
            let entry = self
                .facts
                .channel_repetitions
                .get(id.0 as usize)
                .ok_or("inspection names a missing repetition")?;
            // Unknown foreign/iterator callbacks cannot acquire minimum-entry
            // authority merely because one hypothetical invocation was checked.
            let Some(call) = entry.call else {
                return Ok(false);
            };
            if !self.repetition_entered(call)? {
                return Ok(false);
            }
            repeat = entry.parent;
        }
        Ok(true)
    }

    fn execution(
        &mut self,
        context: InvocationContext,
        direct: Option<CopyCallEventId>,
        require_anchor: bool,
    ) -> Check<Bounds> {
        let facts = self.facts;
        let mut calls = BTreeSet::new();
        calls.extend(direct);
        let mut named = Vec::from_iter(context.invocation);
        let mut closures = Vec::from_iter(context.closure_invocation);
        let mut seen_named = BTreeSet::new();
        let mut seen_closures = BTreeSet::new();
        let mut defaults = Vec::from_iter(context.default_use);
        let mut seen_defaults = BTreeSet::new();
        let mut callback_bounds = Bounds::default();
        while !named.is_empty() || !closures.is_empty() || !defaults.is_empty() {
            self.charge()?;
            if let Some(id) = named.pop() {
                if !seen_named.insert(id) {
                    continue;
                }
                let invocation = facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|invocation| invocation.id == id)
                    .ok_or("channel operation has a missing actual named invocation")?;
                if !invocation.declaration_probe
                    && invocation.caller_activation.is_some()
                    && invocation.source_event.is_none()
                {
                    return Err("actual named callback has no incoming source application".into());
                }
                calls.extend(invocation.source_event);
                named.extend(invocation.parent);
                for caller in self.source_index.caller_links(id, &mut self.work)? {
                    closures.extend(caller.caller_closure_invocation);
                    defaults.extend(caller.default_use);
                }
            } else if let Some(id) = closures.pop() {
                if !seen_closures.insert(id) {
                    continue;
                }
                let invocation = facts
                    .closure_invocations
                    .get(id.0 as usize)
                    .filter(|invocation| invocation.id == id)
                    .ok_or("channel operation has a missing actual closure invocation")?;
                if !invocation.probe && invocation.source_event.is_none() {
                    return Err("actual closure callback has no incoming source application".into());
                }
                if !invocation.probe
                    && let Some(call) = invocation.source_event
                {
                    callback_bounds = callback_bounds.and(self.callback(call, invocation.closure)?);
                }
                calls.extend(invocation.source_event);
                named.extend(invocation.parent_named);
                closures.extend(invocation.parent_closure);
            } else if let Some(id) = defaults.pop() {
                if !seen_defaults.insert(id) {
                    continue;
                }
                let default = facts
                    .default_uses
                    .get(id.0 as usize)
                    .filter(|default| default.id == id)
                    .ok_or("channel operation has a missing actual default evaluation")?;
                match default.origin {
                    crate::sema::default_uses::DefaultOrigin::Call(call) => {
                        calls.insert(call);
                    }
                    crate::sema::default_uses::DefaultOrigin::InvocationFallback(id) => {
                        named.push(id)
                    }
                    crate::sema::default_uses::DefaultOrigin::DeclarationProbe => {}
                }
                named.extend(default.caller.invocation);
                closures.extend(default.caller.closure_invocation);
                defaults.extend(default.caller.default_use);
            }
        }
        if require_anchor && calls.is_empty() {
            return Err("channel operation has no actual source application anchor".into());
        }
        let mut bounds = callback_bounds;
        for call in calls {
            bounds = bounds.and(self.call(call)?);
        }
        Ok(bounds)
    }

    fn repetition_entered(&mut self, id: CopyCallEventId) -> Check<bool> {
        let bounds = self.call(id)?;
        let call = &self.facts.copy_call_events[id.0 as usize];
        let callee = &self.facts.expressions[call.callee_expression.unwrap()].value;
        Ok(bounds.entered
            && matches!(callee.callables.as_slice(), [Callable::Builtin(name)] if matches!(name.as_str(),
            "Io::read_all" | "Io::write_all" | "Array::map" | "Array::filter" | "Array::fold" | "Array::find" | "Array::any" | "Array::all" | "Array::for_each")))
    }

    fn callback(&mut self, id: CopyCallEventId, closure: usize) -> Check<Bounds> {
        let bounds = self.call(id)?;
        let call = &self.facts.copy_call_events[id.0 as usize];
        let callee = &self.facts.expressions[call.callee_expression.unwrap()].value;
        match callee.callables.as_slice() {
            [Callable::Closure(target)] if *target == closure => Ok(bounds),
            [Callable::Builtin(name)]
                if matches!(
                    name.as_str(),
                    "Concurrent::scope"
                        | "Concurrent::fork"
                        | "Io::read_all"
                        | "Io::write_all"
                        | "Array::map"
                        | "Array::filter"
                        | "Array::fold"
                        | "Array::find"
                        | "Array::any"
                        | "Array::all"
                        | "Array::for_each"
                        | "Iter::collect"
                        | "Iter::fold"
                        | "Iter::pull"
                        | "Order::sorted"
                        | "Order::binary_search"
                        | "Heap::push"
                        | "Heap::pop"
                        | "Parallel::map"
                        | "Parallel::map_bounded"
                        | "Parallel::find"
                        | "Parallel::first"
                        | "Parallel::any"
                        | "Parallel::fold"
                        | "Parallel::for_each"
                ) =>
            {
                Ok(bounds)
            }
            [Callable::Builtin(name)]
                if matches!(
                    name.as_str(),
                    "File::with_file" | "Process::with_child" | "Div::budget"
                ) =>
            {
                Ok(bounds.and(Bounds {
                    once: true,
                    entered: false,
                    repeated: false,
                }))
            }
            _ => Ok(bounds.and(Bounds::count(None))),
        }
    }

    fn call(&mut self, id: CopyCallEventId) -> Check<Bounds> {
        if let Some(bounds) = self.calls.get(&id) {
            return Ok(*bounds);
        }
        let facts = self.facts;
        let call = self.source_index.application(id, &mut self.work)?;
        let expression = call
            .callee_expression
            .and_then(|index| facts.expressions.get(index))
            .ok_or("channel source application has no evaluated callee identity")?;
        if expression.value.callables.len() != 1 {
            return Err("channel application has no single selected actual callee".into());
        }
        let (syntax, mut bounds) = self.syntax(call.owner, call.span, true)?;
        let ExprKind::Call { callee, .. } = &syntax.kind else {
            unreachable!()
        };
        if expression.span != callee.span {
            return Err(
                "channel source callee does not belong to this application occurrence".into(),
            );
        }
        for callable in &expression.value.callables {
            self.charge()?;
            if let Callable::Builtin(name) = callable {
                let callback = match name.as_str() {
                    "Array::map" | "Array::filter" | "Array::fold" | "Array::find"
                    | "Array::any" | "Array::all" | "Array::for_each" => {
                        let ExprKind::Call { arguments, .. } = &syntax.kind else {
                            unreachable!()
                        };
                        Some(Bounds::count(
                            arguments
                                .first()
                                .and_then(|argument| cardinality(&argument.value)),
                        ))
                    }
                    "Io::read_all" | "Io::write_all" => Some(Bounds {
                        once: false,
                        entered: true,
                        repeated: true,
                    }),
                    "Iter::collect"
                    | "Iter::fold"
                    | "Iter::pull"
                    | "Array::sort"
                    | "Array::sort_by"
                    | "Order::sorted"
                    | "Order::binary_search"
                    | "Heap::push"
                    | "Heap::pop"
                    | "Parallel::map"
                    | "Parallel::map_bounded"
                    | "Parallel::find"
                    | "Parallel::first"
                    | "Parallel::any"
                    | "Parallel::fold"
                    | "Parallel::for_each" => Some(Bounds::count(None)),
                    _ => None,
                };
                if let Some(callback) = callback {
                    bounds = bounds.and(callback);
                }
            }
        }
        self.calls.insert(id, bounds);
        Ok(bounds)
    }

    fn syntax(
        &mut self,
        owner: Option<CallableOwner>,
        span: Span,
        call_only: bool,
    ) -> Check<(&'a Expr, Bounds)> {
        let role = if call_only {
            source_index::Role::Call
        } else {
            source_index::Role::Expression
        };
        self.source_index.lookup(owner, span, role, &mut self.work)
    }

    #[cfg(test)]
    fn syntax_walk(
        &mut self,
        owner: Option<CallableOwner>,
        span: Span,
        call_only: bool,
    ) -> Check<(&'a Expr, Bounds)> {
        let facts = self.facts;
        let mut stack = Vec::new();
        match owner {
            Some(CallableOwner::Function(id)) => {
                let mut function = None;
                for candidate in &facts.functions {
                    self.charge()?;
                    if candidate.definition == id {
                        function = Some(&candidate.syntax);
                        break;
                    }
                }
                let function = function.ok_or("channel source callable definition is missing")?;
                if let Some(body) = &function.body {
                    stack.push(Node::Block(body, Bounds::default()));
                }
                for statement in &function.signature_where {
                    stack.push(Node::Stmt(statement, Bounds::default()));
                }
                for parameter in &function.parameters {
                    if let Some(default) = &parameter.default {
                        stack.push(Node::Expr(default, Bounds::default()));
                    }
                }
            }
            Some(CallableOwner::Lambda(site)) => {
                let mut closure = None;
                for candidate in &facts.closures {
                    self.charge()?;
                    if candidate.site == Some(site) {
                        closure = Some(candidate);
                        break;
                    }
                }
                let closure = closure.ok_or("channel source closure syntax is missing")?;
                stack.push(Node::Expr(&closure.body, Bounds::default()));
            }
            _ => return Err(
                "channel source callable has no closed syntax for execution-bound reconstruction"
                    .into(),
            ),
        }
        let mut found = None;
        while let Some(node) = stack.pop() {
            self.charge()?;
            match node {
                Node::Expr(expression, bounds) => {
                    if expression.span == span
                        && (!call_only || matches!(expression.kind, ExprKind::Call { .. }))
                    {
                        if found.is_some() {
                            return Err("channel source application syntax is ambiguous".into());
                        }
                        found = Some((expression, bounds));
                    }
                    children(expression, bounds, &mut stack);
                }
                Node::Block(block, bounds) => {
                    for statement in block.statements.iter().chain(&block.where_items) {
                        stack.push(Node::Stmt(statement, bounds));
                    }
                }
                Node::Stmt(statement, bounds) => match &statement.kind {
                    StmtKind::Binding(binding) => {
                        stack.push(Node::Expr(&binding.value, bounds));
                        if let Some(fallback) = &binding.fallback {
                            stack.push(Node::Expr(fallback, bounds));
                        }
                        stack.push(Node::Pattern(&binding.pattern, bounds));
                    }
                    StmtKind::Assignment { target, value, .. } => {
                        stack.push(Node::Expr(target, bounds));
                        stack.push(Node::Expr(value, bounds));
                    }
                    StmtKind::Expr { expression, .. }
                    | StmtKind::HandlerApplication(expression) => {
                        stack.push(Node::Expr(expression, bounds))
                    }
                    StmtKind::Handler(arms) => {
                        for arm in arms {
                            stack.push(Node::Expr(&arm.body, bounds));
                        }
                    }
                    StmtKind::Function(_)
                    | StmtKind::Type(_)
                    | StmtKind::Effect(_)
                    | StmtKind::Use(_) => {}
                },
                Node::Pattern(pattern, bounds) => match &pattern.kind {
                    PatternKind::Value(value) => stack.push(Node::Expr(value, bounds)),
                    PatternKind::Tuple(values)
                    | PatternKind::Alternative(values)
                    | PatternKind::Constructor {
                        arguments: values, ..
                    } => {
                        for value in values {
                            stack.push(Node::Pattern(value, bounds));
                        }
                    }
                    PatternKind::Record { fields, .. } => {
                        for field in fields {
                            stack.push(Node::Pattern(&field.pattern, bounds));
                        }
                    }
                    PatternKind::Mode { pattern, .. } => stack.push(Node::Pattern(pattern, bounds)),
                    _ => {}
                },
            }
            if stack.len() > self.work {
                return Err("channel syntax traversal exceeds its pending work bound".into());
            }
        }
        found.ok_or_else(|| {
            "channel source application is absent from its actual callable syntax".into()
        })
    }
}

fn physical(action: &ChannelAction) -> bool {
    matches!(
        action,
        ChannelAction::Send { .. }
            | ChannelAction::Receive { .. }
            | ChannelAction::TaskFork { .. }
            | ChannelAction::TaskJoin { .. }
    )
}

enum Node<'a> {
    Expr(&'a Expr, Bounds),
    Block(&'a Block, Bounds),
    Stmt(&'a Stmt, Bounds),
    Pattern(&'a Pattern, Bounds),
}
fn children<'a>(expression: &'a Expr, bounds: Bounds, stack: &mut Vec<Node<'a>>) {
    match &expression.kind {
        ExprKind::Loop(body) => stack.push(Node::Block(
            body,
            bounds.and(Bounds {
                once: terminal(body),
                entered: true,
                repeated: !terminal(body),
            }),
        )),
        ExprKind::While { condition, body } => {
            let iteration = Bounds {
                once: terminal(body),
                entered: false,
                repeated: !terminal(body),
            };
            stack.push(Node::Expr(condition, bounds.and(iteration)));
            stack.push(Node::Block(body, bounds.and(iteration)));
        }
        ExprKind::For {
            iterable,
            pattern,
            body,
        } => {
            stack.push(Node::Expr(iterable, bounds));
            let mut iteration = Bounds::count(cardinality(iterable));
            if terminal(body) {
                iteration.once = true;
                iteration.repeated = false;
            }
            stack.push(Node::Pattern(pattern, bounds.and(iteration)));
            stack.push(Node::Block(body, bounds.and(iteration)));
        }
        ExprKind::Block(block) => stack.push(Node::Block(block, bounds)),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            stack.push(Node::Expr(condition, bounds));
            stack.push(Node::Expr(then_branch, bounds));
            if let Some(value) = else_branch {
                stack.push(Node::Expr(value, bounds));
            }
        }
        ExprKind::Match { value, arms, .. } => {
            stack.push(Node::Expr(value, bounds));
            for arm in arms {
                stack.push(Node::Pattern(&arm.pattern, bounds));
                if let Some(guard) = &arm.guard {
                    stack.push(Node::Expr(guard, bounds));
                }
                stack.push(Node::Expr(&arm.body, bounds));
            }
        }
        ExprKind::Is { value, pattern } => {
            stack.push(Node::Expr(value, bounds));
            stack.push(Node::Pattern(pattern, bounds));
        }
        ExprKind::Tuple(values) | ExprKind::Array(values) => {
            for value in values {
                stack.push(Node::Expr(value, bounds));
            }
        }
        ExprKind::Map(values) => {
            for (key, value) in values {
                stack.push(Node::Expr(key, bounds));
                stack.push(Node::Expr(value, bounds));
            }
        }
        ExprKind::Record {
            fields,
            spread,
            members,
            ..
        } => {
            for field in fields {
                stack.push(Node::Expr(&field.value, bounds));
            }
            if let Some(spread) = spread {
                stack.push(Node::Expr(spread, bounds));
            }
            for member in members {
                match member {
                    RecordMember::Field(field) => stack.push(Node::Expr(&field.value, bounds)),
                    RecordMember::Spread(value) => stack.push(Node::Expr(value, bounds)),
                }
            }
        }
        ExprKind::Generic { base, .. }
        | ExprKind::Unary { operand: base, .. }
        | ExprKind::Field { base, .. } => stack.push(Node::Expr(base, bounds)),
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
            stack.push(Node::Expr(left, bounds));
            stack.push(Node::Expr(right, bounds));
        }
        ExprKind::Call { callee, arguments } => {
            stack.push(Node::Expr(callee, bounds));
            for argument in arguments {
                stack.push(Node::Expr(&argument.value, bounds));
            }
        }
        ExprKind::Derive { base, recipe } => {
            if let Some(base) = base {
                stack.push(Node::Expr(base, bounds));
            }
            stack.push(Node::Expr(recipe, bounds));
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                stack.push(Node::Expr(start, bounds));
            }
            if let Some(end) = end {
                stack.push(Node::Expr(end, bounds));
            }
        }
        ExprKind::Control { value, .. } => {
            if let Some(value) = value {
                stack.push(Node::Expr(value, bounds));
            }
        }
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation { expression, .. } = part {
                    stack.push(Node::Expr(expression, bounds));
                }
            }
        }
        // Creating a callable does not enter its body. Its actual invocation
        // has its own owner and incoming application identity above.
        ExprKind::Lambda { .. }
        | ExprKind::Literal(_)
        | ExprKind::Name(_)
        | ExprKind::Path(_)
        | ExprKind::Accessor(_)
        | ExprKind::TypeValue(_)
        | ExprKind::KeyOf(_)
        | ExprKind::Ambient
        | ExprKind::Error => {}
    }
}
fn terminal(body: &Block) -> bool {
    matches!(
        body.statements.last().map(|statement| &statement.kind),
        Some(StmtKind::Expr {
            expression: Expr {
                kind: ExprKind::Control {
                    operation: ControlOperation::Last | ControlOperation::Return,
                    value: None
                },
                ..
            },
            ..
        })
    )
}
fn cardinality(expression: &Expr) -> Option<u64> {
    match &expression.kind {
        ExprKind::Array(values) => u64::try_from(values.len()).ok(),
        ExprKind::Range {
            start: Some(start),
            end: Some(end),
            inclusive,
        } => {
            let integer = |value: &Expr| match &value.kind {
                ExprKind::Literal(Literal::Integer(raw)) => raw.parse::<i128>().ok(),
                _ => None,
            };
            let length = integer(end)?
                .checked_sub(integer(start)?)?
                .checked_add(i128::from(*inclusive))?;
            u64::try_from(length.max(0)).ok()
        }
        _ => None,
    }
}
