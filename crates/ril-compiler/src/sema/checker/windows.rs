//! Read-only windows retain the identity of their actual backing storage.
use super::*;
mod patterns;
pub(super) struct WindowBlockUses {
    pub statements: Vec<Stmt>,
    pub next: usize,
    pub environment: Env,
    pub repeated: bool,
}
pub(super) struct WindowExpressionUses {
    pub bindings: BTreeSet<BindingId>,
    pub certain: bool,
}
const BACKING: &str = "ril__window_backing";

impl Checker {
    pub(super) fn window_expression_uses(
        &self,
        expr: &Expr,
        frame: &Frame,
    ) -> WindowExpressionUses {
        let mut names = BTreeSet::new();
        if !matches!(expr.kind, ExprKind::Block(_)) {
            expressions::collect_names(expr, &mut names);
        }
        WindowExpressionUses {
            bindings: names
                .iter()
                .filter_map(|name| frame.env.get(name).copied())
                .collect(),
            certain: false,
        }
    }
    pub(super) fn window_future_expressions(&mut self, expressions: &[&Expr], frame: &Frame) {
        let mut names = BTreeSet::new();
        for expression in expressions {
            super::expressions::collect_names(expression, &mut names);
        }
        if let Some(context) = self.window_expression_uses.last_mut() {
            context.bindings = names
                .iter()
                .filter_map(|name| frame.env.get(name).copied())
                .collect();
            context.certain = true;
        }
    }
    pub(super) fn has_window(&self, value: &Value) -> bool {
        self.heap
            .reachable(value.origins.nodes.iter().copied())
            .iter()
            .any(|node| self.windows.contains_key(node))
    }
    pub(super) fn refresh_window_fields(&mut self) {
        let Some(span) = self.windows.values().next().map(|info| info.span) else {
            return;
        };
        let windows = self.application_effect.with_work(|work| {
            use crate::sema::source_types::SourceTypesError;
            *work = work
                .checked_sub(1 + self.windows.len())
                .ok_or(SourceTypesError::BudgetExceeded)?;
            for info in self.windows.values() {
                crate::sema::pattern_windows::charge_info(info, work)?;
            }
            Ok::<Vec<_>, SourceTypesError>(
                self.windows
                    .iter()
                    .map(|(node, info)| (*node, info.clone()))
                    .collect(),
            )
        });
        let windows = match windows {
            Ok(windows) => windows,
            Err(error) => {
                self.unsupported(span, format!("window storage projection: {error}"));
                return;
            }
        };
        for (node, window) in windows {
            let publication = self
                .fields
                .get(&(node, Slot::Field(BACKING.into())))
                .map(|value| value.publication)
                .unwrap_or(Publication::Live);
            let selected = self.application_effect.with_work(|work| {
                use crate::sema::source_types::SourceTypesError;
                let scan = self
                    .fields
                    .len()
                    .checked_mul(
                        3 + window.backing.nodes.len().checked_ilog2().unwrap_or(0) as usize,
                    )
                    .ok_or(SourceTypesError::BudgetExceeded)?;
                *work = work
                    .checked_sub(scan + self.heap.nodes[node.0 as usize].fields.len())
                    .ok_or(SourceTypesError::BudgetExceeded)?;
                let selected = crate::sema::pattern_windows::selected_fields(
                    self.fields
                        .iter()
                        .filter(|((parent, _), _)| window.backing.nodes.contains(parent))
                        .map(|((_, slot), value)| (slot, value)),
                    window.lower,
                    window.length,
                    publication,
                    window.cause,
                    work,
                )?;
                for value in selected.values() {
                    *work = work
                        .checked_sub(2 + value.origins.nodes.len())
                        .ok_or(SourceTypesError::BudgetExceeded)?;
                }
                Ok::<_, SourceTypesError>(selected)
            });
            let selected = match selected {
                Ok(selected) => selected,
                Err(error) => {
                    self.unsupported(window.span, format!("window storage projection: {error}"));
                    return;
                }
            };
            self.fields.retain(|(parent, slot), _| {
                *parent != node || !matches!(slot, Slot::Index(_) | Slot::AnyIndex)
            });
            self.heap.nodes[node.0 as usize]
                .fields
                .retain(|slot, _| !matches!(slot, Slot::Index(_) | Slot::AnyIndex));
            for (slot, value) in selected {
                self.heap.nodes[node.0 as usize]
                    .fields
                    .insert(slot.clone(), value.origins.nodes.clone());
                self.fields.insert((node, slot), value);
            }
        }
    }
    fn binding_windows(
        &self,
        id: BindingId,
        seen: &mut BTreeSet<BindingId>,
        output: &mut BTreeSet<NodeId>,
    ) {
        if !seen.insert(id) {
            return;
        }
        self.value_windows(&self.bindings[id].value, seen, output);
    }
    fn value_windows(
        &self,
        value: &Value,
        seen: &mut BTreeSet<BindingId>,
        output: &mut BTreeSet<NodeId>,
    ) {
        let mut pending = vec![value.clone()];
        while let Some(value) = pending.pop() {
            output.extend(
                self.heap
                    .reachable(value.origins.nodes.iter().copied())
                    .into_iter()
                    .filter(|node| self.windows.contains_key(node)),
            );
            for callable in self.graph_callables(&value) {
                let captures: Vec<_> = match callable {
                    Callable::Named(function, _) => {
                        let info = &self.functions[function];
                        let Some(body) = &info.syntax.body else {
                            continue;
                        };
                        let mut names = BTreeSet::new();
                        expressions::collect_names(
                            &Expr {
                                hir_id: None,
                                kind: ExprKind::Block(body.clone()),
                                span: body.span,
                            },
                            &mut names,
                        );
                        names
                            .iter()
                            .filter_map(|name| info.lexical.get(name).copied())
                            .collect()
                    }
                    Callable::Closure(closure) => {
                        self.closures[closure].captures.iter().copied().collect()
                    }
                    _ => continue,
                };
                for capture in captures {
                    if seen.insert(capture) {
                        pending.push(self.bindings[capture].value.clone());
                    }
                }
            }
        }
    }
    fn future_window_nodes(&self) -> (BTreeSet<NodeId>, BTreeSet<NodeId>) {
        let mut definite = BTreeSet::new();
        let mut uncertain = BTreeSet::new();
        for context in &self.window_blocks {
            let statements = if context.repeated {
                &context.statements[..]
            } else {
                &context.statements[context.next..]
            };
            for name in remaining_names(statements) {
                if let Some(binding) = context.environment.get(&name) {
                    self.binding_windows(*binding, &mut BTreeSet::new(), &mut definite);
                }
            }
        }
        for context in &self.window_expression_uses {
            for binding in &context.bindings {
                self.binding_windows(
                    *binding,
                    &mut BTreeSet::new(),
                    if context.certain {
                        &mut definite
                    } else {
                        &mut uncertain
                    },
                );
            }
        }
        for (id, binding) in self.bindings.iter().enumerate() {
            if binding.alive && binding.owner == ScopeId(0) {
                self.binding_windows(id, &mut BTreeSet::new(), &mut uncertain);
            }
            if binding.alive
                && matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
                && !self.completed_cleanups.contains(&id)
            {
                for node in &binding.value.origins.nodes {
                    if let Some(callback) =
                        self.fields.get(&(*node, Slot::Field("on_close".into())))
                    {
                        self.value_windows(callback, &mut BTreeSet::new(), &mut definite);
                    }
                }
            }
        }
        for arm in &self.deferred_arm_cleanups {
            if let Some(suffix) = &arm.suffix {
                for name in remaining_names(&suffix.statements) {
                    if let Some(binding) = arm.frame.env.get(&name) {
                        self.binding_windows(*binding, &mut BTreeSet::new(), &mut definite);
                    }
                }
            }
        }
        for binding in self.active_handler_window_bindings() {
            self.binding_windows(binding, &mut BTreeSet::new(), &mut uncertain);
        }
        definite.extend(
            self.active_iterations
                .iter()
                .flat_map(|origins| origins.nodes.iter().copied())
                .filter(|node| self.windows.contains_key(node)),
        );
        (definite, uncertain)
    }
    pub(super) fn unknown_window_callback(&mut self, callee: &Value, span: Span) {
        let (definite, uncertain) = self.future_window_nodes();
        if definite
            .union(&uncertain)
            .any(|node| !self.origins_disjoint(&self.windows[node].backing, &callee.origins))
        {
            self.unsupported(
                span,
                "unknown callback may structurally invalidate a window used by its continuation",
            );
        }
    }
    pub(super) fn check_window_stability(&mut self, source: &Value, span: Span) {
        if self.windows.is_empty() {
            return;
        }
        let (definite, uncertain) = self.future_window_nodes();
        let affected: Vec<_> = self
            .windows
            .iter()
            .filter(|(_, window)| !self.origins_disjoint(&window.backing, &source.origins))
            .map(|(node, window)| (*node, window.cause))
            .collect();
        for (node, cause) in affected {
            if self
                .active_iterations
                .iter()
                .any(|origins| origins.nodes.contains(&node))
            {
                self.error(
                    "E0526",
                    span,
                    "structural mutation changes a traversed window's backing storage",
                    [cause, source.cause],
                );
            } else if definite.contains(&node) {
                self.error(
                    "E0537",
                    span,
                    "structural mutation precedes a possible later use of a live slice window",
                    [cause, source.cause],
                );
            } else if uncertain.contains(&node) {
                self.unsupported(span,"window liveness through the current expression or module environment requires a complete use-order proof");
            }
        }
    }
    pub(super) fn slice_window(
        &mut self,
        base: &Expr,
        start: Option<&Expr>,
        end: Option<&Expr>,
        inclusive: bool,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let mut source = self.expression(base, frame);
        if source.ty == Ty::Never {
            return source;
        }
        let ty = self.collection_type(&source);
        let Ty::Array(element) = ty else {
            self.error(
                "E0352",
                span,
                "slice windows require an array receiver",
                [source.cause],
            );
            return self.unit(span);
        };
        let source_recency = self.recency_moves.len();
        let lower = start.map(|expr| self.expression(expr, frame));
        if let Some(value) = &lower
            && value.ty == Ty::Never
        {
            if let Some(end) = end {
                let skipped = self.preview_expression(end, frame);
                self.require_type(&skipped, &Ty::Int("int".into()), end.span);
            }
            return value.clone();
        }
        let upper = end.map(|expr| self.expression(expr, frame));
        self.transport_value_since(&mut source, source_recency);
        for (value, source_span) in lower
            .iter()
            .map(|value| (value, start.unwrap().span))
            .chain(upper.iter().map(|value| (value, end.unwrap().span)))
        {
            self.require_type(value, &Ty::Int("int".into()), source_span);
            if value.ty == Ty::Never {
                return value.clone();
            }
        }
        if !source.stable && source.publication != Publication::Immutable {
            self.error(
                "E0531",
                span,
                "live slice windows require a pinned stable source origin",
                [source.cause],
            );
        }
        self.access(&source, None, Mode::Read, span, frame);
        let constant = |value: &Value| match value.constant {
            Some(Constant::Integer(value)) => u64::try_from(value).ok(),
            _ => None,
        };
        let lower = lower
            .as_ref()
            .and_then(constant)
            .or_else(|| start.is_none().then_some(0));
        let source_length = self.known_array_length(&source);
        let upper = if let Some(value) = &upper {
            constant(value).and_then(|value| {
                if inclusive {
                    value.checked_add(1)
                } else {
                    Some(value)
                }
            })
        } else {
            source_length
        };
        let length = lower
            .zip(upper)
            .and_then(|(lower, upper)| upper.checked_sub(lower));
        let mut backing = source.origins.clone();
        let mut offset = lower;
        if source.origins.nodes.len() == 1
            && let Some(parent) = self.windows.get(source.origins.nodes.first().unwrap())
        {
            backing = parent.backing.clone();
            offset = parent
                .lower
                .zip(lower)
                .and_then(|(left, right)| left.checked_add(right));
        } else if source
            .origins
            .nodes
            .iter()
            .any(|node| self.windows.contains_key(node))
        {
            self.unsupported(
                span,
                "joining nested window offsets requires a conditional coordinate proof",
            );
        }
        let node = self.allocate_owned(
            Span {
                file: span.file,
                start: base.span.end,
                end: span.end,
            },
            0x6000_0000,
            frame.owner,
        );
        let cause = self.cause(
            CauseKind::Projection,
            span,
            "read-only window pins selected slots of its backing collection",
            [source.cause],
        );
        self.windows.insert(
            node,
            super::super::WindowInfo {
                pattern: None,
                constant: None,
                backing: backing.clone(),
                lower: offset,
                length,
                span,
                cause,
            },
        );
        let mut retained = source.clone();
        retained.origins = backing;
        retained.permission = Permission::Read;
        retained.construction = false;
        retained.marker = false;
        retained.retention_result = false;
        self.store_field(node, Slot::Field(BACKING.into()), retained);
        self.array_lengths.insert(node, length);
        let mut value = Value::reference(Ty::Array(element), node, cause);
        value.permission = Permission::Read;
        value.publication = source.publication;
        value.construction = false;
        value.stable = source.stable || source.publication == Publication::Immutable;
        value.sources = source.sources.clone();
        value.participants = source.participants.clone();
        value.scoped = source.scoped.clone();
        value.temporary = source.temporary;
        if !source.results.is_empty() {
            self.unsupported(
                span,
                "slice Result membership requires exact conditional producer coverage",
            );
            value.results = source.results.clone();
        }
        value
    }
    pub(super) fn window_projection(
        &mut self,
        base: &Value,
        slot: &Slot,
        span: Span,
        frame: &mut Frame,
        read: bool,
    ) -> Option<Value> {
        if !matches!(slot, Slot::Index(_) | Slot::AnyIndex)
            || base.origins.nodes.is_empty()
            || !base
                .origins
                .nodes
                .iter()
                .all(|node| self.windows.contains_key(node))
        {
            return None;
        }
        let mut values = Vec::new();
        for node in &base.origins.nodes {
            let window = self.windows[node].clone();
            let mut source = self
                .fields
                .get(&(*node, Slot::Field(BACKING.into())))?
                .clone();
            source.origins = window.backing;
            source.permission = Permission::Read;
            source.construction = false;
            source.marker = false;
            source.retention_result = false;
            source.participants = base.participants.clone();
            source.sources = base.sources.clone();
            source.publication = base.publication;
            let mapped = match (slot, window.lower) {
                (Slot::Index(index), Some(lower)) => i64::try_from(lower)
                    .ok()
                    .and_then(|lower| lower.checked_add(*index))
                    .map(Slot::Index)
                    .unwrap_or(Slot::AnyIndex),
                _ => Slot::AnyIndex,
            };
            values.push(self.project(&source, mapped, span, frame, read));
        }
        let mut value = values.remove(0);
        for other in values {
            value = value.join(&other, self.choice(), base.cause);
        }
        value.permission = Permission::Read;
        value.construction = false;
        value.marker = false;
        value.retention_result = false;
        Some(value)
    }
}

fn remaining_names(statements: &[Stmt]) -> BTreeSet<String> {
    fn bound(pattern: &Pattern, names: &mut BTreeSet<String>) {
        match &pattern.kind {
            PatternKind::Name(name) => {
                names.remove(name);
            }
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    bound(item, names);
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    bound(&field.pattern, names);
                }
                if let Some(name) = rest_binding {
                    names.remove(name);
                }
            }
            PatternKind::Mode { pattern, .. } => bound(pattern, names),
            PatternKind::Type {
                binder: Some(name), ..
            } => {
                names.remove(name);
            }
            _ => {}
        }
    }
    let mut names = BTreeSet::new();
    for statement in statements.iter().rev() {
        match &statement.kind {
            StmtKind::Binding(binding) => {
                bound(&binding.pattern, &mut names);
                expressions::collect_names(&binding.value, &mut names);
                if let Some(fallback) = &binding.fallback {
                    expressions::collect_names(fallback, &mut names);
                }
            }
            StmtKind::Assignment {
                target,
                operator,
                value,
            } => {
                if operator == "="
                    && let ExprKind::Name(name) = &target.kind
                {
                    names.remove(name);
                } else {
                    expressions::collect_names(target, &mut names);
                }
                expressions::collect_names(value, &mut names);
            }
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                expressions::collect_names(expression, &mut names)
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    expressions::collect_names(&arm.body, &mut names);
                }
            }
            _ => {}
        }
    }
    names
}
