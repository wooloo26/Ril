//! Lexical environments of block-local named definitions have independent
//! dynamic identities, even when their source declaration is the same.
use super::*;

impl Checker {
    /// Latent handler/helper analysis can discover captures absent from the
    /// syntactic free-name list. Publish their restored complete graph only
    /// after preview rollback; otherwise new Capture edges would be discarded.
    pub(super) fn finalize_closure_environment(&mut self, id: usize, value: &mut Value) {
        let closure = self.closures[id].clone();
        let mut observer = false;
        for (index, binding) in closure.captures.iter().copied().enumerate() {
            let captured = self.capture_value(binding);
            let captured = self.named_environment_value(captured, false);
            let reachable = self.heap.reachable(captured.origins.nodes.iter().copied());
            let live = |value: &Value| {
                value.publication == Publication::Live
                    || value.mutable_environment
                    || value.observer_environment
            };
            observer |= self.bindings[binding].mode.is_reassignable()
                || live(&captured)
                || self.has_writer(&captured)
                || self
                    .fields
                    .iter()
                    .any(|((node, _), value)| reachable.contains(node) && live(value));
            value.scoped.extend(&captured.scoped);
            let slot = Slot::Capture(index as u32);
            let captured = if self.heap.nodes[closure.node.0 as usize].multiplicity
                == Multiplicity::MayMany
            {
                if let Some(previous) = self.fields.get(&(closure.node, slot.clone())).cloned() {
                    previous.join(&captured, self.choice(), value.cause)
                } else {
                    captured
                }
            } else {
                captured
            };
            self.store_field(closure.node, slot, captured);
        }
        let environment = self.heap.reachable([closure.node]);
        observer |= self.fields.iter().any(|((node, _), captured)| {
            environment.contains(node)
                && (captured.publication == Publication::Live
                    || captured.mutable_environment
                    || captured.observer_environment)
        });
        let mutable = closure
            .captures
            .iter()
            .any(|binding| closure.writes.contains(binding));
        value.mutable_environment |= mutable;
        value.observer_environment = observer && !value.mutable_environment;
        if value.mutable_environment || value.observer_environment {
            value.publication = Publication::Live;
            value.permission = if value.mutable_environment {
                Permission::Write
            } else {
                Permission::Read
            };
            if value.observer_environment {
                value.construction = false;
            }
        }
    }

    pub(super) fn declare_lexical_bindings(&mut self, statements: &[Stmt], frame: &Frame) {
        let scope = self.block_boundaries.last().copied().unwrap_or(u32::MAX);
        fn register(
            pattern: &Pattern,
            owner: ScopeId,
            scope: u32,
            table: &mut BTreeMap<(ScopeId, u32, String), Span>,
        ) {
            match &pattern.kind {
                PatternKind::Name(name) => {
                    table
                        .entry((owner, scope, name.clone()))
                        .or_insert(pattern.span);
                }
                PatternKind::Tuple(items)
                | PatternKind::Alternative(items)
                | PatternKind::Constructor {
                    arguments: items, ..
                } => {
                    for item in items {
                        register(item, owner, scope, table);
                    }
                }
                PatternKind::Record { fields, .. } => {
                    for field in fields {
                        register(&field.pattern, owner, scope, table);
                    }
                }
                PatternKind::Mode { pattern, .. } => register(pattern, owner, scope, table),
                _ => {}
            }
        }
        for statement in statements {
            if let StmtKind::Binding(binding) = &statement.kind {
                register(
                    &binding.pattern,
                    frame.owner,
                    scope,
                    &mut self.lexical_declarations,
                );
            }
        }
    }
    pub(super) fn check_named_initialization(&mut self, id: usize) {
        self.check_named_initialization_inner(id, &mut BTreeSet::new());
    }
    fn check_named_initialization_inner(&mut self, id: usize, seen: &mut BTreeSet<usize>) {
        if !seen.insert(id) {
            return;
        }
        let info = self.functions[id].clone();
        let Some(body) = &info.syntax.body else {
            return;
        };
        let expression = Expr {
            kind: ExprKind::Block(body.clone()),
            span: body.span,
        };
        let mut names = BTreeSet::new();
        expressions::collect_names(&expression, &mut names);
        for parameter in &info.syntax.parameters {
            for name in pattern_names(&parameter.pattern) {
                names.remove(&name);
            }
        }
        for name in names {
            let owner = info.owner.unwrap_or(ScopeId(0));
            if let Some(expected) = self
                .lexical_declarations
                .get(&(owner, info.lexical_scope, name.clone()))
                .copied()
                && info
                    .lexical
                    .get(&name)
                    .is_none_or(|binding| self.bindings[*binding].span != expected)
            {
                self.error(
                    "E0207",
                    info.syntax.span,
                    format!("captured lexical binding {name} has not been initialized"),
                    [],
                );
            }
            let functions: Vec<_> = info
                .lexical
                .get(&name)
                .into_iter()
                .flat_map(|binding| self.bindings[*binding].value.callables.iter())
                .filter_map(|callable| match callable {
                    Callable::Named(other) => Some(*other),
                    _ => None,
                })
                .collect();
            for function in functions {
                self.check_named_initialization_inner(function, seen);
            }
        }
    }
    pub(super) fn update_named_lexical_binding(&mut self, binding: BindingId) {
        let source = &self.bindings[binding];
        for function in &mut self.functions {
            if (function.owner == Some(source.owner)
                || (function.owner.is_none() && source.owner == ScopeId(0)))
                && function.lexical_scope == source.lexical_scope
            {
                function.lexical.insert(source.name.clone(), binding);
            }
        }
    }
    fn named_free_bindings(
        &self,
        id: usize,
        seen: &mut BTreeSet<usize>,
        captures: &mut BTreeSet<BindingId>,
        writes: &mut BTreeSet<BindingId>,
    ) {
        if !seen.insert(id) {
            return;
        }
        let function = &self.functions[id];
        let Some(body) = &function.syntax.body else {
            return;
        };
        let expression = Expr {
            kind: ExprKind::Block(body.clone()),
            span: body.span,
        };
        let mut names = BTreeSet::new();
        expressions::collect_names(&expression, &mut names);
        for parameter in &function.syntax.parameters {
            for name in pattern_names(&parameter.pattern) {
                names.remove(&name);
            }
        }
        let mutated = expressions::mutated_names(&expression);
        for name in names {
            let Some(&binding) = function.lexical.get(&name) else {
                continue;
            };
            let source = &self.bindings[binding];
            // Calling another declaration retains its actual source environment,
            // rather than a scalar alias to a declaration being a data capture.
            let declaration = source
                .value
                .callables
                .iter()
                .find_map(|callable| match callable {
                    Callable::Named(other) if source.span == self.functions[*other].syntax.span => {
                        Some(*other)
                    }
                    _ => None,
                });
            if let Some(other) = declaration {
                if self.functions[other].owner.is_some() {
                    self.named_free_bindings(other, seen, captures, writes);
                }
            } else if source.owner != ScopeId(0) && !self.static_value_bindings.contains(&binding) {
                captures.insert(binding);
                if mutated.contains(&name) {
                    writes.insert(binding);
                }
            }
        }
    }
    pub(super) fn ensure_named_environment(&mut self, id: usize) {
        if self.functions[id].owner.is_none() {
            return;
        }
        self.check_named_initialization(id);
        let mut captures = BTreeSet::new();
        let mut writes = BTreeSet::new();
        self.named_free_bindings(id, &mut BTreeSet::new(), &mut captures, &mut writes);
        self.functions[id].captures.extend(captures);
        self.functions[id].writes.extend(writes);
        for binding in self.functions[id].captures.clone() {
            if self.bindings[binding].value.mutable_environment {
                self.functions[id].writes.insert(binding);
            }
        }
        for binding in self.functions[id].writes.clone() {
            if self.bindings[binding].mode.is_reassignable() {
                self.bindings[binding].slot_used = true;
            } else {
                self.mark_write(binding);
            }
        }
        if self.functions[id].captures.is_empty() {
            return;
        }
        let owner = self.functions[id].owner.unwrap();
        let span = self.functions[id].syntax.span;
        let node = if let Some(node) = self.functions[id].environment {
            node
        } else {
            let node = self.allocate_owned(span, 0x4000_0000, owner);
            self.functions[id].environment = Some(node);
            node
        };
        for (index, binding) in self.functions[id].captures.clone().into_iter().enumerate() {
            self.store_field(
                node,
                Slot::Capture(index as u32),
                self.capture_value(binding),
            );
        }
    }
    pub(super) fn named_environment_value(&mut self, mut value: Value, declaration: bool) -> Value {
        let named: Vec<_> = value
            .callables
            .iter()
            .filter_map(|callable| match callable {
                Callable::Named(id) => Some(*id),
                _ => None,
            })
            .collect();
        for id in named {
            self.ensure_named_environment(id);
            let info = self.functions[id].clone();
            let Some(node) = info.environment else {
                continue;
            };
            value.origins.nodes.insert(node);
            let mutable = !info.writes.is_empty();
            let observer = info.captures.iter().any(|binding| {
                self.bindings[*binding].mode.is_reassignable()
                    || self.bindings[*binding].value.publication == Publication::Live
            });
            value.mutable_environment |= mutable;
            value.observer_environment |= observer && !mutable;
            for binding in &info.captures {
                value.scoped.extend(&self.bindings[*binding].value.scoped);
            }
            if declaration {
                value.permission = if mutable {
                    Permission::Write
                } else {
                    Permission::Read
                };
                value.publication = if mutable || observer {
                    Publication::Live
                } else {
                    Publication::Immutable
                };
                value.construction = !info.environment_published;
            } else if mutable || observer {
                // A previously received read handle cannot be upgraded when a
                // later initialized lexical binding reveals more capture shape.
                value.publication = Publication::Live;
                value.construction = false;
            }
        }
        value
    }
    pub(super) fn publish_named_environments(&mut self, value: &Value) {
        for callable in self.graph_callables(value) {
            if let Callable::Named(id) = callable {
                self.functions[id].environment_published = true;
            }
        }
    }
    pub(super) fn captured_loan_overlay(
        &mut self,
        callable: &Callable,
        handle: &Value,
    ) -> Vec<(BindingId, BTreeSet<Participant>, bool)> {
        if !handle
            .participants
            .iter()
            .any(|p| matches!(p, Participant::Loan(_)))
        {
            return Vec::new();
        }
        let captures = match callable {
            Callable::Named(id) => self.functions[*id].captures.clone(),
            Callable::Closure(id) => self.closures[*id].captures.clone(),
            _ => return Vec::new(),
        };
        captures
            .into_iter()
            .map(|id| {
                let value = &mut self.bindings[id].value;
                let saved = (id, value.participants.clone(), value.temporary);
                value.participants = handle.participants.clone();
                value.temporary |= handle.temporary;
                saved
            })
            .collect()
    }
    pub(super) fn restore_captured_loan_overlay(
        &mut self,
        overlay: Vec<(BindingId, BTreeSet<Participant>, bool)>,
    ) {
        for (id, participants, temporary) in overlay {
            self.bindings[id].value.participants = participants;
            self.bindings[id].value.temporary = temporary;
        }
    }
}
pub(super) fn pattern_names(pattern: &Pattern) -> Vec<String> {
    match &pattern.kind {
        PatternKind::Name(name) => vec![name.clone()],
        PatternKind::Tuple(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => items.iter().flat_map(pattern_names).collect(),
        PatternKind::Record { fields, .. } => fields
            .iter()
            .flat_map(|field| pattern_names(&field.pattern))
            .collect(),
        PatternKind::Mode { pattern, .. } => pattern_names(pattern),
        _ => Vec::new(),
    }
}
