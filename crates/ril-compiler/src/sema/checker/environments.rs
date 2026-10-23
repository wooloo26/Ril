//! Lexical environments of block-local named definitions have independent
//! dynamic identities, even when their source declaration is the same.
use super::*;

impl Checker {
    fn named_declaration_owner_matches(
        &self,
        mut lexical: crate::hir::nodes::LexicalOwner,
        actual: Option<CallableOwner>,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<bool, crate::sema::source_types::SourceTypesError> {
        use crate::{hir::nodes::LexicalOwner, sema::source_types::SourceTypesError};
        for _ in 0..128 {
            work.charge(2)?;
            return match (lexical, actual) {
                (LexicalOwner::Module, Some(CallableOwner::Global)) => Ok(true),
                (
                    LexicalOwner::Declaration(statement),
                    Some(CallableOwner::Function(definition)),
                ) => {
                    work.charge(self.functions.len())?;
                    let mut found = false;
                    for function in &self.functions {
                        if function.definition != definition {
                            continue;
                        }
                        if function.hir_id != Some(statement) {
                            return Err(SourceTypesError::Unresolved);
                        }
                        found = true;
                    }
                    let parent = self
                        .semantic_hir
                        .statement(statement)
                        .ok_or(SourceTypesError::MissingNode)?;
                    Ok(found && matches!(parent.kind, crate::hir::nodes::StmtKind::Function(_)))
                }
                (LexicalOwner::Lambda(expression), Some(CallableOwner::Lambda(site))) => {
                    let original = self
                        .application_effect
                        .closure_sites
                        .get(site.0 as usize)
                        .ok_or(SourceTypesError::MissingNode)?;
                    Ok(original.id == site && original.source == expression)
                }
                (LexicalOwner::HandlerArm { statement, .. }, _) => {
                    lexical = self
                        .semantic_hir
                        .statement(statement)
                        .ok_or(SourceTypesError::MissingNode)?
                        .info
                        .owner;
                    continue;
                }
                _ => Ok(false),
            };
        }
        Err(SourceTypesError::BudgetExceeded)
    }
    pub(super) fn original_named_declaration_with_work(
        &mut self,
        binding: BindingId,
    ) -> Result<Option<usize>, crate::sema::source_types::SourceTypesError> {
        let mut lease = self.application_effect.lease_work(4_000_000);
        let declaration = self.original_named_declaration(binding, lease.work());
        let returned = self.application_effect.return_work(lease);
        declaration.and_then(|declaration| returned.map(|()| declaration))
    }
    /// The function's own lexical binding is a dynamic reverse edge to its
    /// original declaration. A value alias, parameter or equal span is not it.
    pub(super) fn original_named_declaration(
        &self,
        binding: BindingId,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<Option<usize>, crate::sema::source_types::SourceTypesError> {
        use crate::sema::source_types::SourceTypesError;
        work.charge(4)?;
        let source = self
            .bindings
            .get(binding)
            .ok_or(SourceTypesError::MissingNode)?;
        if source.parameter || source.pattern.is_some() || source.birth.is_some() {
            if source.declaration.is_some() {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok(None);
        }
        let [Callable::Named(index)] = source.value.callables.as_slice() else {
            return Ok(None);
        };
        let function = self
            .functions
            .get(*index)
            .ok_or(SourceTypesError::MissingNode)?;
        work.text(&function.syntax.name)?;
        work.charge(1 + function.lexical.len().checked_ilog2().unwrap_or(0) as usize)?;
        if function.lexical.get(&function.syntax.name) != Some(&binding) {
            if source.declaration.is_some() {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok(None);
        }
        let statement = source.declaration.ok_or(SourceTypesError::MissingNode)?;
        if function.hir_id != Some(statement) {
            return Err(SourceTypesError::Unresolved);
        }
        let original = self
            .semantic_hir
            .statement(statement)
            .ok_or(SourceTypesError::MissingNode)?;
        let crate::hir::nodes::StmtKind::Function(declaration) = &original.kind else {
            return Err(SourceTypesError::Unresolved);
        };
        work.text(&declaration.name)?;
        work.text(&source.name)?;
        if declaration.name != function.syntax.name
            || source.name != declaration.name
            || source.owner != function.owner.unwrap_or(ScopeId(0))
            || source.lexical_scope != function.lexical_scope
            || source.context.owner != function.lexical_owner
        {
            return Err(SourceTypesError::Unresolved);
        }
        if !self.named_declaration_owner_matches(
            original.info.owner,
            function.lexical_owner,
            work,
        )? {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(declaration.parameters.len() + function.syntax.parameters.len())?;
        if declaration.parameters.len() != function.syntax.parameters.len()
            || declaration
                .parameters
                .iter()
                .zip(&function.syntax.parameters)
                .any(|(original, syntax)| {
                    Some(original.pattern) != syntax.pattern.hir_id
                        || original.ty != syntax.ty.as_ref().and_then(|ty| ty.hir_id)
                        || original.default
                            != syntax.default.as_ref().and_then(|value| value.hir_id)
                        || original.mode != syntax.mode
                })
            || declaration.return_type
                != function
                    .syntax
                    .return_type
                    .as_ref()
                    .and_then(|ty| ty.hir_id)
        {
            return Err(SourceTypesError::Unresolved);
        }
        match (&declaration.body, &function.syntax.body) {
            (Some(original), Some(syntax)) => {
                work.charge(
                    original.statements.len()
                        + original.where_items.len()
                        + syntax.statements.len()
                        + syntax.where_items.len(),
                )?;
                if original.statements.len() != syntax.statements.len()
                    || original.where_items.len() != syntax.where_items.len()
                    || original
                        .statements
                        .iter()
                        .zip(&syntax.statements)
                        .any(|(id, statement)| Some(*id) != statement.hir_id)
                    || original
                        .where_items
                        .iter()
                        .zip(&syntax.where_items)
                        .any(|(id, statement)| Some(*id) != statement.hir_id)
                {
                    return Err(SourceTypesError::Unresolved);
                }
            }
            (None, None) => {}
            _ => return Err(SourceTypesError::Unresolved),
        }
        Ok(Some(*index))
    }
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
            table: &mut BTreeMap<(ScopeId, u32, String), Option<ril_compiler_core::ids::PatternId>>,
        ) {
            match &pattern.kind {
                PatternKind::Name(name) | PatternKind::Rest(Some(name)) if name != "_" => {
                    table
                        .entry((owner, scope, name.clone()))
                        .or_insert(pattern.hir_id);
                }
                PatternKind::Tuple(items)
                | PatternKind::Array(items)
                | PatternKind::Alternative(items)
                | PatternKind::Constructor {
                    arguments: items, ..
                } => {
                    for item in items {
                        register(item, owner, scope, table);
                    }
                }
                PatternKind::Record {
                    fields,
                    rest_binding,
                    ..
                } => {
                    for field in fields {
                        register(&field.pattern, owner, scope, table);
                    }
                    if let Some(name) = rest_binding.as_ref().filter(|name| name.as_str() != "_") {
                        table
                            .entry((owner, scope, name.clone()))
                            .or_insert(pattern.hir_id);
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
        let mut names = BTreeSet::new();
        expressions::collect_block_names(body, &mut names);
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
            {
                if expected.is_none() {
                    self.unsupported(
                        info.syntax.span,
                        "captured lexical declaration lacks its original HIR pattern identity",
                    );
                } else if info
                    .lexical
                    .get(&name)
                    .is_none_or(|binding| self.bindings[*binding].pattern != expected)
                {
                    self.error(
                        "E0207",
                        info.syntax.span,
                        format!("captured lexical binding {name} has not been initialized"),
                        [],
                    );
                }
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
                function.typing_environment = self
                    .type_source
                    .derive_environment(&function.typing_environment, &function.lexical);
            }
        }
    }
    fn named_free_bindings(
        &self,
        id: usize,
        seen: &mut BTreeSet<usize>,
        captures: &mut BTreeSet<BindingId>,
        writes: &mut BTreeSet<BindingId>,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<(), crate::sema::source_types::SourceTypesError> {
        use crate::sema::source_types::SourceTypesError;
        work.charge(2 + seen.len().checked_ilog2().unwrap_or(0) as usize)?;
        if !seen.insert(id) {
            return Ok(());
        }
        let function = &self.functions[id];
        let Some(body) = &function.syntax.body else {
            return Ok(());
        };
        let mut syntax_work = work.remaining();
        let before = syntax_work;
        let admitted =
            crate::static_eval::charge_function_syntax_clone(&function.syntax, &mut syntax_work)
                .and_then(|()| {
                    crate::static_eval::charge_function_syntax_clone(
                        &function.syntax,
                        &mut syntax_work,
                    )
                });
        work.charge(before - syntax_work)?;
        admitted.ok_or(SourceTypesError::BudgetExceeded)?;
        let mut names = BTreeSet::new();
        expressions::collect_block_names(body, &mut names);
        for parameter in &function.syntax.parameters {
            for name in pattern_names(&parameter.pattern) {
                names.remove(&name);
            }
        }
        let mutated = expressions::mutated_block_names(body);
        for name in names {
            let Some(&binding) = function.lexical.get(&name) else {
                continue;
            };
            let source = &self.bindings[binding];
            // Calling another declaration retains its actual source environment,
            // rather than a scalar alias to a declaration being a data capture.
            let declaration = self.original_named_declaration(binding, work)?;
            if let Some(other) = declaration {
                if self.functions[other].owner.is_some() {
                    self.named_free_bindings(other, seen, captures, writes, work)?;
                }
            } else if source.owner != ScopeId(0) && !self.static_value_bindings.contains(&binding) {
                captures.insert(binding);
                if mutated.contains(&name) {
                    writes.insert(binding);
                }
            }
        }
        Ok(())
    }
    pub(super) fn ensure_named_environment(&mut self, id: usize) {
        if self.functions[id].owner.is_none() {
            return;
        }
        self.check_named_initialization(id);
        let mut captures = BTreeSet::new();
        let mut writes = BTreeSet::new();
        let mut lease = self.application_effect.lease_work(4_000_000);
        let result = self.named_free_bindings(
            id,
            &mut BTreeSet::new(),
            &mut captures,
            &mut writes,
            lease.work(),
        );
        let result = result.and(self.application_effect.return_work(lease));
        if let Err(error) = result {
            self.unsupported(
                self.functions[id].syntax.span,
                format!("named environment declaration identity: {error}"),
            );
            return;
        }
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
        PatternKind::Name(name) | PatternKind::Rest(Some(name)) if name != "_" => {
            vec![name.clone()]
        }
        PatternKind::Tuple(items)
        | PatternKind::Array(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => items.iter().flat_map(pattern_names).collect(),
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => fields
            .iter()
            .flat_map(|field| pattern_names(&field.pattern))
            .chain(
                rest_binding
                    .iter()
                    .filter(|name| name.as_str() != "_")
                    .cloned(),
            )
            .collect(),
        PatternKind::Mode { pattern, .. } => pattern_names(pattern),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod declaration_identity_tests {
    use super::*;

    #[test]
    fn original_named_bindings_require_their_statement_and_actual_creation_scope() {
        // This test enters Checker directly rather than analyze_constants.
        // Match the production analysis worker's existing finite stack.
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("ril-declaration-identities".into())
                .stack_size(16 * 1024 * 1024)
                .spawn_scoped(scope, check_original_named_binding_identities)
                .unwrap()
                .join()
                .unwrap();
        });
    }

    fn check_original_named_binding_identities() {
        use crate::sema::source_types::{SourceTypesError, WorkLimit};
        let source = ril_test::case_source(
            "tests/regressions/evaluation-identity.ril::named-declaration-binding-identities",
        );
        let parsed = ril_syntax::parse(source);
        assert!(parsed.diagnostics.is_empty());
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        assert!(
            checker
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.severity != Severity::Error),
            "{:?}",
            checker.diagnostics
        );
        let declarations: Vec<_> = checker
            .functions
            .iter()
            .enumerate()
            .filter_map(|(index, function)| {
                if function.syntax.name != "read" {
                    return None;
                }
                let binding = *function.lexical.get("read")?;
                Some((
                    index,
                    binding,
                    function.hir_id.unwrap(),
                    function.owner.unwrap(),
                ))
            })
            .collect();
        assert!(
            declarations.len() >= 3,
            "the real factories must instantiate local declarations"
        );
        for &(index, binding, _, _) in &declarations {
            assert_eq!(
                checker.original_named_declaration(binding, &mut WorkLimit::new(65536)),
                Ok(Some(index))
            );
        }
        let (index, binding, statement, _) = declarations[0];
        let alias = checker
            .bindings
            .iter()
            .position(|binding| binding.name == "alias" && binding.pattern.is_some())
            .expect("real callable alias");
        let parameter = checker
            .bindings
            .iter()
            .position(|binding| binding.name == "read" && binding.parameter)
            .expect("real same-name callable parameter");
        for candidate in [alias, parameter] {
            let span = checker.bindings[candidate].span;
            checker.bindings[candidate].span = checker.functions[index].syntax.span;
            assert_eq!(
                checker.original_named_declaration(candidate, &mut WorkLimit::new(65536)),
                Ok(None)
            );
            checker.bindings[candidate].span = span;
        }
        let span = checker.bindings[binding].span;
        checker.bindings[binding].span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        assert_eq!(
            checker.original_named_declaration(binding, &mut WorkLimit::new(65536)),
            Ok(Some(index))
        );
        checker.bindings[binding].span = span;
        checker.bindings[binding].declaration = None;
        assert_eq!(
            checker.original_named_declaration(binding, &mut WorkLimit::new(65536)),
            Err(SourceTypesError::MissingNode)
        );
        checker.bindings[binding].declaration = Some(statement);
        let other_statement = declarations
            .iter()
            .find(|(_, _, other, _)| *other != statement)
            .expect("same-name declaration with a different canonical statement")
            .2;
        checker.functions[index].hir_id = Some(other_statement);
        assert!(
            checker
                .original_named_declaration(binding, &mut WorkLimit::new(65536))
                .is_err()
        );
        checker.functions[index].hir_id = Some(statement);
        let (_, other_binding, _, _) = declarations
            .iter()
            .find(|(_, _, other, owner)| *other == statement && *owner != declarations[0].3)
            .copied()
            .expect("the same declaration in another actual factory activation");
        checker.functions[index]
            .lexical
            .insert("read".into(), other_binding);
        assert!(
            checker
                .original_named_declaration(binding, &mut WorkLimit::new(65536))
                .is_err()
        );
        checker.functions[index]
            .lexical
            .insert("read".into(), binding);
        assert_eq!(
            checker.original_named_declaration(binding, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
    }

    #[test]
    fn captured_initialization_uses_pattern_identity_instead_of_diagnostic_spans() {
        let parsed = ril_syntax::parse(
            "fn example(){let other=8;let value=7;assert(read()==7) where fn read()->int &{closure,value}{value}}",
        );
        assert!(parsed.diagnostics.is_empty());
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        let function = checker
            .functions
            .iter()
            .position(|function| {
                function.syntax.name == "read" && function.lexical.contains_key("value")
            })
            .unwrap();
        let binding = checker.functions[function].lexical["value"];
        let other = checker.functions[function].lexical["other"];
        let original_span = checker.bindings[binding].span;
        let original_pattern = checker.bindings[binding]
            .pattern
            .expect("original binding pattern");
        assert_ne!(Some(original_pattern), checker.bindings[other].pattern);
        checker.diagnostics.clear();
        checker.bindings[binding].span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        checker.check_named_initialization(function);
        assert!(
            checker
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != "E0207"),
            "{:?}",
            checker.diagnostics
        );
        checker.bindings[binding].span = original_span;
        checker.bindings[binding].pattern = checker.bindings[other].pattern;
        checker.check_named_initialization(function);
        assert!(
            checker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0207")
        );
    }
}
