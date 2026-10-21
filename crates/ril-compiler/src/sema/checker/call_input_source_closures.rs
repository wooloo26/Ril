//! Source views for immutable local bindings and completed lambda bodies.
//! These type coordinates do not grant publication, loans or callable rows.
use super::*;

impl Checker {
    pub(in crate::sema::checker) fn record_typed_local_source(
        &mut self,
        binding: &Binding,
        target: Option<&source_reception::Target>,
        start: usize,
        frame: &Frame,
    ) {
        if binding.ty.is_none() || binding.mode != BindingMode::Let {
            return;
        }
        let mut paths = Vec::new();
        let source_key = target.and_then(|target| target.key());
        pattern_sources(&binding.pattern, source_key.as_ref(), &mut paths, &mut 4096);
        for id in start..self.bindings.len() {
            let actual = &self.bindings[id];
            if actual.parameter
                || actual.owner != frame.owner
                || actual.mode != BindingMode::Let
                || actual.value.permission != Permission::Read
                || actual.value.publication != Publication::Immutable
            {
                continue;
            }
            let key = paths
                .iter()
                .find(|(span, name, _)| *span == actual.span && *name == actual.name)
                .and_then(|(_, _, key)| key.clone());
            // A known declaration with an unavailable key stays unavailable.
            self.call_input_source.local_views.insert(id, key);
        }
    }

    pub(super) fn formal_source_type_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let (syntax, environment) = self.formal_source_declaration(value, syntax, frame)?;
        self.with_typing_environment(&environment, |checker| {
            let key = checker.record_bound_key(&syntax, &checker.record_bound_scope())?;
            checker.selected_bound_key(&key)
        })
    }

    /// Projection selects the declared member before applying an instance.
    /// Selecting an entire open aggregate would require a closed witness for
    /// siblings that do not participate in the actual projection.
    pub(super) fn raw_formal_source_type_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let (syntax, environment) = self.formal_source_declaration(value, syntax, frame)?;
        self.with_typing_environment(&environment, |checker| {
            checker.record_bound_key(&syntax, &checker.record_bound_scope())
        })
    }

    pub(super) fn formal_source_receiving_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let (syntax, environment) = self.formal_source_declaration(value, syntax, frame)?;
        self.with_typing_environment(&environment, |checker| {
            checker.freeze_source_receiving_target(&syntax).key()
        })
    }

    fn formal_source_declaration(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<(TypeExpr, crate::sema::context::FrozenEnvironment)> {
        let ExprKind::Name(name) = &syntax.kind else {
            return None;
        };
        let id = *frame.env.get(name)?;
        if value.sources != BTreeSet::from([id]) {
            return None;
        }
        self.formal_binding_declaration(id, name)
    }

    fn formal_binding_declaration(
        &self,
        id: BindingId,
        name: &str,
    ) -> Option<(TypeExpr, crate::sema::context::FrozenEnvironment)> {
        let binding = self.bindings.get(id)?;
        if !binding.parameter || binding.name != name {
            return None;
        }
        let pattern = binding.pattern?;
        let parameters = match binding.context.owner? {
            CallableOwner::Function(definition) => {
                &self
                    .functions
                    .iter()
                    .find(|info| info.definition == definition)?
                    .syntax
                    .parameters
            }
            CallableOwner::Lambda(site) => {
                let invocation = self
                    .closure_invocations
                    .get(binding.context.closure_invocation?.0 as usize)?;
                let closure = self.closures.get(invocation.closure)?;
                if invocation.activation != Some(binding.owner) || closure.site != Some(site) {
                    return None;
                }
                &closure.parameters
            }
            CallableOwner::Global => return None,
        };
        let parameter = parameters.iter().find(|parameter| {
            parameter.pattern.hir_id == Some(pattern)
                && matches!(&parameter.pattern.kind,PatternKind::Name(actual) if actual==name)
        })?;
        let syntax = parameter.ty.as_ref()?;
        // Bound the original header before retaining an owned syntax copy.
        // Its names are interpreted only after entering the captured environment.
        crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())?;
        Some((syntax.clone(), binding.typing_environment.clone()))
    }

    pub(in crate::sema::checker) fn declared_formal_source(
        &mut self,
        id: BindingId,
        name: &str,
    ) -> Option<ArgumentKey> {
        let (syntax, environment) = self.formal_binding_declaration(id, name)?;
        self.with_typing_environment(&environment, |checker| {
            checker.freeze_source_receiving_target(&syntax).key()
        })
    }

    pub(in crate::sema::checker) fn remember_closure_source(
        &mut self,
        index: usize,
        result: &Value,
        frame: &Frame,
    ) {
        let Some(id) = self.closure_invocation_stack.last().copied() else {
            return;
        };
        let invocation = &self.closure_invocations[id.0 as usize];
        let closure = self.closures[index].clone();
        if !invocation.probe
            || invocation.closure != index
            || invocation.activation != Some(frame.owner)
            || invocation.parent_named != closure.creation_invocation
            || invocation.parent_closure != closure.creation_closure
            || !frame.return_source_valid
            || closure
                .parameters
                .iter()
                .any(|parameter| parameter.ty.is_none())
        {
            return;
        }
        let context = self.invocation_context(frame.callable_owner);
        if self
            .application_effect
            .contexts
            .iter()
            .filter(|row| {
                row.context == context
                    && self
                        .application_effect
                        .expressions
                        .get(row.expression)
                        .is_some_and(|fact| {
                            fact.source_id.is_some()
                                && fact.source_id == closure.body.hir_id
                                && fact.value.cause == result.cause
                                && fact.value.ty == result.ty
                        })
            })
            .count()
            != 1
        {
            return;
        }
        let Some(result) = self.raw_original_source_receiving_key(result, &closure.body, frame)
        else {
            return;
        };
        let mut parameters = Vec::new();
        for parameter in &closure.parameters {
            let Some(syntax) = parameter.ty.as_ref() else {
                return;
            };
            let Some(key) = self.freeze_source_receiving_target(syntax).key() else {
                return;
            };
            parameters.push((parameter.mode, key));
        }
        let Some(contract) = self.lambda_contract(index) else {
            return;
        };
        let key = ArgumentKey::Callable {
            parameters,
            result: Box::new(result),
            annotations: contract
                .annotations
                .iter()
                .map(|annotation| annotation.text.replace(' ', ""))
                .collect(),
        };
        if source_reception::complete(&key, &mut 4096).is_some() {
            self.call_input_source
                .closure_views
                .insert(index, (id.0, key));
        }
    }

    pub(super) fn original_closure_source_key(&self, value: &Value) -> Option<ArgumentKey> {
        let [Callable::Closure(index)] = value.callables.as_slice() else {
            return None;
        };
        let (id, key) = self.call_input_source.closure_views.get(index)?;
        let invocation = self.closure_invocations.get(*id as usize)?;
        let closure = self.closures.get(*index)?;
        (invocation.id.0 == *id
            && invocation.closure == *index
            && invocation.probe
            && invocation.status == crate::sema::copy_contract::CopyInvocationStatus::Completed
            && invocation.parent_named == closure.creation_invocation
            && invocation.parent_closure == closure.creation_closure)
            .then_some(())?;
        self.closure_public_view_agrees(value, key)?
            .then(|| key.clone())
    }

    fn closure_public_view_agrees(&self, value: &Value, key: &ArgumentKey) -> Option<bool> {
        let ArgumentKey::Callable { annotations, .. } = key else {
            return None;
        };
        if value.callable_bounds.iter().any(|bound| {
            bound
                .annotations
                .iter()
                .map(|annotation| annotation.text.replace(' ', ""))
                .collect::<Vec<_>>()
                != *annotations
        }) {
            return Some(false);
        }
        for bound in value.callable_returns.iter().filter(|bound| !bound.raw) {
            let mut parameters = value.signature.clone()?;
            for parameter in &mut parameters {
                parameter.default = None;
            }
            let syntax = TypeExpr {
                hir_id: None,
                text: String::new(),
                span: bound.span,
                kind: TypeKind::Callable {
                    parameters,
                    result: Some(Box::new(bound.syntax.clone())),
                    annotations: vec![],
                },
            };
            let mut original = crate::static_eval::effects::bounded_argument_key(
                &syntax,
                &bound.typing_environment.generic_context,
            )?;
            let ArgumentKey::Callable {
                annotations: actual,
                ..
            } = &mut original
            else {
                unreachable!()
            };
            *actual = annotations.clone();
            let mut selected = BTreeMap::new();
            for (identity, witness) in &bound.typing_environment.generic_type_witnesses {
                if !witness.validate_closed() {
                    return None;
                }
                selected.insert(
                    identity.clone(),
                    crate::static_eval::effects::bounded_argument_key(
                        &witness.syntax,
                        &BTreeMap::new(),
                    )?,
                );
            }
            for (identity, ty) in &bound.typing_environment.generic_substitutions {
                if selected.contains_key(identity) {
                    continue;
                }
                let key = match ty {
                    Ty::Generic(identity) => {
                        let binder = self.generic_binders.get(identity)?;
                        let function = self
                            .functions
                            .iter()
                            .find(|function| function.definition == binder.definition)?;
                        if !crate::sema::record_bounds::certifies_type_sort(
                            identity,
                            binder,
                            function.syntax.generics.get(binder.index as usize)?,
                            &self.record_bounds,
                        ) {
                            return None;
                        }
                        ArgumentKey::Binder {
                            identity: identity.clone(),
                            sort: crate::sema::effect_identity::StaticBinderSort::Type,
                        }
                    }
                    Ty::Unit | Ty::Bool | Ty::Str | Ty::Bytes | Ty::Int(_) | Ty::Float(_) => {
                        let syntax = io_types::data_type(ty, bound.span)?;
                        crate::static_eval::effects::bounded_argument_key(
                            &syntax,
                            &BTreeMap::new(),
                        )?
                    }
                    _ => return None,
                };
                selected.insert(identity.clone(), key);
            }
            if super::select(&original, &selected, &mut 4096, 0)? != *key {
                return Some(false);
            }
        }
        Some(true)
    }
}

fn pattern_sources(
    pattern: &Pattern,
    key: Option<&ArgumentKey>,
    out: &mut Vec<(Span, String, Option<ArgumentKey>)>,
    work: &mut usize,
) {
    let Some(next) = work.checked_sub(1) else {
        return;
    };
    *work = next;
    match &pattern.kind {
        PatternKind::Name(name) => out.push((pattern.span, name.clone(), key.cloned())),
        PatternKind::Mode { pattern, .. } => pattern_sources(pattern, key, out, work),
        PatternKind::Tuple(items) => {
            for (index, pattern) in items.iter().enumerate() {
                let child = key.and_then(|key| match key {
                    ArgumentKey::Tuple(items) => items.get(index),
                    _ => None,
                });
                pattern_sources(pattern, child, out, work);
            }
        }
        PatternKind::Record { fields, .. } => {
            for field in fields {
                let child = key.and_then(|key| match key {
                    ArgumentKey::Record { fields, .. } => fields
                        .iter()
                        .find(|(name, ..)| name == &field.name)
                        .map(|(_, _, key)| key),
                    _ => None,
                });
                pattern_sources(&field.pattern, child, out, work);
            }
        }
        _ => {}
    }
}
