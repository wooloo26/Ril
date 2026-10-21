//! Result Type selection keeps the original declaration's source coordinates.
use super::*;
use crate::hir::application::AstApplication;
use crate::sema::{effect_identity::StaticBinderSort, record_bounds::BoundScope};
impl Checker {
    /// Resolve only the actual producing result's flexible leaves before the
    /// immutable observation is recorded. This grants no array shape or mode.
    pub(in crate::sema::checker) fn prepare_producing_result_context(
        &mut self,
        syntax: &Expr,
        value: &mut Value,
        expected: Option<&Ty>,
        source: Option<&source_reception::Target>,
        frame: &Frame,
    ) {
        let Some(expected) = expected else { return };
        self.prepare_original_carrier_context(syntax, value, expected, source, frame);
        if AstApplication::from_ast(syntax).is_none()
            || self.pending_result_binders(value).is_empty()
        {
            return;
        }
        let context = self.invocation_context(frame.callable_owner);
        let calls: Vec<_> = self
            .copy_invocations
            .iter()
            .filter(|call| {
                call.source_event
                    .and_then(|id| self.copy_call_events.get(id.0 as usize))
                    .is_some_and(|event| event.matches_source(syntax))
                    && call.parent == context.invocation
                    && call.caller_owner == context.owner
                    && call.source_event.is_some()
                    && call.result.as_ref().is_some_and(|result| {
                        result.value.cause == value.cause
                            && result.value.ty == value.ty
                            && result.value.pending_inference == value.pending_inference
                    })
            })
            .collect();
        if calls.len() == 1 {
            self.contextual_result_inference(value, expected, syntax.span);
            if let Some(key) = self.original_called_result_source(value, syntax, frame)
                && key.is_closed()
                && let Some(syntax) = closed_result_syntax(&key, syntax.span, &mut 4096)
            {
                // This is the callee's actual declared structure with its
                // producing leaves selected, never a receiving shell cast.
                value.source_type_witness = self.source_type_from_frozen_syntax(&syntax);
            }
        }
    }

    fn prepare_original_carrier_context(
        &mut self,
        syntax: &Expr,
        value: &mut Value,
        expected: &Ty,
        source: Option<&source_reception::Target>,
        frame: &Frame,
    ) {
        let Some(application) = AstApplication::from_ast(syntax) else {
            return;
        };
        let (callee, arguments) = (application.callee, &application.operands);
        let Some(&(event, context)) = self.call_input_source.carriers.get(&value.cause.0) else {
            return;
        };
        if context != self.invocation_context(frame.callable_owner) || arguments.len() != 1 {
            return;
        }
        let Some(event) = self.copy_call_events.get(event.0 as usize) else {
            return;
        };
        let Some(token) = event.callee_expression else {
            return;
        };
        let Some(callee_fact) = self.application_effect.expressions.get(token) else {
            return;
        };
        if !event.matches_source(syntax)
            || callee_fact.source_id.is_none()
            || callee_fact.source_id != callee.hir_id
            || !callee_fact.value.sources.is_empty()
        {
            return;
        }
        let [Callable::Builtin(name)] = callee_fact.value.callables.as_slice() else {
            return;
        };
        let Some(success) = value.result_tag else {
            return;
        };
        if name.strip_prefix("Prelude::").unwrap_or(name) != if success { "Ok" } else { "Err" } {
            return;
        }
        let (Ty::Result(ok, error), Ty::Result(expected_ok, expected_error)) =
            (&value.ty, expected)
        else {
            return;
        };
        let (active, inactive, expected_inactive) = if success {
            (ok, error, expected_error)
        } else {
            (error, ok, expected_ok)
        };
        if **inactive != Ty::Unknown {
            return;
        }
        let payload = if success {
            value.result_success.as_deref()
        } else {
            value.result_error.as_deref()
        };
        let Some(payload) = payload else { return };
        let active_key = payload
            .source_type_witness
            .as_ref()
            .filter(|witness| witness.validate_closed())
            .and_then(|witness| {
                crate::static_eval::effects::bounded_argument_key(&witness.syntax, &BTreeMap::new())
            })
            .or_else(|| {
                // An open row remains the real operand's Source. Only the
                // absent branch receives a context; no active type is copied
                // from the expected Result declaration.
                let input = self.call_input_source.supplied.get(&event.id)?.get(&0)?;
                let token = input.expression?;
                let actual = self.application_effect.expressions.get(token)?;
                (input.context == context
                    && actual.source_id.is_some()
                    && actual.source_id == arguments[0].expression.hir_id
                    && actual.value.cause == payload.cause
                    && self
                        .application_effect
                        .contexts
                        .get(token)
                        .is_some_and(|row| {
                            row.expression == token
                                && row.context == context
                                && row.argument_of == Some((event.id, 0))
                        }))
                .then(|| input.key.clone())
                .flatten()
            });
        let Some(active_key) = active_key else { return };
        let inactive_key = source
            .and_then(|source| source.key())
            .and_then(|key| match key {
                ArgumentKey::Name { name, arguments }
                    if name == "Result" && arguments.len() == 2 =>
                {
                    Some(arguments[usize::from(success)].clone())
                }
                _ => None,
            })
            .or_else(|| match expected_inactive.as_ref() {
                Ty::Unit | Ty::Bool | Ty::Str | Ty::Bytes | Ty::Int(_) | Ty::Float(_) => {
                    io_types::data_type(expected_inactive, syntax.span).and_then(|syntax| {
                        crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())
                    })
                }
                _ => None,
            });
        let Some(inactive_key) = inactive_key else {
            return;
        };
        let keys = if success {
            vec![active_key, inactive_key]
        } else {
            vec![inactive_key, active_key]
        };
        let key = ArgumentKey::Name {
            name: "Result".into(),
            arguments: keys,
        };
        if source_reception::complete(&key, &mut 4096).is_none() {
            return;
        }
        value.ty = if success {
            Ty::Result(active.clone(), expected_inactive.clone())
        } else {
            Ty::Result(expected_inactive.clone(), active.clone())
        };
        self.call_input_source
            .carrier_sources
            .insert(value.cause.0, key.clone());
        value.source_type_witness = closed_result_syntax(&key, syntax.span, &mut 4096)
            .and_then(|original| self.source_type_from_frozen_syntax(&original));
    }

    pub(super) fn original_carrier_source_key(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let application = AstApplication::from_ast(syntax)?;
        if application.operands.len() != 1 {
            return None;
        }
        let (event, context) = self.call_input_source.carriers.get(&value.cause.0)?;
        if *context != self.invocation_context(frame.callable_owner) {
            return None;
        }
        let event = self.copy_call_events.get(event.0 as usize)?;
        let root = event.result_expression?;
        if !event.matches_source(syntax)
            || !self
                .application_effect
                .expressions
                .get(root)
                .is_some_and(|fact| {
                    fact.source_id.is_some()
                        && fact.source_id == syntax.hir_id
                        && fact.value.cause == value.cause
                })
            || !self
                .application_effect
                .contexts
                .get(root)
                .is_some_and(|row| row.expression == root && row.context == *context)
        {
            return None;
        }
        self.call_input_source
            .carrier_sources
            .get(&value.cause.0)
            .cloned()
    }

    fn producing_source_selection(
        &self,
        call: &crate::sema::copy_contract::CopyInvocation,
        binder: &str,
        key: ArgumentKey,
        value: &Value,
    ) -> Option<ArgumentKey> {
        if !matches!(&key, ArgumentKey::Binder { identity, .. } if identity == binder) {
            return Some(key);
        }
        let result = &call.result.as_ref()?.value;
        let summaries: Vec<_> = self
            .invocations
            .iter()
            .filter(|summary| {
                summary.context.is_some_and(|context| {
                    context.invocation == Some(call.id)
                        && context.owner == Some(CallableOwner::Function(call.target))
                })
            })
            .collect();
        let [summary] = summaries.as_slice() else {
            return Some(key);
        };
        let meta = format!("{binder}:invocation:{}", summary.activation?.0);
        let before = result_causes(self, result.cause)?;
        if self
            .inference_resolutions
            .iter()
            .filter(|row| {
                row.binder == binder
                    && row.selected == Ty::Generic(meta.clone())
                    && before.contains(&row.cause.0)
            })
            .count()
            != 1
        {
            return Some(key);
        }
        let after = result_causes(self, value.cause)?;
        let selections: Vec<_> = self
            .inference_resolutions
            .iter()
            .filter(|row| {
                row.binder == meta && after.contains(&row.cause.0) && after.contains(&row.origin.0)
            })
            .collect();
        let [selection] = selections.as_slice() else {
            return Some(key);
        };
        match &selection.selected {
            Ty::Generic(identity) => {
                let actual = self.generic_binders.get(identity)?;
                let function = self
                    .functions
                    .iter()
                    .find(|info| info.definition == actual.definition)?;
                crate::sema::record_bounds::certifies_type_sort(
                    identity,
                    actual,
                    function.syntax.generics.get(actual.index as usize)?,
                    &self.record_bounds,
                )
                .then(|| ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                })
            }
            ty @ (Ty::Unit | Ty::Bool | Ty::Str | Ty::Bytes | Ty::Int(_) | Ty::Float(_)) => {
                let syntax = io_types::data_type(ty, selection.site)?;
                crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())
            }
            _ => None,
        }
    }

    pub(super) fn original_called_result_source(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let application = AstApplication::from_ast(syntax)?;
        let callee = application.callee;
        let context = self.invocation_context(frame.callable_owner);
        let causes = result_causes(self, value.cause)?;
        let calls: Vec<_> = self
            .copy_invocations
            .iter()
            .filter(|call| {
                call.source_event
                    .and_then(|id| self.copy_call_events.get(id.0 as usize))
                    .is_some_and(|event| event.matches_source(syntax))
                    && call.parent == context.invocation
                    && call.caller_owner == context.owner
                    && call
                        .result
                        .as_ref()
                        .is_some_and(|result| causes.contains(&result.value.cause.0))
            })
            .collect();
        let [call] = calls.as_slice() else {
            return None;
        };
        let event = self.copy_call_events.get(call.source_event?.0 as usize)?;
        let expression = self
            .application_effect
            .expressions
            .get(event.callee_expression?)?;
        if Some(event.id) != call.source_event
            || event.target != Some(call.target)
            || !event.matches_source(syntax)
            || expression.source_id.is_none()
            || expression.source_id != callee.hir_id
            || event.parent != context.invocation
            || event.owner != context.owner
        {
            return None;
        }
        if self
            .application_effect
            .contexts
            .iter()
            .filter(|row| {
                row.expression == event.callee_expression.unwrap() && row.context == context
            })
            .count()
            != 1
        {
            return None;
        }
        let [Callable::Named(index)] = expression.value.callables.as_slice() else {
            return None;
        };
        if self.functions.get(*index)?.definition != call.target
            || expression.value.sources.len() != 1
        {
            return None;
        }
        let binding = self.bindings.get(*expression.value.sources.first()?)?;
        if binding.parameter
            || binding.span != self.functions[*index].syntax.span
            || binding.name != self.functions[*index].syntax.name
        {
            return None;
        }
        let target = self
            .functions
            .iter()
            .find(|function| function.definition == call.target)?;
        let mut scope = BoundScope {
            types: target.typing_environment.generic_context.clone(),
            rows: target.typing_environment.bound_row_context.clone(),
        };
        for (index, parameter) in target.syntax.generics.iter().enumerate() {
            let binder = self.generic_binders.values().find(|binder| {
                binder.definition == target.definition
                    && binder.index as usize == index
                    && binder.name == parameter.name
            })?;
            scope
                .types
                .insert(parameter.name.clone(), binder.identity.clone());
        }
        for row in self
            .bound_rows
            .iter()
            .filter(|row| row.definition == target.definition)
        {
            if scope
                .rows
                .insert(row.name.clone(), row.id)
                .is_some_and(|old| old != row.id)
            {
                return None;
            }
        }
        let key = self.original_source_header_key(target.syntax.return_type.as_ref()?, &scope)?;
        let rows: Vec<_> = self
            .effect_invocations
            .iter()
            .filter(|row| row.invocation == Some(call.id) && row.function == call.target)
            .collect();
        let [row] = rows.as_slice() else {
            return None;
        };
        if row.site != call.span || row.arguments.len() != target.syntax.generics.len() {
            return None;
        }
        let mut selected = BTreeMap::new();
        for (index, argument) in row.arguments.iter().enumerate() {
            let parameter = &target.syntax.generics[index];
            if argument.definition != call.target
                || argument.index as usize != index
                || scope.types.get(&parameter.name) != Some(&argument.binder)
            {
                return None;
            }
            let binder = self.generic_binders.get(&argument.binder)?;
            if !crate::sema::record_bounds::certifies_type_sort(
                &argument.binder,
                binder,
                parameter,
                &self.record_bounds,
            ) {
                // Key/Const positions remain in the exact owned argument
                // table, but cannot supply Type leaves to this substitution.
                continue;
            }
            let key = match &argument.key {
                Some(key) => key.clone(),
                None => {
                    let bound = self.record_bounds.iter().find(|bound| {
                        bound.definition == call.target
                            && bound.binder == argument.binder
                            && bound.generic_index as usize == index
                    })?;
                    let expected_context = InvocationContext {
                        owner: Some(CallableOwner::Function(call.target)),
                        invocation: Some(call.id),
                        ..context
                    };
                    let identities: Vec<_> = self
                        .scoped_source_identities
                        .iter()
                        .enumerate()
                        .filter(|(ordinal, source)| {
                            source.id.0 as usize == *ordinal
                                && source.required == bound.id
                                && source.binder == argument.binder
                                && source.context == expected_context
                                && !source.occurrences.is_empty()
                        })
                        .collect();
                    let [(_, source)] = identities.as_slice() else {
                        return None;
                    };
                    crate::sema::source_reception::complete(&source.key, &mut 4096)?;
                    source.key.clone()
                }
            };
            selected.insert(
                argument.binder.clone(),
                self.producing_source_selection(call, &argument.binder, key, value)?,
            );
        }
        for argument in &row.captured_arguments {
            let binder = self.generic_binders.get(&argument.binder)?;
            if selected.contains_key(&argument.binder)
                || binder.definition != argument.definition
                || binder.index != argument.index
                || !target
                    .typing_environment
                    .generic_context
                    .values()
                    .any(|identity| identity == &argument.binder)
            {
                return None;
            }
            let declaration = self
                .functions
                .iter()
                .find(|function| function.definition == binder.definition)?;
            if !crate::sema::record_bounds::certifies_type_sort(
                &argument.binder,
                binder,
                declaration.syntax.generics.get(binder.index as usize)?,
                &self.record_bounds,
            ) {
                continue;
            }
            selected.insert(argument.binder.clone(), argument.key.clone()?);
        }
        super::select(&key, &selected, &mut 4096, 0)
    }
}

fn result_causes(checker: &Checker, root: CauseId) -> Option<BTreeSet<u32>> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut work = 4096usize;
    while let Some(id) = pending.pop() {
        work = work.checked_sub(1)?;
        if seen.insert(id.0) {
            pending.extend(
                checker
                    .explanations
                    .causes
                    .get(id.0 as usize)?
                    .parents
                    .iter()
                    .copied(),
            );
        }
    }
    Some(seen)
}

pub(in crate::sema::checker) fn storage_closed_source_syntax(
    key: &ArgumentKey,
    span: Span,
) -> Option<TypeExpr> {
    closed_result_syntax(key, span, &mut 4096)
}

fn closed_result_syntax(key: &ArgumentKey, span: Span, work: &mut usize) -> Option<TypeExpr> {
    *work = work.checked_sub(1)?;
    let mut child = |key| closed_result_syntax(key, span, work);
    let kind = match key {
        ArgumentKey::Name { name, arguments } => TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments: arguments.iter().map(&mut child).collect::<Option<_>>()?,
        },
        ArgumentKey::Array {
            length: None,
            element,
        } => TypeKind::Array {
            length: None,
            element: Box::new(child(element)?),
        },
        ArgumentKey::Tuple(items) => {
            TypeKind::Tuple(items.iter().map(&mut child).collect::<Option<_>>()?)
        }
        ArgumentKey::Map { key, value } => TypeKind::Map {
            key: Box::new(child(key)?),
            value: Box::new(child(value)?),
        },
        ArgumentKey::Record { fields, row: None } => TypeKind::Record {
            fields: fields
                .iter()
                .map(|(name, mutable, key)| {
                    Some(ril_syntax::ast::TypeField {
                        name: name.clone(),
                        mutable: *mutable,
                        ty: child(key)?,
                        span,
                    })
                })
                .collect::<Option<_>>()?,
            row: None,
        },
        // A full fixed/Fn leaf requires its retained source syntax. Do not
        // manufacture modes, bounds, dimensions or an arbitrary Closed key.
        _ => return None,
    };
    Some(TypeExpr {
        hir_id: None,
        text: String::new(),
        kind,
        span,
    })
}
