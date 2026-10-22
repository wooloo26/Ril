//! Constructor payload reception precedes every source ascription. The same
//! supplied operand receipts used by named calls retain the physical roots.
use super::*;

impl Checker {
    /// The actual constructor callee selects its already admitted declaration
    /// graph. Neither a receiving annotation nor an erased owner retypes it.
    pub(super) fn original_constructor_result_schema(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
    ) -> InputSource {
        let Some(application) = crate::hir::application::AstApplication::from_ast(syntax) else {
            return Ok(None);
        };
        let context = self.invocation_context(frame.callable_owner);
        work.charge(self.copy_call_events.len())?;
        let mut events = self.copy_call_events.iter().filter(|event| {
            event.matches_source(syntax)
                && event.owner == context.owner
                && event.parent == context.invocation
                && event.result_expression.is_some_and(|root| {
                    self.application_effect
                        .expressions
                        .get(root)
                        .is_some_and(|fact| {
                            fact.source_id == syntax.hir_id && fact.value.cause == value.cause
                        })
                })
        });
        let Some(event) = events.next() else {
            return Ok(None);
        };
        if events.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        let root = event
            .result_expression
            .ok_or(SourceTypesError::MissingNode)?;
        let callee = event
            .callee_expression
            .ok_or(SourceTypesError::MissingNode)?;
        let fact = self
            .application_effect
            .expressions
            .get(callee)
            .ok_or(SourceTypesError::MissingNode)?;
        if fact.source_id != application.callee.hir_id
            || fact.source_id.is_none()
            || !self
                .application_effect
                .contexts
                .get(callee)
                .is_some_and(|row| row.expression == callee && row.context == context)
            || !self
                .application_effect
                .contexts
                .get(root)
                .is_some_and(|row| row.expression == root && row.context == context)
        {
            return Err(SourceTypesError::Unresolved);
        }
        let [Callable::Constructor(name)] = fact.value.callables.as_slice() else {
            return Ok(None);
        };
        let constructor = self
            .constructors
            .get(name)
            .ok_or(SourceTypesError::MissingNode)?;
        if value.variant_tag.as_ref() != Some(&constructor.tag)
            || constructor.typing_environment.is_poisoned()
        {
            return Err(SourceTypesError::Unresolved);
        }
        let Some(view) = constructor.source else {
            return Ok(None);
        };
        if view.environment != constructor.typing_environment.id() {
            return Err(SourceTypesError::Unresolved);
        }
        let source = self.source_schema_view(view, work)?;
        Ok(Some(source))
    }

    pub(in crate::sema::checker) fn check_constructor_input_sources(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        event: Option<CopyCallEventId>,
        frame: &Frame,
    ) -> bool {
        let Some(constructor) = self.constructors.get(name).cloned() else {
            return false;
        };
        let Some(payload) = constructor.payload_syntax else {
            if args.is_empty() {
                return true;
            }
            self.unsupported(
                constructor.span,
                "constructor payload requires its genuine source declaration",
            );
            return false;
        };
        let syntax: Vec<_> = match (&payload.kind, args.len()) {
            (_, 1) => vec![payload],
            (TypeKind::Tuple(items), count) if count == items.len() => items.clone(),
            _ => return true, // the existing arity/type rule diagnoses this case
        };
        let mut valid = true;
        for (slot, (syntax, (_, value, span))) in syntax.iter().zip(args).enumerate() {
            let target = self.freeze_source_receiving_target(syntax);
            if target.sensitivity == source_reception::SchemaSensitivity::NotRequired {
                continue;
            }
            let input = (|| {
                let event_id = event?;
                let event = self.copy_call_events.get(event_id.0 as usize)?;
                let context = self.invocation_context(frame.callable_owner);
                if event.id != event_id
                    || event.owner != context.owner
                    || event.parent != context.invocation
                {
                    return None;
                }
                let callee = self
                    .application_effect
                    .expressions
                    .get(event.callee_expression?)?;
                if !callee.value.callables.iter().any(
                    |callable| matches!(callable, Callable::Constructor(actual) if actual == name),
                ) {
                    return None;
                }
                let preparations: Vec<_> = self
                    .call_arguments
                    .iter()
                    .filter(|row| row.source_event == event_id)
                    .collect();
                let [preparation] = preparations.as_slice() else {
                    return None;
                };
                if !preparation.slots_bound
                    || !preparation.evaluation_complete
                    || preparation.target.is_some()
                    || preparation.slots.len() != args.len()
                    || preparation.slots.get(slot)
                        != Some(&crate::sema::default_uses::ArgumentSource::Supplied)
                {
                    return None;
                }
                let input = self.call_input_source.supplied.get(&event_id)?.get(&slot)?;
                let token = preparation.supplied.get(&(slot as u32))?;
                if input.context != context
                    || input.default.is_some()
                    || input.expression != Some(token.expression)
                    || input.allocation_epoch != token.allocation_epoch
                    || token.allocation_epoch > self.recency_moves.len()
                    || !preparation.evaluated.iter().any(|evaluation| {
                        evaluation.role != EvaluationRole::Callee
                            && evaluation.observation == *token
                    })
                    || !preparation.evaluated.iter().any(|evaluation| {
                        evaluation.role == EvaluationRole::Callee
                            && Some(evaluation.observation.expression) == event.callee_expression
                    })
                {
                    return None;
                }
                let observation = self.application_effect.expressions.get(token.expression)?;
                let row = self.application_effect.contexts.get(token.expression)?;
                if row.expression != token.expression
                    || row.context != context
                    || row.argument_of != Some((event_id, slot as u32))
                {
                    return None;
                }
                let mut transported = observation.value.clone();
                self.transport_value_since(&mut transported, input.allocation_epoch);
                if transported != *value {
                    return None;
                }
                Some(input.clone())
            })();
            let answer = input
                .as_ref()
                .ok_or(SourceTypesError::MissingNode)
                .and_then(|input| {
                    input_compatible(
                        target.schema.as_ref().ok_or(SourceTypesError::Unresolved)?,
                        input,
                        &mut WorkLimit::new(16384),
                    )
                });
            match answer {
                Ok(true) => {}
                Ok(false) => {
                    self.error("E0301", *span,
                        "original constructor payload source does not fit its declared dimensions or callable modes", [value.cause]);
                    valid = false;
                }
                Err(error) => {
                    self.unsupported(*span, format!("constructor payload lacks its complete original source and actual operand receipt: {error}"));
                    valid = false;
                }
            }
        }
        valid
    }
}
