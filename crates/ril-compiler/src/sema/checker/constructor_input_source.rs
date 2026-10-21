//! Constructor payload reception precedes every source ascription. The same
//! supplied operand receipts used by named calls retain the physical roots.
use super::*;

impl Checker {
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
            let answer = target.key().as_ref().and_then(|expected| {
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
                match &input.key {
                    Some(actual) => target.receive(actual, Some(&input.fresh), &mut 4096),
                    None => input_compatible(expected, input),
                }
            });
            match answer {
                Some(true) => {}
                Some(false) => {
                    self.error("E0301", *span,
                        "original constructor payload source does not fit its declared dimensions or callable modes", [value.cause]);
                    valid = false;
                }
                None => {
                    self.unsupported(*span, "constructor payload lacks its complete original source and actual operand receipt");
                    valid = false;
                }
            }
        }
        valid
    }
}
