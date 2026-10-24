//! Store inputs belong to the actual intrinsic call and its supplied slots.
//! Neither collection contents nor a runtime length reconstructs an original
//! element schema. The original receiver input is read before any insertion
//! inference or storage transfer can change the current value.
use super::*;

#[derive(Clone, Copy)]
enum Part {
    Element,
    MapKey,
    MapValue,
}

impl Checker {
    pub(in crate::sema::checker) fn check_storage_intrinsic_inputs(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &Frame,
    ) -> bool {
        let (arity, parts): (_, &[(usize, Part)]) = match name {
            "Array::push" => (2, &[(1, Part::Element)]),
            "Array::insert" => (3, &[(2, Part::Element)]),
            "Map::set" => (3, &[(1, Part::MapKey), (2, Part::MapValue)]),
            "Set::insert" => (2, &[(1, Part::Element)]),
            _ => return true,
        };
        // The existing intrinsic diagnoses arity and cannot store anything on
        // that path. This additional check never replaces those diagnostics.
        if args.len() != arity {
            return true;
        }
        let diagnostics = self.diagnostics.len();
        let unsupported = self.unsupported.len();
        let answer = (|| {
            let mut work = WorkLimit::new(16384);
            let event = self
                .application_effect
                .current_call_event()
                .ok_or(SourceTypesError::MissingNode)?;
            let receiver = self
                .storage_supplied_input(event, 0, &args[0].1, span, frame, &mut work)?
                .ok_or(SourceTypesError::MissingNode)?;
            let (original, environment) = receiver
                .input_source(
                    SourceTypesRef::Live(self.type_source.storage.live_types()),
                    &mut work,
                )?
                .into_known()
                .ok_or(SourceTypesError::Unresolved)?;
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            for &(slot, part) in parts {
                let path = match part {
                    Part::Element => crate::sema::source_types::SourcePath::Element,
                    Part::MapKey => crate::sema::source_types::SourcePath::MapKey,
                    Part::MapValue => crate::sema::source_types::SourcePath::MapValue,
                };
                let expected = original.project_steps(&[path], &mut work)?;
                match expected.sensitivity(&mut work) {
                    crate::sema::source_types::SourceSensitivity::Absent { .. } => continue,
                    crate::sema::source_types::SourceSensitivity::Unknown { reason } => {
                        return Err(reason);
                    }
                    crate::sema::source_types::SourceSensitivity::Sensitive { .. } => {}
                }
                let input = self
                    .storage_supplied_input(event, slot, &args[slot].1, span, frame, &mut work)?
                    .ok_or(SourceTypesError::MissingNode)?;
                if !input_compatible(
                    &expected,
                    &input,
                    SourceTypesRef::Live(self.type_source.storage.live_types()),
                    &mut work,
                )? {
                    return Ok(false);
                }
                if expected.contains_callable(&mut work)? {
                    let target = self.owned_type_receiving_target(
                        expected,
                        environment.clone(),
                        args[slot].2,
                        &mut work,
                    )?;
                    let syntax = target
                        .syntax
                        .as_deref()
                        .ok_or(SourceTypesError::Unresolved)?;
                    let origin = super::contracts::SignatureSource::receiving(&target)
                        .ok_or(SourceTypesError::Unresolved)?;
                    let unsupported = self.unsupported.len();
                    self.with_typing_environment(&target.environment, |checker| {
                        checker.check_signature_modes(&input.value, syntax);
                        checker.check_receiving_callable_bounds_from(&input.value, syntax, &origin);
                    });
                    if self.diagnostics.len() != diagnostics
                        || self.unsupported.len() != unsupported
                    {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        })();
        match answer {
            Ok(true) => true,
            Ok(false) => {
                if self.diagnostics.len() == diagnostics && self.unsupported.len() == unsupported {
                    self.error(
                        "E0301",
                        span,
                        "stored input source does not fit the receiver's original element or key schema",
                        args.iter().map(|(_, value, _)| value.cause),
                    );
                }
                false
            }
            Err(error) => {
                self.unsupported(
                    span,
                    format!("storage input requires the original receiver schema and its actual supplied operand observations: {error}"),
                );
                false
            }
        }
    }

    fn storage_supplied_input(
        &self,
        event: CopyCallEventId,
        slot: usize,
        value: &Value,
        span: Span,
        frame: &Frame,
        work: &mut WorkLimit,
    ) -> Result<Option<Input>, SourceTypesError> {
        let candidate = (|| {
            let actual_context = self.invocation_context(frame.callable_owner);
            let call = self.copy_call_events.get(event.0 as usize)?;
            if call.id != event
                || call.span != span
                || call.owner != actual_context.owner
                || call.parent != actual_context.invocation
            {
                return None;
            }
            let input = self.call_input_source.supplied.get(&event)?.get(&slot)?;
            let expression = input.observation?;
            if input.context != actual_context
                || input.default.is_some()
                || input.allocation_epoch > self.recency_moves.len()
            {
                return None;
            }
            let mut preparations = self
                .call_arguments
                .iter()
                .filter(|preparation| preparation.source_event == event);
            let preparation = preparations.next()?;
            if preparations.next().is_some()
                || !preparation.slots_bound
                || !preparation.evaluation_complete
                || preparation.slots.get(slot)
                    != Some(&crate::sema::default_uses::ArgumentSource::Supplied)
                || preparation.supplied.get(&(slot as u32))
                    != Some(&crate::sema::default_uses::SuppliedArgument {
                        expression,
                        allocation_epoch: input.allocation_epoch,
                    })
            {
                return None;
            }
            let row = self.application_effect.contexts.get(expression)?;
            let original = self.application_effect.expressions.get(expression)?;
            if row.expression != expression
                || row.context != actual_context
                || row.argument_of != Some((event, slot as u32))
            {
                return None;
            }
            Some((input, original))
        })();
        let Some((input, original)) = candidate else {
            return Ok(None);
        };
        let transported = self.physical_value_at(original, self.recency_moves.len(), work)?;
        let mut remaining = work.remaining();
        let before = remaining;
        let same = crate::sema::evaluated::same_birth_value(&transported, value, &mut remaining);
        work.charge(before - remaining)?;
        if !same? {
            return Ok(None);
        }
        work.charge(1)?;
        Ok(Some(input.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compatible(
        expected: &ArgumentKey,
        input: &(Input, crate::sema::source_types::LiveSourceTypes),
    ) -> Option<bool> {
        input_compatible(
            &SourceSchema::import(expected, None, &mut WorkLimit::new(16384)).unwrap(),
            &input.0,
            SourceTypesRef::Live(&input.1),
            &mut WorkLimit::new(16384),
        )
        .ok()
    }

    fn input(
        key: ArgumentKey,
        fresh: Construction,
    ) -> (Input, crate::sema::source_types::LiveSourceTypes) {
        let context = InvocationContext {
            invocation: None,
            owner: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        };
        let mut packet = EvaluatedValue::new(Value::scalar(Ty::Unknown, None, CauseId(0)), 0);
        let mut types = crate::sema::source_types::LiveSourceTypes::default();
        let schema = SourceSchema::import(&key, None, &mut WorkLimit::new(16384)).unwrap();
        let source = SourceRef::intern(
            &schema,
            FrozenEnvironment::default(),
            &mut types,
            &mut WorkLimit::new(16384),
        )
        .unwrap();
        packet
            .capture_birth_source(
                Ok(CapturedSource::Known(source)),
                Some(std::sync::Arc::new(fresh)),
            )
            .unwrap();
        (
            Input {
                context,
                packet: std::sync::Arc::new(packet),
                default: None,
            },
            types,
        )
    }

    fn array(length: Option<u64>, element: ArgumentKey) -> ArgumentKey {
        ArgumentKey::Array {
            length: length.map(|length| format!("const(int:{length})")),
            element: Box::new(element),
        }
    }

    fn integer_key() -> ArgumentKey {
        ArgumentKey::Name {
            name: "int".into(),
            arguments: vec![],
        }
    }

    #[test]
    fn a_stored_empty_array_cannot_erase_its_declared_inner_dimension() {
        let expected = array(Some(0), array(Some(2), integer_key()));
        let mismatching = array(Some(0), array(Some(3), integer_key()));
        assert_eq!(
            compatible(&expected, &input(mismatching, Construction::Opaque)),
            Some(false)
        );
        assert_eq!(
            compatible(&expected, &input(expected.clone(), Construction::Opaque)),
            Some(true)
        );
        // Only a genuinely empty construction may take its new element
        // context. Physical Source replay must independently prove this AST.
        assert_eq!(
            compatible(
                &expected,
                &input(array(Some(0), integer_key()), Construction::Array(vec![]))
            ),
            Some(true)
        );
    }

    #[test]
    fn storage_receiving_keeps_dynamic_outer_and_invariant_stored_inner_coordinates() {
        let expected = array(None, array(Some(2), integer_key()));
        assert_eq!(
            compatible(
                &expected,
                &input(
                    array(Some(4), array(Some(2), integer_key())),
                    Construction::Opaque
                )
            ),
            Some(true)
        );
        assert_eq!(
            compatible(
                &expected,
                &input(
                    array(Some(4), array(Some(3), integer_key())),
                    Construction::Opaque
                )
            ),
            Some(false)
        );
    }
}
