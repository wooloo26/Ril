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
        let answer = (|| {
            let mut work = WorkLimit::new(16384);
            let event = self
                .application_effect
                .current_call_event()
                .ok_or(SourceTypesError::MissingNode)?;
            let receiver = self
                .storage_supplied_input(event, 0, &args[0].1, span, frame)
                .ok_or(SourceTypesError::MissingNode)?;
            let (original, environment) = receiver
                .input_source()?
                .as_ref()
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
                    .storage_supplied_input(event, slot, &args[slot].1, span, frame)
                    .ok_or(SourceTypesError::MissingNode)?;
                if !storage_compatible(&expected, &input, &mut work)? {
                    return Ok(false);
                }
            }
            Ok(true)
        })();
        match answer {
            Ok(true) => true,
            Ok(false) => {
                self.error(
                    "E0301",
                    span,
                    "stored input source does not fit the receiver's original element or key schema",
                    args.iter().map(|(_, value, _)| value.cause),
                );
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
    ) -> Option<Input> {
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
        let mut transported = original.value.clone();
        self.transport_value_since(&mut transported, input.allocation_epoch);
        if transported != *value {
            return None;
        }
        Some(input.clone())
    }
}

fn storage_compatible(
    expected: &SourceSchema,
    input: &Input,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    if let Some((actual, _)) = input.input_source()?
        && let (Some(expected), Some(actual)) = (
            expected.callable_annotations(work)?,
            actual.callable_annotations(work)?,
        )
        && expected != actual
    {
        return Err(SourceTypesError::Unresolved);
    }
    input_compatible(expected, input, work)
}
#[cfg(test)]
mod tests {
    use super::*;

    fn compatible(expected: &ArgumentKey, input: &Input) -> Option<bool> {
        storage_compatible(
            &SourceSchema::import(expected, None, &mut WorkLimit::new(16384)).unwrap(),
            input,
            &mut WorkLimit::new(16384),
        )
        .ok()
    }

    fn input(key: ArgumentKey, fresh: Construction) -> Input {
        let context = InvocationContext {
            invocation: None,
            owner: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        };
        let mut packet = EvaluatedValue::new(Value::scalar(Ty::Unknown, None, CauseId(0)), 0);
        packet
            .capture_birth_source(
                Ok(Some((
                    SourceSchema::import(&key, None, &mut WorkLimit::new(16384)).unwrap(),
                    FrozenEnvironment::default(),
                ))),
                Some(std::sync::Arc::new(fresh)),
            )
            .unwrap();
        Input {
            context,
            packet: std::sync::Arc::new(packet),
            default: None,
        }
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

    #[test]
    fn source_coordinates_do_not_prove_an_unrelated_callable_bound_row() {
        let callable = |annotations| ArgumentKey::Callable {
            parameters: vec![],
            result: Box::new(integer_key()),
            annotations,
        };
        let expected = callable(vec!["@{}".into()]);
        assert_eq!(
            compatible(
                &expected,
                &input(callable(vec!["@Fiber".into()]), Construction::Opaque)
            ),
            None
        );
    }
}
