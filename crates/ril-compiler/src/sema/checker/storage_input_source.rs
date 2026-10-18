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
            let event = self.copy_operation_events.last().copied().flatten()?;
            let receiver = self.storage_supplied_input(event, 0, &args[0].1, span, frame)?;
            let original = receiver.key.as_ref()?;
            source_reception::complete(original, &mut 4096)?;
            for &(slot, part) in parts {
                let expected = collection_part(original, part)?;
                // A genuine scalar-only source graph has no additional
                // dimension/callable coordinate duty. Ordinary typing and all
                // publication permissions still run in the intrinsic.
                if crate::sema::source_types::key_is_coordinate_free(expected) {
                    continue;
                }
                let input = self.storage_supplied_input(event, slot, &args[slot].1, span, frame)?;
                if !storage_compatible(expected, &input)? {
                    return Some(false);
                }
            }
            Some(true)
        })();
        match answer {
            Some(true) => true,
            Some(false) => {
                self.error(
                    "E0301",
                    span,
                    "stored input source does not fit the receiver's original element or key schema",
                    args.iter().map(|(_, value, _)| value.cause),
                );
                false
            }
            None => {
                self.unsupported(
                    span,
                    "storage input requires the original receiver schema and its actual supplied operand observations",
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
        let expression = input.expression?;
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
        let row = self.invocation_expressions.get(expression)?;
        let original = self.expression_facts.get(expression)?;
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

fn collection_part(key: &ArgumentKey, part: Part) -> Option<&ArgumentKey> {
    match (key, part) {
        (ArgumentKey::Array { element, .. }, Part::Element) => Some(element),
        (ArgumentKey::Map { key, .. }, Part::MapKey) => Some(key),
        (ArgumentKey::Map { value, .. }, Part::MapValue) => Some(value),
        (ArgumentKey::Name { name, arguments }, Part::Element)
            if matches!(name.as_str(), "Set" | "Prelude::Set") && arguments.len() == 1 =>
        {
            Some(&arguments[0])
        }
        _ => None,
    }
}

fn storage_compatible(expected: &ArgumentKey, input: &Input) -> Option<bool> {
    // Top-level Fn receiving coordinates alone do not compare its bound rows.
    // Until the original frozen bound environment is supplied by the storage
    // ledger, unequal rows provide no additional proof at this store boundary.
    if let (
        ArgumentKey::Callable { annotations, .. },
        Some(ArgumentKey::Callable {
            annotations: actual,
            ..
        }),
    ) = (expected, &input.key)
        && annotations != actual
    {
        return None;
    }
    input_compatible(expected, input)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn input(key: ArgumentKey, fresh: Construction) -> Input {
        Input {
            context: InvocationContext {
                invocation: None,
                owner: None,
                closure: None,
                closure_invocation: None,
                budget_validation: false,
                default_use: None,
            },
            expression: None,
            allocation_epoch: 0,
            key: Some(key),
            fresh,
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
            storage_compatible(&expected, &input(mismatching, Construction::Opaque)),
            Some(false)
        );
        assert_eq!(
            storage_compatible(&expected, &input(expected.clone(), Construction::Opaque)),
            Some(true)
        );
        // Only a genuinely empty construction may take its new element
        // context. Physical Source replay must independently prove this AST.
        assert_eq!(
            storage_compatible(
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
            storage_compatible(
                &expected,
                &input(
                    array(Some(4), array(Some(2), integer_key())),
                    Construction::Opaque
                )
            ),
            Some(true)
        );
        assert_eq!(
            storage_compatible(
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
            storage_compatible(
                &expected,
                &input(callable(vec!["@Fiber".into()]), Construction::Opaque)
            ),
            None
        );
    }
}
