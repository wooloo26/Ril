//! Independently check the original receiver and supplied store operand.
//! An intrinsic's current collection contents never establish its member type.
use super::*;
use crate::sema::{copy_contract::CopyCallEvent, default_uses::ArgumentSource, model::Callable};

#[derive(Clone, Copy)]
enum Part {
    Element,
    MapKey,
    MapValue,
}

impl Replay<'_> {
    pub(super) fn storage_input_sources(
        &self,
        event: &CopyCallEvent,
        syntax: &Expr,
        callee: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check {
        let [Callable::Builtin(name)] = callee.callables.as_slice() else {
            return Ok(());
        };
        let (arity, stores): (_, &[(usize, Part)]) = match name.as_str() {
            "Array::push" => (2, &[(1, Part::Element)]),
            "Array::insert" => (3, &[(2, Part::Element)]),
            "Map::set" => (3, &[(1, Part::MapKey), (2, Part::MapValue)]),
            "Set::insert" => (2, &[(1, Part::Element)]),
            _ => return Ok(()),
        };
        let application = AstApplication::from_ast(syntax)
            .ok_or_else(|| "storage intrinsic is missing its original application".to_owned())?;
        let arguments = &application.operands;
        require(
            event.matches_source(syntax)
                && event.owner == context.owner
                && event.parent == context.invocation
                && event.target.is_none()
                && arguments.len() == arity,
            "storage intrinsic changed its original application or supplied slot mapping",
        )?;
        let preparations: Vec<_> = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id)
            .collect();
        let [preparation] = preparations.as_slice() else {
            return Err("storage intrinsic has no unique actual argument preparation".into());
        };
        require(
            preparation.target.is_none()
                && preparation.evaluation_complete
                && preparation.slots == vec![ArgumentSource::Supplied; arity]
                && preparation.supplied.len() == arity,
            "storage intrinsic lost a completed physical operand",
        )?;
        let labels = if let Some(parameters) = &callee.signature {
            crate::hir::application::parameter_labels(parameters)
        } else if let Some(id) = crate::sema::builtin_sources::generic_reference(callee) {
            let token = event
                .callee_expression
                .ok_or("primitive interface has no actual callee")?;
            require(
                self.original_observed_source_key(application.callee, token, context, sites)?
                    == ArgumentKey::GenericBuiltin(id),
                "primitive public interface has no original declaration Source",
            )?;
            crate::sema::source_types::polymorphic::parameter_labels(id)
        } else {
            vec![None; arity]
        };
        let mapping: Vec<_> = crate::hir::application::bind_slots(
            &labels,
            arguments.iter().map(|argument| argument.label),
        )
        .into_iter()
        .collect::<Result<_, _>>()
        .map_err(|code| format!("primitive public argument mapping is invalid: {code}"))?;
        require(
            labels.len() == arity,
            "primitive public interface changed its arity",
        )?;
        let original = |slot: usize| -> Check<usize> {
            let index = mapping
                .iter()
                .position(|actual| *actual == slot)
                .ok_or("primitive slot has no written input")?;
            let supplied = preparation
                .supplied
                .get(&(slot as u32))
                .ok_or_else(|| "storage intrinsic supplied slot is absent".to_owned())?;
            let value = self
                .facts
                .expressions
                .get(supplied.expression)
                .ok_or_else(|| "storage intrinsic operand observation is absent".to_owned())?;
            require(
                supplied.allocation_epoch <= self.facts.allocation_history.len()
                    && value.source_id.is_some()
                    && value.source_id == arguments[index].expression.hir_id
                    && self
                        .observations
                        .row(supplied.expression, &mut 4096)
                        .is_ok_and(|row| {
                            row.context == context
                                && row.argument_of == Some((event.id, slot as u32))
                        }),
                "storage intrinsic operand borrowed another occurrence, epoch or context",
            )?;
            self.input_operand_interval(event, slot, supplied.expression, context, sites)?;
            Ok(supplied.expression)
        };
        let receiver = self.original_observed_source_key(
            arguments[mapping
                .iter()
                .position(|slot| *slot == 0)
                .ok_or("primitive receiver is absent")?]
            .expression,
            original(0)?,
            context,
            sites,
        )?;
        require(
            source_reception::complete(&receiver, &mut 4096).is_some(),
            "storage intrinsic receiver has no complete original schema",
        )?;
        for &(slot, part) in stores {
            let expected = collection_part(&receiver, part).ok_or_else(|| {
                "storage intrinsic receiver has no declared member projection".to_owned()
            })?;
            if crate::sema::source_types::key_is_coordinate_free_with_declarations(
                expected,
                self.facts.semantic_hir.as_deref(),
            ) {
                continue;
            }
            let observation = original(slot)?;
            let written = mapping
                .iter()
                .position(|actual| *actual == slot)
                .ok_or("primitive stored slot is absent")?;
            let actual = self.input_source_reception(
                expected,
                arguments[written].expression,
                &self.facts.expressions[observation].value,
                context,
                sites,
                Some(observation),
            )?;
            if let (
                ArgumentKey::Callable {
                    annotations: expected,
                    ..
                },
                Some(ArgumentKey::Callable {
                    annotations: actual,
                    ..
                }),
            ) = (expected, actual.as_ref())
            {
                require(
                    expected == actual,
                    "storage callable bounds require their original frozen lexical proof",
                )?;
            }
        }
        Ok(())
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
