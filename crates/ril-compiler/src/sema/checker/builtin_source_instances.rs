//! Independently derive primitive-instance constraints from frozen Source views.
//! This does not consume the checker's bound-probe success or obligation flags.
use super::*;
use crate::sema::{effect_identity::ArgumentKey, source_types::polymorphic};
use ril_compiler_core::builtin_calls::GenericBuiltin;

fn snapshot_values(
    snapshot: &crate::sema::copy_contract::CopyValueSnapshot,
) -> impl Iterator<Item = &Value> {
    std::iter::once(&snapshot.value).chain(
        snapshot
            .nodes
            .iter()
            .flat_map(|node| node.fields.iter().map(|(_, value)| value)),
    )
}

fn instance(id: GenericBuiltin, key: &ArgumentKey) -> Result<(), String> {
    if let ArgumentKey::GenericBuiltin(actual) = key {
        return (id == *actual)
            .then_some(())
            .ok_or("primitive view changed its declaration".into());
    }
    let selected = polymorphic::instantiate_key(id, key)
        .map_err(|error| format!("primitive instance lacks complete Source: {error:?}"))?
        .ok_or("primitive instance changed full types, result or modes")?;
    let ArgumentKey::Callable { annotations, .. } = key else {
        unreachable!()
    };
    if !selected.fits_bounds(annotations) {
        return Err("primitive instance exceeds its original callable capability bound".into());
    }
    Ok(())
}

fn ids(value: &Value) -> impl Iterator<Item = GenericBuiltin> + '_ {
    value
        .callables
        .iter()
        .filter_map(|callable| match callable {
            Callable::Builtin(name) => GenericBuiltin::lookup(name),
            _ => None,
        })
}

pub(super) fn validate(facts: &SemanticFacts) -> Result<(), (Span, CauseId, String)> {
    if !facts
        .builtin_source_observations
        .iter()
        .any(|row| matches!(row.full_header, BuiltinDeclaration::Generic(_)))
    {
        return Ok(());
    }
    let fallback = facts.expressions.first().map_or(
        Span {
            file: FileId(0),
            start: 0,
            end: 0,
        },
        |fact| fact.span,
    );
    let mut work = 1_000_000usize;
    // Declaration sources survive even when a mutable binding's current value
    // has changed. Use the original initializer as well as its current view.
    for source in &facts.binding_sources {
        if !source.path.as_ref().is_some_and(|path| path.is_empty()) {
            continue;
        }
        let run = || -> Result<(), String> {
            let binding = facts
                .bindings
                .get(source.binding)
                .ok_or("primitive view has no binding")?;
            let original = facts
                .expressions
                .get(source.initializer.expression)
                .ok_or("primitive initializer is absent")?;
            if facts.source_types.binding_type(source.binding).is_none() {
                return Ok(());
            }
            let (schema, _) = facts
                .source_types
                .binding_schema(source.binding, None, &mut WorkLimit::new(16384))
                .map_err(|error| format!("primitive view lost its frozen Source graph: {error}"))?;
            for id in ids(&original.value).chain(ids(&binding.value)) {
                if !schema
                    .is_builtin_instance(id, &mut WorkLimit::new(16384))
                    .map_err(|error| error.to_string())?
                {
                    return Err(
                        "primitive view exceeds its original complete Source declaration".into(),
                    );
                }
            }
            if ids(&binding.value).next().is_some()
                && let Some(witness) = &binding.value.source_type_witness
            {
                let actual = crate::static_eval::effects::bounded_argument_key(
                    &witness.syntax,
                    &BTreeMap::new(),
                )
                .ok_or("primitive view has an incomplete source witness")?;
                let mut budget = WorkLimit::new(16384);
                if !schema
                    .equivalent_key(&actual, &mut budget)
                    .map_err(|error| error.to_string())?
                {
                    return Err("primitive view changed its frozen declaration Source".into());
                }
            }
            if !binding.mode.is_mutable()
                && ids(&original.value).any(|id| !ids(&binding.value).any(|current| current == id))
            {
                return Err(
                    "immutable primitive binding lost its original callable identity".into(),
                );
            }
            Ok(())
        };
        run().map_err(|error| {
            (
                fallback,
                facts
                    .bindings
                    .get(source.binding)
                    .map_or(CauseId(0), |b| b.value.cause),
                error,
            )
        })?;
    }
    let roots = facts
        .expressions
        .iter()
        .map(|fact| (&fact.value, fact.span))
        .chain(
            facts
                .bindings
                .iter()
                .map(|binding| (&binding.value, binding.span)),
        )
        .chain(facts.fields.values().map(|value| (value, fallback)))
        .chain(facts.copy_invocations.iter().flat_map(|call| {
            call.entry
                .arguments
                .iter()
                .flat_map(|(_, arg)| snapshot_values(arg).map(|value| (value, call.span)))
                .chain(
                    call.result
                        .iter()
                        .flat_map(|result| snapshot_values(result).map(|value| (value, call.span))),
                )
        }))
        .chain(facts.closure_invocations.iter().flat_map(|call| {
            call.entry
                .arguments
                .iter()
                .map(|(_, value, _)| (value, call.site))
        }));
    let mut pending = Vec::new();
    for (value, span) in roots {
        if pending.len() >= work {
            return Err((
                span,
                value.cause,
                "primitive instance roots exceed the replay budget".into(),
            ));
        }
        pending.push((value, span));
    }
    while let Some((value, span)) = pending.pop() {
        work = work.checked_sub(1).ok_or((
            span,
            value.cause,
            "primitive instance replay exceeds its value budget".into(),
        ))?;
        let run = || -> Result<(), String> {
            let declarations: Vec<_> = ids(value).collect();
            if declarations.is_empty() || value.signature.is_none() {
                return Ok(());
            }
            let key = value
                .source_type_witness
                .as_ref()
                .filter(|witness| witness.validate_closed())
                .and_then(|witness| {
                    crate::static_eval::effects::bounded_argument_key(
                        &witness.syntax,
                        &BTreeMap::new(),
                    )
                })
                .or_else(|| {
                    // Every possible source must retain the same complete
                    // view. One convenient binding cannot certify a join.
                    let mut common = None;
                    for binding in &value.sources {
                        let source = facts.source_types.binding_type(*binding)?;
                        let key = facts.source_types.key(source).ok()?;
                        if common.as_ref().is_some_and(|previous| previous != &key) {
                            return None;
                        }
                        common = Some(key);
                    }
                    common
                })
                .ok_or("primitive instance lost its complete receiving Source")?;
            if !matches!(key, ArgumentKey::Callable { .. }) {
                return Err(
                    "a selected primitive signature borrowed an unapplied source scheme".into(),
                );
            }
            for id in declarations {
                instance(id, &key)?;
                for bound in &value.callable_bounds {
                    let selected = polymorphic::instantiate_key(id, &key)
                        .map_err(|error| error.to_string())?
                        .ok_or("primitive bound has no selected Source instance")?;
                    if !selected.fits_bounds(
                        &bound
                            .annotations
                            .iter()
                            .map(|row| row.text.clone())
                            .collect::<Vec<_>>(),
                    ) {
                        return Err("primitive retained an incompatible callable bound".into());
                    }
                }
            }
            Ok(())
        };
        run().map_err(|error| (span, value.cause, error))?;
        pending.extend(
            [
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.option_payload,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .map(|value| (value.as_ref(), span)),
        );
        pending.extend(
            value
                .variant_witnesses
                .values()
                .map(|value| (value.as_ref(), span)),
        );
    }
    Ok(())
}
