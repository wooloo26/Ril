//! Independent checks for physical builtin source observations. This validates
//! their original contracts; it never pays a receiving bound or an effect duty.
use super::*;
use crate::sema::SemanticFacts;

pub(crate) fn actual_prelude_name(
    facts: &SemanticFacts,
    context: InvocationContext,
    actual: &Expr,
    identity: &str,
) -> Result<(), String> {
    source::actual_prelude_name(facts, context, actual, identity)
}

pub(crate) fn validate(facts: &SemanticFacts) -> Result<(), (Span, CauseId, String)> {
    let mut seen = BTreeSet::new();
    for observation in &facts.builtin_source_observations {
        let span = facts
            .expressions
            .get(observation.expression)
            .map_or(observation.full_header.span, |fact| fact.span);
        let mut run = || -> Result<(), String> {
            if !seen.insert(observation.expression) {
                return Err("builtin source repeats a physical expression".into());
            }
            let contract = builtin_source_types::contract(&observation.identity, span)
                .ok_or("builtin source has no canonical standard header")?;
            let fact = facts
                .expressions
                .get(observation.expression)
                .ok_or("builtin source expression is absent")?;
            if observation.full_header != contract.source
                || observation.concrete_effects != BTreeSet::from(["Fiber".into()])
                || observation.written_formals != BTreeSet::from([0])
                || observation.captures != contract.captures
                || observation.cause != fact.value.cause
                || !matches!(fact.value.callables.as_slice(), [Callable::Builtin(name)] if name == &observation.identity)
                || !fact.value.sources.is_empty()
            {
                return Err(
                    "builtin source changed its original header, rows or capture identity".into(),
                );
            }
            let TypeKind::Callable { parameters, .. } = &observation.full_header.kind else {
                return Err("builtin source header is not Fn".into());
            };
            if fact.value.signature.as_ref() != Some(parameters) {
                return Err("builtin source changed its original parameter signature".into());
            }
            let rows: Vec<_> = facts
                .invocation_expressions
                .iter()
                .filter(|row| row.expression == observation.expression)
                .collect();
            if !matches!(rows.as_slice(), [row] if row.context == observation.context) {
                return Err("builtin source lost its unique actual caller context".into());
            }
            let cause = facts
                .explanations
                .causes
                .get(observation.cause.0 as usize)
                .ok_or("builtin source cause is absent")?;
            if cause.id != observation.cause
                || cause.span != Some(span)
                || !cause.parents.is_empty()
                || facts.explanations.kinds.get(observation.cause.0 as usize)
                    != Some(&CauseKind::Source)
            {
                return Err("builtin source borrowed a derived or unrelated cause".into());
            }
            source::actual_name(
                facts,
                observation.context.owner,
                span,
                &observation.identity,
            )
        };
        run().map_err(|message| (span, observation.cause, message))?;
    }
    // Reconstruct reverse coverage from original expressions, so deleting the
    // whole observation arena cannot erase its Source obligation.
    for row in &facts.invocation_expressions {
        let Some(fact) = facts.expressions.get(row.expression) else {
            continue;
        };
        let [Callable::Builtin(name)] = fact.value.callables.as_slice() else {
            continue;
        };
        if builtin_source_types::contract(name, fact.span).is_none()
            || !fact.value.sources.is_empty()
            || facts.explanations.kinds.get(fact.value.cause.0 as usize) != Some(&CauseKind::Source)
        {
            continue;
        }
        let identity = source::direct_identity(facts, row.context.owner, fact.span)
            .map_err(|message| (fact.span, fact.value.cause, message))?;
        if identity.as_deref() == Some(name) && !seen.contains(&row.expression) {
            return Err((
                fact.span,
                fact.value.cause,
                "canonical builtin source lost its required original observation".into(),
            ));
        }
    }
    Ok(())
}

pub(crate) fn original_canonical_key(
    facts: &SemanticFacts,
    value: &Value,
    actual: &Expr,
    context: crate::sema::effect_identity::InvocationContext,
) -> Option<crate::sema::effect_identity::ArgumentKey> {
    let name = match &actual.kind {
        ExprKind::Name(name) => name.clone(),
        ExprKind::Path(path) => path.join("::"),
        _ => return None,
    };
    if !value.sources.is_empty() {
        return None;
    }
    let contract = builtin_source_types::contract(&name, actual.span)?;
    let mut matching = facts
        .builtin_source_observations
        .iter()
        .filter(|observation| {
            observation.context == context
                && observation.identity == name
                && observation.cause == value.cause
                && facts
                    .expressions
                    .get(observation.expression)
                    .is_some_and(|fact| fact.span == actual.span && fact.value == *value)
        });
    let observation = matching.next()?;
    if matching.next().is_some()
        || observation.full_header != contract.source
        || observation.concrete_effects != BTreeSet::from(["Fiber".into()])
        || observation.written_formals != BTreeSet::from([0])
        || !observation.captures.is_empty()
        || facts
            .invocation_expressions
            .iter()
            .filter(|row| row.expression == observation.expression && row.context == context)
            .count()
            != 1
    {
        return None;
    }
    source::actual_name(facts, context.owner, actual.span, &name).ok()?;
    let syntax = super::super::source_types::expand_builtin_source_syntax(
        &BTreeMap::new(),
        &observation.full_header,
        0,
    )?;
    let key = crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())?;
    crate::sema::source_reception::complete(&key, &mut 4096)?;
    Some(key)
}

#[path = "builtin_source_syntax.rs"]
mod source;
