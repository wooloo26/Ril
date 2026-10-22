//! Independent declaration and result coverage over physical HIR occurrences.
//! A later view, erased Ty or neighboring call cannot replace this evidence.
use super::*;
use crate::sema::{
    SemanticFacts,
    source_types::{SourceBuilder, WorkLimit, builtins, reception},
};
#[path = "builtin_source_instances.rs"]
mod instances;
pub(crate) use source::NameIndex as BuiltinNameIndex;

fn effects(contract: &builtin_source_types::Contract) -> BTreeSet<String> {
    contract
        .effects
        .iter()
        .map(|effect| match effect {
            builtin_source_types::SystemEffect::Fiber => "Fiber".into(),
        })
        .collect()
}

fn index_work<T>(
    work: &mut WorkLimit,
    query: impl FnOnce(&mut usize) -> Result<T, String>,
) -> Result<T, String> {
    let before = work.remaining();
    let mut remaining = before;
    let result = query(&mut remaining);
    work.charge(before - remaining)
        .map_err(|error| error.to_string())?;
    result
}

fn original_descriptor(
    contract: &builtin_source_types::Contract,
    value: &Value,
    work: &mut WorkLimit,
) -> Result<(), String> {
    work.charge(1 + value.callables.len())
        .map_err(|error| error.to_string())?;
    for callable in &value.callables {
        if let Callable::Builtin(name) = callable {
            work.text(name).map_err(|error| error.to_string())?;
        }
    }
    let before = work.remaining();
    let mut remaining = before;
    let admitted = crate::sema::clone_work::ty(&mut remaining, &value.ty, 0).is_some()
        && value.signature.as_ref().is_none_or(|parameters| {
            remaining = match remaining.checked_sub(parameters.len()) {
                Some(remaining) => remaining,
                None => return false,
            };
            parameters.iter().all(|parameter| {
                crate::static_eval::charge_parameter_syntax_clone(parameter, &mut remaining)
                    .is_some()
            })
        });
    work.charge(before - remaining)
        .map_err(|error| error.to_string())?;
    if !admitted {
        return Err("builtin descriptor exceeds its original Source work bound".into());
    }
    match &contract.source {
        BuiltinDeclaration::Numeric(id) => {
            if value.signature.is_some()
                || value.ty != Ty::Unknown
                || !matches!(value.callables.as_slice(), [Callable::Builtin(name)] if name == id.name())
            {
                return Err("numeric builtin source changed its original catalog recipe".into());
            }
        }
        BuiltinDeclaration::Generic(id) => {
            if value.signature.is_some()
                || value.ty != Ty::Unknown
                || !matches!(value.callables.as_slice(), [Callable::Builtin(name)] if name == id.name())
            {
                return Err("generic builtin source changed its universal descriptor".into());
            }
        }
        BuiltinDeclaration::Syntax(TypeExpr {
            kind: TypeKind::Callable { parameters, .. },
            ..
        }) => {
            if value.signature.as_ref() != Some(parameters)
                || !matches!(value.callables.as_slice(), [Callable::Builtin(name)] if name == contract.identity.name())
            {
                return Err(
                    "builtin source changed its original callable or parameter signature".into(),
                );
            }
        }
        BuiltinDeclaration::Syntax(_)
            if matches!(
                contract.identity,
                builtin_source_types::Identity::Constant(_)
            ) =>
        {
            if !value.callables.is_empty()
                || value.signature.is_some()
                || standard::constant_ty(contract.identity.name()).as_ref() != Some(&value.ty)
            {
                return Err(
                    "builtin data constant changed its canonical type or became callable".into(),
                );
            }
        }
        _ => return Err("builtin source declaration has no supported kind".into()),
    }
    Ok(())
}

pub(crate) fn validate(facts: &SemanticFacts) -> Result<(), (Span, CauseId, String)> {
    let fallback = facts
        .expressions
        .first()
        .map(|fact| fact.span)
        .unwrap_or(Span {
            file: FileId(0),
            start: 0,
            end: 0,
        });
    let contexts = physical_contexts(facts).map_err(|message| (fallback, CauseId(0), message))?;
    if facts.invocation_expressions.is_empty() && facts.builtin_source_observations.is_empty() {
        return validate_results(facts, &contexts);
    }
    let mut source_work = WorkLimit::new(1 << 20);
    let names = index_work(&mut source_work, |work| {
        BuiltinNameIndex::new_with_work(facts, work)
    })
    .map_err(|message| (fallback, CauseId(0), message))?;
    source_work
        .charge(facts.builtin_source_observations.len())
        .map_err(|error| (fallback, CauseId(0), error.to_string()))?;
    let mut seen = BTreeSet::new();
    for observation in &facts.builtin_source_observations {
        let span = facts
            .expressions
            .get(observation.expression)
            .map_or(fallback, |fact| fact.span);
        let mut run = || -> Result<(), String> {
            source_work.charge(8).map_err(|error| error.to_string())?;
            if !crate::sema::builtin_sources::is_catalog_environment(&observation.environment) {
                return Err("builtin Source lost its canonical declaration environment".into());
            }
            if !seen.insert(observation.expression) {
                return Err("builtin source repeats a physical expression".into());
            }
            let contract = builtin_source_types::contract(&observation.identity, span)
                .ok_or("builtin source has no canonical standard declaration")?;
            let fact = facts
                .expressions
                .get(observation.expression)
                .ok_or("builtin source expression is absent")?;
            if observation.full_header != contract.source
                || observation.concrete_effects != effects(&contract)
                || observation.written_formals != contract.written_formals.iter().copied().collect()
                || observation.captures != contract.captures
                || observation.cause != fact.value.cause
                || !fact.value.sources.is_empty()
            {
                return Err(
                    "builtin source changed its original declaration, rows or capture identity"
                        .into(),
                );
            }
            original_descriptor(&contract, &fact.value, &mut source_work)?;
            if contexts.get(&observation.expression) != Some(&observation.context) {
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
            index_work(&mut source_work, |work| {
                names.actual_name(
                    observation.context.owner,
                    fact.source_id
                        .ok_or("builtin reference has no HIR identity")?,
                    &observation.identity,
                    work,
                )
            })
        };
        run().map_err(|message| (span, observation.cause, message))?;
    }
    // Reverse obligations come from actual HIR names, even if the producer's
    // declaration arena or callable tags have been deleted or altered.
    for row in &facts.invocation_expressions {
        let Some(fact) = facts.expressions.get(row.expression) else {
            continue;
        };
        let Some(id) = fact.source_id else { continue };
        let identity = index_work(&mut source_work, |work| {
            names.direct_identity(row.context.owner, id, work)
        })
        .map_err(|message| (fact.span, fact.value.cause, message))?;
        if identity.is_some() && !seen.contains(&row.expression) {
            return Err((
                fact.span,
                fact.value.cause,
                "canonical builtin source lost its required original observation".into(),
            ));
        }
    }
    validate_results(facts, &contexts)?;
    instances::validate(facts)
}

fn physical_contexts(facts: &SemanticFacts) -> Result<BTreeMap<usize, InvocationContext>, String> {
    let mut work = WorkLimit::new(1 << 20);
    work.charge(facts.invocation_expressions.len())
        .map_err(|error| error.to_string())?;
    let mut contexts = BTreeMap::new();
    for row in &facts.invocation_expressions {
        if contexts.insert(row.expression, row.context).is_some() {
            return Err("builtin validation repeats a physical caller context".into());
        }
    }
    Ok(contexts)
}

fn validate_results(
    facts: &SemanticFacts,
    contexts: &BTreeMap<usize, InvocationContext>,
) -> Result<(), (Span, CauseId, String)> {
    if facts.copy_call_events.is_empty() {
        return Ok(());
    }
    let fallback = &facts.copy_call_events[0];
    let index_error = |message| (fallback.span, CauseId(0), message);
    let mut work = WorkLimit::new(1 << 20);
    work.charge(facts.copy_call_events.len())
        .map_err(|error| index_error(error.to_string()))?;
    work.charge(facts.call_arguments.len())
        .map_err(|error| index_error(error.to_string()))?;
    let mut preparations = BTreeMap::new();
    for row in &facts.call_arguments {
        if preparations.insert(row.source_event, row).is_some() {
            return Err(index_error("call repeats its physical preparation".into()));
        }
    }
    // Effect operations may legally use the same spelling. Their declaration
    // must be present in actual HIR; a producer map entry cannot waive a result.
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or_else(|| index_error("builtin result validation has no HIR".into()))?;
    work.charge(hir.statements().len())
        .map_err(|error| index_error(error.to_string()))?;
    let mut operations = BTreeSet::new();
    for (_, statement) in hir.statements() {
        if let crate::hir::nodes::StmtKind::Effect {
            name,
            operations: declarations,
            ..
        } = &statement.kind
        {
            work.charge(declarations.len())
                .map_err(|error| index_error(error.to_string()))?;
            if name.len() > 64 {
                continue;
            }
            for &id in declarations {
                let Some(crate::hir::nodes::Stmt {
                    kind: crate::hir::nodes::StmtKind::Function(function),
                    ..
                }) = hir.statement(id)
                else {
                    return Err(index_error(
                        "effect operation has no HIR declaration".into(),
                    ));
                };
                if function.name.len() <= 64 {
                    let name = format!("{name}::{}", function.name);
                    if let Some(id) = builtins::BuiltinId::lookup(&name) {
                        operations.insert(id);
                    }
                }
            }
        }
    }
    for event in &facts.copy_call_events {
        let Some(callee) = event
            .callee_expression
            .and_then(|id| facts.expressions.get(id))
        else {
            continue;
        };
        work.charge(callee.value.callables.len())
            .map_err(|error| index_error(error.to_string()))?;
        let definitions = callee
            .value
            .callables
            .iter()
            .map(|target| match target {
                Callable::Builtin(name) => {
                    builtins::BuiltinId::lookup(name).filter(|id| !operations.contains(id))
                }
                _ => None,
            })
            .collect::<Option<Vec<_>>>();
        let Some(definitions) = definitions.filter(|ids| !ids.is_empty()) else {
            continue;
        };
        let run = || -> Result<(), String> {
            let result_id = event
                .result_expression
                .ok_or("closed builtin call lost its actual result occurrence")?;
            let result = facts
                .expressions
                .get(result_id)
                .ok_or("closed builtin result occurrence is absent")?;
            let preparation = preparations
                .get(&event.id)
                .ok_or("closed builtin has no unique physical preparation")?;
            let callee_context = contexts
                .get(&event.callee_expression.unwrap())
                .ok_or("closed builtin callee has no actual caller context")?;
            if contexts.get(&result_id) != Some(callee_context)
                || callee_context.owner != event.owner
                || callee_context.invocation != event.parent
                || result.source_id != event.source_id
                || result.source_id.is_none()
            {
                return Err(
                    "closed builtin result borrowed a different HIR application or activation"
                        .into(),
                );
            }
            if preparation.evaluated.iter().any(|row| {
                facts
                    .expressions
                    .get(row.observation.expression)
                    .is_some_and(|fact| fact.value.ty == Ty::Never)
            }) {
                return Ok(());
            }
            if !preparation.evaluation_complete || !preparation.slots_bound {
                return Err(
                    "closed builtin result borrowed an incomplete or different HIR application"
                        .into(),
                );
            }
            for id in definitions {
                let mut work = WorkLimit::new(4096);
                let graph = id
                    .definition()
                    .graph(&mut work)
                    .map_err(|error| error.to_string())?;
                let actual = result
                    .value
                    .source_type_witness
                    .as_ref()
                    .ok_or("closed builtin result lost its original declaration view")?;
                if !actual.validate_closed() {
                    return Err("closed builtin result source is not a closed original view".into());
                }
                let actual = crate::static_eval::effects::bounded_argument_key(
                    &actual.syntax,
                    &BTreeMap::new(),
                )
                .ok_or("closed builtin result source is not complete")?;
                let mut imported = SourceBuilder::new().map_err(|error| error.to_string())?;
                let actual = imported
                    .import_key(&actual, &mut work)
                    .map_err(|error| error.to_string())?;
                if !reception::equivalent(&graph.types, graph.result, &imported, actual, &mut work)
                    .map_err(|error| error.to_string())?
                    || builtins::erased_type(&graph.types, graph.result, &mut work)
                        .ok()
                        .as_ref()
                        != Some(&result.value.ty)
                {
                    return Err(
                        "closed builtin result changed its original declared source schema".into(),
                    );
                }
            }
            Ok(())
        };
        run().map_err(|message| (event.span, callee.value.cause, message))?;
    }
    Ok(())
}

pub(crate) fn original_canonical_source(
    facts: &SemanticFacts,
    usage: &super::CanonicalBuiltinUse<'_>,
    names: &BuiltinNameIndex<'_>,
    work: &mut WorkLimit,
) -> Result<
    Option<(
        crate::sema::source_types::SourceSchema,
        crate::sema::context::FrozenEnvironment,
    )>,
    String,
> {
    let Some((declaration, environment)) = canonical_declaration(facts, usage, names, work)? else {
        return Ok(None);
    };
    let schema = builtin_source_types::source_schema(&declaration, work)
        .map_err(|error| error.to_string())?;
    Ok(schema.map(|schema| (schema, environment)))
}

pub(crate) fn original_numeric_declaration(
    facts: &SemanticFacts,
    usage: &super::CanonicalBuiltinUse<'_>,
    names: &BuiltinNameIndex<'_>,
    work: &mut WorkLimit,
) -> Result<Option<ril_compiler_core::numeric_builtins::NumericBuiltin>, String> {
    Ok(
        canonical_declaration(facts, usage, names, work)?.and_then(|(declaration, _)| {
            if let BuiltinDeclaration::Numeric(id) = declaration {
                Some(id)
            } else {
                None
            }
        }),
    )
}

pub(crate) fn original_canonical_key(
    facts: &SemanticFacts,
    usage: &super::CanonicalBuiltinUse<'_>,
    names: &BuiltinNameIndex<'_>,
    work: &mut WorkLimit,
) -> Result<Option<crate::sema::effect_identity::ArgumentKey>, String> {
    // Compatibility consumers still receive the original declaration's key;
    // the checked graph query never exports and readmits an observed graph.
    canonical_declaration(facts, usage, names, work).map(|source| {
        source.and_then(|(declaration, _)| builtin_source_types::source_key(&declaration))
    })
}

fn canonical_declaration(
    facts: &SemanticFacts,
    usage: &super::CanonicalBuiltinUse<'_>,
    names: &BuiltinNameIndex<'_>,
    work: &mut WorkLimit,
) -> Result<Option<(BuiltinDeclaration, crate::sema::context::FrozenEnvironment)>, String> {
    let super::CanonicalBuiltinUse {
        value,
        actual,
        context,
        observation: actual_observation,
    } = *usage;
    work.charge(1).map_err(|error| error.to_string())?;
    if !names.matches_facts(facts) {
        return Err("canonical builtin Source borrowed another program's lexical index".into());
    }
    let name = match &actual.kind {
        ExprKind::Name(name) => {
            work.text(name).map_err(|error| error.to_string())?;
            name.clone()
        }
        ExprKind::Path(path) => {
            work.charge(path.len()).map_err(|error| error.to_string())?;
            for part in path {
                work.text(part).map_err(|error| error.to_string())?;
            }
            path.join("::")
        }
        _ => return Ok(None),
    };
    if !value.sources.is_empty() {
        return Ok(None);
    }
    let Some(contract) = builtin_source_types::contract(&name, actual.span) else {
        return Ok(None);
    };
    let source_id = actual
        .hir_id
        .ok_or("canonical builtin Source lost its original HIR")?;
    let Some(identity) = index_work(work, |work| {
        names.direct_identity(context.owner, source_id, work)
    })?
    else {
        return Ok(None);
    };
    if identity != name {
        return Err("canonical builtin Source borrowed another HIR name".into());
    }
    work.charge(facts.builtin_source_observations.len() + facts.invocation_expressions.len() + 8)
        .map_err(|error| error.to_string())?;
    let mut matching = facts
        .builtin_source_observations
        .iter()
        .filter(|observation| observation.expression == actual_observation);
    let observation = matching
        .next()
        .ok_or("canonical builtin Source lost its physical observation")?;
    if matching.next().is_some()
        || observation.context != context
        || observation.identity != name
        || observation.cause != value.cause
        || !facts
            .expressions
            .get(actual_observation)
            .is_some_and(|fact| fact.source_id == Some(source_id))
        || !facts
            .evaluations
            .get(actual_observation)
            .is_some_and(|record| {
                record.id.0 as usize == actual_observation
                    && record.context == context
                    && record
                        .identity
                        .is_some_and(|identity| identity.source == source_id)
            })
        || !crate::sema::builtin_sources::is_catalog_environment(&observation.environment)
        || observation.full_header != contract.source
        || observation.concrete_effects != effects(&contract)
        || observation.written_formals != contract.written_formals.iter().copied().collect()
        || observation.captures != contract.captures
        || facts
            .invocation_expressions
            .iter()
            .filter(|row| row.expression == observation.expression && row.context == context)
            .count()
            != 1
    {
        return Err(
            "canonical builtin Source changed its declaration, environment or physical origin"
                .into(),
        );
    }
    if !index_work(work, |work| {
        crate::sema::evaluated::same_birth_value(
            &facts.expressions[actual_observation].value,
            value,
            work,
        )
        .map_err(|error| error.to_string())
    })? {
        return Err("canonical builtin Source changed its actual observed value".into());
    }
    original_descriptor(&contract, value, work)?;
    // The original declaration is already authenticated above. Numeric
    // native defaults remain a catalog recipe until a real arity is selected.
    Ok(Some((contract.source, observation.environment.clone())))
}
#[path = "builtin_source_syntax.rs"]
mod source;
