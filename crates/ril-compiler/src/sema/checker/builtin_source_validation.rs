//! Independent declaration and result coverage over physical HIR occurrences.
//! A later view, erased Ty or neighboring call cannot replace this evidence.
use super::*;
use crate::sema::{
    SemanticFacts,
    source_types::{SourceBuilder, WorkLimit, builtins, reception},
};
#[path = "builtin_source_instances.rs"]
mod instances;

pub(crate) fn actual_prelude_name(
    facts: &SemanticFacts,
    context: InvocationContext,
    actual: &Expr,
    identity: &str,
) -> Result<(), String> {
    source::actual_prelude_name(facts, context, actual, identity)
}

fn effects(contract: &builtin_source_types::Contract) -> BTreeSet<String> {
    contract
        .effects
        .iter()
        .map(|effect| match effect {
            builtin_source_types::SystemEffect::Fiber => "Fiber".into(),
        })
        .collect()
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
    let names = source::NameIndex::new(facts).map_err(|message| (fallback, CauseId(0), message))?;
    let mut source_work = WorkLimit::new(1 << 20);
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
            match &contract.source {
                BuiltinDeclaration::Generic(id) => {
                    if fact.value.signature.is_some()
                        || fact.value.ty != Ty::Unknown
                        || !matches!(fact.value.callables.as_slice(), [Callable::Builtin(name)] if name == id.name())
                    {
                        return Err(
                            "generic builtin source changed its universal descriptor".into()
                        );
                    }
                }
                BuiltinDeclaration::Syntax(TypeExpr {
                    kind: TypeKind::Callable { parameters, .. },
                    ..
                }) => {
                    if fact.value.signature.as_ref() != Some(parameters)
                        || !matches!(fact.value.callables.as_slice(), [Callable::Builtin(name)] if name == &observation.identity)
                    {
                        return Err(
                            "builtin source changed its original callable or parameter signature"
                                .into(),
                        );
                    }
                }
                BuiltinDeclaration::Syntax(_)
                    if matches!(
                        contract.identity,
                        builtin_source_types::Identity::Constant(_)
                    ) =>
                {
                    if !fact.value.callables.is_empty()
                        || fact.value.signature.is_some()
                        || standard::constant_ty(&observation.identity).as_ref()
                            != Some(&fact.value.ty)
                    {
                        return Err(
                            "builtin data constant changed its canonical type or became callable"
                                .into(),
                        );
                    }
                }
                _ => return Err("builtin source declaration has no supported kind".into()),
            }
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
            names.actual_name(
                observation.context.owner,
                fact.source_id
                    .ok_or("builtin reference has no HIR identity")?,
                &observation.identity,
            )
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
        let identity = names
            .direct_identity(row.context.owner, id)
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
    value: &Value,
    actual: &Expr,
    context: InvocationContext,
    work: &mut WorkLimit,
) -> Result<
    Option<(
        crate::sema::source_types::SourceSchema,
        crate::sema::context::FrozenEnvironment,
    )>,
    String,
> {
    let Some((key, environment)) = canonical_declaration(facts, value, actual, context, work)?
    else {
        return Ok(None);
    };
    let schema = crate::sema::source_types::SourceSchema::import(&key, None, work)
        .map_err(|error| error.to_string())?;
    Ok(Some((schema, environment)))
}

pub(crate) fn original_canonical_key(
    facts: &SemanticFacts,
    value: &Value,
    actual: &Expr,
    context: InvocationContext,
) -> Result<Option<crate::sema::effect_identity::ArgumentKey>, String> {
    // Compatibility consumers still receive the original declaration's key;
    // the checked graph query never exports and readmits an observed graph.
    canonical_declaration(facts, value, actual, context, &mut WorkLimit::new(16384))
        .map(|source| source.map(|(key, _)| key))
}

fn canonical_declaration(
    facts: &SemanticFacts,
    value: &Value,
    actual: &Expr,
    context: InvocationContext,
    work: &mut WorkLimit,
) -> Result<
    Option<(
        crate::sema::effect_identity::ArgumentKey,
        crate::sema::context::FrozenEnvironment,
    )>,
    String,
> {
    work.charge(1).map_err(|error| error.to_string())?;
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
    let names = source::NameIndex::new(facts)?;
    let Some(identity) = names.direct_identity(context.owner, source_id)? else {
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
        .filter(|observation| {
            observation.context == context
                && observation.identity == name
                && observation.cause == value.cause
                && facts
                    .expressions
                    .get(observation.expression)
                    .is_some_and(|fact| fact.source_id == Some(source_id) && fact.value == *value)
        });
    let observation = matching
        .next()
        .ok_or("canonical builtin Source lost its physical observation")?;
    if matching.next().is_some()
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
    let key = builtin_source_types::source_key(&observation.full_header)
        .ok_or("canonical builtin Source header is not complete")?;
    Ok(Some((key, observation.environment.clone())))
}
#[path = "builtin_source_syntax.rs"]
mod source;
