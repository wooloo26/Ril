//! Explicit application and resumption inputs share the graph receiving
//! relation. Expected views come from the original operation declaration;
//! actual views come from the original physical operand before ascription.
use super::*;
use crate::hir::nodes as hir;
use crate::sema::{
    effect_identity::ArgumentKey,
    model::Callable,
    source_reception::{self, Construction},
    source_types::WorkLimit,
};
use ril_compiler_core::ids::{ActivationEpochId, ExprId};

fn receive(
    facts: &crate::sema::SemanticFacts,
    expected: &ArgumentKey,
    input: (Option<ArgumentKey>, Construction),
) -> Result<(), String> {
    let (actual, fresh) = input;
    if let Some(answer) = source_reception::empty_context(expected, &fresh, &mut 4096) {
        return answer
            .then_some(())
            .ok_or_else(|| "empty receiver input differs from its declared Source view".into());
    }
    let actual = actual.ok_or("receiver input has no complete original Source view")?;
    let actual = crate::sema::source_types::declarations::expanded_key(
        &actual,
        facts
            .semantic_hir
            .as_deref()
            .ok_or("receiver input has no canonical HIR")?,
        &mut WorkLimit::new(16384),
    )
    .map_err(|error| format!("receiver input declaration: {error}"))?;
    match source_reception::compatible(expected, &actual, Some(&fresh), &mut 16384) {
        Some(true) => Ok(()),
        Some(false) => Err("receiver input differs from its declared complete Source view".into()),
        None => Err("receiver input has an unresolved Source obligation".into()),
    }
}

pub(crate) fn validate(facts: &crate::sema::SemanticFacts) -> Result<(), String> {
    let frames = FrameIndex::new(facts)?;
    let sources = crate::sema::record_bound_validation::OriginalOperandSources::new(facts)?;
    let mut preparations = BTreeMap::new();
    for row in &facts.call_arguments {
        if preparations.insert(row.source_event, row).is_some() {
            return Err("receiver input has duplicate application preparations".into());
        }
    }
    for event in &facts.copy_call_events {
        let Some(index) = event.callee_expression else {
            continue;
        };
        let callee = facts
            .expressions
            .get(index)
            .ok_or("operation receiver callee is outside its arena")?;
        let [Callable::Builtin(name)] = callee.value.callables.as_slice() else {
            continue;
        };
        let Some(operation) = facts.operations.get(name) else {
            continue;
        };
        let preparation = preparations
            .get(&event.id)
            .ok_or("operation input has no original application preparation")?;
        if !preparation.evaluation_complete {
            continue;
        }
        let signature = frames.signature(
            operation,
            callee
                .source_id
                .ok_or("operation input has no original selector")?,
            facts
                .evaluations
                .get(index)
                .ok_or("operation input callee has no actual context")?
                .context,
        )?;
        let ArgumentKey::Callable { parameters, .. } = signature.expanded else {
            return Err("operation input lost its Source signature".into());
        };
        if parameters.len() != preparation.slots.len() {
            return Err("operation input changed the original parameter arity".into());
        }
        for (slot, (_, expected)) in parameters.iter().enumerate() {
            receive(facts, expected, sources.input(event.id, slot as u32)?)?;
        }
    }
    let mut children = BTreeMap::<(ActivationEpochId, ExprId), Vec<_>>::new();
    for activation in &facts.activations {
        if activation.kind == crate::sema::application_effect::ActivationKind::Expression
            && let (Some(parent), Some(source)) = (activation.parent, activation.source)
        {
            children
                .entry((parent, source))
                .or_default()
                .push(activation);
        }
    }
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or("receiver inputs have no canonical HIR")?;
    for activation in &facts.activations {
        if activation.kind != crate::sema::application_effect::ActivationKind::ControlTransfer {
            continue;
        }
        let Some(hir::Expr {
            kind:
                hir::ExprKind::Control {
                    operation: ril_syntax::ast::ControlOperation::Resume,
                    value,
                },
            ..
        }) = activation.source.and_then(|id| hir.expression(id))
        else {
            return Err("resumption transfer lost its original HIR control node".into());
        };
        let frame = frames
            .operation(activation.scope)?
            .ok_or("resumption input has no actual operation receiver")?;
        if frame.entry.context != activation.context {
            return Err("resumption input belongs to another operation activation".into());
        }
        let signature = frames.receiver_signature(&frame)?;
        let ArgumentKey::Callable { result, .. } = signature.expanded else {
            return Err("resumption input has no complete operation result Source".into());
        };
        let input = if let Some(source) = value {
            let Some(nodes) = children.get(&(activation.id, *source)) else {
                return Err("resumption operand has no original child evaluation".into());
            };
            let [child] = nodes.as_slice() else {
                return Err("resumption input borrowed an ambiguous child occurrence".into());
            };
            let observation = child
                .result
                .ok_or("resumption input has no completed offered value")?
                .0 as usize;
            if facts
                .expressions
                .get(observation)
                .is_some_and(|fact| fact.value.ty == crate::sema::model::Ty::Never)
            {
                continue;
            }
            sources.observed(*source, observation)?
        } else {
            (Some(ArgumentKey::Tuple(vec![])), Construction::Opaque)
        };
        receive(facts, &result, input)?;
    }
    Ok(())
}
