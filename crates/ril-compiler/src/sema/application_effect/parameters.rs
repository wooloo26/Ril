//! A parameter can be received while preparing defaults, before its callable
//! body exists. Derive those scopes from actual application/default receipts.
use super::*;
use crate::hir::nodes::{self as hir, HirProgram};
use crate::sema::{
    default_uses::{ArgumentSource, DefaultOrigin},
    model::{BindingInfo, Callable},
};
use std::collections::BTreeMap;

struct Preparation<'a> {
    context: InvocationContext,
    source: ExprId,
    event: CopyCallEventId,
    slots: &'a [ArgumentSource],
    defaults: BTreeMap<crate::sema::default_uses::DefaultUseId, usize>,
}

pub(super) struct Preparations<'a> {
    scopes: BTreeMap<ScopeId, Preparation<'a>>,
    /// Earliest default that physically reads each prepared parameter. An
    /// unrelated later default never authorizes a forward reference here.
    reads: BTreeMap<usize, usize>,
}

fn charge(work: &mut usize, count: usize) -> Result<(), String> {
    *work = work
        .checked_sub(count)
        .ok_or_else(|| "parameter activation coverage exceeds its work bound".to_owned())?;
    Ok(())
}

impl<'a> Preparations<'a> {
    pub(super) fn new(facts: &'a SemanticFacts, work: &mut usize) -> Result<Self, String> {
        let mut result = Self {
            scopes: BTreeMap::new(),
            reads: BTreeMap::new(),
        };
        if facts.default_uses.is_empty() {
            return Ok(result);
        }
        let mut arguments = BTreeMap::new();
        charge(work, facts.call_arguments.len())?;
        for row in &facts.call_arguments {
            if arguments.insert(row.source_event, row).is_some() {
                return Err("parameter preparation has duplicate application slots".into());
            }
        }
        for receipt in &facts.default_uses {
            charge(work, 1)?;
            let (
                Some(ril_compiler_core::ids::CallableOwner::Lambda(site)),
                DefaultOrigin::Call(event),
            ) = (receipt.owner, receipt.origin)
            else {
                continue;
            };
            let original = facts
                .copy_call_events
                .get(event.0 as usize)
                .filter(|row| row.id == event)
                .ok_or_else(|| "default preparation lost its application event".to_owned())?;
            let callee = original
                .callee_expression
                .and_then(|index| {
                    facts
                        .expressions
                        .get(index)
                        .zip(facts.evaluations.get(index))
                })
                .ok_or_else(|| "default preparation lost its physical callee".to_owned())?;
            let [Callable::Closure(closure)] = callee.0.value.callables.as_slice() else {
                return Err("default preparation has no unique actual lambda".into());
            };
            let closure = facts
                .closures
                .get(*closure)
                .filter(|closure| closure.site == Some(site))
                .ok_or_else(|| "default preparation borrowed another lambda object".to_owned())?;
            let source = closure
                .hir_id
                .ok_or_else(|| "default lambda has no HIR declaration".to_owned())?;
            let Some(hir::Expr {
                kind: hir::ExprKind::Lambda { parameters, .. },
                ..
            }) = facts
                .semantic_hir
                .as_deref()
                .and_then(|hir| hir.expression(source))
            else {
                return Err("default lambda has no original HIR header".into());
            };
            let syntax = parameters
                .get(receipt.parameter as usize)
                .and_then(|parameter| parameter.default)
                .ok_or_else(|| {
                    "default preparation has no original parameter expression".to_owned()
                })?;
            let root = receipt
                .result_expression
                .and_then(|index| {
                    facts
                        .expressions
                        .get(index)
                        .zip(facts.evaluations.get(index))
                })
                .ok_or_else(|| "default preparation lost its root occurrence".to_owned())?;
            let row = arguments
                .get(&event)
                .ok_or_else(|| "default preparation has no actual slots".to_owned())?;
            let mut context = receipt.caller;
            context.owner = receipt.owner;
            let mut evaluation = context;
            evaluation.default_use = Some(receipt.id);
            if root.0.source_id != Some(syntax)
                || root.1.context != evaluation
                || callee.1.context != receipt.caller
                || facts.scopes.parent(&root.1.scope) != Some(&callee.1.scope)
                || row.slots.get(receipt.parameter as usize)
                    != Some(&ArgumentSource::Default(receipt.id))
            {
                return Err(
                    "default parameter preparation borrowed another scope or occurrence".into(),
                );
            }
            let prepared = Preparation {
                context,
                source,
                event,
                slots: &row.slots,
                defaults: BTreeMap::new(),
            };
            charge(work, 1)?;
            let previous = if let Some(previous) = result.scopes.get_mut(&root.1.scope) {
                if previous.context != context
                    || previous.source != source
                    || previous.event != event
                {
                    return Err(
                        "one parameter scope borrowed unrelated default applications".into(),
                    );
                }
                previous
            } else {
                result.scopes.entry(root.1.scope).or_insert(prepared)
            };
            if previous
                .defaults
                .insert(receipt.id, receipt.parameter as usize)
                .is_some()
            {
                return Err("default preparation repeats one receipt identity".into());
            }
        }
        for (value, evaluation) in facts.expressions.iter().zip(&facts.evaluations) {
            charge(work, 1)?;
            let Some(prepared) = result.scopes.get(&evaluation.scope) else {
                continue;
            };
            let Some(hir::Expr {
                kind: hir::ExprKind::Name(name),
                ..
            }) = value
                .source_id
                .and_then(|id| facts.semantic_hir.as_deref()?.expression(id))
            else {
                continue;
            };
            charge(work, value.value.sources.len())?;
            for &id in &value.value.sources {
                let Some(binding) = facts.bindings.get(id).filter(|binding| {
                    binding.parameter && binding.owner == evaluation.scope && binding.name == *name
                }) else {
                    continue;
                };
                if binding.context != prepared.context {
                    return Err("default read borrowed another parameter introduction".into());
                }
                let index = evaluation
                    .context
                    .default_use
                    .and_then(|id| prepared.defaults.get(&id))
                    .ok_or_else(|| {
                        "prepared parameter read has no matching default occurrence".to_owned()
                    })?;
                result
                    .reads
                    .entry(id)
                    .and_modify(|first| *first = (*first).min(*index))
                    .or_insert(*index);
            }
        }
        Ok(result)
    }

    pub(super) fn accepts(
        &self,
        id: usize,
        binding: &BindingInfo,
        source: ExprId,
        hir: &HirProgram,
        work: &mut usize,
    ) -> Result<bool, String> {
        let Some(prepared) = self.scopes.get(&binding.owner) else {
            return Ok(false);
        };
        if prepared.context != binding.context || prepared.source != source {
            return Ok(false);
        }
        let Some(hir::Expr {
            kind: hir::ExprKind::Lambda { parameters, .. },
            ..
        }) = hir.expression(source)
        else {
            return Ok(false);
        };
        for (index, parameter) in parameters.iter().enumerate() {
            if self.reads.get(&id).is_some_and(|first| index >= *first) {
                break;
            }
            charge(work, 1)?;
            let mut pending = vec![parameter.pattern];
            while let Some(pattern) = pending.pop() {
                if Some(pattern) == binding.pattern {
                    return Ok(prepared
                        .slots
                        .get(index)
                        .is_some_and(|slot| *slot != ArgumentSource::Missing));
                }
                match &hir
                    .pattern(pattern)
                    .ok_or_else(|| "parameter HIR pattern is absent".to_owned())?
                    .kind
                {
                    hir::PatternKind::Mode { pattern, .. } => {
                        charge(work, 1)?;
                        pending.push(*pattern);
                    }
                    hir::PatternKind::Tuple(items) | hir::PatternKind::Alternative(items) => {
                        charge(work, items.len())?;
                        pending.extend(items)
                    }
                    hir::PatternKind::Record { fields, .. } => {
                        charge(work, fields.len())?;
                        pending.extend(fields.iter().map(|field| field.pattern))
                    }
                    hir::PatternKind::Constructor { arguments, .. } => {
                        charge(work, arguments.len())?;
                        pending.extend(arguments);
                    }
                    _ => {}
                }
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_later_default_cannot_authorize_an_earlier_forward_parameter_read() {
        let source = ril_test::case_source(
            "tests/regressions/evaluation-identity.ril::closure-default-lexical-environment",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let prepared = Preparations::new(facts, &mut 4096).unwrap();
        let scope = facts.evaluations[facts.default_uses[0].result_expression.unwrap()].scope;
        let (id, first) = facts
            .bindings
            .iter()
            .enumerate()
            .find(|(_, binding)| {
                binding.parameter && binding.name == "first" && binding.owner == scope
            })
            .unwrap();
        let third = facts
            .bindings
            .iter()
            .find(|binding| binding.parameter && binding.name == "third" && binding.owner == scope)
            .unwrap();
        let hir::LexicalOwner::Lambda(source) =
            hir.pattern(first.pattern.unwrap()).unwrap().info.owner
        else {
            panic!("original lambda parameter")
        };
        assert!(prepared.accepts(id, first, source, hir, &mut 4096).unwrap());
        let mut changed = first.clone();
        changed.pattern = third.pattern;
        assert!(
            !prepared
                .accepts(id, &changed, source, hir, &mut 4096)
                .unwrap()
        );
    }
}
