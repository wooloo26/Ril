//! Owned application observations. Source identity, evaluation identity and
//! allocation recency are recorded together, without rewriting past values.
use super::{
    ExpressionFact, SemanticFacts,
    copy_contract::CopyCallEventId,
    effect_identity::{InvocationContext, InvocationExpression},
    facts::ScopeId,
};
use ril_compiler_core::{
    ids::{ActivationEpochId, CallableOwner, ClosureSiteId, EvaluationOccurrenceId, ExprId},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};
mod activations;
mod entries;
pub use activations::{ActivationKind, EvaluationActivation};
mod parameters;
pub(crate) use entries::record_field_source;
pub(crate) use entries::signature_assumption;
pub use entries::{CallableEntry, EntryArgument, EntryOrigin, InputOrigin, ScalarInput};
pub(crate) use entries::{ScalarSource, record_callback};

/// The static node and its actual evaluation activation form one occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct OccurrenceIdentity {
    pub source: ExprId,
    pub activation: ActivationEpochId,
}

#[derive(Debug, Clone)]
pub struct EvaluationRecord {
    pub id: EvaluationOccurrenceId,
    pub identity: Option<OccurrenceIdentity>,
    pub scope: ScopeId,
    pub context: InvocationContext,
    pub allocation_epoch: usize,
}

pub(crate) struct ApplicationEffectDomain {
    pub activations: Vec<EvaluationActivation>,
    active: Vec<ActivationEpochId>,
    calls: Vec<std::sync::Arc<EntryOrigin>>,
    pub expressions: Vec<ExpressionFact>,
    pub contexts: Vec<InvocationExpression>,
    pub evaluations: Vec<EvaluationRecord>,
    pub closure_sites: Vec<super::model::ClosureSite>,
    closure_sources: BTreeMap<(CallableOwner, ExprId), ClosureSiteId>,
    by_source: BTreeMap<(ExprId, InvocationContext), Vec<usize>>,
    remaining: usize,
    pub exhausted: bool,
}

impl Default for ApplicationEffectDomain {
    fn default() -> Self {
        Self {
            activations: Vec::new(),
            active: Vec::new(),
            calls: Vec::new(),
            expressions: Vec::new(),
            contexts: Vec::new(),
            evaluations: Vec::new(),
            closure_sites: Vec::new(),
            closure_sources: BTreeMap::new(),
            by_source: BTreeMap::new(),
            remaining: 4_000_000,
            exhausted: false,
        }
    }
}

impl ApplicationEffectDomain {
    pub(crate) fn enter_call(
        &mut self,
        origin: EntryOrigin,
    ) -> Option<std::sync::Arc<EntryOrigin>> {
        if !self.admit(2) {
            return None;
        }
        let origin = std::sync::Arc::new(origin);
        self.calls.push(origin.clone());
        Some(origin)
    }
    pub(crate) fn leave_call(&mut self, origin: &std::sync::Arc<EntryOrigin>) {
        let active = self.calls.pop().expect("balanced call entry");
        assert!(std::sync::Arc::ptr_eq(&active, origin));
    }
    pub(crate) fn current_entry(&self) -> Option<&std::sync::Arc<EntryOrigin>> {
        self.calls.last()
    }
    pub(crate) fn current_call_event(&self) -> Option<CopyCallEventId> {
        match self.current_entry()?.as_ref() {
            EntryOrigin::Application(id) => Some(*id),
            _ => None,
        }
    }
    pub(crate) fn enclosing_application(&self) -> Option<CopyCallEventId> {
        self.calls
            .iter()
            .rev()
            .find_map(|origin| match origin.as_ref() {
                EntryOrigin::Application(id) => Some(*id),
                _ => None,
            })
    }
    pub(crate) fn admit(&mut self, count: usize) -> bool {
        let Some(remaining) = self.remaining.checked_sub(count) else {
            self.exhausted = true;
            return false;
        };
        self.remaining = remaining;
        true
    }

    pub(crate) fn closure_site(
        &mut self,
        owner: CallableOwner,
        source: ExprId,
        span: Span,
    ) -> Option<ClosureSiteId> {
        if let Some(&site) = self.closure_sources.get(&(owner, source)) {
            return Some(site);
        }
        self.remaining = self.remaining.checked_sub(1).or_else(|| {
            self.exhausted = true;
            None
        })?;
        let id = ClosureSiteId(u32::try_from(self.closure_sites.len()).ok()?);
        self.closure_sources.insert((owner, source), id);
        self.closure_sites.push(super::model::ClosureSite {
            id,
            owner,
            source,
            span,
        });
        Some(id)
    }

    pub(crate) fn observe(
        &mut self,
        create: impl FnOnce() -> ExpressionFact,
        context: InvocationContext,
        scope: ScopeId,
        argument_of: Option<(CopyCallEventId, u32)>,
    ) -> Option<usize> {
        if !self.admit(3) {
            return None;
        }
        let fact = create();
        let activation =
            self.allocate_activation(fact.source_id, scope, context, ActivationKind::Emission)?;
        self.record_observation(activation, fact, context, scope, argument_of)
    }

    pub(crate) fn observe_in(
        &mut self,
        activation: ActivationEpochId,
        create: impl FnOnce() -> ExpressionFact,
        context: InvocationContext,
        scope: ScopeId,
        argument_of: Option<(CopyCallEventId, u32)>,
    ) -> Option<usize> {
        // Charge before copying the value or growing any recorder arena.
        let Some(remaining) = self.remaining.checked_sub(1) else {
            self.exhausted = true;
            return None;
        };
        self.remaining = remaining;
        let fact = create();
        self.record_observation(activation, fact, context, scope, argument_of)
    }

    fn record_observation(
        &mut self,
        activation: ActivationEpochId,
        fact: ExpressionFact,
        context: InvocationContext,
        scope: ScopeId,
        argument_of: Option<(CopyCallEventId, u32)>,
    ) -> Option<usize> {
        let ordinal = self.expressions.len() as u32;
        let frame = self.activations.get_mut(activation.0 as usize)?;
        if frame.id != activation
            || frame.source != fact.source_id
            || frame.scope != scope
            || frame.context != context
            || frame.result.is_some()
        {
            self.exhausted = true;
            return None;
        }
        frame.result = Some(EvaluationOccurrenceId(ordinal));
        if frame.kind == ActivationKind::Emission {
            frame.end_expression = Some(ordinal as usize + 1);
        }
        if let Some(source) = fact.source_id {
            self.by_source
                .entry((source, context))
                .or_default()
                .push(ordinal as usize);
        }
        self.evaluations.push(EvaluationRecord {
            id: EvaluationOccurrenceId(ordinal),
            identity: fact
                .source_id
                .map(|source| OccurrenceIdentity { source, activation }),
            scope,
            context,
            allocation_epoch: fact.allocation_epoch,
        });
        self.contexts.push(InvocationExpression {
            context,
            expression: ordinal as usize,
            argument_of,
        });
        self.expressions.push(fact);
        Some(ordinal as usize)
    }

    pub(crate) fn occurrences(&self, source: ExprId, context: InvocationContext) -> &[usize] {
        self.by_source
            .get(&(source, context))
            .map_or(&[], Vec::as_slice)
    }
}

/// Coverage comes from the physical value arena, independently of whether a
/// producer left any occurrence records. Removing the whole ledger fails.
pub(crate) fn validate(facts: &SemanticFacts) -> Result<(), (Span, String)> {
    let fallback = facts
        .expressions
        .first()
        .map(|fact| fact.span)
        .unwrap_or(Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        });
    if facts.evaluations.len() != facts.expressions.len()
        || facts.invocation_expressions.len() != facts.expressions.len()
        || facts.expressions.len() > 1_000_000
    {
        return Err((
            fallback,
            "evaluation arena has incomplete occurrence coverage".into(),
        ));
    }
    let mut identities = BTreeSet::new();
    activations::validate(facts).map_err(|message| (fallback, message))?;
    entries::validate(facts).map_err(|message| (fallback, message))?;
    super::scopes::validate(facts).map_err(|message| (fallback, message))?;
    super::scopes::validate_receptions(facts).map_err(|message| (fallback, message))?;
    let mut contexts = vec![None; facts.expressions.len()];
    for context in &facts.invocation_expressions {
        let Some(slot) = contexts.get_mut(context.expression) else {
            return Err((
                fallback,
                "evaluation context is outside the physical arena".into(),
            ));
        };
        if slot.replace(context).is_some() {
            return Err((
                fallback,
                "evaluation has duplicate physical contexts".into(),
            ));
        }
    }
    for (index, (record, value)) in facts.evaluations.iter().zip(&facts.expressions).enumerate() {
        let Some(identity) = record.identity else {
            return Err((value.span, "evaluation has no original HIR node".into()));
        };
        if record.id.0 as usize != index
            || Some(identity.source) != value.source_id
            || record.allocation_epoch != value.allocation_epoch
            || !facts.scopes.contains(&record.scope)
            || contexts[index].is_none_or(|context| context.context != record.context)
            || !identities.insert(identity)
            || facts
                .semantic_hir
                .as_ref()
                .is_none_or(|hir| hir.expression(identity.source).is_none())
        {
            return Err((
                value.span,
                "evaluation changed its node, activation, scope or birth epoch".into(),
            ));
        }
    }
    if facts.bindings.len() > 1_000_000 {
        return Err((
            fallback,
            "binding activation coverage exceeds its work bound".into(),
        ));
    }
    let observed_scopes: BTreeSet<_> = facts
        .evaluations
        .iter()
        .map(|record| record.scope)
        .collect();
    let mut observed_bindings = BTreeSet::<usize>::new();
    let mut binding_work = 1_000_000usize;
    for expression in &facts.expressions {
        binding_work = binding_work
            .checked_sub(expression.value.sources.len())
            .ok_or_else(|| {
                (
                    expression.span,
                    "binding observation coverage exceeds its work bound".into(),
                )
            })?;
        observed_bindings.extend(expression.value.sources.iter().copied());
    }
    let preparations = parameters::Preparations::new(facts, &mut binding_work)
        .map_err(|message| (fallback, message))?;
    binding_work = binding_work
        .checked_sub(facts.closures.len())
        .ok_or_else(|| {
            (
                fallback,
                "lambda declaration coverage exceeds its work bound".into(),
            )
        })?;
    let closure_headers: BTreeSet<_> = facts
        .closures
        .iter()
        .filter_map(|closure| {
            Some((
                closure.hir_id?,
                closure
                    .site
                    .map(ril_compiler_core::ids::CallableOwner::Lambda),
            ))
        })
        .collect();
    let mut parameter_bindings = BTreeSet::new();
    for (id, binding) in facts
        .bindings
        .iter()
        .enumerate()
        .filter(|(_, binding)| binding.parameter)
    {
        let Some(hir) = facts.semantic_hir.as_deref() else {
            continue;
        };
        let Some(crate::hir::nodes::LexicalOwner::Lambda(source)) = binding
            .pattern
            .and_then(|pattern| hir.pattern(pattern))
            .map(|pattern| pattern.info.owner)
        else {
            continue;
        };
        binding_work = binding_work.checked_sub(1).ok_or_else(|| {
            (
                binding.span,
                "parameter identity coverage exceeds its work bound".into(),
            )
        })?;
        if !parameter_bindings.insert((binding.owner, binding.pattern)) {
            return Err((
                binding.span,
                "parameter activation has duplicate declaration bindings".into(),
            ));
        }
        // Preparing a lambda header can allocate formal anchors without
        // entering a body. Actual reads independently prevent relabelling an
        // entered parameter as one of these unused declaration anchors.
        if !observed_scopes.contains(&binding.owner)
            && !observed_bindings.contains(&id)
            && closure_headers.contains(&(source, binding.context.owner))
        {
            continue;
        }
        if preparations
            .accepts(id, binding, source, hir, &mut binding_work)
            .map_err(|message| (binding.span, message))?
        {
            continue;
        }
        let valid = binding
            .context
            .closure_invocation
            .and_then(|id| facts.closure_invocations.get(id.0 as usize))
            .is_some_and(|call| {
                Some(call.id) == binding.context.closure_invocation
                    && call.activation == Some(binding.owner)
                    && Some(call.closure) == binding.context.closure
                    && facts.closures.get(call.closure).is_some_and(|closure| {
                        closure.hir_id == Some(source)
                            && closure
                                .site
                                .map(ril_compiler_core::ids::CallableOwner::Lambda)
                                == binding.context.owner
                    })
            });
        if !valid {
            return Err((
                binding.span,
                "lambda binding lost its original declaration activation".into(),
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_closure_identity_ignores_equal_or_changed_diagnostic_spans() {
        let mut domain = ApplicationEffectDomain::default();
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 1,
            end: 2,
        };
        let owner = CallableOwner::Global;
        let first = domain.closure_site(owner, ExprId(1), span).unwrap();
        let second = domain.closure_site(owner, ExprId(2), span).unwrap();
        assert_ne!(first, second);
        let changed = Span {
            start: 99,
            end: 100,
            ..span
        };
        assert_eq!(domain.closure_site(owner, ExprId(1), changed), Some(first));
        assert_eq!(domain.closure_sites[first.0 as usize].span, span);
        assert_eq!(domain.closure_sites.len(), 2);
        domain.remaining = 0;
        assert_eq!(domain.closure_site(owner, ExprId(3), span), None);
        assert!(domain.exhausted);
        assert_eq!(domain.closure_sites.len(), 2);
    }

    #[test]
    fn exhausted_observation_budget_does_not_copy_or_allocate_evidence() {
        let mut domain = ApplicationEffectDomain {
            remaining: 2,
            ..Default::default()
        };
        let context = InvocationContext {
            invocation: None,
            owner: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        };
        assert_eq!(
            domain.observe(
                || panic!("copy ran before budget admission"),
                context,
                ScopeId(0),
                None
            ),
            None
        );
        assert!(domain.exhausted);
        assert!(domain.expressions.is_empty());
        assert!(domain.contexts.is_empty());
        assert!(domain.evaluations.is_empty());
    }
}
