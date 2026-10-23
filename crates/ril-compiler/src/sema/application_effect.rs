//! Owned application observations. Source identity, evaluation identity and
//! allocation recency are recorded together, without rewriting past values.
use super::context::FrozenEnvId;
use super::source_types::{SourceTypesError, WorkLimit};
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
use std::sync::Arc;
mod activations;
mod entries;
pub(crate) mod generated_entries;
#[path = "named_declarations.rs"]
mod named_declarations;
mod signature_inputs;
pub use activations::{ActivationKind, EvaluationActivation};
mod parameters;
pub(crate) use entries::record_field_source;
pub use entries::{
    CallableEntry, EntryArgument, EntryOrigin, InputOrigin, ScalarInput, ScopeInput,
};
pub(crate) use entries::{ScalarSource, record_callback};
pub(crate) use signature_inputs::{
    AuthenticatedSignatureInput, closure_signature_assumption, signature_assumption,
};
pub use signature_inputs::{SignatureFormal, SignatureProbeSource};

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
    /// Actual evaluation context, distinct from a declaration's Source view.
    /// None is an explicit missing environment obligation, never a default.
    pub environment: Option<FrozenEnvId>,
}

/// Owned emitter output before a physical occurrence and its sole packet exist.
/// This is not retained evidence and cannot supply a Source or birth receipt.
pub(crate) struct ObservationInput {
    pub(crate) source_id: Option<ExprId>,
    pub(crate) allocation_epoch: usize,
    pub(crate) span: Span,
    pub(crate) value: super::model::Value,
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
    work_owner: Arc<()>,
    pub exhausted: bool,
}

/// Linear temporary credit, removed from the recorder before a query starts.
/// The owner only authenticates refunds; it supplies no semantic authority.
pub(crate) struct WorkLease {
    owner: Arc<()>,
    issued: usize,
    work: WorkLimit,
}
impl WorkLease {
    pub(crate) fn work(&mut self) -> &mut WorkLimit {
        &mut self.work
    }
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
            work_owner: Arc::new(()),
            exhausted: false,
        }
    }
}

impl ApplicationEffectDomain {
    /// Reserve at most the query's old local cap. Nested recorder work can
    /// spend only the unleased remainder, never the same credit twice.
    pub(crate) fn lease_work(&mut self, cap: usize) -> WorkLease {
        if self.exhausted {
            self.remaining = 0;
        }
        let issued = self.remaining.min(cap);
        self.remaining -= issued;
        WorkLease {
            owner: self.work_owner.clone(),
            issued,
            work: WorkLimit::new(issued),
        }
    }

    /// Consume the lease exactly once. Only its unused, original credit may
    /// return, and an exhausted recorder can never regain spending power.
    pub(crate) fn return_work(&mut self, lease: WorkLease) -> Result<(), SourceTypesError> {
        if !Arc::ptr_eq(&self.work_owner, &lease.owner) || lease.work.remaining() > lease.issued {
            self.exhausted = true;
            self.remaining = 0;
            return Err(SourceTypesError::ForeignIdentity);
        }
        if self.exhausted {
            self.remaining = 0;
            return Err(SourceTypesError::BudgetExceeded);
        }
        let Some(remaining) = self.remaining.checked_add(lease.work.remaining()) else {
            self.exhausted = true;
            self.remaining = 0;
            return Err(SourceTypesError::BudgetExceeded);
        };
        self.remaining = remaining;
        Ok(())
    }

    /// Pure HIR cursor queries spend the same monotone work allowance as
    /// application recording. A failed query must be handled by its caller;
    /// this interface never grants a fresh allowance for another prefix.
    pub(crate) fn with_work<R>(&mut self, query: impl FnOnce(&mut usize) -> R) -> R {
        if self.exhausted {
            self.remaining = 0;
        }
        query(&mut self.remaining)
    }

    /// Borrow immutable evaluation rows together with their shared allowance.
    /// Queries may copy or transport a row only after charging that allowance.
    pub(crate) fn with_evaluation_work<R>(
        &mut self,
        query: impl FnOnce(
            &[ExpressionFact],
            &[EvaluationRecord],
            &[EvaluationActivation],
            &mut usize,
        ) -> R,
    ) -> R {
        if self.exhausted {
            self.remaining = 0;
        }
        query(
            &self.expressions,
            &self.evaluations,
            &self.activations,
            &mut self.remaining,
        )
    }

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
        if self.exhausted {
            self.remaining = 0;
            return false;
        }
        let Some(remaining) = self.remaining.checked_sub(count) else {
            self.exhausted = true;
            self.remaining = 0;
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
        create: impl FnOnce() -> ObservationInput,
        context: InvocationContext,
        scope: ScopeId,
        environment: Option<FrozenEnvId>,
        argument_of: Option<(CopyCallEventId, u32)>,
    ) -> Option<usize> {
        if !self.admit(3) {
            return None;
        }
        let fact = create();
        let activation =
            self.allocate_activation(fact.source_id, scope, context, ActivationKind::Emission)?;
        self.record_observation(activation, fact, context, scope, environment, argument_of)
    }

    pub(crate) fn observe_in(
        &mut self,
        activation: ActivationEpochId,
        create: impl FnOnce() -> ObservationInput,
        context: InvocationContext,
        scope: ScopeId,
        environment: Option<FrozenEnvId>,
        argument_of: Option<(CopyCallEventId, u32)>,
    ) -> Option<usize> {
        // Charge before copying the value or growing any recorder arena.
        let Some(remaining) = self.remaining.checked_sub(1) else {
            self.exhausted = true;
            return None;
        };
        self.remaining = remaining;
        let fact = create();
        self.record_observation(activation, fact, context, scope, environment, argument_of)
    }

    fn record_observation(
        &mut self,
        activation: ActivationEpochId,
        fact: ObservationInput,
        context: InvocationContext,
        scope: ScopeId,
        environment: Option<FrozenEnvId>,
        argument_of: Option<(CopyCallEventId, u32)>,
    ) -> Option<usize> {
        // The immutable birth and physical packet each allocate one Arc. Keep
        // their admission in this recorder's original total allowance.
        if !self.admit(3) {
            return None;
        }
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
        let record = EvaluationRecord {
            id: EvaluationOccurrenceId(ordinal),
            identity: fact
                .source_id
                .map(|source| OccurrenceIdentity { source, activation }),
            scope,
            context,
            allocation_epoch: fact.allocation_epoch,
            environment,
        };
        let packet = Arc::new(super::evaluated::EvaluatedValue::observed(
            fact.value,
            ordinal as usize,
            &record,
        ));
        self.evaluations.push(record);
        self.contexts.push(InvocationExpression {
            context,
            expression: ordinal as usize,
            argument_of,
        });
        self.expressions.push(ExpressionFact {
            source_id: fact.source_id,
            allocation_epoch: fact.allocation_epoch,
            span: fact.span,
            value: super::evaluated::PhysicalValue::from_packet(packet),
        });
        Some(ordinal as usize)
    }

    pub(crate) fn packet_at(
        &mut self,
        observation: usize,
    ) -> Result<Arc<super::evaluated::EvaluatedValue>, SourceTypesError> {
        if !self.admit(2) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let record = self
            .evaluations
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let fact = self
            .expressions
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let packet = fact.value.packet();
        let birth = packet.birth_coordinates();
        if record.id.0 as usize != observation
            || birth.observation != Some(observation)
            || birth.identity != record.identity
            || birth.context != Some(record.context)
            || birth.environment != record.environment
            || birth.allocation_epoch != record.allocation_epoch
            || packet.current_epoch() != record.allocation_epoch
            || fact.allocation_epoch != record.allocation_epoch
            || fact.source_id != record.identity.map(|identity| identity.source)
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(packet.clone())
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
    let mut binding_work = 1_000_000usize;
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
        let environment = record.environment.ok_or_else(|| {
            (
                value.span,
                "evaluation has no original frozen environment".into(),
            )
        })?;
        let mut environment_work = WorkLimit::new(binding_work);
        let resolved = facts
            .source_types
            .environment(environment, &mut environment_work);
        binding_work = environment_work.remaining();
        resolved.map_err(|error| {
            (
                value.span,
                format!("evaluation environment cannot be verified: {error}"),
            )
        })?;
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
    named_declarations::validate(facts, &mut binding_work)
        .map_err(|message| (fallback, message))?;
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
    fn leased_capture_and_nested_work_spend_one_total_allowance() {
        let mut domain = ApplicationEffectDomain {
            remaining: 100,
            ..Default::default()
        };
        let mut lease = domain.lease_work(16);
        assert_eq!(domain.remaining, 84);
        assert_eq!(lease.work().remaining(), 16);
        lease.work().charge(9).unwrap();
        assert!(domain.admit(11));
        domain.return_work(lease).unwrap();
        assert_eq!(domain.remaining, 80);
        assert!(!domain.exhausted);

        let mut outer = domain.lease_work(20);
        let mut inner = domain.lease_work(13);
        outer.work().charge(3).unwrap();
        inner.work().charge(5).unwrap();
        domain.return_work(outer).unwrap();
        domain.return_work(inner).unwrap();
        assert_eq!(domain.remaining, 72);
    }

    #[test]
    fn work_refunds_cannot_restore_exhaustion_or_cross_recorder_ownership() {
        let mut domain = ApplicationEffectDomain {
            remaining: 7,
            ..Default::default()
        };
        let lease = domain.lease_work(16384);
        assert_eq!(domain.remaining, 0);
        assert!(!domain.admit(1));
        assert_eq!(
            domain.return_work(lease),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert!(domain.exhausted);
        assert_eq!(domain.remaining, 0);
        let mut empty = domain.lease_work(16384);
        assert_eq!(empty.work().remaining(), 0);
        assert_eq!(
            domain.return_work(empty),
            Err(SourceTypesError::BudgetExceeded)
        );

        let mut first = ApplicationEffectDomain {
            remaining: 12,
            ..Default::default()
        };
        let mut other = ApplicationEffectDomain {
            remaining: 19,
            ..Default::default()
        };
        let lease = first.lease_work(8);
        assert_eq!(
            other.return_work(lease),
            Err(SourceTypesError::ForeignIdentity)
        );
        assert_eq!(first.remaining, 4);
        assert!(other.exhausted);
        assert_eq!(other.remaining, 0);
    }

    #[test]
    fn failed_admission_cannot_leave_smaller_requests_spendable() {
        let mut domain = ApplicationEffectDomain {
            remaining: 6,
            ..Default::default()
        };
        assert!(!domain.admit(7));
        assert!(domain.exhausted);
        assert_eq!(domain.remaining, 0);
        assert!(!domain.admit(1));
        assert!(!domain.admit(0));
        assert_eq!(domain.remaining, 0);
    }

    #[test]
    fn capture_budget_failure_remains_distinct_from_unknown_and_uncaptured_source() {
        use crate::sema::{
            context::FrozenEnvironment,
            evaluated::{CapturedSource, EvaluatedValue},
            model::{Ty, Value},
            source_types::LiveSourceTypes,
            source_types_ref::SourceTypesRef,
        };
        use ril_compiler_core::diagnostic::CauseId;
        let mut types = LiveSourceTypes::default();
        let value = || Value::scalar(Ty::Unit, None, CauseId(0));
        let uncaptured = EvaluatedValue::new(value(), 0);
        assert!(matches!(
            uncaptured.input_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::SourceNotCaptured)
        ));
        let mut domain = ApplicationEffectDomain {
            remaining: 6,
            ..Default::default()
        };
        let mut lease = domain.lease_work(16384);
        let failure = lease.work().charge(7).unwrap_err();
        let mut failed = EvaluatedValue::new(value(), 0);
        failed.capture_birth_source(Err(failure), None).unwrap();
        domain.return_work(lease).unwrap();
        assert_eq!(
            domain.remaining, 6,
            "a rejected preflight allocated and consumed nothing"
        );
        assert!(matches!(
            failed.input_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut unknown = EvaluatedValue::new(value(), 0);
        let environment = FrozenEnvironment::default();
        let environment_id = types
            .intern_environment(environment, &mut WorkLimit::new(4096))
            .unwrap();
        unknown
            .capture_birth_source(Ok(CapturedSource::Unknown(environment_id)), None)
            .unwrap();
        let source = unknown
            .input_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
            .unwrap();
        assert!(source.schema.is_none());
        assert_eq!(source.environment.id(), environment_id);
        let mut attempted = EvaluatedValue::new(value(), 0);
        let lease = domain.lease_work(16384);
        assert!(!domain.admit(1));
        let error = domain.return_work(lease).unwrap_err();
        attempted
            .capture_birth_source(Err(error.clone()), None)
            .unwrap();
        attempted.fail_current_source(error);
        let source = unknown
            .birth_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096))
            .unwrap();
        assert!(
            source.schema.is_none(),
            "a genuinely unknown birth remains distinct from failed capture"
        );
        assert_eq!(source.environment.id(), environment_id);
        assert!(matches!(
            attempted.birth_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(attempted.has_captured_source());
        assert!(matches!(
            attempted.input_source(SourceTypesRef::Live(&types), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

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
                None,
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
