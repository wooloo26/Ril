//! Independent checks on solved semantic structure. This token is not a
//! permission proof or a replay of historical heap disjointness/borrow authority.
use super::{
    SemanticFacts,
    facts::{Multiplicity, NodeId, OriginKind, Participant, ScopeId, Slot},
    model::{AccessFact, AccessOwners, Callable, Origins, Value},
    relations::{Atom, Condition},
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use std::collections::BTreeSet;

fn optional_representation_type(mut ty: &super::model::Ty) -> &super::model::Ty {
    while let super::model::Ty::Immutable(inner) = ty {
        ty = inner;
    }
    ty
}

fn optional_payload_type(ty: &super::model::Ty) -> Option<&super::model::Ty> {
    match optional_representation_type(ty) {
        super::model::Ty::Optional(payload) => Some(payload),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationIssueKind {
    MissingGlobalScope,
    InvalidScope(ScopeId),
    ScopeCycle(ScopeId),
    InvalidOrigin(NodeId),
    InvalidCause(CauseId),
    CauseTable,
    InvalidCondition(u32),
    InvalidPivot(u32),
    ContradictoryRelation(NodeId, NodeId),
    InvalidMultiplicity(NodeId),
    FieldGraphMismatch(NodeId, Slot),
    InvalidRoot(u32),
    InvalidBinding(usize),
    InvalidCallable(usize),
    InvalidLoan(u32),
    LoanCycle(u32),
    InvalidAllocationMove(usize),
    AccessEpoch {
        observed: usize,
        current: usize,
        final_epoch: usize,
    },
    OriginCoverage,
    OwnershipCoverage,
    EmptyKnownOwnership(NodeId),
    InvalidHandler(usize),
    MissingBoundaryEvidence,
    BoundaryCauseMismatch,
    ConcurrentIdentityShape,
    IncompleteParallelTermination,
    InvocationLoanEnd(String),
    ResumptionAnswer(String),
    SourceTypeWitness,
    BuiltinSource(String),
    GeneratedSource(String),
    StorageSource(String),
    EvaluationIdentity(String),
    ClosureActivation(String),
    StaticArgument(String),
    SymbolicRow(String),
    InvalidResultProducer(u32),
    InvalidOptionalTag(u32, String),
    RecordBound(String),
    ChannelMessage(String),
}

#[derive(Debug, Clone)]
pub struct ValidationIssue {
    pub kind: ValidationIssueKind,
    pub span: Option<Span>,
    pub cause: Option<CauseId>,
}

/// Only the named structural checks have passed. This does not establish any
/// new capability, reconstruct a missing boundary proof, or authorize lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValidatedStructure {
    pub allocation_epoch: usize,
    pub origins: usize,
    pub checked_accesses: usize,
}

pub fn solved_facts(facts: &SemanticFacts) -> Result<ValidatedStructure, Vec<ValidationIssue>> {
    let mut validator = Validator {
        facts,
        issues: vec![],
        checked_accesses: 0,
    };
    validator.structure();
    validator.boundaries();
    if let Err(message) = super::symbolic_rows::validate(facts) {
        validator.issue(ValidationIssueKind::SymbolicRow(message), None, None);
    }
    if let Err((span, message)) = super::application_effect::validate(facts) {
        validator.issue(
            ValidationIssueKind::EvaluationIdentity(message),
            Some(span),
            None,
        );
    }
    if let Err((span, cause, message)) = super::evaluation_identity::validate(facts) {
        validator.issue(
            ValidationIssueKind::EvaluationIdentity(message),
            Some(span),
            cause,
        );
    }
    if let Err((span, cause, message)) =
        super::record_bound_validation::validate_storage_sources(facts)
    {
        validator.issue(
            ValidationIssueKind::StorageSource(message),
            Some(span),
            cause,
        );
    }
    let mut closure_activations = std::collections::BTreeSet::new();
    if let Err(message) = super::record_bound_validation::validate_callable_inputs(facts) {
        validator.issue(ValidationIssueKind::ClosureActivation(message), None, None);
    }
    for invocation in &facts.closure_invocations {
        let complete = invocation.status == super::copy_contract::CopyInvocationStatus::Completed;
        if (complete && invocation.activation.is_none())
            || invocation.activation.is_some_and(|activation| {
                !closure_activations.insert(activation)
                    || activation == invocation.caller_activation
                    || !facts.scopes.contains(&activation)
                    || facts.scopes.parent(&activation) != Some(&invocation.caller_activation)
            })
        {
            validator.issue(
                ValidationIssueKind::ClosureActivation(
                    "closure entry lost its unique actual frame and caller scope".into(),
                ),
                Some(invocation.site),
                None,
            );
        }
    }
    if let Err((span, cause, message)) = super::checker::validate_generated_sources(facts) {
        validator.issue(
            ValidationIssueKind::GeneratedSource(message),
            Some(span),
            cause,
        );
    }
    if let Err((span, cause, message)) = super::checker::validate_builtin_source_observations(facts)
    {
        validator.issue(
            ValidationIssueKind::BuiltinSource(message),
            Some(span),
            Some(cause),
        );
    }
    if let Err((span, cause, message)) = super::record_bound_validation::validate(facts) {
        validator.issue(ValidationIssueKind::RecordBound(message), Some(span), cause);
    }
    if let Err((span, cause, message)) = super::channel_message_validation::validate(facts) {
        validator.issue(
            ValidationIssueKind::ChannelMessage(message),
            Some(span),
            cause,
        );
    }
    if let Err((span, message)) = super::static_argument_validation::validate(facts) {
        validator.issue(
            ValidationIssueKind::StaticArgument(message),
            Some(span),
            None,
        );
    }
    if let Err((span, cause)) = super::source_type_validation::validate(facts) {
        validator.issue(
            ValidationIssueKind::SourceTypeWitness,
            Some(span),
            Some(cause),
        );
    }
    for start in &facts.invocation_loan_starts {
        validator.scope(start.activation, false, Some(start.span));
        validator.value(&start.source, Some(start.span));
        validator.cause(start.cause, Some(start.span));
    }
    for end in &facts.invocation_loan_ends {
        validator.scope(end.activation, false, Some(end.span));
        validator.cause(end.cause, Some(end.span));
        for (loan, parents) in &end.loans {
            validator.participant(super::facts::Participant::Loan(*loan), Some(end.span));
            for parent in parents {
                validator.participant(*parent, Some(end.span));
            }
        }
    }
    if let Err((span, cause, message)) = super::invocation_loans::validate(facts) {
        validator.issue(
            ValidationIssueKind::InvocationLoanEnd(message),
            Some(span),
            cause,
        );
    }
    if let Err((span, cause, message)) = super::resumption::validate(facts) {
        validator.issue(
            ValidationIssueKind::ResumptionAnswer(message),
            Some(span),
            cause,
        );
    }
    if validator.issues.is_empty() {
        Ok(ValidatedStructure {
            allocation_epoch: facts.allocation_history.len(),
            origins: facts.heap.nodes.len(),
            checked_accesses: validator.checked_accesses,
        })
    } else {
        Err(validator.issues)
    }
}

struct Validator<'a> {
    facts: &'a SemanticFacts,
    issues: Vec<ValidationIssue>,
    checked_accesses: usize,
}
impl Validator<'_> {
    fn optional_tag_problem(
        &self,
        value: &Value,
        identity: ril_compiler_core::ids::OptionalTagId,
    ) -> Option<String> {
        let Some(tag) = self.facts.optional_tags.get(identity.0 as usize) else {
            return Some("tag has no arena entry".into());
        };
        if tag.id != identity {
            return Some("tag identity differs from its arena index".into());
        }
        if !self.cause_contains(value.cause, tag.cause) {
            return Some(format!(
                "value cause {} does not retain tag source cause {}",
                value.cause.0, tag.cause.0
            ));
        }
        if let Some(payload) = &value.option_payload
            && payload.ty != tag.payload_type
        {
            return Some(format!(
                "payload type {:?} differs from tag payload type {:?}",
                payload.ty, tag.payload_type
            ));
        }
        if let Some(payload) = optional_payload_type(&value.ty) {
            if payload != &tag.payload_type {
                return Some(format!(
                    "optional type payload {payload:?} differs from tag payload type {:?}",
                    tag.payload_type
                ));
            }
        } else if !matches!(
            optional_representation_type(&value.ty),
            super::model::Ty::Named(_)
                | super::model::Ty::Applied { .. }
                | super::model::Ty::Generic(_)
                | super::model::Ty::Projection { .. }
                | super::model::Ty::Unknown
        ) {
            return Some(format!(
                "tag was retained on a non-optional value of type {:?}",
                value.ty
            ));
        }
        None
    }
    fn cause_contains(&self, current: CauseId, source: CauseId) -> bool {
        let mut pending = vec![current];
        let mut visited = BTreeSet::new();
        while let Some(cause) = pending.pop() {
            if cause == source {
                return true;
            }
            if visited.insert(cause.0)
                && let Some(cause) = self.facts.explanations.causes.get(cause.0 as usize)
            {
                pending.extend(cause.parents.iter().copied());
            }
        }
        false
    }
    fn issue(&mut self, kind: ValidationIssueKind, span: Option<Span>, cause: Option<CauseId>) {
        if self.issues.len() < 64 {
            self.issues.push(ValidationIssue { kind, span, cause });
        }
    }
    fn origin(&mut self, node: NodeId, span: Option<Span>) -> bool {
        let valid = (node.0 as usize) < self.facts.heap.nodes.len();
        if !valid {
            self.issue(ValidationIssueKind::InvalidOrigin(node), span, None);
        }
        valid
    }
    fn scope(&mut self, scope: ScopeId, formal: bool, span: Option<Span>) {
        if !(self.facts.scopes.contains(&scope) || formal && scope == ScopeId(u32::MAX)) {
            self.issue(ValidationIssueKind::InvalidScope(scope), span, None);
        }
    }
    fn cause(&mut self, cause: CauseId, span: Option<Span>) {
        if self
            .facts
            .explanations
            .causes
            .get(cause.0 as usize)
            .is_none_or(|entry| entry.id != cause)
        {
            self.issue(ValidationIssueKind::InvalidCause(cause), span, None);
        }
    }
    fn participant(&mut self, participant: Participant, span: Option<Span>) {
        match participant {
            Participant::Root(root) => {
                if self
                    .facts
                    .bindings
                    .get(root.0 as usize)
                    .is_none_or(|binding| binding.root != root)
                {
                    self.issue(ValidationIssueKind::InvalidRoot(root.0), span, None);
                }
            }
            Participant::Loan(loan) => {
                if !self.facts.loan_parents.contains_key(&loan) {
                    self.issue(ValidationIssueKind::InvalidLoan(loan.0), span, None);
                }
            }
        }
    }
    fn origins(&mut self, origins: &Origins, span: Option<Span>) {
        for &node in &origins.nodes {
            self.origin(node, span);
        }
        for branches in origins.choices.values() {
            let covered: BTreeSet<_> = branches
                .iter()
                .flat_map(|branch| branch.iter().copied())
                .collect();
            if branches.is_empty() || covered != origins.nodes {
                self.issue(ValidationIssueKind::OriginCoverage, span, None);
            }
        }
    }
    fn value(&mut self, value: &Value, span: Option<Span>) {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            self.origins(&value.origins, span);
            self.cause(value.cause, span);
            if let Some(identity) = value.option_identity
                && let Some(reason) = self.optional_tag_problem(value, identity)
            {
                self.issue(
                    ValidationIssueKind::InvalidOptionalTag(identity.0, reason),
                    span,
                    Some(value.cause),
                );
            }
            for &producer in value
                .results
                .iter()
                .chain(&value.outer_results)
                .chain(&value.must_results)
                .chain(&value.must_outer_results)
            {
                if self
                    .facts
                    .result_duties
                    .get(producer as usize)
                    .is_none_or(|duty| duty.id != producer)
                {
                    self.issue(
                        ValidationIssueKind::InvalidResultProducer(producer),
                        span,
                        Some(value.cause),
                    );
                }
            }
            for &participant in &value.participants {
                self.participant(participant, span);
            }
            for &binding in value
                .sources
                .iter()
                .chain(&value.scoped)
                .chain(&value.callback_parameters)
            {
                if binding >= self.facts.bindings.len() {
                    self.issue(
                        ValidationIssueKind::InvalidBinding(binding),
                        span,
                        Some(value.cause),
                    );
                }
            }
            for callable in &value.callables {
                let invalid = match callable {
                    Callable::Named(id) => (*id >= self.facts.functions.len()).then_some(*id),
                    Callable::Closure(id) => (*id >= self.facts.closures.len()).then_some(*id),
                    _ => None,
                };
                if let Some(id) = invalid {
                    self.issue(
                        ValidationIssueKind::InvalidCallable(id),
                        span,
                        Some(value.cause),
                    );
                }
            }
            pending.extend(
                [
                    &value.option_payload,
                    &value.result_payload,
                    &value.result_success,
                    &value.result_error,
                    &value.variant_payload,
                ]
                .into_iter()
                .flatten()
                .map(Box::as_ref),
            );
            pending.extend(value.variant_witnesses.values().map(Box::as_ref));
        }
    }
    fn structure(&mut self) {
        let facts = self.facts;
        for (index, tag) in facts.optional_tags.iter().enumerate() {
            if tag.id.0 as usize != index {
                self.issue(
                    ValidationIssueKind::InvalidOptionalTag(
                        tag.id.0,
                        "tag identity differs from its arena index".into(),
                    ),
                    None,
                    Some(tag.cause),
                );
            }
            self.scope(tag.creation_owner, true, None);
            self.cause(tag.cause, None);
        }
        for (index, duty) in facts.result_duties.iter().enumerate() {
            if duty.id as usize != index {
                self.issue(
                    ValidationIssueKind::InvalidResultProducer(duty.id),
                    Some(duty.span),
                    Some(duty.cause),
                );
            }
            self.scope(duty.creation_owner, true, Some(duty.span));
            self.scope(duty.owner, true, Some(duty.span));
            self.cause(duty.cause, Some(duty.span));
        }
        if !facts.scopes.contains(&ScopeId(0)) {
            self.issue(ValidationIssueKind::MissingGlobalScope, None, None);
        }
        if facts.scopes.contains(&ScopeId(u32::MAX)) {
            self.issue(
                ValidationIssueKind::InvalidScope(ScopeId(u32::MAX)),
                None,
                None,
            );
        }
        if facts.scopes.is_poisoned() {
            self.issue(
                ValidationIssueKind::InvalidScope(ScopeId(u32::MAX)),
                None,
                None,
            );
        }
        for (&child, &parent) in facts.scopes.parents() {
            self.scope(child, false, None);
            self.scope(parent, false, None);
            let mut seen = BTreeSet::new();
            let mut current = child;
            while let Some(parent) = facts.scopes.parent(&current) {
                if !seen.insert(current) {
                    self.issue(ValidationIssueKind::ScopeCycle(child), None, None);
                    break;
                }
                current = *parent;
            }
        }
        if facts.explanations.causes.len() != facts.explanations.kinds.len() {
            self.issue(ValidationIssueKind::CauseTable, None, None);
        }
        for (index, cause) in facts.explanations.causes.iter().enumerate() {
            if cause.id.0 as usize != index
                || cause
                    .parents
                    .iter()
                    .any(|parent| parent.0 as usize >= index)
            {
                self.issue(
                    ValidationIssueKind::InvalidCause(cause.id),
                    cause.span,
                    None,
                );
            }
        }
        let pivots: BTreeSet<_> = facts
            .heap
            .nodes
            .iter()
            .filter_map(|node| match node.kind {
                OriginKind::Formal(pivot) => Some(pivot),
                _ => None,
            })
            .collect();
        let conditions = facts.heap.conditions.node_count() as u32 + 2;
        for (id, atom, low, high) in facts.heap.conditions.decisions() {
            if low.0 >= id.0 || high.0 >= id.0 || low == high {
                self.issue(ValidationIssueKind::InvalidCondition(id.0), None, None);
            }
            let (a, b) = match atom {
                Atom::Equal(a, b) | Atom::Disjoint(a, b) => (a, b),
            };
            for pivot in [a, b] {
                if !pivots.contains(&pivot) {
                    self.issue(ValidationIssueKind::InvalidPivot(pivot.0), None, None);
                }
            }
        }
        for (a, b, relation) in facts.heap.relations() {
            self.origin(a, None);
            self.origin(b, None);
            for condition in [relation.equal, relation.disjoint] {
                if condition.0 >= conditions {
                    self.issue(
                        ValidationIssueKind::InvalidCondition(condition.0),
                        None,
                        None,
                    );
                }
            }
            if relation.equal == Condition::TRUE && relation.disjoint == Condition::TRUE
                || a == b && relation.disjoint == Condition::TRUE
            {
                self.issue(ValidationIssueKind::ContradictoryRelation(a, b), None, None);
            }
            if a == b
                && relation.equal == Condition::TRUE
                && facts
                    .heap
                    .nodes
                    .get(a.0 as usize)
                    .is_some_and(|node| node.multiplicity == Multiplicity::MayMany)
            {
                self.issue(ValidationIssueKind::InvalidMultiplicity(a), None, None);
            }
        }
        for (index, node) in facts.heap.nodes.iter().enumerate() {
            let id = NodeId(index as u32);
            self.scope(node.owner, matches!(node.kind, OriginKind::Formal(_)), None);
            self.cause(node.cause, None);
            if matches!(node.kind, OriginKind::Older(_))
                && node.multiplicity != Multiplicity::MayMany
            {
                self.issue(
                    ValidationIssueKind::InvalidMultiplicity(id),
                    None,
                    Some(node.cause),
                );
            }
            for root in &node.writable_roots {
                self.participant(Participant::Root(*root), None);
            }
            for (slot, children) in &node.fields {
                for &child in children {
                    self.origin(child, None);
                }
                if facts
                    .fields
                    .get(&(id, slot.clone()))
                    .is_none_or(|value| value.origins.nodes != *children)
                {
                    self.issue(
                        ValidationIssueKind::FieldGraphMismatch(id, slot.clone()),
                        None,
                        Some(node.cause),
                    );
                }
            }
        }
        for ((node, slot), value) in &facts.fields {
            if self.origin(*node, None)
                && facts.heap.nodes[node.0 as usize].fields.get(slot) != Some(&value.origins.nodes)
            {
                self.issue(
                    ValidationIssueKind::FieldGraphMismatch(*node, slot.clone()),
                    None,
                    Some(value.cause),
                );
            }
            self.value(value, None);
        }
        for (index, binding) in facts.bindings.iter().enumerate() {
            if binding.root.0 as usize != index {
                self.issue(
                    ValidationIssueKind::InvalidRoot(binding.root.0),
                    Some(binding.span),
                    Some(binding.value.cause),
                );
            }
            self.scope(binding.owner, false, Some(binding.span));
            if let Some(cell) = binding.cell {
                self.origin(cell, Some(binding.span));
            }
            self.value(&binding.value, Some(binding.span));
        }
        for expression in &facts.expressions {
            if let Some(value) =
                expression.value_at(facts.allocation_history.len(), &facts.allocation_history)
            {
                self.value(&value, Some(expression.span));
            } else {
                self.issue(
                    ValidationIssueKind::InvalidAllocationMove(expression.allocation_epoch),
                    Some(expression.span),
                    Some(expression.value.cause),
                );
            }
        }
        for constant in &facts.constant_values {
            self.value(&constant.value, Some(constant.span));
        }
        for &node in facts
            .storage_types
            .keys()
            .chain(facts.array_lengths.keys())
            .chain(&facts.fixed_arrays)
        {
            self.origin(node, None);
        }
        for (node, _) in &facts.uncertain_slots {
            self.origin(*node, None);
        }
        for (&node, window) in &facts.windows {
            self.origin(node, Some(window.span));
            self.origins(&window.backing, Some(window.span));
            self.cause(window.cause, Some(window.span));
        }
        for summary in facts.invocations.iter().chain(
            facts
                .definition_checks
                .iter()
                .map(|definition| &definition.invocation),
        ) {
            for access in &summary.accesses {
                self.origin(access.origin, None);
                self.participant(access.participant, None);
            }
            for &node in summary
                .escaped_origins
                .iter()
                .chain(&summary.retained_origins)
                .chain(&summary.new_environments)
            {
                self.origin(node, None);
            }
            for &owner in &summary.owners {
                self.scope(owner, false, None);
            }
        }
        for (&loan, parents) in &facts.loan_parents {
            for &parent in parents {
                self.participant(parent, None);
                if let Participant::Loan(parent) = parent
                    && parent.0 >= loan.0
                {
                    self.issue(ValidationIssueKind::LoanCycle(loan.0), None, None);
                }
            }
        }
        for (index, &(recent, older)) in facts.allocation_history.iter().enumerate() {
            let valid = self.origin(recent, None) & self.origin(older, None);
            if valid
                && !(recent != older
                    && matches!((facts.heap.nodes[recent.0 as usize].kind, facts.heap.nodes[older.0 as usize].kind), (OriginKind::Fresh(a), OriginKind::Older(b)) if a == b))
            {
                self.issue(
                    ValidationIssueKind::InvalidAllocationMove(index),
                    None,
                    None,
                );
            }
        }
    }
    fn access(&mut self, access: &AccessFact) {
        self.checked_accesses += 1;
        let span = Some(access.span);
        let final_epoch = self.facts.allocation_history.len();
        if access.observed_recency > access.recency || access.recency != final_epoch {
            self.issue(
                ValidationIssueKind::AccessEpoch {
                    observed: access.observed_recency,
                    current: access.recency,
                    final_epoch,
                },
                span,
                Some(access.cause),
            );
        }
        self.origins(&access.origins, span);
        let owners: BTreeSet<_> = access.origin_owners.keys().copied().collect();
        if owners != access.origins.nodes {
            self.issue(
                ValidationIssueKind::OwnershipCoverage,
                span,
                Some(access.cause),
            );
        }
        for (&origin, owners) in &access.origin_owners {
            self.origin(origin, span);
            if let AccessOwners::Known(owners) = owners {
                if owners.is_empty() {
                    self.issue(
                        ValidationIssueKind::EmptyKnownOwnership(origin),
                        span,
                        Some(access.cause),
                    );
                }
                let formal = self
                    .facts
                    .heap
                    .nodes
                    .get(origin.0 as usize)
                    .is_some_and(|node| matches!(node.kind, OriginKind::Formal(_)));
                for &owner in owners {
                    self.scope(owner, formal, span);
                }
            }
        }
        for &participant in &access.participants {
            self.participant(participant, span);
        }
        self.cause(access.cause, span);
    }
    fn boundaries(&mut self) {
        for boundary in &self.facts.parallel_boundaries {
            self.cause(boundary.cause, Some(boundary.span));
            let count = boundary.callbacks.len();
            let complete = match boundary.operation {
                super::ParallelOperation::Join => count == 2,
                super::ParallelOperation::Join3 => count == 3,
                super::ParallelOperation::Fold => count >= 3,
                _ => count >= 1,
            };
            if !complete {
                self.issue(
                    ValidationIssueKind::MissingBoundaryEvidence,
                    Some(boundary.span),
                    Some(boundary.cause),
                );
            }
            for callback in &boundary.callbacks {
                self.cause(callback.cause, Some(boundary.span));
                if self
                    .facts
                    .explanations
                    .causes
                    .get(boundary.cause.0 as usize)
                    .is_some_and(|cause| !cause.parents.contains(&callback.cause))
                {
                    self.issue(
                        ValidationIssueKind::BoundaryCauseMismatch,
                        Some(boundary.span),
                        Some(boundary.cause),
                    );
                }
                if callback.termination.may_diverge
                    || callback.termination.unresolved
                    || !callback.termination.callable_parameters.is_empty()
                {
                    self.issue(
                        ValidationIssueKind::IncompleteParallelTermination,
                        Some(boundary.span),
                        Some(callback.cause),
                    );
                }
                for &handler in &callback.selected_handlers {
                    if !self.facts.handlers.iter().any(|fact| fact.id == handler) {
                        self.issue(
                            ValidationIssueKind::InvalidHandler(handler),
                            Some(boundary.span),
                            Some(callback.cause),
                        );
                    }
                }
                for access in &callback.accesses {
                    self.access(access);
                }
            }
        }
        for boundary in &self.facts.concurrent_boundaries {
            if boundary.task == Some(boundary.scope)
                || matches!(
                    boundary.kind,
                    super::ConcurrentBoundaryKind::Fork | super::ConcurrentBoundaryKind::Join
                ) && boundary.task.is_none()
            {
                self.issue(
                    ValidationIssueKind::ConcurrentIdentityShape,
                    Some(boundary.span),
                    Some(boundary.cause),
                );
            }
            self.origin(boundary.scope, Some(boundary.span));
            if let Some(task) = boundary.task {
                self.origin(task, Some(boundary.span));
            }
            self.cause(boundary.cause, Some(boundary.span));
        }
    }
}

#[cfg(test)]
mod tests;
