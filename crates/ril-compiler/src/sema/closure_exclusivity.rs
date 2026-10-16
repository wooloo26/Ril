//! Conditional alias requirements belong to one closure object and invocation.
//! A signature probe records requirements; it is not an actual-argument proof.
use super::{
    copy_contract::CopyInvocationStatus,
    copy_templates::InstanceId,
    default_uses::DefaultUseId,
    effect_identity::ClosureInvocationId,
    facts::{HeapNode, NodeId, Participant},
    model::{AccessFact, Mode, Origins},
    relations::Relation,
};
use ril_compiler_core::{
    ids::{CallableOwner, ClosureSiteId, DefinitionId},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

pub use ril_compiler_core::ids::{ClosureCheckId, ClosureDiscardId, ClosureObjectId};
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Conflict {
    ReadWrite,
    WriteWrite,
}
impl Conflict {
    pub fn code(self) -> &'static str {
        match self {
            Self::ReadWrite => "E0524",
            Self::WriteWrite => "E0523",
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Requirement {
    pub left: usize,
    pub right: usize,
    pub conflict: Conflict,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    Proved,
    Pending,
    Discharged {
        calls: BTreeSet<ClosureInvocationId>,
        discards: BTreeSet<ClosureDiscardId>,
    },
    Rejected,
    Unsupported,
}
#[derive(Debug, Clone)]
pub struct ClosureExclusivityCheck {
    pub id: ClosureCheckId,
    pub closure: ClosureObjectId,
    pub site: Option<ClosureSiteId>,
    pub invocation: ClosureInvocationId,
    pub creation_named: Option<InstanceId>,
    pub creation_closure: Option<ClosureInvocationId>,
    pub creation_default: Option<DefaultUseId>,
    pub probe: bool,
    pub body_complete: bool,
    pub span: Span,
    pub allocation_epoch: usize,
    pub accesses: Vec<AccessFact>,
    /// Frozen observed origins, not a complete reachable value/copy graph.
    /// Relations contain the pairs queried for this footprint's conditions.
    pub nodes: Vec<(NodeId, HeapNode)>,
    pub relations: Vec<(NodeId, NodeId, Relation)>,
    pub requirements: Vec<Requirement>,
    pub resolution: Resolution,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ClosureExclusivityCertificate {
    pub objects: BTreeMap<ClosureObjectId, BTreeSet<ClosureInvocationId>>,
    pub templates: BTreeMap<ClosureObjectId, BTreeSet<ClosureObjectId>>,
    pub discarded: BTreeMap<ClosureObjectId, ClosureDiscardId>,
}
/// A normal expression statement consumes its entire newly created callable.
/// This receipt changes no creation-time capability, loan, or Result duty.
#[derive(Debug, Clone)]
pub struct ClosureDiscard {
    pub id: ClosureDiscardId,
    pub closure: ClosureObjectId,
    pub created_start: ClosureObjectId,
    pub created_end: ClosureObjectId,
    pub named_start: InstanceId,
    pub named_end: InstanceId,
    pub owner: Option<CallableOwner>,
    pub named: Option<InstanceId>,
    pub invocation: Option<ClosureInvocationId>,
    pub span: Span,
    pub allocation_epoch: usize,
    pub value: super::copy_contract::CopyValueSnapshot,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExposureKind {
    Returned,
    Stored,
}
#[derive(Debug, Clone)]
pub struct ClosureExposure {
    pub closure: ClosureObjectId,
    pub kind: ExposureKind,
    pub owner: Option<CallableOwner>,
    pub named: Option<InstanceId>,
    pub invocation: Option<ClosureInvocationId>,
    pub span: Span,
}

pub fn requirements(
    accesses: &[AccessFact],
    mut disjoint: impl FnMut(&Origins, &Origins) -> bool,
) -> Vec<Requirement> {
    let mut result = vec![];
    for (left, a) in accesses.iter().enumerate() {
        for (right, b) in accesses.iter().enumerate().skip(left + 1) {
            if a.mode != Mode::Write && b.mode != Mode::Write {
                continue;
            }
            if a.participants.is_empty()
                || b.participants.is_empty()
                || (a.participants.len() == 1 && a.participants == b.participants)
                || !a
                    .participants
                    .iter()
                    .chain(&b.participants)
                    .any(|p| matches!(p, Participant::Loan(_)))
            {
                continue;
            }
            let separate_slots = match (&a.slot, &b.slot) {
                (Some(a), Some(b)) => {
                    a != b
                        && !matches!(
                            a,
                            super::facts::Slot::AnyIndex | super::facts::Slot::RowTail(_)
                        )
                        && !matches!(
                            b,
                            super::facts::Slot::AnyIndex | super::facts::Slot::RowTail(_)
                        )
                }
                _ => false,
            };
            if separate_slots || disjoint(&a.origins, &b.origins) {
                continue;
            }
            let writes = |participants: &BTreeSet<Participant>| {
                accesses.iter().any(|access| {
                    access.mode != Mode::Read && !access.participants.is_disjoint(participants)
                })
            };
            result.push(Requirement {
                left,
                right,
                conflict: if writes(&a.participants) && writes(&b.participants) {
                    Conflict::WriteWrite
                } else {
                    Conflict::ReadWrite
                },
            });
        }
    }
    result
}

pub fn completed_actual_calls(
    object: ClosureObjectId,
    calls: &[super::effect_identity::ClosureInvocation],
    checks: &[ClosureExclusivityCheck],
) -> Option<BTreeSet<ClosureInvocationId>> {
    let actual: Vec<_> = calls
        .iter()
        .filter(|call| call.closure == object.0 as usize && !call.probe)
        .collect();
    if actual.is_empty()
        || actual.iter().any(|call| {
            call.budget_validation
                || call.status != CopyInvocationStatus::Completed
                || !checks.iter().any(|check| {
                    check.closure == object
                        && check.invocation == call.id
                        && !check.probe
                        && check.body_complete
                        && check.requirements.is_empty()
                        && check.resolution == Resolution::Proved
                })
        })
    {
        return None;
    }
    Some(actual.into_iter().map(|call| call.id).collect())
}

pub struct CoverageInput<'a> {
    pub final_epoch: usize,
    pub closures: &'a [super::model::ClosureInfo],
    pub sites: &'a [super::model::ClosureSite],
    pub functions: &'a [super::model::FunctionInfo],
    pub named: &'a [super::copy_contract::CopyInvocation],
    pub calls: &'a [super::effect_identity::ClosureInvocation],
    pub checks: &'a [ClosureExclusivityCheck],
    pub exposures: &'a [ClosureExposure],
    pub discards: &'a [ClosureDiscard],
    pub references: &'a [super::copy_contract::CopyReference],
    pub events: &'a [super::copy_contract::CopyCallEvent],
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoverageFailure {
    Malformed(ClosureCheckId),
    MalformedInvocation(ClosureInvocationId),
    MissingCheck(ClosureInvocationId),
    MalformedDiscard(ClosureDiscardId),
    MissingSite(ClosureObjectId),
    UncoveredObject(ClosureObjectId),
    ExposedObject(ClosureObjectId),
    ExposedCreator(DefinitionId),
    IncompleteCreator(InstanceId),
    UninstantiatedCreator(DefinitionId),
    MissingCreation(InstanceId, ClosureSiteId),
    RecursiveCreator(DefinitionId),
    UnresolvedCreatorContext(InstanceId),
}
impl CoverageInput<'_> {
    fn lexical_function(
        &self,
        mut owner: Option<CallableOwner>,
    ) -> Result<Option<DefinitionId>, ()> {
        let mut seen = BTreeSet::new();
        loop {
            match owner {
                Some(CallableOwner::Global) => return Ok(None),
                Some(CallableOwner::Function(id)) => return Ok(Some(id)),
                Some(CallableOwner::Lambda(id)) if seen.insert(id) => {
                    owner = Some(
                        self.sites
                            .iter()
                            .find(|site| site.id == id)
                            .ok_or(())?
                            .owner,
                    );
                }
                _ => return Err(()),
            }
        }
    }
    fn acyclic_creator(&self, owner: DefinitionId) -> Result<(), CoverageFailure> {
        let mut edges = BTreeMap::<DefinitionId, BTreeSet<DefinitionId>>::new();
        let mut unknown = vec![];
        for call in self.named.iter().filter(|call| !call.declaration_probe) {
            match self.lexical_function(call.caller_owner) {
                Ok(Some(caller)) => {
                    edges.entry(caller).or_default().insert(call.target);
                }
                Ok(None) => {}
                Err(()) => unknown.push((call.id, call.target)),
            }
        }
        let reaches = |start: DefinitionId, target: DefinitionId| {
            let mut pending = vec![start];
            let mut seen = BTreeSet::new();
            while let Some(next) = pending.pop() {
                if next == target {
                    return true;
                }
                if seen.insert(next) {
                    pending.extend(edges.get(&next).into_iter().flatten().copied());
                }
            }
            false
        };
        if edges
            .get(&owner)
            .into_iter()
            .flatten()
            .any(|next| reaches(*next, owner))
        {
            return Err(CoverageFailure::RecursiveCreator(owner));
        }
        if let Some((id, _)) = unknown
            .into_iter()
            .find(|(_, target)| reaches(*target, owner))
        {
            return Err(CoverageFailure::UnresolvedCreatorContext(id));
        }
        Ok(())
    }
    fn private_creator(&self, owner: DefinitionId) -> bool {
        self.functions
            .iter()
            .any(|function| function.definition == owner)
            && !self.functions.iter().any(|function| {
                function.definition == owner
                    && function.syntax.visibility == ril_syntax::ast::Visibility::Public
            })
            && !self
                .references
                .iter()
                .any(|reference| reference.target == owner && reference.direct_call.is_none())
    }
    fn direct_call(&self, call: &super::copy_contract::CopyInvocation) -> bool {
        let Some(event) = call
            .source_event
            .and_then(|id| self.events.get(id.0 as usize))
        else {
            return false;
        };
        call.direct
            && event.id == call.source_event.unwrap()
            && event.direct
            && event.target == Some(call.target)
            && event.owner == call.caller_owner
            && event.parent == call.parent
            && event.span == call.span
            && !event.references.is_empty()
            && event.references.iter().all(|id| {
                self.references.get(id.0 as usize).is_some_and(|reference| {
                    reference.id == *id
                        && reference.direct_call == Some(event.id)
                        && reference.target == call.target
                        && reference.owner == event.owner
                        && reference.parent == event.parent
                })
            })
    }
    fn exposures_are_closed(&self, object: ClosureObjectId) -> bool {
        self.exposures
            .iter()
            .filter(|exposure| exposure.closure == object)
            .all(|exposure| {
                if exposure.kind == ExposureKind::Stored {
                    return false;
                }
                let Some(CallableOwner::Function(owner)) = exposure.owner else {
                    return false;
                };
                self.private_creator(owner)
                    && exposure
                        .named
                        .and_then(|id| self.named.get(id.0 as usize))
                        .is_some_and(|call| {
                            call.id == exposure.named.unwrap()
                                && call.target == owner
                                && call.status == CopyInvocationStatus::Completed
                                && (call.declaration_probe || self.direct_call(call))
                        })
            })
    }
    fn actual_object(
        &self,
        object: ClosureObjectId,
        discarded: &mut BTreeMap<ClosureObjectId, ClosureDiscardId>,
    ) -> Result<BTreeSet<ClosureInvocationId>, CoverageFailure> {
        if !self.exposures_are_closed(object) {
            return Err(CoverageFailure::ExposedObject(object));
        }
        if let Some(calls) = completed_actual_calls(object, self.calls, self.checks) {
            return Ok(calls);
        }
        // Discard cannot replace the proof of any real invocation, including
        // failed, incomplete, or budget-validation executions.
        if self
            .calls
            .iter()
            .any(|call| call.closure == object.0 as usize && !call.probe)
        {
            return Err(CoverageFailure::UncoveredObject(object));
        }
        if let Some(discard) = self
            .discards
            .iter()
            .find(|discard| discard.closure == object)
        {
            discarded.insert(object, discard.id);
            return Ok(BTreeSet::new());
        }
        Err(CoverageFailure::UncoveredObject(object))
    }
}

pub fn close(input: &CoverageInput<'_>) -> Result<ClosureExclusivityCertificate, CoverageFailure> {
    for (index, discard) in input.discards.iter().enumerate() {
        let value = &discard.value.value;
        let nodes: BTreeSet<_> = discard.value.nodes.iter().map(|node| node.origin).collect();
        if discard.id.0 as usize != index
            || discard.created_start > discard.closure
            || discard.closure >= discard.created_end
            || discard.created_end.0 as usize > input.closures.len()
            || discard.named_start > discard.named_end
            || discard.named_end.0 as usize > input.named.len()
            || discard.allocation_epoch > input.final_epoch
            || value.callables != [super::model::Callable::Closure(discard.closure.0 as usize)]
            || !value.callback_parameters.is_empty()
            || nodes.len() != discard.value.nodes.len()
            || value.origins.nodes.is_empty()
            || !value.origins.nodes.is_subset(&nodes)
            || discard.value.nodes.iter().any(|node| {
                node.fact
                    .fields
                    .values()
                    .any(|children| !children.is_subset(&nodes))
                    || node.fact.fields.iter().any(|(slot, children)| {
                        node.fields
                            .iter()
                            .find(|(stored, _)| stored == slot)
                            .is_none_or(|(_, value)| value.origins.nodes != *children)
                    })
            })
            || discard.named.is_some_and(|id| {
                input.named.get(id.0 as usize).is_none_or(|call| {
                    call.id != id || call.status != CopyInvocationStatus::Completed
                })
            })
            || discard.invocation.is_some_and(|id| {
                input.calls.get(id.0 as usize).is_none_or(|call| {
                    call.id != id
                        || call.probe
                        || call.budget_validation
                        || call.status != CopyInvocationStatus::Completed
                })
            })
            || discard.owner.is_none()
        {
            return Err(CoverageFailure::MalformedDiscard(discard.id));
        }
        let created = &input.closures[discard.closure.0 as usize];
        let mut creator = created.creation_invocation;
        let mut seen = BTreeSet::new();
        while creator != discard.named {
            let Some(id) = creator else {
                return Err(CoverageFailure::MalformedDiscard(discard.id));
            };
            let Some(call) = input.named.get(id.0 as usize) else {
                return Err(CoverageFailure::MalformedDiscard(discard.id));
            };
            if !seen.insert(id)
                || id < discard.named_start
                || id >= discard.named_end
                || call.id != id
                || call.status != CopyInvocationStatus::Completed
            {
                return Err(CoverageFailure::MalformedDiscard(discard.id));
            }
            creator = call.parent;
        }
    }
    let mut checked_invocations = BTreeSet::new();
    for (index, check) in input.checks.iter().enumerate() {
        let call = input.calls.get(check.invocation.0 as usize);
        let info = input.closures.get(check.closure.0 as usize);
        if check.id.0 as usize != index
            || !checked_invocations.insert(check.invocation)
            || call.is_none_or(|call| {
                call.id != check.invocation
                    || call.closure != check.closure.0 as usize
                    || call.probe != check.probe
            })
            || info.is_none_or(|info| {
                info.site != check.site
                    || info.creation_invocation != check.creation_named
                    || info.creation_closure != check.creation_closure
                    || info.creation_default != check.creation_default
            })
        {
            return Err(CoverageFailure::Malformed(check.id));
        }
        if check.allocation_epoch > input.final_epoch
            || check.accesses.iter().any(|access| {
                access.recency != check.allocation_epoch || access.observed_recency > access.recency
                    || access.origin_owners.keys().copied().collect::<BTreeSet<_>>() != access.origins.nodes
                    || access.origin_owners.values().any(|owner| matches!(owner, super::model::AccessOwners::Known(scopes) if scopes.is_empty()))
                    || access.origins.choices.values().any(|branches| branches.iter().flatten().copied().collect::<BTreeSet<_>>() != access.origins.nodes)
            })
        {
            return Err(CoverageFailure::Malformed(check.id));
        }
        let nodes: BTreeSet<_> = check.nodes.iter().map(|(node, _)| *node).collect();
        if nodes.len() != check.nodes.len()
            || check
                .accesses
                .iter()
                .any(|access| !access.origins.nodes.is_subset(&nodes))
        {
            return Err(CoverageFailure::Malformed(check.id));
        }
        let relations: BTreeMap<_, _> = check
            .relations
            .iter()
            .map(|(a, b, relation)| ((a.min(b), a.max(b)), *relation))
            .collect();
        if relations.len() != check.relations.len()
            || check
                .relations
                .iter()
                .any(|(a, b, _)| !nodes.contains(a) || !nodes.contains(b))
        {
            return Err(CoverageFailure::Malformed(check.id));
        }
        let known = |a: &Origins, b: &Origins| {
            let pairs = |a: &BTreeSet<NodeId>, b: &BTreeSet<NodeId>| {
                a.iter().all(|a| {
                    b.iter().all(|b| {
                        relations
                            .get(&(a.min(b), a.max(b)))
                            .is_some_and(|relation| {
                                relation.disjoint == super::relations::Condition::TRUE
                            })
                    })
                })
            };
            a.choices.iter().any(|(choice, left)| {
                b.choices.get(choice).is_some_and(|right| {
                    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| pairs(a, b))
                })
            }) || pairs(&a.nodes, &b.nodes)
        };
        if requirements(&check.accesses, known) != check.requirements {
            return Err(CoverageFailure::Malformed(check.id));
        }
    }
    // An omitted completed probe is not evidence that its body had no accesses.
    // Require the collector's one-to-one invocation receipt even when removing
    // the probe would otherwise leave an empty conditional certificate.
    for (index, call) in input.calls.iter().enumerate() {
        if call.id.0 as usize != index
            || call.closure >= input.closures.len()
            || call
                .parent_closure
                .is_some_and(|parent| parent.0 >= call.id.0)
            || call.parent_named.is_some_and(|parent| {
                input
                    .named
                    .get(parent.0 as usize)
                    .is_none_or(|named| named.id != parent)
            })
        {
            return Err(CoverageFailure::MalformedInvocation(call.id));
        }
        if call.status == CopyInvocationStatus::Completed && !checked_invocations.contains(&call.id)
        {
            return Err(CoverageFailure::MissingCheck(call.id));
        }
    }
    let pending: BTreeSet<_> = input
        .checks
        .iter()
        .filter(|check| check.probe && !check.requirements.is_empty())
        .map(|check| check.closure)
        .collect();
    let mut certificate = ClosureExclusivityCertificate::default();
    for object in pending {
        let info = &input.closures[object.0 as usize];
        let site = info.site.ok_or(CoverageFailure::MissingSite(object))?;
        let creator = info
            .creation_invocation
            .and_then(|id| input.named.get(id.0 as usize));
        let returned_by_creator = creator.is_some_and(|creator| {
            input.exposures.iter().any(|exposure| {
                exposure.closure == object
                    && exposure.kind == ExposureKind::Returned
                    && exposure.named == Some(creator.id)
                    && exposure.owner == Some(CallableOwner::Function(creator.target))
            })
        });
        let template = creator.filter(|creator| creator.declaration_probe && returned_by_creator);
        let Some(creator) = template else {
            certificate.objects.insert(
                object,
                input.actual_object(object, &mut certificate.discarded)?,
            );
            continue;
        };
        if !input.exposures_are_closed(object) || !input.private_creator(creator.target) {
            return Err(CoverageFailure::ExposedCreator(creator.target));
        }
        input.acyclic_creator(creator.target)?;
        if info.creation_closure.is_some()
            || info.creation_default.is_some()
            || input
                .sites
                .iter()
                .find(|candidate| candidate.id == site)
                .is_none_or(|site| site.owner != CallableOwner::Function(creator.target))
        {
            return Err(CoverageFailure::MissingSite(object));
        }
        let instances: Vec<_> = input
            .named
            .iter()
            .filter(|call| call.target == creator.target && !call.declaration_probe)
            .collect();
        if instances.is_empty() {
            return Err(CoverageFailure::UninstantiatedCreator(creator.target));
        }
        let mut objects = BTreeSet::new();
        for call in instances {
            if call.status != CopyInvocationStatus::Completed
                || call.result.is_none()
                || !input.direct_call(call)
            {
                return Err(CoverageFailure::IncompleteCreator(call.id));
            }
            let mut parent = call.parent;
            let mut seen = BTreeSet::new();
            while let Some(id) = parent {
                let Some(ancestor) = input.named.get(id.0 as usize) else {
                    return Err(CoverageFailure::IncompleteCreator(call.id));
                };
                if !seen.insert(id) || ancestor.target == creator.target {
                    return Err(CoverageFailure::RecursiveCreator(creator.target));
                }
                parent = ancestor.parent;
            }
            let created: Vec<_> = input
                .closures
                .iter()
                .enumerate()
                .filter(|(_, closure)| {
                    closure.site == Some(site) && closure.creation_invocation == Some(call.id)
                })
                .collect();
            if created.is_empty() {
                return Err(CoverageFailure::MissingCreation(call.id, site));
            }
            for (id, closure) in created {
                let actual = ClosureObjectId(id as u32);
                if closure.creation_default.is_some()
                    || closure.creation_closure.is_some_and(|id| {
                        input.calls.get(id.0 as usize).is_none_or(|parent| {
                            parent.probe
                                || parent.budget_validation
                                || parent.status != CopyInvocationStatus::Completed
                        })
                    })
                {
                    return Err(CoverageFailure::UncoveredObject(actual));
                }
                let calls = input.actual_object(actual, &mut certificate.discarded)?;
                certificate.objects.insert(actual, calls);
                objects.insert(actual);
            }
        }
        certificate.templates.insert(object, objects);
    }
    Ok(certificate)
}

pub fn validate(facts: &super::SemanticFacts) -> Result<(), String> {
    super::copy_template_closure::validate_events(facts)?;
    let input = CoverageInput {
        final_epoch: facts.allocation_history.len(),
        closures: &facts.closures,
        sites: &facts.closure_sites,
        functions: &facts.functions,
        named: &facts.copy_invocations,
        calls: &facts.closure_invocations,
        checks: &facts.closure_exclusivity_checks,
        exposures: &facts.closure_exposures,
        discards: &facts.closure_discards,
        references: &facts.copy_references,
        events: &facts.copy_call_events,
    };
    let expected =
        close(&input).map_err(|error| format!("conditional closure exclusivity: {error:?}"))?;
    let pending = facts
        .closure_exclusivity_checks
        .iter()
        .any(|check| check.probe && !check.requirements.is_empty());
    if !pending && facts.closure_exclusivity_certificate.is_some() {
        return Err("closure coverage certificate has no conditional requirements".into());
    }
    if pending && facts.closure_exclusivity_certificate.as_ref() != Some(&expected) {
        return Err(
            "conditional closure exclusivity coverage certificate differs from actual invocations"
                .into(),
        );
    }
    for check in &facts.closure_exclusivity_checks {
        if !check.probe || check.requirements.is_empty() {
            continue;
        }
        let calls = expected
            .objects
            .get(&check.closure)
            .cloned()
            .or_else(|| {
                expected.templates.get(&check.closure).map(|objects| {
                    objects
                        .iter()
                        .flat_map(|object| expected.objects[object].iter().copied())
                        .collect()
                })
            })
            .ok_or("conditional closure object has no complete coverage")?;
        let objects = expected
            .templates
            .get(&check.closure)
            .cloned()
            .unwrap_or_else(|| [check.closure].into());
        let discards = objects
            .iter()
            .filter_map(|object| expected.discarded.get(object).copied())
            .collect();
        if check.resolution != (Resolution::Discharged { calls, discards }) {
            return Err("conditional closure requirements remain pending".into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
