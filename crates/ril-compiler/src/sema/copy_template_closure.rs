//! Reconstruct the exact-instance obligations used by the template certificate.
//! This is shared by final checking and the defensive Core/entry boundary.
use super::{SemanticFacts, copy_contract::*, copy_templates as domain};
use ril_compiler_core::ids::DefinitionId;
use std::collections::{BTreeMap, BTreeSet};

fn established(boundary: &CopyBoundary) -> bool {
    use super::copy_eligibility::Constituent;
    boundary
        .output
        .as_ref()
        .is_some_and(|output| output.nested_copy_dependencies().is_empty())
        && boundary.requirements.is_empty()
        && !boundary.template
        && boundary.template_root.is_none()
        && boundary.constituents.iter().all(|part| {
            matches!(
                part.qualification,
                Constituent::Ordinary | Constituent::EnvironmentFreeCallable
            )
        })
        && boundary
            .output_nodes
            .iter()
            .flat_map(|node| &node.fields)
            .all(|(_, value)| value.nested_copy_dependencies().is_empty())
}

fn executed_within(
    calls: &[CopyInvocation],
    root: domain::InstanceId,
    mut child: domain::InstanceId,
) -> bool {
    let mut seen = BTreeSet::new();
    while seen.insert(child) {
        if root == child {
            return true;
        }
        let Some(call) = calls.get(child.0 as usize) else {
            return false;
        };
        if call.declaration_probe {
            return false;
        }
        let Some(parent) = call.parent else {
            return false;
        };
        child = parent;
    }
    false
}

pub fn template_owners(
    boundaries: &[CopyBoundary],
    calls: &[CopyInvocation],
) -> BTreeSet<DefinitionId> {
    calls
        .iter()
        .filter(|call| {
            call.declaration_probe
                && call.boundaries.iter().any(|id| {
                    boundaries
                        .get(id.0 as usize)
                        .is_some_and(|boundary| boundary.template)
                })
        })
        .map(|call| call.target)
        .collect()
}

pub fn ancestor(
    calls: &[CopyInvocation],
    mut child: domain::InstanceId,
    parent: domain::InstanceId,
) -> bool {
    let mut seen = BTreeSet::new();
    while seen.insert(child) {
        if child == parent {
            return true;
        }
        let Some(next) = calls.get(child.0 as usize).and_then(|call| call.parent) else {
            return false;
        };
        child = next;
    }
    false
}

pub struct InstanceProofs {
    pub actual: Vec<domain::Instance>,
    pub discharges:
        BTreeMap<(domain::InstanceId, CopyBoundaryId), super::resource_copy::CopyDischarge>,
}

pub fn instances(
    templates: &BTreeMap<DefinitionId, domain::Template>,
    boundaries: &[CopyBoundary],
    calls: &[CopyInvocation],
    events: &[CopyCallEvent],
    resources: &[super::resource_copy::ResourceCloneEvent],
) -> Result<InstanceProofs, String> {
    use super::resource_copy::{CopyDischarge, sender_contract};
    let mut actual = Vec::new();
    let mut discharges = BTreeMap::new();
    for call in calls
        .iter()
        .filter(|call| templates.contains_key(&call.target))
    {
        if call.declaration_probe {
            if call.status != CopyInvocationStatus::Completed {
                return Err("copy template declaration has an unfinished consumer proof".into());
            }
            continue;
        }
        if !call.direct {
            return Err("copy template is used through an unproved indirect call".into());
        }
        let dependencies: Vec<_> = call
            .boundaries
            .iter()
            .map(|id| {
                boundaries
                    .get(id.0 as usize)
                    .ok_or_else(|| "copy invocation references a missing boundary".to_string())
            })
            .collect::<Result<_, _>>()?;
        let pending: Vec<_> = dependencies
            .iter()
            .filter(|boundary| boundary.output.is_none())
            .collect();
        // Only unresolved conditions actually anchored to an ancestor's formal
        // input can remain a declaration probe. A concrete/unknown producer or
        // a failed instance is never removed by this rule.
        let formal_probe = call.status == CopyInvocationStatus::Completed
            && !pending.is_empty()
            && call
                .caller
                .is_some_and(|caller| templates.contains_key(&caller))
            && pending.iter().all(|boundary| {
                boundary.template
                    && boundary.template_root.is_some_and(|root| {
                        calls.get(root.0 as usize).is_some_and(|probe| {
                            probe.declaration_probe && templates.contains_key(&probe.target)
                        }) && ancestor(calls, call.id, root)
                    })
            });
        if formal_probe {
            continue;
        }
        let coverage = boundaries
            .iter()
            .filter(|boundary| boundary.template && boundary.owner == Some(call.target))
            .all(|required| {
                let ordinary = dependencies
                    .iter()
                    .find(|proof| {
                        proof.owner == required.owner
                            && proof.span == required.span
                            && proof.mode == required.mode
                            && proof.invocation == Some(call.id)
                            && established(proof)
                            && proof
                                .source_event
                                .and_then(|id| events.get(id.0 as usize))
                                .is_some_and(|event| {
                                    event.parent == Some(call.id)
                                        && event.copy_operation == Some(proof.mode)
                                })
                    })
                    .map(|proof| CopyDischarge::Ordinary(proof.id));
                let sender = || {
                    use super::copy_eligibility::{AbstractMember, Constituent};
                    // Only a generic whole input can instantiate to a Sender.
                    // A row, callable or nested resource remains its own duty.
                    if required.mode != CopyMode::Mutable
                        || !required.constituents.iter().any(|part| {
                            part.path.is_empty()
                                && matches!(
                                    part.qualification,
                                    Constituent::Deferred(AbstractMember::DataBinder(_))
                                )
                        })
                    {
                        return None;
                    }
                    let template_event = required
                        .source_event
                        .and_then(|id| events.get(id.0 as usize))?;
                    if template_event.copy_operation != Some(CopyMode::Mutable)
                        || template_event.parent != required.invocation
                    {
                        return None;
                    }
                    call.resource_copies.iter().find_map(|id| {
                        let event = resources
                            .get(id.0 as usize)
                            .filter(|event| event.id == *id)?;
                        let syntax = event
                            .source_event
                            .and_then(|id| events.get(id.0 as usize))?;
                        (event.owner == required.owner
                            && event.span == required.span
                            && sender_contract(event, call, syntax))
                        .then_some(CopyDischarge::Sender(*id))
                    })
                };
                if let Some(proof) = ordinary.or_else(sender) {
                    discharges.insert((call.id, required.id), proof);
                    true
                } else {
                    false
                }
            });
        let qualification = if call.status == CopyInvocationStatus::Rejected {
            domain::Qualification::Rejected
        } else if call.status == CopyInvocationStatus::Completed && pending.is_empty() && coverage {
            domain::Qualification::Established
        } else {
            domain::Qualification::Pending
        };
        actual.push(domain::Instance {
            id: call.id,
            site: domain::Site {
                owner: call.caller,
                target: call.target,
                source: (call.span.file.0, call.span.start, call.span.end),
            },
            qualification,
        });
    }
    Ok(InstanceProofs { actual, discharges })
}

pub(crate) fn validate_events(facts: &SemanticFacts) -> Result<(), String> {
    use super::model::Callable;
    let mut expected = BTreeMap::<_, usize>::new();
    for (expression, fact) in facts.expressions.iter().enumerate() {
        for callable in &fact.value.callables {
            if let Callable::Named(index) = callable {
                let target = facts
                    .functions
                    .get(*index)
                    .ok_or("copy reference has an unknown callable")?
                    .definition;
                *expected.entry((expression, target)).or_default() += 1;
            }
        }
    }
    let contexts: BTreeMap<_, _> = facts
        .invocation_expressions
        .iter()
        .map(|expression| (expression.expression, expression.context))
        .collect();
    for (index, reference) in facts.copy_references.iter().enumerate() {
        if reference.id.0 as usize != index
            || facts
                .expressions
                .get(reference.expression)
                .is_none_or(|fact| fact.span != reference.span)
            || contexts.get(&reference.expression).is_none_or(|context| {
                context.owner != reference.owner || context.invocation != reference.parent
            })
        {
            return Err("copy reference event identity differs from its expression".into());
        }
        let count = expected
            .get_mut(&(reference.expression, reference.target))
            .ok_or("copy reference event has no matching expression")?;
        if *count == 0 {
            return Err("copy reference event is duplicated".into());
        }
        *count -= 1;
        if let Some(id) = reference.direct_call {
            let event = facts
                .copy_call_events
                .get(id.0 as usize)
                .ok_or("copy reference has no call event")?;
            if !event.direct
                || event.target != Some(reference.target)
                || event.owner != reference.owner
                || event.parent != reference.parent
                || !event.references.contains(&reference.id)
            {
                return Err("copy reference does not belong to its direct call event".into());
            }
        }
    }
    if expected.values().any(|count| *count != 0) {
        return Err("copy reference event coverage is incomplete".into());
    }
    for (index, event) in facts.copy_call_events.iter().enumerate() {
        if event.id.0 as usize != index {
            return Err("copy call event identity is invalid".into());
        }
        if event.copy_operation.is_some() {
            let Some(expression) = event.callee_expression else {
                return Err("copy operation has no evaluated callee evidence".into());
            };
            let actual = facts.expressions.get(expression).and_then(|fact| {
                match fact.value.callables.as_slice() {
                    [Callable::Builtin(name)]
                        if matches!(name.as_str(), "clone" | "Prelude::clone") =>
                    {
                        Some(CopyMode::Mutable)
                    }
                    [Callable::Builtin(name)]
                        if matches!(name.as_str(), "clone_immut" | "Prelude::clone_immut") =>
                    {
                        Some(CopyMode::Immutable)
                    }
                    _ => None,
                }
            });
            if actual != event.copy_operation
                || contexts.get(&expression).is_none_or(|context| {
                    context.owner != event.owner || context.invocation != event.parent
                })
            {
                return Err("copy operation differs from its evaluated callee evidence".into());
            }
        }
        if event.direct && (event.target.is_none() || event.references.is_empty()) {
            return Err("direct copy call event has no callee evidence".into());
        }
        let mut seen = BTreeSet::new();
        for id in &event.references {
            let reference = facts
                .copy_references
                .get(id.0 as usize)
                .ok_or("copy call event has a missing callee reference")?;
            if !seen.insert(*id)
                || (event.direct
                    && (reference.direct_call != Some(event.id)
                        || Some(reference.target) != event.target
                        || reference.owner != event.owner
                        || reference.parent != event.parent))
            {
                return Err("copy call event does not own its direct references".into());
            }
        }
    }
    let mut used = BTreeSet::new();
    for (index, call) in facts.copy_invocations.iter().enumerate() {
        if call.id.0 as usize != index {
            return Err("copy invocation identity is invalid".into());
        }
        let direct = if let Some(id) = call.source_event {
            let event = facts
                .copy_call_events
                .get(id.0 as usize)
                .ok_or("copy invocation has a missing syntax event")?;
            if event.owner != call.caller_owner
                || event.span != call.span
                || event.parent != call.parent
            {
                return Err("copy invocation borrowed another syntax event".into());
            }
            let direct = event.direct && event.target == Some(call.target);
            if direct && !used.insert(id) {
                return Err("direct copy call event was consumed more than once".into());
            }
            direct
        } else {
            false
        };
        if call.direct != direct || (call.declaration_probe && call.source_event.is_some()) {
            return Err("copy invocation directness differs from its syntax event".into());
        }
    }
    Ok(())
}

pub fn validate(facts: &SemanticFacts) -> Result<(), String> {
    let owners = template_owners(&facts.copy_boundaries, &facts.copy_invocations);
    if !facts
        .copy_boundaries
        .iter()
        .any(|boundary| boundary.template)
    {
        return if facts.copy_template_closure.is_none() {
            Ok(())
        } else {
            Err("copy template certificate has no template".into())
        };
    }
    let Some(closure) = &facts.copy_template_closure else {
        return Err("copy templates lack a closed actual-instance certificate".into());
    };
    validate_events(facts)?;
    if owners != closure.templates.keys().copied().collect() {
        return Err("copy template owner coverage differs".into());
    }
    for boundary in facts
        .copy_boundaries
        .iter()
        .filter(|boundary| boundary.template)
    {
        if boundary.output.is_some()
            || !boundary.output_nodes.is_empty()
            || !boundary.output_relations.is_empty()
            || boundary.requirements.is_empty()
            || boundary.template_root.is_none_or(|id| {
                facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .is_none_or(|call| !call.declaration_probe)
            })
        {
            return Err("conditional copy boundary cannot be an established output".into());
        }
    }
    let actual = instances(
        &closure.templates,
        &facts.copy_boundaries,
        &facts.copy_invocations,
        &facts.copy_call_events,
        &facts.resource_clones,
    )?;
    if actual.discharges != closure.discharges {
        return Err("copy template resource/ordinary discharge choices differ".into());
    }
    for proof in closure.discharges.values() {
        if let super::resource_copy::CopyDischarge::Sender(id) = proof {
            let event = facts
                .resource_clones
                .get(id.0 as usize)
                .ok_or("Sender discharge references a missing intrinsic event")?;
            let boundary = event
                .boundary
                .as_ref()
                .ok_or("Sender discharge lacks its checked boundary")?;
            if !facts.concurrent_boundaries.iter().any(|registered| {
                registered.kind == super::ConcurrentBoundaryKind::CloneSender
                    && registered.cause == boundary.cause
                    && registered.span == boundary.span
            }) || !facts.explanations.causes.iter().any(|cause| {
                cause.id == boundary.cause && cause.parents.contains(&event.source.value.cause)
            }) {
                return Err(
                    "Sender discharge did not originate from its checked resource boundary".into(),
                );
            }
        }
    }
    let rebuilt = domain::close(&closure.templates, &actual.actual)
        .map_err(|error| format!("copy template closure remains unproved: {error:?}"))?;
    if rebuilt != closure.certificate {
        return Err("copy template certificate omits or changes an actual instance".into());
    }
    for (&owner, template) in &closure.templates {
        let escaped = facts
            .copy_references
            .iter()
            .any(|reference| reference.target == owner && reference.direct_call.is_none())
            || facts
                .copy_invocations
                .iter()
                .any(|call| !call.declaration_probe && call.target == owner && !call.direct);
        if template.escaped != escaped {
            return Err("copy template extraction coverage differs".into());
        }
        if !facts
            .functions
            .iter()
            .any(|function| function.definition == owner)
            || facts.functions.iter().any(|function| {
                function.definition == owner
                    && function.syntax.visibility == ril_syntax::ast::Visibility::Public
            })
        {
            return Err("copy template owner is not a private checked declaration".into());
        }
        let mut dependencies = BTreeSet::new();
        for probe in facts
            .copy_invocations
            .iter()
            .filter(|call| call.declaration_probe && call.target == owner)
        {
            for call in facts
                .copy_invocations
                .iter()
                .filter(|call| !call.declaration_probe && owners.contains(&call.target))
            {
                if executed_within(&facts.copy_invocations, probe.id, call.id) {
                    dependencies.insert(call.target);
                }
            }
        }
        if dependencies != template.dependencies {
            return Err("copy template dependency closure differs".into());
        }
        let sites: BTreeSet<_> = facts
            .copy_invocations
            .iter()
            .filter(|call| !call.declaration_probe && call.target == owner)
            .map(|call| domain::Site {
                owner: call.caller,
                target: owner,
                source: (call.span.file.0, call.span.start, call.span.end),
            })
            .collect();
        if sites != template.sites {
            return Err("copy template certificate does not cover every call site".into());
        }
    }
    Ok(())
}
