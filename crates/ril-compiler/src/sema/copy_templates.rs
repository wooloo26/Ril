//! Finite direct-call template analysis. Declaration probes, real instances
//! and escaped uses determine which deferred copy requirements can be discharged.
use super::copy_contract::*;
use ril_compiler_core::ids::DefinitionId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstanceId(pub u32);
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Site {
    pub owner: Option<DefinitionId>,
    pub target: DefinitionId,
    pub source: (u32, u32, u32),
}
#[derive(Debug, Clone)]
pub struct Template {
    pub public: bool,
    pub escaped: bool,
    /// All source uses must be exact direct calls, not just the calls observed
    /// on one successful path. Extraction or an unknown use sets `escaped`.
    pub sites: BTreeSet<Site>,
    pub dependencies: BTreeSet<DefinitionId>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Qualification {
    Established,
    Pending,
    Rejected,
}
#[derive(Debug, Clone)]
pub struct Instance {
    pub id: InstanceId,
    pub site: Site,
    /// An instance is one actual substitution, never a merged per-span row.
    pub qualification: Qualification,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    Exposed(DefinitionId),
    Uninstantiated(DefinitionId),
    MissingSite(Site),
    InvalidInstance(InstanceId),
    UnprovedInstance(InstanceId),
    MissingDependency(DefinitionId),
    Recursive(BTreeSet<DefinitionId>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Certificate {
    pub instances: BTreeMap<DefinitionId, BTreeSet<InstanceId>>,
    pub dependency_order: Vec<DefinitionId>,
}

pub fn close(
    templates: &BTreeMap<DefinitionId, Template>,
    actual: &[Instance],
) -> Result<Certificate, Failure> {
    let mut instances: BTreeMap<DefinitionId, BTreeSet<InstanceId>> = BTreeMap::new();
    let mut checked_sites = BTreeSet::new();
    let mut ids = BTreeSet::new();
    for instance in actual {
        if !ids.insert(instance.id)
            || !templates
                .get(&instance.site.target)
                .is_some_and(|template| template.sites.contains(&instance.site))
        {
            return Err(Failure::InvalidInstance(instance.id));
        }
        // A nearby success, including at exactly the same source span, cannot
        // discharge a different actual instance's condition.
        if instance.qualification != Qualification::Established {
            return Err(Failure::UnprovedInstance(instance.id));
        }
        checked_sites.insert(instance.site.clone());
        instances
            .entry(instance.site.target)
            .or_default()
            .insert(instance.id);
    }
    for (&owner, template) in templates {
        if template.public || template.escaped {
            return Err(Failure::Exposed(owner));
        }
        if !instances.contains_key(&owner) {
            return Err(Failure::Uninstantiated(owner));
        }
        for site in &template.sites {
            if site.target != owner || !checked_sites.contains(site) {
                return Err(Failure::MissingSite(site.clone()));
            }
        }
        for dependency in &template.dependencies {
            if !templates.contains_key(dependency) {
                return Err(Failure::MissingDependency(*dependency));
            }
        }
    }
    let mut remaining: BTreeSet<_> = templates.keys().copied().collect();
    let mut dependency_order = Vec::new();
    while !remaining.is_empty() {
        let ready = remaining
            .iter()
            .copied()
            .find(|owner| templates[owner].dependencies.is_disjoint(&remaining));
        let Some(owner) = ready else {
            return Err(Failure::Recursive(remaining));
        };
        remaining.remove(&owner);
        dependency_order.push(owner);
    }
    Ok(Certificate {
        instances,
        dependency_order,
    })
}

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

pub fn ancestor(calls: &[CopyInvocation], mut child: InstanceId, parent: InstanceId) -> bool {
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

pub struct InstanceSet {
    pub actual: Vec<Instance>,
    pub discharges: BTreeMap<(InstanceId, CopyBoundaryId), super::resource_copy::CopyDischarge>,
}

pub fn instances(
    templates: &BTreeMap<DefinitionId, Template>,
    boundaries: &[CopyBoundary],
    calls: &[CopyInvocation],
    events: &[CopyCallEvent],
    resources: &[super::resource_copy::ResourceCloneEvent],
) -> Result<InstanceSet, String> {
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
            Qualification::Rejected
        } else if call.status == CopyInvocationStatus::Completed && pending.is_empty() && coverage {
            Qualification::Established
        } else {
            Qualification::Pending
        };
        actual.push(Instance {
            id: call.id,
            site: Site {
                owner: call.caller,
                target: call.target,
                source: (call.span.file.0, call.span.start, call.span.end),
            },
            qualification,
        });
    }
    Ok(InstanceSet { actual, discharges })
}
