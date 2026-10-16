//! Closed direct-call template proof domain. Frontend evidence distinguishes
//! declaration probes from every actual substitution and every escaped use;
//! final validation reconstructs these inputs before accepting the certificate.
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
