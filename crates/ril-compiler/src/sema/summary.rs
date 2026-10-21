//! Finite invocation summaries and dependency-driven monotone iteration.
use super::facts::{NodeId, Participant, ScopeId};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Access {
    Read,
    Write,
    Retain,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Footprint {
    pub origin: NodeId,
    pub participant: Participant,
    pub access: Access,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CallbackDependency {
    pub parameter: u32,
    pub projection: Vec<String>,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InvocationSummary {
    /// The actual named activation represented by this local summary.
    /// Dependency inclusion preserves its identity and never copies a callee's.
    pub activation: Option<ScopeId>,
    pub context: Option<super::effect_identity::InvocationContext>,
    pub channel_messages: BTreeSet<super::channel_messages::ChannelMessageId>,
    pub copy_boundaries: BTreeSet<super::copy_contract::CopyBoundaryId>,
    pub performed_operations: std::collections::BTreeSet<u64>,
    pub selected_handlers: BTreeSet<usize>,
    pub handler_environment: bool,
    pub accesses: BTreeSet<Footprint>,
    pub concrete_state: BTreeMap<u32, Access>,
    /// Actual formal callback callee observations, not concrete state accesses.
    pub symbolic_uses: BTreeSet<ril_compiler_core::ids::EvaluationOccurrenceId>,
    pub effects: BTreeSet<String>,
    pub callbacks: BTreeSet<CallbackDependency>,
    pub escaped_origins: BTreeSet<NodeId>,
    pub retained_origins: BTreeSet<NodeId>,
    pub new_environments: BTreeSet<NodeId>,
    pub owners: BTreeSet<ScopeId>,
    /// Unknown recursive/external dependencies cannot be treated as empty rows.
    pub unresolved: BTreeSet<u32>,
}
impl InvocationSummary {
    pub fn include(&mut self, other: &Self) {
        self.channel_messages.extend(&other.channel_messages);
        self.copy_boundaries.extend(&other.copy_boundaries);
        self.performed_operations
            .extend(&other.performed_operations);
        self.selected_handlers.extend(&other.selected_handlers);
        self.handler_environment |= other.handler_environment;
        self.accesses.extend(other.accesses.iter().cloned());
        for (&origin, &mode) in &other.concrete_state {
            self.concrete_state
                .entry(origin)
                .and_modify(|old| *old = (*old).max(mode))
                .or_insert(mode);
        }
        self.effects.extend(other.effects.iter().cloned());
        self.symbolic_uses.extend(&other.symbolic_uses);
        self.callbacks.extend(other.callbacks.iter().cloned());
        self.escaped_origins.extend(&other.escaped_origins);
        self.retained_origins.extend(&other.retained_origins);
        self.new_environments.extend(&other.new_environments);
        self.owners.extend(&other.owners);
        self.unresolved.extend(&other.unresolved);
    }
}

/// SCC-independent work queue. Strongly connected dependencies naturally reach
/// a fixed point because every summary component has a finite monotone domain.
/// Edges are explicit; a cycle alone contributes no authority or proof.
pub fn close_invocation_dependencies(
    local: &[InvocationSummary],
    callees: &[BTreeSet<usize>],
) -> Vec<InvocationSummary> {
    assert_eq!(local.len(), callees.len());
    let mut summaries = local.to_vec();
    let mut callers = vec![BTreeSet::new(); local.len()];
    for (caller, dependencies) in callees.iter().enumerate() {
        for &callee in dependencies {
            if let Some(users) = callers.get_mut(callee) {
                users.insert(caller);
            } else {
                summaries[caller].unresolved.insert(callee as u32);
            }
        }
    }
    let mut queued = vec![true; local.len()];
    let mut queue: VecDeque<_> = (0..local.len()).collect();
    while let Some(index) = queue.pop_front() {
        queued[index] = false;
        let mut next = summaries[index].clone();
        for &callee in &callees[index] {
            if let Some(summary) = summaries.get(callee) {
                next.include(summary);
            }
        }
        if next != summaries[index] {
            summaries[index] = next;
            for &caller in &callers[index] {
                if !queued[caller] {
                    queued[caller] = true;
                    queue.push_back(caller);
                }
            }
        }
    }
    summaries
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn recursive_dependencies_retain_effects_and_unknown_callees() {
        let mut local = vec![InvocationSummary::default(); 3];
        local[1].effects.insert("Log".into());
        let calls = vec![[1].into(), [0, 2].into(), [99].into()];
        let summaries = close_invocation_dependencies(&local, &calls);
        assert!(summaries[0].effects.contains("Log"));
        assert!(summaries[0].unresolved.contains(&99));
        assert_eq!(summaries, close_invocation_dependencies(&summaries, &calls));
    }
}
