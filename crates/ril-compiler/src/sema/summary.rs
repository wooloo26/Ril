//! Finite invocation summaries and dependency-driven monotone iteration.
use super::facts::{NodeId, Participant, ScopeId};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
mod identities;
pub(crate) use identities::validate;

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
    /// The actual callable activation represented by this local summary.
    /// Dependency inclusion preserves its identity and never copies a callee's.
    pub activation: Option<ScopeId>,
    pub context: Option<super::effect_identity::InvocationContext>,
    pub channel_messages: BTreeSet<super::channel_messages::ChannelMessageId>,
    pub copy_boundaries: BTreeSet<super::copy_contract::CopyBoundaryId>,
    pub performed_operations: std::collections::BTreeSet<u64>,
    pub selected_handlers: BTreeSet<usize>,
    pub handler_environment: bool,
    pub parameter_write: bool,
    pub retention: bool,
    pub capture: bool,
    pub accesses: BTreeSet<Footprint>,
    /// Named state accesses, keyed by binding identity rather than heap origin.
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
    /// Preserve all latent contract axes from a checked frame. This projection
    /// is a claim about that frame, not a certificate of row satisfaction.
    pub(crate) fn from_obligations(obligations: &super::model::Obligations) -> Self {
        let mut summary = Self {
            copy_boundaries: obligations.copy_boundaries.clone(),
            performed_operations: obligations.performed_operations.clone(),
            selected_handlers: obligations.selected_handlers.clone(),
            handler_environment: obligations.handler_environment,
            parameter_write: obligations.parameter_write,
            retention: obligations.retention,
            capture: obligations.capture,
            effects: obligations.effects.clone(),
            symbolic_uses: obligations.symbolic_uses.clone(),
            ..Self::default()
        };
        for (&binding, &mode) in &obligations.named {
            summary.concrete_state.insert(binding as u32, mode.into());
        }
        for access in &obligations.accesses {
            for &origin in &access.origins.nodes {
                for &participant in &access.participants {
                    summary.accesses.insert(Footprint {
                        origin,
                        participant,
                        access: access.mode.into(),
                    });
                }
            }
        }
        summary
    }

    pub fn include(&mut self, other: &Self) {
        self.channel_messages.extend(&other.channel_messages);
        self.copy_boundaries.extend(&other.copy_boundaries);
        self.performed_operations
            .extend(&other.performed_operations);
        self.selected_handlers.extend(&other.selected_handlers);
        self.handler_environment |= other.handler_environment;
        self.parameter_write |= other.parameter_write;
        self.retention |= other.retention;
        self.capture |= other.capture;
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

impl From<super::model::Mode> for Access {
    fn from(mode: super::model::Mode) -> Self {
        match mode {
            super::model::Mode::Read => Self::Read,
            super::model::Mode::Write => Self::Write,
            super::model::Mode::Retain => Self::Retain,
        }
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
        local[1].parameter_write = true;
        local[2].retention = true;
        local[2].capture = true;
        let calls = vec![[1].into(), [0, 2].into(), [99].into()];
        let summaries = close_invocation_dependencies(&local, &calls);
        assert!(summaries[0].effects.contains("Log"));
        assert!(summaries[0].unresolved.contains(&99));
        assert!(summaries[0].parameter_write && summaries[0].retention && summaries[0].capture);
        assert_eq!(summaries, close_invocation_dependencies(&summaries, &calls));
    }

    #[test]
    fn entered_closures_and_named_calls_keep_distinct_summaries_through_core() {
        use ril_compiler_core::ids::InvocationSummaryId;
        let source = r#"
fn plus(value: int) -> int { value + 1 }
fn append(mut values: []int) &mut { Array::push(mut values, 1) }
pub fn example() {
    let call = \value: int -> plus(value)
    assert(call(2) == 3)
    assert(call(3) == 4)
    let mut values: []int = []
    let write = \mut values: []int -> { Array::push(mut values, 2) }
    write(mut values)
    append(mut values)
}
"#;
        for target in ["pointer32", "pointer64"] {
            let verified = crate::Session::with_options(
                source.as_bytes().to_vec(),
                crate::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap();
            let facts = verified.facts();
            validate(facts, &mut 16384).unwrap();
            assert!(validate(facts, &mut 0).is_err());
            assert!(facts.copy_invocations.iter().any(|call| {
                call.summary
                    .is_some_and(|id| facts.invocations[id.0 as usize].parameter_write)
            }));
            let calls: Vec<_> = facts
                .closure_invocations
                .iter()
                .filter(|call| call.summary.is_some())
                .collect();
            assert!(calls.len() >= 3);
            assert!(calls.iter().any(|call| facts.invocations[call.summary.unwrap().0 as usize].parameter_write));
            let first = calls[0];
            let sibling = calls
                .iter()
                .find(|call| call.id != first.id && call.closure == first.closure)
                .unwrap();
            assert_ne!(first.summary, sibling.summary);
            assert_ne!(first.activation, sibling.activation);
            let _core = crate::lower::lower_core(&verified).unwrap();
            for mutation in 0..6 {
                let mut changed = facts.clone();
                let id = first.summary.unwrap();
                match mutation {
                    0 => changed.closure_invocations[first.id.0 as usize].summary = None,
                    1 => changed.closure_invocations[first.id.0 as usize].summary = sibling.summary,
                    2 => {
                        changed.closure_invocations[first.id.0 as usize].summary =
                            Some(InvocationSummaryId(u32::MAX))
                    }
                    3 => changed.invocations[id.0 as usize].activation = sibling.activation,
                    4 => changed.invocations[id.0 as usize].context = None,
                    5 => changed
                        .invocations
                        .push(changed.invocations[id.0 as usize].clone()),
                    _ => unreachable!(),
                }
                assert!(
                    validate(&changed, &mut 16384).is_err(),
                    "mutation {mutation} accepted"
                );
            }
        }
    }
}
