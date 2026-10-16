//! Value-indexed copy preconditions. A deferred condition is not a positive
//! eligibility fact and cannot be discharged from a type or row name alone.
use super::facts::NodeId;
use super::model::rows::RowIdentity;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AbstractMember {
    DataBinder(String),
    RowBinder(RowIdentity),
    CallableEnvironment,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dependency {
    /// Actual abstract value identity, independent of its type binder.
    pub source: NodeId,
    pub member: AbstractMember,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rejection {
    Resource,
    RetainedEnvironment,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constituent {
    /// Ordinary live or readonly data can be copied. Explicit immutable
    /// descendants affect the output graph, not source copy eligibility.
    Ordinary,
    EnvironmentFreeCallable,
    Deferred(AbstractMember),
    Rejected(Rejection),
    /// Missing graph/carrier evidence is distinct from a declared binder.
    Incomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub constituent: Constituent,
    pub children: BTreeSet<NodeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Requirements {
    pub deferred: BTreeSet<Dependency>,
    pub rejected: BTreeSet<(NodeId, Rejection)>,
    pub incomplete: BTreeSet<NodeId>,
}

impl Requirements {
    pub fn established(&self) -> bool {
        self.deferred.is_empty() && self.rejected.is_empty() && self.incomplete.is_empty()
    }

    /// A caller inherits every reachable requirement of every admitted target.
    /// Another branch's successful copy is never evidence for this source.
    pub fn include(&mut self, other: &Self) {
        self.deferred.extend(other.deferred.iter().cloned());
        self.rejected.extend(other.rejected.iter().copied());
        self.incomplete.extend(&other.incomplete);
    }

    /// Instantiate each symbolic input with its complete actual graph. Unknown
    /// actual constituents remain requirements anchored to their own origins.
    pub fn instantiate(
        &self,
        arguments: &BTreeMap<NodeId, BTreeSet<NodeId>>,
        actual: &BTreeMap<NodeId, Node>,
    ) -> Self {
        let mut result = Self {
            rejected: self.rejected.clone(),
            incomplete: self.incomplete.clone(),
            ..Self::default()
        };
        for dependency in &self.deferred {
            match arguments.get(&dependency.source) {
                Some(roots) if !roots.is_empty() => result.include(&assess(actual, roots)),
                _ => {
                    // An empty origin set is not automatically a scalar; that
                    // fact must come from an explicit ordinary constituent.
                    result.incomplete.insert(dependency.source);
                }
            }
        }
        result
    }
}

pub fn assess(graph: &BTreeMap<NodeId, Node>, roots: &BTreeSet<NodeId>) -> Requirements {
    let mut result = Requirements::default();
    let mut seen = BTreeSet::new();
    let mut pending: Vec<_> = roots.iter().copied().collect();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        let Some(value) = graph.get(&node) else {
            result.incomplete.insert(node);
            continue;
        };
        match &value.constituent {
            Constituent::Ordinary | Constituent::EnvironmentFreeCallable => {}
            Constituent::Deferred(member) => {
                result.deferred.insert(Dependency {
                    source: node,
                    member: member.clone(),
                });
            }
            Constituent::Rejected(reason) => {
                result.rejected.insert((node, *reason));
            }
            Constituent::Incomplete => {
                result.incomplete.insert(node);
            }
        }
        pending.extend(&value.children);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_eligibility_matches_an_independent_concrete_reachability_oracle() {
        // Exhaust every three-object graph, placement of one forbidden object,
        // and root. Cycles or fresh outer shells cannot hide the bad member.
        for edges in 0u16..512 {
            for rejected in 0..3 {
                let graph: BTreeMap<_, _> = (0..3)
                    .map(|a| {
                        (
                            NodeId(a),
                            Node {
                                constituent: if a == rejected {
                                    Constituent::Rejected(Rejection::Resource)
                                } else {
                                    Constituent::Ordinary
                                },
                                children: (0..3)
                                    .filter(|b| edges & (1 << (a * 3 + b)) != 0)
                                    .map(NodeId)
                                    .collect(),
                            },
                        )
                    })
                    .collect();
                let mut reach = [[false; 3]; 3];
                for (a, row) in reach.iter_mut().enumerate() {
                    for (b, cell) in row.iter_mut().enumerate() {
                        *cell = a == b || edges & (1 << (a * 3 + b)) != 0;
                    }
                }
                for middle in 0..3 {
                    for a in 0..3 {
                        for b in 0..3 {
                            reach[a][b] |= reach[a][middle] && reach[middle][b];
                        }
                    }
                }
                for root in 0..3 {
                    let requirements = assess(&graph, &[NodeId(root)].into());
                    assert_eq!(
                        requirements.established(),
                        !reach[root as usize][rejected as usize]
                    );
                }
            }
        }
    }

    #[test]
    fn same_binder_in_separate_values_has_separate_call_requirements() {
        let graph = [
            (
                NodeId(0),
                Node {
                    constituent: Constituent::Deferred(AbstractMember::RowBinder(
                        RowIdentity::Binder("R".into()),
                    )),
                    children: BTreeSet::new(),
                },
            ),
            (
                NodeId(1),
                Node {
                    constituent: Constituent::Deferred(AbstractMember::RowBinder(
                        RowIdentity::Binder("R".into()),
                    )),
                    children: BTreeSet::new(),
                },
            ),
        ]
        .into();
        let requirements = assess(&graph, &[NodeId(0), NodeId(1)].into());
        assert_eq!(requirements.deferred.len(), 2);
        let actual = [
            (
                NodeId(2),
                Node {
                    constituent: Constituent::Ordinary,
                    children: BTreeSet::new(),
                },
            ),
            (
                NodeId(3),
                Node {
                    constituent: Constituent::Rejected(Rejection::RetainedEnvironment),
                    children: BTreeSet::new(),
                },
            ),
        ]
        .into();
        let checked = requirements.instantiate(
            &[
                (NodeId(0), [NodeId(2)].into()),
                (NodeId(1), [NodeId(3)].into()),
            ]
            .into(),
            &actual,
        );
        assert!(!checked.established());
        assert_eq!(
            checked.rejected,
            [(NodeId(3), Rejection::RetainedEnvironment)].into()
        );
        assert!(
            !requirements
                .instantiate(&[(NodeId(0), [NodeId(2)].into())].into(), &actual)
                .established()
        );
    }

    #[test]
    fn helper_forwarding_and_joins_never_discard_unresolved_or_missing_members() {
        let source = [(
            NodeId(0),
            Node {
                constituent: Constituent::Deferred(AbstractMember::DataBinder("T".into())),
                children: BTreeSet::new(),
            },
        )]
        .into();
        let requirements = assess(&source, &[NodeId(0)].into());
        let forwarded = [(
            NodeId(1),
            Node {
                constituent: Constituent::Deferred(AbstractMember::DataBinder("U".into())),
                children: BTreeSet::new(),
            },
        )]
        .into();
        let requirements =
            requirements.instantiate(&[(NodeId(0), [NodeId(1)].into())].into(), &forwarded);
        assert_eq!(requirements.deferred.first().unwrap().source, NodeId(1));
        let complete = [(
            NodeId(2),
            Node {
                constituent: Constituent::EnvironmentFreeCallable,
                children: BTreeSet::new(),
            },
        )]
        .into();
        assert!(
            requirements
                .instantiate(&[(NodeId(1), [NodeId(2)].into())].into(), &complete)
                .established()
        );
        let mut merged = Requirements::default();
        merged.include(&requirements);
        merged.include(&assess(
            &[(
                NodeId(3),
                Node {
                    constituent: Constituent::Incomplete,
                    children: BTreeSet::new(),
                },
            )]
            .into(),
            &[NodeId(3)].into(),
        ));
        assert!(!merged.established());
        assert_eq!(merged.deferred, requirements.deferred);
        assert_eq!(merged.incomplete, [NodeId(3)].into());
    }

    #[test]
    fn callable_shape_does_not_prove_an_environment_free_value() {
        let requirements = assess(
            &[(
                NodeId(0),
                Node {
                    constituent: Constituent::Deferred(AbstractMember::CallableEnvironment),
                    children: BTreeSet::new(),
                },
            )]
            .into(),
            &[NodeId(0)].into(),
        );
        assert!(!requirements.established());
        for (constituent, eligible) in [
            (Constituent::EnvironmentFreeCallable, true),
            (Constituent::Rejected(Rejection::RetainedEnvironment), false),
            (Constituent::Incomplete, false),
        ] {
            let actual = [(
                NodeId(1),
                Node {
                    constituent,
                    children: BTreeSet::new(),
                },
            )]
            .into();
            let selected =
                requirements.instantiate(&[(NodeId(0), [NodeId(1)].into())].into(), &actual);
            assert_eq!(selected.established(), eligible);
        }
    }
}
