//! Provenance identities, heap shape, permission lattice and explanation graph.
use super::relations::{Conditions, Pivot, Relation};
use ril_compiler_core::{
    diagnostic::{Cause, CauseId},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SiteId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ScopeId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LoanId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RootId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Permission {
    Read,
    Write,
}
impl Permission {
    pub fn meet(self, other: Self) -> Self {
        self.min(other)
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Publication {
    Immutable,
    Live,
    Unpublished,
}
impl Publication {
    pub fn join(self, other: Self) -> Self {
        if self == other { self } else { Self::Live }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Participant {
    Loan(LoanId),
    Root(RootId),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reference {
    pub origins: BTreeSet<NodeId>,
    pub permission: Permission,
    pub publication: Publication,
    pub participants: BTreeSet<Participant>,
    pub owner: ScopeId,
    pub cause: CauseId,
}
impl Reference {
    pub fn restrict(&mut self, permission: Permission) {
        self.permission = self.permission.meet(permission);
        if permission == Permission::Read && self.publication == Publication::Unpublished {
            // Read-only reception ends initial construction authority; it does
            // not imply immutability of the reachable graph.
            self.publication = Publication::Live;
        }
    }
    pub fn join(&self, other: &Self, cause: CauseId) -> Self {
        Self {
            origins: self.origins.union(&other.origins).copied().collect(),
            permission: self.permission.meet(other.permission),
            publication: self.publication.join(other.publication),
            participants: self
                .participants
                .union(&other.participants)
                .copied()
                .collect(),
            owner: self.owner.min(other.owner),
            cause,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Slot {
    Field(String),
    /// A complete, opaque set of members carried by a rigid record row.
    /// This edge participates in graph traversal but is never a user projection.
    RowTail(super::model::rows::RowIdentity),
    Tuple(u32),
    Index(i64),
    AnyIndex,
    Capture(u32),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OriginKind {
    Formal(Pivot),
    Global,
    Fresh(SiteId),
    Older(SiteId),
    Environment,
    Opaque,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Multiplicity {
    One,
    MayMany,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeapNode {
    pub kind: OriginKind,
    pub multiplicity: Multiplicity,
    pub owner: ScopeId,
    pub fields: BTreeMap<Slot, BTreeSet<NodeId>>,
    pub writable_roots: BTreeSet<RootId>,
    pub escaping: bool,
    pub cause: CauseId,
}

/// The shape graph has finite program-site/summary nodes; cycles are backedges.
#[derive(Debug, Clone, Default)]
pub struct Heap {
    pub nodes: Vec<HeapNode>,
    relations: BTreeMap<(NodeId, NodeId), Relation>,
    recent: BTreeMap<SiteId, NodeId>,
    older: BTreeMap<SiteId, NodeId>,
    pub conditions: Conditions,
}
impl Heap {
    pub fn relations(&self) -> impl Iterator<Item = (NodeId, NodeId, Relation)> + '_ {
        self.relations
            .iter()
            .map(|(&(a, b), &relation)| (a, b, relation))
    }
    pub fn insert(&mut self, node: HeapNode) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }
    pub fn symbolic(&mut self, pivot: Pivot, owner: ScopeId, cause: CauseId) -> NodeId {
        let id = self.insert(HeapNode {
            kind: OriginKind::Formal(pivot),
            multiplicity: Multiplicity::One,
            owner,
            fields: BTreeMap::new(),
            writable_roots: BTreeSet::new(),
            escaping: false,
            cause,
        });
        for i in 0..id.0 {
            if let OriginKind::Formal(other) = self.nodes[i as usize].kind {
                let relation = Relation::symbolic(&mut self.conditions, pivot, other);
                self.set_relation(id, NodeId(i), relation);
            }
        }
        id
    }
    pub fn fresh(
        &mut self,
        site: SiteId,
        owner: ScopeId,
        cause: CauseId,
    ) -> (NodeId, Option<(NodeId, NodeId)>) {
        self.fresh_in_scopes(site, owner, cause, &BTreeMap::new())
    }
    pub(crate) fn fresh_in_scopes(
        &mut self,
        site: SiteId,
        owner: ScopeId,
        cause: CauseId,
        parents: &BTreeMap<ScopeId, ScopeId>,
    ) -> (NodeId, Option<(NodeId, NodeId)>) {
        if let Some(&recent) = self.recent.get(&site) {
            let previous = self.nodes[recent.0 as usize].clone();
            let had_older = self.older.contains_key(&site);
            let older = if let Some(&id) = self.older.get(&site) {
                self.nodes[id.0 as usize].owner =
                    common_owner(self.nodes[id.0 as usize].owner, previous.owner, parents);
                id
            } else {
                let id = self.insert(HeapNode {
                    kind: OriginKind::Older(site),
                    multiplicity: Multiplicity::MayMany,
                    // The history contains prior allocations, never the new
                    // allocation whose caller caused this recency transition.
                    owner: previous.owner,
                    fields: BTreeMap::new(),
                    writable_roots: BTreeSet::new(),
                    escaping: false,
                    cause: previous.cause,
                });
                self.older.insert(site, id);
                id
            };
            // Older denotes every earlier batch. A new member may invalidate
            // a sufficient equality/disjointness condition from its history.
            // Capture these relations before resetting the recent node.
            for index in 0..self.nodes.len() {
                let other = NodeId(index as u32);
                if other == recent || other == older {
                    continue;
                }
                let moved = self.relation(recent, other);
                let relation = if had_older {
                    self.relation(older, other)
                        .join(moved, &mut self.conditions)
                } else {
                    moved
                };
                self.set_relation(older, other, relation);
            }
            for (slot, origins) in previous.fields {
                self.nodes[older.0 as usize]
                    .fields
                    .entry(slot)
                    .or_default()
                    .extend(
                        origins
                            .into_iter()
                            .map(|id| if id == recent { older } else { id }),
                    );
            }
            self.nodes[older.0 as usize]
                .writable_roots
                .extend(previous.writable_roots);
            self.nodes[older.0 as usize].escaping |= previous.escaping;
            for node in &mut self.nodes {
                for origins in node.fields.values_mut() {
                    if origins.remove(&recent) {
                        origins.insert(older);
                    }
                }
            }
            self.nodes[recent.0 as usize] = HeapNode {
                kind: OriginKind::Fresh(site),
                multiplicity: Multiplicity::One,
                owner,
                fields: BTreeMap::new(),
                writable_roots: BTreeSet::new(),
                escaping: false,
                cause,
            };
            self.relations.remove(&(recent, recent));
            for i in 0..self.nodes.len() {
                if NodeId(i as u32) != recent {
                    self.set_relation(recent, NodeId(i as u32), Relation::DISJOINT);
                }
            }
            (recent, Some((recent, older)))
        } else {
            let id = self.insert(HeapNode {
                kind: OriginKind::Fresh(site),
                multiplicity: Multiplicity::One,
                owner,
                fields: BTreeMap::new(),
                writable_roots: BTreeSet::new(),
                escaping: false,
                cause,
            });
            self.recent.insert(site, id);
            for i in 0..id.0 {
                self.set_relation(id, NodeId(i), Relation::DISJOINT);
            }
            (id, None)
        }
    }
    pub fn relation(&self, a: NodeId, b: NodeId) -> Relation {
        if a == b {
            if self.nodes[a.0 as usize].multiplicity == Multiplicity::MayMany {
                return Relation::UNKNOWN;
            }
            if let Some(relation) = self.relations.get(&(a, b)) {
                return *relation;
            }
            return if matches!(self.nodes[a.0 as usize].kind, OriginKind::Older(_)) {
                Relation::UNKNOWN
            } else {
                Relation::EQUAL
            };
        }
        *self
            .relations
            .get(&(a.min(b), a.max(b)))
            .unwrap_or(&Relation::UNKNOWN)
    }
    pub fn set_relation(&mut self, a: NodeId, b: NodeId, relation: Relation) {
        if a == b && relation.equal != super::relations::Condition::TRUE {
            self.nodes[a.0 as usize].multiplicity = Multiplicity::MayMany;
        }
        let relation = if a == b && self.nodes[a.0 as usize].multiplicity == Multiplicity::MayMany {
            Relation::UNKNOWN
        } else {
            relation
        };
        self.relations.insert((a.min(b), a.max(b)), relation);
    }
    /// Only a separate exact-member certificate may refine a formal family.
    /// Recency summaries can never be restored to singleton objects.
    pub(crate) fn prove_singleton_formal(&mut self, node: NodeId) {
        assert!(matches!(
            self.nodes[node.0 as usize].kind,
            OriginKind::Formal(_)
        ));
        self.nodes[node.0 as usize].multiplicity = Multiplicity::One;
        self.relations.remove(&(node, node));
    }
    pub fn reachable(&self, roots: impl IntoIterator<Item = NodeId>) -> BTreeSet<NodeId> {
        let mut seen = BTreeSet::new();
        let mut work: Vec<_> = roots.into_iter().collect();
        while let Some(id) = work.pop() {
            if seen.insert(id) {
                for targets in self.nodes[id.0 as usize].fields.values() {
                    work.extend(targets);
                }
            }
        }
        seen
    }
}

/// An owner used to exempt local accesses must enclose every represented
/// allocation. Unknown or unrelated ancestry falls back to the global scope.
fn common_owner(a: ScopeId, b: ScopeId, parents: &BTreeMap<ScopeId, ScopeId>) -> ScopeId {
    let ancestors = |mut owner| {
        let mut result = Vec::new();
        while !result.contains(&owner) {
            result.push(owner);
            let Some(parent) = parents.get(&owner) else {
                break;
            };
            owner = *parent;
        }
        result
    };
    let a = ancestors(a);
    ancestors(b)
        .into_iter()
        .find(|owner| a.contains(owner))
        .unwrap_or(ScopeId(0))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CauseKind {
    Source,
    Allocation,
    Projection,
    Restriction,
    BranchJoin,
    Call,
    Capture,
    Retention,
    Loan,
    Escape,
    Handler,
    Cleanup,
    MissingProof,
}
#[derive(Debug, Clone, Default)]
pub struct Explanations {
    pub causes: Vec<Cause>,
    pub kinds: Vec<CauseKind>,
}
impl Explanations {
    pub fn add(
        &mut self,
        kind: CauseKind,
        span: Option<Span>,
        description: impl Into<String>,
        parents: impl IntoIterator<Item = CauseId>,
    ) -> CauseId {
        let id = CauseId(self.causes.len() as u32);
        self.causes.push(Cause {
            id,
            span,
            description: description.into(),
            parents: parents.into_iter().collect(),
        });
        self.kinds.push(kind);
        id
    }
    pub fn chain(&self, id: CauseId) -> Vec<Cause> {
        let mut visited = BTreeSet::new();
        let mut work = vec![id];
        while let Some(id) = work.pop() {
            if visited.insert(id.0) {
                work.extend(self.causes[id.0 as usize].parents.iter().copied());
            }
        }
        visited
            .into_iter()
            .map(|i| self.causes[i as usize].clone())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::relations::Condition;
    #[test]
    fn allocation_history_owners_enclose_every_prior_concrete_owner() {
        let parents: BTreeMap<_, _> = [
            (ScopeId(1), ScopeId(0)),
            (ScopeId(2), ScopeId(1)),
            (ScopeId(3), ScopeId(1)),
            (ScopeId(4), ScopeId(2)),
        ]
        .into();
        let encloses = |mut child: ScopeId, owner: ScopeId| {
            loop {
                if child == owner {
                    return true;
                }
                let Some(parent) = parents.get(&child) else {
                    return false;
                };
                child = *parent;
            }
        };
        for sequence in 0..625usize {
            let mut heap = Heap::default();
            let mut prior = Vec::new();
            let mut selected = sequence;
            for index in 0..4 {
                let owner = ScopeId((selected % 5) as u32);
                selected /= 5;
                let (recent, movement) =
                    heap.fresh_in_scopes(SiteId(0), owner, CauseId(index), &parents);
                assert_eq!(heap.nodes[recent.0 as usize].owner, owner);
                if let Some((_, older)) = movement {
                    let history = &heap.nodes[older.0 as usize];
                    assert!(
                        prior
                            .iter()
                            .all(|previous| encloses(*previous, history.owner)),
                        "{prior:?} -> {history:?}"
                    );
                    if prior.iter().all(|previous| *previous == prior[0]) {
                        assert_eq!(
                            history.owner, prior[0],
                            "a new allocation cannot claim older history"
                        );
                    }
                    assert_eq!(history.multiplicity, Multiplicity::MayMany);
                }
                prior.push(owner);
            }
        }
        let mut heap = Heap::default();
        heap.fresh(SiteId(0), ScopeId(11), CauseId(0));
        heap.fresh(SiteId(0), ScopeId(12), CauseId(1));
        let (_, movement) = heap.fresh(SiteId(0), ScopeId(13), CauseId(2));
        assert_eq!(heap.nodes[movement.unwrap().1.0 as usize].owner, ScopeId(0));
    }

    #[test]
    fn access_transport_is_per_observation_and_preserves_participants_and_choices() {
        use crate::sema::model::{AccessFact, Mode, Origins};
        let movement = [(NodeId(0), NodeId(1)), (NodeId(0), NodeId(1))];
        for epoch in 0..=2 {
            for node in [NodeId(0), NodeId(1)] {
                let make = || AccessFact {
                    observed_recency: epoch,
                    recency: epoch,
                    origin_owners: [(
                        node,
                        crate::sema::model::AccessOwners::Known([ScopeId(3)].into()),
                    )]
                    .into(),
                    origins: Origins {
                        nodes: [node].into(),
                        choices: [(7, vec![[node].into(), [node].into()])].into(),
                    },
                    slot: Some(Slot::Field("value".into())),
                    mode: Mode::Write,
                    participants: [Participant::Root(RootId(3)), Participant::Loan(LoanId(4))]
                        .into(),
                    cause: CauseId(5),
                    span: Span {
                        file: ril_compiler_core::source::FileId(0),
                        start: 0,
                        end: 1,
                    },
                };
                let mut once = make();
                once.transport(&movement);
                let expected = if node == NodeId(0) && epoch < 2 {
                    NodeId(1)
                } else {
                    node
                };
                assert_eq!(once.origins.nodes, [expected].into());
                assert_eq!(
                    once.origins.choices[&7],
                    vec![[expected].into(), [expected].into()]
                );
                assert_eq!(once.participants, make().participants);
                assert_eq!(once.mode, Mode::Write);
                assert_eq!(once.cause, CauseId(5));
                assert_eq!(once.observed_recency, epoch);
                assert_eq!(
                    once.origin_owners,
                    [(
                        expected,
                        crate::sema::model::AccessOwners::Known([ScopeId(3)].into())
                    )]
                    .into()
                );
                let mut staged = make();
                staged.transport(&movement[..epoch.max(1)]);
                staged.transport(&movement);
                staged.transport(&movement);
                assert_eq!(staged.origins, once.origins);
                assert_eq!(staged.recency, 2);
            }
        }
    }
    #[test]
    fn access_owner_transport_unions_only_the_observed_sources_and_unknown_absorbs() {
        use crate::sema::model::{AccessFact, AccessOwners, Mode, Origins};
        let known = |id| AccessOwners::Known([ScopeId(id)].into());
        for right in [
            Some(known(4)),
            Some(AccessOwners::Unknown),
            Some(AccessOwners::Known(BTreeSet::new())),
            None,
        ] {
            let mut access = AccessFact {
                observed_recency: 0,
                recency: 0,
                origin_owners: [(NodeId(0), known(3))].into(),
                origins: Origins {
                    nodes: [NodeId(0), NodeId(1)].into(),
                    choices: BTreeMap::new(),
                },
                slot: None,
                mode: Mode::Write,
                participants: BTreeSet::new(),
                cause: CauseId(0),
                span: Span {
                    file: ril_compiler_core::source::FileId(0),
                    start: 0,
                    end: 0,
                },
            };
            if let Some(right) = &right {
                access.origin_owners.insert(NodeId(1), right.clone());
            }
            access.transport(&[(NodeId(0), NodeId(1))]);
            let expected = if right == Some(known(4)) {
                AccessOwners::Known([ScopeId(3), ScopeId(4)].into())
            } else {
                AccessOwners::Unknown
            };
            assert_eq!(access.origin_owners, [(NodeId(1), expected)].into());
            assert_eq!(access.observed_recency, 0);
        }
    }
    #[test]
    fn batch_summary_does_not_make_the_next_allocation_a_summary() {
        let mut heap = Heap::default();
        let (first, _) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
        heap.set_relation(first, first, Relation::UNKNOWN);
        assert_eq!(heap.relation(first, first), Relation::UNKNOWN);
        heap.set_relation(first, first, Relation::EQUAL);
        assert_eq!(heap.relation(first, first), Relation::UNKNOWN);
        assert!(
            heap.relations()
                .any(|(a, b, relation)| a == first && b == first && relation == Relation::UNKNOWN)
        );
        let (next, movement) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
        let (_, older) = movement.unwrap();
        assert_eq!(heap.relation(next, next), Relation::EQUAL);
        assert_eq!(heap.relation(older, older), Relation::UNKNOWN);
        assert_eq!(heap.relation(next, older), Relation::DISJOINT);
    }
    #[test]
    fn older_relations_only_keep_evidence_true_of_every_moved_batch() {
        for historical in [Relation::EQUAL, Relation::DISJOINT, Relation::UNKNOWN] {
            for incoming in [Relation::EQUAL, Relation::DISJOINT, Relation::UNKNOWN] {
                let mut heap = Heap::default();
                let (recent, _) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
                let (other, _) = heap.fresh(SiteId(1), ScopeId(0), CauseId(0));
                heap.set_relation(recent, other, historical);
                let (_, movement) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
                let (_, older) = movement.unwrap();
                assert_eq!(heap.relation(older, other), historical);
                heap.set_relation(recent, other, incoming);
                heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
                let joined = heap.relation(older, other);
                assert_eq!(
                    joined.equal == Condition::TRUE,
                    historical.equal == Condition::TRUE && incoming.equal == Condition::TRUE
                );
                assert_eq!(
                    joined.disjoint == Condition::TRUE,
                    historical.disjoint == Condition::TRUE && incoming.disjoint == Condition::TRUE
                );
            }
        }
    }
    #[test]
    fn recency_is_finite_and_new_object_is_disjoint_from_older_instances() {
        let mut heap = Heap::default();
        let (first, _) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
        for _ in 0..100 {
            let (recent, remap) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
            let (_, older) = remap.unwrap();
            assert_eq!(first, recent);
            assert_eq!(heap.relation(recent, older), Relation::DISJOINT);
            assert_eq!(heap.relation(older, older), Relation::UNKNOWN);
        }
        assert_eq!(heap.nodes.len(), 2);
    }
    #[test]
    fn cyclic_reachability_terminates() {
        let mut heap = Heap::default();
        let (a, _) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
        heap.nodes[a.0 as usize]
            .fields
            .insert(Slot::Field("next".into()), [a].into());
        assert_eq!(heap.reachable([a]), [a].into());
    }
    #[test]
    fn readonly_join_cannot_restore_construction_authority() {
        let mut a = Reference {
            origins: [NodeId(0)].into(),
            permission: Permission::Write,
            publication: Publication::Unpublished,
            participants: BTreeSet::new(),
            owner: ScopeId(0),
            cause: CauseId(0),
        };
        let original = a.clone();
        a.restrict(Permission::Read);
        let joined = original.join(&a, CauseId(1));
        assert_eq!(joined.permission, Permission::Read);
        assert_eq!(joined.publication, Publication::Live);
    }
}
