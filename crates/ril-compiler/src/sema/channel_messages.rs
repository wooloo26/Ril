//! Outcome-indexed conservation evidence for channel Result messages.
//!
//! These records describe actual events. They do not certify copying, grant
//! endpoint authority, or turn a matching type or source site into a send.

use super::{
    copy_contract::CopyValueSnapshot,
    effect_identity::InvocationContext,
    facts::{NodeId, ScopeId, Slot},
    result_conditions::ConditionEvaluationId,
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use std::collections::{BTreeMap, BTreeSet};

pub const MAX_GUARD_TERMS: usize = 256;
pub const MAX_GUARD_LITERALS: usize = 128;
const MAX_GUARD_WORK: usize = 65_536;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChannelMessageId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChannelRepetitionId(pub u32);

/// A representative callback analysis is not a proof of its physical event
/// count. The half-open interval includes transitive helper and cleanup events.
#[derive(Debug, Clone)]
pub struct ChannelRepetition {
    pub id: ChannelRepetitionId,
    pub parent: Option<ChannelRepetitionId>,
    pub context: InvocationContext,
    pub activation: ScopeId,
    pub call: Option<super::copy_contract::CopyCallEventId>,
    pub start_sequence: u64,
    pub end_sequence: Option<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GuardLiteral {
    Optional {
        identity: ril_compiler_core::ids::OptionalTagId,
        present: bool,
    },
    /// The tag of one physical producer/version. This records presence only;
    /// it is not a receipt that its tag has actually been inspected.
    Result {
        producer: u32,
        version: u32,
        success: bool,
    },
    Transport {
        event: ChannelMessageId,
        producer: u32,
        version: u32,
        success: bool,
    },
    Boolean {
        evaluation: ConditionEvaluationId,
        truth: bool,
    },
}
impl GuardLiteral {
    fn identity(self) -> (u8, u32, u32) {
        match self {
            Self::Transport { event, .. } => (0, event.0, 0),
            Self::Boolean { evaluation, .. } => (1, evaluation.0, 0),
            Self::Result {
                producer, version, ..
            } => (2, producer, version),
            Self::Optional { identity, .. } => (3, identity.0, 0),
        }
    }
    fn truth(self) -> bool {
        match self {
            Self::Transport { success, .. } | Self::Result { success, .. } => success,
            Self::Boolean { truth, .. } => truth,
            Self::Optional { present, .. } => present,
        }
    }
    fn opposite(self) -> Self {
        match self {
            Self::Optional { identity, present } => Self::Optional {
                identity,
                present: !present,
            },
            Self::Result {
                producer,
                version,
                success,
            } => Self::Result {
                producer,
                version,
                success: !success,
            },
            Self::Transport {
                event,
                producer,
                version,
                success,
            } => Self::Transport {
                event,
                producer,
                version,
                success: !success,
            },
            Self::Boolean { evaluation, truth } => Self::Boolean {
                evaluation,
                truth: !truth,
            },
        }
    }
    fn contradicts(self, other: Self) -> bool {
        match (self, other) {
            (
                Self::Optional {
                    identity: a,
                    present: x,
                },
                Self::Optional {
                    identity: b,
                    present: y,
                },
            ) => a == b && x != y,
            (
                Self::Result {
                    producer: a,
                    version: av,
                    success: x,
                },
                Self::Result {
                    producer: b,
                    version: bv,
                    success: y,
                },
            ) => a == b && av == bv && x != y,
            (
                Self::Transport {
                    event: a,
                    success: x,
                    ..
                },
                Self::Transport {
                    event: b,
                    success: y,
                    ..
                },
            ) => a == b && x != y,
            (
                Self::Boolean {
                    evaluation: a,
                    truth: x,
                },
                Self::Boolean {
                    evaluation: b,
                    truth: y,
                },
            ) => a == b && x != y,
            _ => false,
        }
    }
}

/// Disjunction of conjunctions. False has no terms; true has one empty term.
/// Every constructor/operation normalizes, removes contradictions, deduplicates
/// and absorbs stronger terms. Work exhaustion is explicit, never true.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChannelGuard {
    pub terms: BTreeSet<BTreeSet<GuardLiteral>>,
    /// An unavailable bounded formula is never an authorization to continue.
    pub incomplete: bool,
}
impl Default for ChannelGuard {
    fn default() -> Self {
        Self::always()
    }
}
impl ChannelGuard {
    pub fn always() -> Self {
        Self {
            terms: [BTreeSet::new()].into(),
            incomplete: false,
        }
    }
    pub fn never() -> Self {
        Self {
            terms: BTreeSet::new(),
            incomplete: false,
        }
    }
    pub fn literal(literal: GuardLiteral) -> Self {
        Self {
            terms: [[literal].into()].into(),
            incomplete: false,
        }
    }
    pub fn is_never(&self) -> bool {
        !self.incomplete && self.terms.is_empty()
    }
    pub fn unavailable() -> Self {
        Self {
            terms: BTreeSet::new(),
            incomplete: true,
        }
    }

    pub fn normalized(&self) -> Option<Self> {
        if !self.bounded() {
            return None;
        }
        let mut terms = BTreeSet::new();
        let mut work = 0_usize;
        for term in &self.terms {
            let contradictory = contradictory(term, &mut work)?;
            if contradictory {
                continue;
            }
            insert_absorbed(&mut terms, term.clone(), &mut work)?;
        }
        // Both continuations of a plain boolean do not accumulate 2^N
        // equivalent paths before the first channel operation.

        loop {
            let mut consensus = None;
            'pairs: for a in &terms {
                for b in &terms {
                    charge(&mut work, a.len().checked_add(b.len())?.checked_add(1)?)?;
                    let left = a.difference(b).copied().collect::<Vec<_>>();
                    let right = b.difference(a).copied().collect::<Vec<_>>();
                    if let ([left], [right]) = (left.as_slice(), right.as_slice())
                        && left.contradicts(*right)
                    {
                        consensus = Some(a.intersection(b).copied().collect::<BTreeSet<_>>());
                        break 'pairs;
                    }
                }
            }
            let Some(term) = consensus else {
                break;
            };
            insert_absorbed(&mut terms, term, &mut work)?;
        }
        Some(Self {
            terms,
            incomplete: false,
        })
    }

    fn bounded(&self) -> bool {
        !(self.incomplete
            || self.terms.len() > MAX_GUARD_TERMS
            || self
                .terms
                .iter()
                .any(|term| term.len() > MAX_GUARD_LITERALS))
    }

    pub fn or(&self, other: &Self) -> Option<Self> {
        if !self.bounded() || !other.bounded() {
            return None;
        }
        let terms = self.terms.union(&other.terms).cloned().collect();
        Self {
            terms,
            incomplete: false,
        }
        .normalized()
    }
    pub fn and(&self, other: &Self) -> Option<Self> {
        if !self.bounded() || !other.bounded() {
            return None;
        }
        let mut work = 0_usize;
        // Idempotence preserves the exact physical literal support. Comparison
        // costs at most 1 + 256 clauses + 256*128 literals = 33,025 units.
        // Normalization retains its existing independent bounded phase; a raw
        // equal guard cannot bypass contradictions, absorption or consensus.
        if self.same_structure(other, &mut work)? {
            return self.normalized();
        }
        // Exact raw clause-set inclusion is absorption, not a truth-table or
        // support equivalence test. A matching diagonal product exists for
        // every clause of the selected operand, and absorbs all other products.
        let contained = match self.terms.len().cmp(&other.terms.len()) {
            std::cmp::Ordering::Less => self
                .raw_clauses_contained_in(other, &mut work)?
                .then_some(self),
            std::cmp::Ordering::Greater => other
                .raw_clauses_contained_in(self, &mut work)?
                .then_some(other),
            std::cmp::Ordering::Equal => None,
        };
        if let Some(guard) = contained {
            return guard.normalized();
        }
        // Every selected clause needs a full physical subclause witness in the
        // other operand. Then the old product set contains that entire clause,
        // which absorbs every stronger product; its normalized support remains
        // identical. This never proves a nonempty inactive case unreachable.
        if self.terms_physically_imply(other, &mut work)? {
            return self.normalized();
        }
        if other.terms_physically_imply(self, &mut work)? {
            return other.normalized();
        }
        let mut terms = BTreeSet::new();
        for a in &self.terms {
            for b in &other.terms {
                work = work.checked_add(a.len().checked_add(b.len())?.checked_add(1)?)?;

                if work > MAX_GUARD_WORK {
                    return None;
                }
                let term = a.union(b).copied().collect::<BTreeSet<_>>();
                if term.len() > MAX_GUARD_LITERALS {
                    return None;
                }
                if contradictory(&term, &mut work)? {
                    continue;
                }
                insert_absorbed(&mut terms, term, &mut work)?;
                if terms.len() > MAX_GUARD_TERMS {
                    return None;
                }
            }
        }
        Self {
            terms,
            incomplete: false,
        }
        .normalized()
    }

    fn same_structure(&self, other: &Self, work: &mut usize) -> Option<bool> {
        charge(work, 1)?;
        if self.incomplete != other.incomplete || self.terms.len() != other.terms.len() {
            return Some(false);
        }
        for (left, right) in self.terms.iter().zip(&other.terms) {
            charge(work, 1)?;
            if left.len() != right.len() {
                return Some(false);
            }
            for (left, right) in left.iter().zip(right) {
                charge(work, 1)?;
                // GuardLiteral equality includes sort and every physical
                // identity, generation and truth field, including transport
                // producer/version fields beyond its logical event key.
                if left != right {
                    return Some(false);
                }
            }
        }
        Some(true)
    }

    fn raw_clauses_contained_in(&self, other: &Self, work: &mut usize) -> Option<bool> {
        charge(work, 1)?;
        if self.incomplete || other.incomplete || self.terms.len() > other.terms.len() {
            return Some(false);
        }
        let mut candidates = other.terms.iter();
        let mut next = candidates.next();
        for term in &self.terms {
            loop {
                let Some(candidate) = next else {
                    return Some(false);
                };
                // This ordered merge performs no cloning. Charge all literals
                // in both clauses before their full physical comparison.
                charge(
                    work,
                    term.len().checked_add(candidate.len())?.checked_add(1)?,
                )?;
                match term.cmp(candidate) {
                    std::cmp::Ordering::Less => return Some(false),
                    std::cmp::Ordering::Equal => {
                        next = candidates.next();
                        break;
                    }
                    std::cmp::Ordering::Greater => next = candidates.next(),
                }
            }
        }
        Some(true)
    }

    fn terms_physically_imply(&self, other: &Self, work: &mut usize) -> Option<bool> {
        charge(work, 1)?;
        if self.incomplete || other.incomplete {
            return Some(false);
        }
        for term in &self.terms {
            charge(work, 1)?;
            let mut witnessed = false;
            for candidate in &other.terms {
                charge(work, 1)?;
                if candidate.len() > term.len() {
                    continue;
                }
                charge(work, term.len().checked_add(candidate.len())?)?;
                if candidate.is_subset(term) {
                    witnessed = true;
                    break;
                }
            }
            if !witnessed {
                return Some(false);
            }
        }
        Some(true)
    }
    pub fn not(&self) -> Option<Self> {
        if !self.bounded() {
            return None;
        }
        let mut result = Self::always();
        for term in &self.terms {
            let opposite = Self {
                terms: term
                    .iter()
                    .map(|literal| [literal.opposite()].into())
                    .collect(),
                incomplete: false,
            };
            result = result.and(&opposite)?;
        }

        Some(result)
    }
}

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_add(amount)?;
    #[cfg(test)]
    {
        if *work > MAX_GUARD_WORK {}
    }
    (*work <= MAX_GUARD_WORK).then_some(())
}

fn insert_absorbed(
    terms: &mut BTreeSet<BTreeSet<GuardLiteral>>,
    term: BTreeSet<GuardLiteral>,
    work: &mut usize,
) -> Option<()> {
    let mut remove = Vec::new();
    for old in terms.iter() {
        charge(work, old.len().checked_add(term.len())?.checked_add(1)?)?;
        if old.is_subset(&term) {
            return Some(());
        }
        if term.is_subset(old) {
            remove.push(old.clone());
        }
    }
    for old in remove {
        terms.remove(&old);
    }
    terms.insert(term);
    Some(())
}

fn contradictory(term: &BTreeSet<GuardLiteral>, work: &mut usize) -> Option<bool> {
    let mut assignments = BTreeMap::new();
    for literal in term {
        *work = work.checked_add(1)?;

        if *work > MAX_GUARD_WORK {
            return None;
        }
        if assignments
            .insert(literal.identity(), literal.truth())
            .is_some_and(|old| old != literal.truth())
        {
            return Some(true);
        }
    }
    Some(false)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ChannelAnchor {
    Known { channel: NodeId, scope: NodeId },
    Formal { endpoint: NodeId, scope: NodeId },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChannelBindingPath {
    pub binding: usize,
    pub projection: Vec<Slot>,
}

#[derive(Debug, Clone)]
pub struct ChannelReceiveSource {
    pub guard: ChannelGuard,
    /// None is a newly produced symbolic incoming value for a formal receiver,
    /// never a certificate consuming a submitted caller-owned producer.
    pub send: Option<ChannelMessageId>,
}

#[derive(Debug, Clone)]
pub enum ChannelAction {
    /// Spawn occurs before any observation in the child's body.
    TaskFork { child: NodeId },
    /// Completion of this join orders subsequent parent observations.
    TaskJoin { child: NodeId },
    Send {
        endpoint: CopyValueSnapshot,
        anchor: ChannelAnchor,
        payload: CopyValueSnapshot,
        transport: CopyValueSnapshot,
        producer_versions: BTreeMap<u32, u32>,
        original_owners: BTreeMap<u32, ScopeId>,
        dependencies: BTreeSet<ChannelBindingPath>,
    },
    Receive {
        endpoint: CopyValueSnapshot,
        anchor: ChannelAnchor,
        payload: CopyValueSnapshot,
        transport: CopyValueSnapshot,
        producer_versions: BTreeMap<u32, u32>,
        sources: Vec<ChannelReceiveSource>,
        dependencies: BTreeSet<ChannelBindingPath>,
    },
    /// Actual tag test, independent from selecting its truth continuation.
    /// Nested payload tests retain the selected constructor parent separately.
    TagTest {
        subject: CopyValueSnapshot,
        success: bool,
        pattern: Span,
        producer_versions: BTreeMap<u32, u32>,
    },
    /// A complete normal pattern evaluation, before a truth continuation is
    /// chosen. Source replay independently derives any usable truth; this
    /// receipt does not itself inspect, transfer or authorize the subject.
    ConditionEvaluated {
        evaluation: ConditionEvaluationId,
        subject_expression: usize,
        subject: CopyValueSnapshot,
    },
    Inspect {
        value: CopyValueSnapshot,
        producer_versions: BTreeMap<u32, u32>,
    },
    /// Selection is tied to the evaluated boolean's immutable evidence and
    /// versioned producers, never merely a source pattern or diagnostic span.
    Select {
        evaluation: ConditionEvaluationId,
        truth: bool,
    },
    /// A copy/family alias preserves the original physical event outcome.
    /// This map conveys identity only and supplies no Result inspection.
    ResultAliases { map: BTreeMap<u32, BTreeSet<u32>> },
    /// A particular ordinary owner transition. The immutable producer registry
    /// remains the creation origin; this frozen carrier proves membership at
    /// the transition instead of consulting the final mutable heap.
    ResultTransfer {
        from: ScopeId,
        to: ScopeId,
        source: CopyValueSnapshot,
        producers: BTreeSet<u32>,
    },
}

#[derive(Debug, Clone)]
pub struct ChannelMessageFact {
    pub id: ChannelMessageId,
    pub source_event: Option<super::copy_contract::CopyCallEventId>,
    pub repetition: Option<ChannelRepetitionId>,
    pub sequence: u64,
    pub context: InvocationContext,
    /// Executing task at this observation, distinct from lexical activation.
    /// None is the parent/root task, never an unknown child identity.
    pub task: Option<NodeId>,
    pub activation: ScopeId,
    pub span: Span,
    pub cause: CauseId,
    pub allocation_epoch: usize,
    pub guard: ChannelGuard,
    pub action: ChannelAction,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelExitKind {
    /// Coverage of this actual invocation's normal/returned continuations.
    /// Its unit receipt supplies no producer return or inspection authority.
    Complete,
    Callable,
    Return,
    Receiver,
    Scope,
    Abnormal,
}

#[derive(Debug, Clone)]
pub struct ChannelExitFact {
    pub sequence: u64,
    pub context: InvocationContext,
    pub activation: ScopeId,
    pub span: Span,
    pub cause: CauseId,
    pub allocation_epoch: usize,
    pub guard: ChannelGuard,
    pub kind: ChannelExitKind,
    pub anchor: Option<ChannelAnchor>,
    pub returned: CopyValueSnapshot,
}

#[cfg(test)]
#[path = "channel_guard_idempotence_tests.rs"]
mod idempotence_tests;
