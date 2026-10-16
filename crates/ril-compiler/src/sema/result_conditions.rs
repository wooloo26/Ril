//! Evidence carried by one boolean value, independent of its diagnostic span.
use super::channel_messages::{ChannelGuard, GuardLiteral};
use super::effect_identity::InvocationContext;
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConditionEvaluationId(pub u32);

#[derive(Debug, Clone, Default)]
pub struct ConditionInspections {
    pub when_true: BTreeSet<u32>,
    pub when_false: BTreeSet<u32>,
    pub versions: BTreeMap<u32, u32>,
    pub evaluations: BTreeSet<ConditionEvaluationId>,
    pub channel_when_true: ChannelGuard,
    pub channel_when_false: ChannelGuard,
}
impl PartialEq for ConditionInspections {
    fn eq(&self, other: &Self) -> bool {
        self.when_true == other.when_true
            && self.when_false == other.when_false
            && self.versions == other.versions
            && ((!self.channel_dependent() && !other.channel_dependent())
                || (self.channel_when_true == other.channel_when_true
                    && self.channel_when_false == other.channel_when_false))
    }
}
impl Eq for ConditionInspections {}

impl ConditionInspections {
    pub fn branch_join(&self, left: Option<bool>, other: &Self, right: Option<bool>) -> Self {
        let paths = [(left, self), (right, other)];
        let mut result = Self::default();
        let mut conflicts = BTreeSet::new();
        for truth in [false, true] {
            let mut possible = paths
                .iter()
                .filter(|(constant, _)| constant.is_none_or(|value| value == truth));
            let Some((_, first)) = possible.next() else {
                continue;
            };
            let mut chosen = first.outcome(truth).clone();
            for (_, next) in possible {
                chosen.retain(|id| {
                    next.outcome(truth).contains(id)
                        && first.versions.get(id) == next.versions.get(id)
                });
            }
            for id in &chosen {
                if let Some(version) = first.versions.get(id)
                    && result
                        .versions
                        .insert(*id, *version)
                        .is_some_and(|old| old != *version)
                {
                    conflicts.insert(*id);
                }
            }
            *result.outcome_mut(truth) = chosen;
        }
        result.evaluations = self
            .evaluations
            .union(&other.evaluations)
            .copied()
            .collect();
        result.strip(&conflicts);
        if self.channel_dependent() || other.channel_dependent() {
            for truth in [false, true] {
                let guard = [(left, self), (right, other)]
                    .into_iter()
                    .filter(|(constant, _)| constant.is_none_or(|value| value == truth))
                    .try_fold(ChannelGuard::never(), |guard, (_, evidence)| {
                        guard.or(evidence.channel_outcome(truth))
                    });
                *result.channel_outcome_mut(truth) =
                    guard.unwrap_or_else(ChannelGuard::unavailable);
            }
        }
        result
    }
    pub fn sequence(
        &self,
        left: Option<bool>,
        other: &Self,
        right: Option<bool>,
        conjunction: bool,
    ) -> Self {
        let mut result = Self::default();
        let mut conflicts = BTreeSet::new();
        for truth in [false, true] {
            let mut paths: Vec<BTreeMap<u32, u32>> = Vec::new();
            for a in [false, true] {
                if left.is_some_and(|known| known != a) {
                    continue;
                }
                if a != conjunction {
                    if a == truth {
                        paths.push(
                            self.outcome(a)
                                .iter()
                                .filter_map(|id| self.versions.get(id).map(|v| (*id, *v)))
                                .collect(),
                        );
                    }
                    continue;
                }
                for b in [false, true] {
                    if right.is_some_and(|known| known != b) || b != truth {
                        continue;
                    }
                    let mut path: BTreeMap<_, _> = self
                        .outcome(a)
                        .iter()
                        .filter_map(|id| self.versions.get(id).map(|v| (*id, *v)))
                        .collect();
                    for id in other.outcome(b) {
                        if let Some(version) = other.versions.get(id) {
                            path.insert(*id, *version);
                        }
                    }
                    paths.push(path);
                }
            }
            if let Some(first) = paths.first() {
                let certain: BTreeSet<_> = first
                    .iter()
                    .filter(|(id, version)| paths.iter().all(|path| path.get(id) == Some(version)))
                    .map(|(id, _)| *id)
                    .collect();
                for id in &certain {
                    if result
                        .versions
                        .insert(*id, first[id])
                        .is_some_and(|old| old != first[id])
                    {
                        conflicts.insert(*id);
                    }
                }
                *result.outcome_mut(truth) = certain;
            }
        }
        result.evaluations = self
            .evaluations
            .union(&other.evaluations)
            .copied()
            .collect();
        result.strip(&conflicts);
        if self.channel_dependent() || other.channel_dependent() {
            for truth in [false, true] {
                let mut guard = ChannelGuard::never();
                for a in [false, true] {
                    if left.is_some_and(|known| known != a) {
                        continue;
                    }
                    if a != conjunction {
                        if a == truth {
                            guard = guard
                                .or(self.channel_outcome(a))
                                .unwrap_or_else(ChannelGuard::unavailable);
                        }
                        continue;
                    }
                    for b in [false, true] {
                        if right.is_some_and(|known| known != b) || b != truth {
                            continue;
                        }
                        guard = self
                            .channel_outcome(a)
                            .and(other.channel_outcome(b))
                            .and_then(|path| guard.or(&path))
                            .unwrap_or_else(ChannelGuard::unavailable);
                    }
                }
                *result.channel_outcome_mut(truth) = guard;
            }
        }
        result
    }
    pub fn outcome(&self, truth: bool) -> &BTreeSet<u32> {
        if truth {
            &self.when_true
        } else {
            &self.when_false
        }
    }
    fn outcome_mut(&mut self, truth: bool) -> &mut BTreeSet<u32> {
        if truth {
            &mut self.when_true
        } else {
            &mut self.when_false
        }
    }
    pub fn negate(&mut self) {
        std::mem::swap(&mut self.when_true, &mut self.when_false);
        std::mem::swap(&mut self.channel_when_true, &mut self.channel_when_false);
    }
    pub fn strip(&mut self, ids: &BTreeSet<u32>) {
        self.when_true.retain(|id| !ids.contains(id));
        self.when_false.retain(|id| !ids.contains(id));
        self.versions.retain(|id, _| !ids.contains(id));
        for truth in [false, true] {
            let guard = self.channel_outcome_mut(truth);
            guard.terms = guard.terms.iter().map(|term| term.iter().copied().filter(|literal| {
                !matches!(literal, GuardLiteral::Transport { producer, .. } | GuardLiteral::Result { producer, .. } if ids.contains(producer))
            }).collect()).collect();
            *guard = guard.normalized().unwrap_or_else(ChannelGuard::unavailable);
        }
    }
    pub fn channel_outcome(&self, truth: bool) -> &ChannelGuard {
        if truth {
            &self.channel_when_true
        } else {
            &self.channel_when_false
        }
    }
    pub fn channel_outcome_mut(&mut self, truth: bool) -> &mut ChannelGuard {
        if truth {
            &mut self.channel_when_true
        } else {
            &mut self.channel_when_false
        }
    }
    pub fn channel_dependent(&self) -> bool {
        [self.channel_outcome(false), self.channel_outcome(true)]
            .into_iter()
            .any(|guard| {
                guard.incomplete
                    || guard.terms.iter().flatten().any(|literal| {
                        matches!(
                            literal,
                            GuardLiteral::Transport { .. }
                                | GuardLiteral::Result { .. }
                                | GuardLiteral::Optional { .. }
                        )
                    })
            })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionKind {
    Plain,
    Pattern,
    Negation,
    Conjunction,
    Disjunction,
}

#[derive(Debug, Clone)]
pub struct ConditionEvaluation {
    pub id: ConditionEvaluationId,
    pub context: InvocationContext,
    pub span: Span,
    pub cause: CauseId,
    pub kind: ConditionKind,
    pub constant: Option<bool>,
    pub inspections: ConditionInspections,
}

#[cfg(test)]
mod tests {
    use super::*;
    fn proof(when_true: &[u32], when_false: &[u32]) -> ConditionInspections {
        ConditionInspections {
            when_true: when_true.iter().copied().collect(),
            when_false: when_false.iter().copied().collect(),
            versions: when_true
                .iter()
                .chain(when_false)
                .map(|id| (*id, 0))
                .collect(),
            evaluations: BTreeSet::new(),
            ..Default::default()
        }
    }
    #[test]
    fn outcome_meets_follow_short_circuit_paths_and_constant_reachability() {
        let a = proof(&[1], &[2]);
        let b = proof(&[3], &[4]);
        let and = a.sequence(None, &b, None, true);
        assert_eq!(and.when_true, [1, 3].into());
        assert!(and.when_false.is_empty());
        let or = a.sequence(None, &b, None, false);
        assert!(or.when_true.is_empty());
        assert_eq!(or.when_false, [2, 4].into());
        let only_right = a.branch_join(Some(false), &b, None);
        assert_eq!(only_right.when_true, [3].into());
        assert!(only_right.when_false.is_empty());
    }
    #[test]
    fn trace_identity_does_not_change_semantic_stability_and_versions_never_mix() {
        let mut left = proof(&[7], &[7]);
        let mut right = left.clone();
        left.evaluations.insert(ConditionEvaluationId(1));
        right.evaluations.insert(ConditionEvaluationId(99));
        assert_eq!(left, right);
        right.versions.insert(7, 1);
        let joined = left.branch_join(Some(false), &right, Some(true));
        assert!(joined.when_true.is_empty() && joined.when_false.is_empty());
        let joined = left.branch_join(None, &right, None);
        assert!(joined.when_true.is_empty() && joined.when_false.is_empty());
    }
}
