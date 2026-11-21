use std::collections::{BTreeMap, BTreeSet};

use ril_base::span::Span;
use ril_frontend::syntax::Mode;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Access {
    Immutable,
    Ref,
    Mut,
    Shared,
}

impl Access {
    pub const fn from_mode(mode: Mode) -> Self {
        match mode {
            Mode::Plain => Self::Immutable,
            Mode::Ref => Self::Ref,
            Mode::Mut | Mode::New | Mode::Via | Mode::Infer => Self::Mut,
            Mode::Shared => Self::Shared,
        }
    }

    pub const fn writes(self) -> bool {
        matches!(self, Self::Mut | Self::Shared)
    }

    pub const fn project(self, member: Self) -> Self {
        match (self, member) {
            (Self::Immutable, _) | (Self::Ref, Self::Immutable) => Self::Immutable,
            (Self::Ref, _) => Self::Ref,
            (_, mode) => mode,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Coordinate {
    Field(String),
    Index(String),
    Dynamic,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Region {
    pub source: Span,
    pub selection: Vec<Coordinate>,
}

impl Region {
    pub(super) fn overlaps(&self, other: &Self) -> bool {
        self.source == other.source
            && self
                .selection
                .iter()
                .zip(&other.selection)
                .all(|(a, b)| a == b || *a == Coordinate::Dynamic || *b == Coordinate::Dynamic)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Origin {
    pub region: Region,
    pub mode: Access,
    pub new: bool,
    pub dependencies: BTreeSet<Span>,
    pub branches: BTreeMap<Span, usize>,
    pub confined: Option<Span>,
    pub draft: bool,
}

impl Origin {
    pub(super) fn overlaps(&self, other: &Self) -> bool {
        self.region.overlaps(&other.region)
            && self
                .branches
                .iter()
                .all(|(branch, a)| other.branches.get(branch).is_none_or(|b| a == b))
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Datum {
    pub roots: Vec<Origin>,
    pub members: BTreeMap<Coordinate, Datum>,
    pub results: BTreeSet<Span>,
    pub requires_new: bool,
    pub latent_effects: BTreeSet<String>,
    pub environments: BTreeSet<Span>,
    pub invocations: BTreeMap<Span, BTreeMap<Span, BTreeSet<Span>>>,
    pub stateful_handler: bool,
    pub task_scope: Option<Span>,
    pub result_fresh: bool,
}

impl Datum {
    pub(super) fn source(span: Span, mode: Access, new: bool) -> Self {
        Self {
            roots: vec![Origin {
                region: Region {
                    source: span,
                    selection: Vec::new(),
                },
                mode,
                new,
                dependencies: BTreeSet::new(),
                branches: BTreeMap::new(),
                confined: None,
                draft: false,
            }],
            requires_new: new,
            ..Self::default()
        }
    }

    pub(super) fn origins(&self) -> Box<dyn Iterator<Item = &Origin> + '_> {
        Box::new(
            self.roots
                .iter()
                .chain(self.members.values().flat_map(Self::origins)),
        )
    }

    pub(super) fn visit_origins(
        &self,
        path: &mut Vec<Coordinate>,
        visit: &mut impl FnMut(&[Coordinate], &Origin),
    ) {
        for origin in &self.roots {
            visit(path, origin);
        }
        for (coordinate, member) in &self.members {
            path.push(coordinate.clone());
            member.visit_origins(path, visit);
            path.pop();
        }
    }

    pub(super) fn transform(&mut self, f: &mut impl FnMut(&mut Origin)) {
        self.roots.iter_mut().for_each(&mut *f);
        for member in self.members.values_mut() {
            member.transform(f);
        }
    }

    pub(super) fn results(&self) -> BTreeSet<Span> {
        self.results
            .iter()
            .copied()
            .chain(self.members.values().flat_map(Self::results))
            .collect()
    }

    pub(super) fn joined(mut self, mut other: Self) -> Self {
        self.roots.append(&mut other.roots);
        self.roots.sort_unstable();
        self.roots.dedup();
        // Widen branch correlations before fact growth makes nested branches impractical.
        if self.roots.len() > 24 {
            for root in &mut self.roots {
                root.branches.clear();
            }
            self.roots.sort_unstable();
            self.roots.dedup();
        }
        for (coordinate, value) in other.members {
            let slot = self.members.entry(coordinate).or_default();
            *slot = std::mem::take(slot).joined(value);
        }
        self.results.append(&mut other.results);
        self.requires_new &= other.requires_new;
        self.latent_effects.append(&mut other.latent_effects);
        self.environments.append(&mut other.environments);
        for (owner, sources) in other.invocations {
            let captures = self.invocations.entry(owner).or_default();
            for (source, targets) in sources {
                captures.entry(source).or_default().extend(targets);
            }
        }
        self.stateful_handler |= other.stateful_handler;
        self.result_fresh &= other.result_fresh;
        if self.task_scope != other.task_scope {
            self.task_scope = None;
        }
        self
    }

    pub(super) fn project(&self, coordinate: Coordinate, mode: Access) -> Self {
        let known = self.members.get(&coordinate).cloned().or_else(|| {
            (coordinate == Coordinate::Dynamic)
                .then(|| self.members.values().cloned().reduce(Self::joined))
                .flatten()
        });
        if let Some(mut member) = known {
            self.attenuate(&mut member);
            return member;
        }
        let roots: Vec<_> = self
            .roots
            .iter()
            .map(|origin| {
                let mut origin = origin.clone();
                origin.region.selection.push(coordinate.clone());
                if !origin.draft {
                    origin.mode = origin.mode.project(mode);
                    // The schema of an opaque member selection can expose authority
                    // which survived the transfer of its enclosing new object.
                    if matches!(mode, Access::Ref | Access::Shared) {
                        origin.new = false;
                    }
                }
                origin
            })
            .collect();
        Self {
            requires_new: self.requires_new && roots.iter().all(|root| root.new),
            roots,
            results: self.results.clone(),
            ..Self::default()
        }
    }

    fn attenuate(&self, member: &mut Self) {
        if self.roots.iter().all(|root| !root.mode.writes()) {
            let access = if self.roots.iter().all(|root| root.mode == Access::Immutable) {
                Access::Immutable
            } else {
                Access::Ref
            };
            member.transform(&mut |origin| origin.mode = access.project(origin.mode));
        }
    }

    pub(super) fn slot_projection(&self, coordinate: Coordinate) -> Self {
        let mut roots = self.roots.clone();
        for root in &mut roots {
            root.region.selection.push(coordinate.clone());
        }
        Self {
            roots,
            ..Self::default()
        }
    }

    pub(super) fn creates_environment(&self) -> bool {
        !self.environments.is_empty() || self.members.values().any(Self::creates_environment)
    }

    pub(super) fn writers(&self) -> bool {
        !self.roots.is_empty() && self.roots.iter().all(|root| root.mode.writes())
    }

    pub(super) fn root_dependencies(&self) -> impl Iterator<Item = Span> + '_ {
        self.roots.iter().flat_map(|origin| {
            origin
                .dependencies
                .iter()
                .copied()
                .chain(std::iter::once(origin.region.source))
        })
    }
}

#[derive(Clone)]
pub(super) struct Slot {
    pub decl: Span,
    pub variable: bool,
    pub mode: Mode,
    pub value: Datum,
}

#[derive(Clone)]
struct Replacement {
    value: Datum,
    definite: bool,
}

#[derive(Clone, Default)]
pub(super) struct Ledger {
    pub slots: BTreeMap<Span, Slot>,
    pub revoked: BTreeSet<Span>,
    pub obligations: BTreeSet<Span>,
    pub inspected: BTreeSet<Span>,
    pub iteration: Vec<Datum>,
    pub holds: Vec<(Mode, Datum)>,
    pub choices: BTreeMap<Span, usize>,
    replacements: BTreeMap<Region, Replacement>,
}

impl Ledger {
    pub(super) fn hold_conflict(&self, value: &Datum, mode: Mode) -> Option<bool> {
        self.holds
            .iter()
            .find_map(|(held_mode, held)| conflicts(value, mode, held, *held_mode))
    }

    pub(super) fn stamp(&self, value: &mut Datum) {
        value.transform(&mut |origin| {
            origin
                .branches
                .extend(self.choices.iter().map(|(&k, &v)| (k, v)));
        });
    }

    pub(super) fn take_choice(&mut self, span: Span, arm: usize) {
        self.choices.insert(span, arm);
        for slot in self.slots.values_mut() {
            slot.value.transform(&mut |origin| {
                origin.branches.insert(span, arm);
            });
        }
        for replacement in self.replacements.values_mut() {
            replacement.value.transform(&mut |origin| {
                origin.branches.insert(span, arm);
            });
        }
    }

    pub(super) fn merge(&mut self, prior: &Self, alternatives: &[Self]) {
        self.slots = prior.slots.clone();
        self.revoked = prior.revoked.clone();
        self.obligations = prior.obligations.clone();
        for branch in alternatives {
            self.revoked.extend(&branch.revoked);
            self.obligations.extend(&branch.obligations);
        }
        self.inspected = if alternatives.is_empty() {
            prior.inspected.clone()
        } else {
            alternatives
                .iter()
                .flat_map(|branch| &branch.inspected)
                .filter(|item| {
                    alternatives.iter().all(|branch| {
                        branch.inspected.contains(item) || !branch.obligations.contains(item)
                    })
                })
                .copied()
                .collect()
        };
        for (id, slot) in &mut self.slots {
            if let Some(value) = alternatives
                .iter()
                .filter_map(|branch| branch.slots.get(id).map(|slot| slot.value.clone()))
                .reduce(Datum::joined)
            {
                slot.value = value;
            }
        }
        self.choices = prior.choices.clone();
        self.merge_replacements(prior, alternatives);
    }

    fn merge_replacements(&mut self, prior: &Self, alternatives: &[Self]) {
        if alternatives.is_empty() {
            self.replacements.clone_from(&prior.replacements);
            return;
        }
        let regions: BTreeSet<_> = alternatives
            .iter()
            .flat_map(|branch| branch.replacements.keys())
            .collect();
        self.replacements = regions
            .into_iter()
            .filter_map(|region| {
                let entries: Vec<_> = alternatives
                    .iter()
                    .filter_map(|branch| branch.replacements.get(region))
                    .collect();
                let definite = entries.len() == alternatives.len()
                    && entries.iter().all(|entry| entry.definite);
                let value = entries
                    .into_iter()
                    .map(|entry| entry.value.clone())
                    .reduce(Datum::joined)?;
                Some((region.clone(), Replacement { value, definite }))
            })
            .collect();
    }

    pub(super) fn replace_member(&mut self, slot: &Datum, mut value: Datum) {
        self.stamp(&mut value);
        let single = slot
            .roots
            .first()
            .is_some_and(|first| slot.roots.iter().all(|root| root.region == first.region));
        for origin in &slot.roots {
            let region = &origin.region;
            let definite = single && !region.selection.contains(&Coordinate::Dynamic);
            if definite {
                self.replacements.insert(
                    region.clone(),
                    Replacement {
                        value: value.clone(),
                        definite,
                    },
                );
            } else {
                for (key, entry) in &mut self.replacements {
                    if key.selection.len() == region.selection.len() && key.overlaps(region) {
                        entry.value = std::mem::take(&mut entry.value).joined(value.clone());
                    }
                }
                self.replacements
                    .entry(region.clone())
                    .or_insert_with(|| Replacement {
                        value: value.clone(),
                        definite,
                    });
            }
        }
    }

    pub(super) fn project(&self, base: &Datum, coordinate: Coordinate, mode: Access) -> Datum {
        let slot = base.slot_projection(coordinate.clone());
        let mut always = !slot.roots.is_empty();
        let mut changed = None;
        for origin in slot.roots {
            let region = &origin.region;
            let exact = self.replacements.get(region);
            always &= exact.is_some_and(|entry| entry.definite);
            let candidates = self.replacements.iter().filter_map(|(key, entry)| {
                (key.selection.len() == region.selection.len()
                    && (key == region
                        || !exact.is_some_and(|exact| exact.definite) && key.overlaps(region)))
                .then_some(&entry.value)
            });
            changed = changed
                .into_iter()
                .chain(candidates.cloned())
                .reduce(Datum::joined);
        }
        let Some(mut changed) = changed else {
            return base.project(coordinate, mode);
        };
        base.attenuate(&mut changed);
        if always {
            changed
        } else {
            base.project(coordinate, mode).joined(changed)
        }
    }

    pub(super) fn snapshot(&self, value: &Datum) -> Datum {
        if self.replacements.is_empty() {
            return value.clone();
        }
        self.snapshot_members(value, &mut BTreeSet::new())
    }

    fn snapshot_members(&self, value: &Datum, ancestors: &mut BTreeSet<Region>) -> Datum {
        let mut snapshot = value.clone();
        let regions: BTreeSet<_> = value.roots.iter().map(|root| root.region.clone()).collect();
        if regions.iter().any(|region| ancestors.contains(region)) {
            snapshot.members.clear();
            return snapshot;
        }
        ancestors.extend(regions.iter().cloned());
        let mut coordinates: BTreeSet<_> = value.members.keys().cloned().collect();
        for key in self.replacements.keys() {
            for region in &regions {
                if key.overlaps(region)
                    && let [coordinate] = key
                        .selection
                        .get(region.selection.len()..)
                        .unwrap_or_default()
                {
                    coordinates.insert(coordinate.clone());
                }
            }
        }
        for coordinate in coordinates {
            let member = self.project(value, coordinate.clone(), Access::Mut);
            snapshot
                .members
                .insert(coordinate, self.snapshot_members(&member, ancestors));
        }
        for region in regions {
            ancestors.remove(&region);
        }
        snapshot
    }

    pub(super) fn inspect(&mut self, datum: &Datum) {
        self.inspected.extend(datum.results());
    }

    pub(super) fn dead(&self, datum: &Datum) -> bool {
        datum.origins().any(|origin| {
            origin
                .dependencies
                .iter()
                .any(|token| self.revoked.contains(token))
        })
    }
}

pub(super) fn conflicts(left: &Datum, lmode: Mode, right: &Datum, rmode: Mode) -> Option<bool> {
    left.origins().find_map(|a| {
        right.origins().find_map(|b| {
            let left_writable = a.mode.writes()
                && matches!(lmode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via);
            let right_writable = b.mode.writes()
                && matches!(rmode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via);
            let left_ref = lmode == Mode::Ref || lmode == Mode::New && a.mode == Access::Ref;
            let right_ref = rmode == Mode::Ref || rmode == Mode::New && b.mode == Access::Ref;
            if a.overlaps(b) && !(lmode == Mode::Shared && rmode == Mode::Shared) {
                if left_writable && right_writable {
                    return Some(true);
                }
                if left_writable && right_ref || right_writable && left_ref {
                    return Some(false);
                }
            }
            None
        })
    })
}
