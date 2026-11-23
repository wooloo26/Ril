use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

use ril_base::span::Span;
use ril_frontend::syntax::Mode;
use serde::{Deserialize, Serialize};

use super::ReturnAllocation;

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

    pub(super) const fn as_mode(self) -> Mode {
        match self {
            Self::Immutable => Mode::Plain,
            Self::Ref => Mode::Ref,
            Self::Mut => Mode::Mut,
            Self::Shared => Mode::Shared,
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
    instance: RegionInstance,
    returned: Option<AllocationIdentity>,
    invocation: Vec<InvocationSite>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct InvocationSite {
    pub span: Span,
    pub ordinal: usize,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct AllocationIdentity {
    pub index: usize,
    pub summarized: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum RegionInstance {
    Source,
    Allocation,
    PriorAllocations,
}

impl Region {
    pub(super) fn root(source: Span) -> Self {
        Self {
            source,
            selection: Vec::new(),
            instance: RegionInstance::Source,
            returned: None,
            invocation: Vec::new(),
        }
    }

    pub(super) fn allocation(source: Span) -> Self {
        Self {
            instance: RegionInstance::Allocation,
            ..Self::root(source)
        }
    }

    pub(super) fn returned(source: Span, identity: AllocationIdentity) -> Self {
        Self {
            returned: Some(identity),
            ..Self::allocation(source)
        }
    }

    pub(super) fn set_invocation(&mut self, invocation: &[InvocationSite]) {
        self.invocation.extend_from_slice(invocation);
    }

    fn summarized(&self) -> bool {
        self.instance == RegionInstance::PriorAllocations
            || self.returned.is_some_and(|identity| identity.summarized)
    }

    fn age_allocation(&mut self, inside_loop: bool) {
        if inside_loop && self.instance == RegionInstance::Allocation {
            self.instance = RegionInstance::PriorAllocations;
        }
    }

    pub(super) fn overlaps(&self, other: &Self) -> bool {
        let symbolic =
            self.instance == RegionInstance::Source || other.instance == RegionInstance::Source;
        self.source == other.source
            && (symbolic || self.invocation == other.invocation)
            && self
                .returned
                .zip(other.returned)
                .is_none_or(|(left, right)| left.index == right.index)
            && (symbolic || self.instance == other.instance)
            && self
                .selection
                .iter()
                .zip(&other.selection)
                .all(|(a, b)| a == b || *a == Coordinate::Dynamic || *b == Coordinate::Dynamic)
    }

    pub(super) fn matches_axis(&self, projection: &Self) -> bool {
        self.source == projection.source
            && self.selection.len() == projection.selection.len()
            && self
                .selection
                .iter()
                .zip(&projection.selection)
                .all(|(axis, step)| axis == step || *axis == Coordinate::Dynamic)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Reception {
    Fixed(Access),
    // A mode bound by a formal parameter or one of its member schemas.
    Axis(Region),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Origin {
    pub region: Region,
    pub mode: Access,
    pub inherits_mode: bool,
    pub callback_result: Option<CallbackOrigin>,
    pub return_allocation: Option<AllocationIdentity>,
    pub reception: Vec<Reception>,
    pub new: bool,
    // A marker on this expression, independent of the source's existing access.
    pub explicit_share: bool,
    // A direct read of a replaceable slot cannot anchor a ref binding.
    pub from_variable: bool,
    pub call_borrow: bool,
    pub dependencies: BTreeSet<Occurrence>,
    pub anchor_scopes: BTreeSet<Span>,
    pub branches: Choices,
    variant: Option<String>,
    pub confined: Option<Span>,
    pub draft: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct CallbackOrigin {
    pub template: usize,
    pub cap: Option<Access>,
}

impl Origin {
    pub(super) fn fix_mode(&mut self, access: Access) {
        self.mode = access;
        self.explicit_share = false;
        self.inherits_mode = false;
        self.reception.clear();
        if let Some(result) = &mut self.callback_result {
            result.cap = Some(access);
        }
    }

    pub(super) fn project_mode(&mut self, member: Mode) {
        if member == Mode::Shared {
            self.call_borrow = false;
        }
        if member == Mode::Via || self.inherits_mode || !self.reception.is_empty() {
            if self.reception.is_empty() {
                self.reception.push(if self.inherits_mode {
                    Reception::Axis(Region::root(self.region.source))
                } else {
                    Reception::Fixed(self.mode)
                });
            }
            self.reception.push(if member == Mode::Via {
                Reception::Axis(self.region.clone())
            } else {
                Reception::Fixed(Access::from_mode(member))
            });
        }
        self.mode = self.mode.project(Access::from_mode(member));
        self.inherits_mode = false;
        if self.mode == Access::Immutable {
            self.reception.clear();
        }
    }

    pub(super) fn overlaps(&self, other: &Self) -> bool {
        self.region.overlaps(&other.region) && compatible(&self.branches, &other.branches)
    }

    pub(super) fn dependency_spans(&self) -> impl Iterator<Item = Span> + '_ {
        self.dependencies.iter().map(|dependency| dependency.span)
    }
}

pub(super) type Choices = BTreeMap<Occurrence, usize>;
pub(super) type Handoff = (Span, Span);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Occurrence {
    pub span: Span,
    pub prior_iteration: bool,
}

impl From<Span> for Occurrence {
    fn from(span: Span) -> Self {
        Self {
            span,
            prior_iteration: false,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ResultOccurrence {
    pub span: Span,
    places: BTreeSet<(ResultHolder, Vec<Coordinate>)>,
    created_in: Choices,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ResultHolder {
    Binding(Span),
    Iterable(usize),
    Handler(usize),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ResultReference {
    occurrence: ResultOccurrence,
    branches: Choices,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Revocation {
    Formal(Handoff),
    Callback { site: Span, position: usize },
}

type Revocations = BTreeMap<Option<Revocation>, BTreeSet<Choices>>;
const BRANCH_LIMIT: usize = 24;

fn compatible(a: &Choices, b: &Choices) -> bool {
    a.iter()
        .all(|(branch, arm)| b.get(branch).is_none_or(|other| arm == other))
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Datum {
    pub roots: Vec<Origin>,
    pub members: BTreeMap<Coordinate, Datum>,
    pub(super) results: BTreeSet<ResultReference>,
    pub requires_new: bool,
    pub latent_effects: BTreeSet<String>,
    pub environments: BTreeSet<Span>,
    pub publications: BTreeMap<Span, bool>,
    pub invocations: BTreeMap<Span, BTreeMap<Span, BTreeSet<Span>>>,
    pub stateful_handler: bool,
    pub task_scope: Option<Span>,
    pub result_fresh: bool,
}

impl Datum {
    pub(super) fn source(span: Span, mode: Access, new: bool) -> Self {
        Self {
            roots: vec![Origin {
                region: if new {
                    Region::allocation(span)
                } else {
                    Region::root(span)
                },
                mode,
                inherits_mode: false,
                callback_result: None,
                return_allocation: None,
                reception: Vec::new(),
                new,
                explicit_share: false,
                from_variable: false,
                call_borrow: false,
                dependencies: BTreeSet::new(),
                anchor_scopes: BTreeSet::new(),
                branches: BTreeMap::new(),
                variant: None,
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
        self.visit_nodes(path, &mut |path, node| {
            for origin in &node.roots {
                visit(path, origin);
            }
        });
    }

    fn visit_nodes(
        &self,
        path: &mut Vec<Coordinate>,
        visit: &mut impl FnMut(&[Coordinate], &Self),
    ) {
        visit(path, self);
        for (coordinate, member) in &self.members {
            path.push(coordinate.clone());
            member.visit_nodes(path, visit);
            path.pop();
        }
    }

    pub(super) fn transform(&mut self, f: &mut impl FnMut(&mut Origin)) {
        self.roots.iter_mut().for_each(&mut *f);
        for member in self.members.values_mut() {
            member.transform(f);
        }
    }

    pub(super) fn mark_call_allocations<'d>(
        values: impl Iterator<Item = &'d mut Self>,
        body: Span,
    ) {
        let values: Vec<_> = values.collect();
        let mut regions = BTreeMap::<Region, BTreeSet<_>>::new();
        for (output, value) in values.iter().enumerate() {
            value.visit_origins(&mut Vec::new(), &mut |path, origin| {
                let source = origin.region.source;
                if origin.region.instance != RegionInstance::Source
                    && source.file == body.file
                    && source.start >= body.start
                    && source.end <= body.end
                {
                    regions.entry(origin.region.clone()).or_default().insert((
                        output,
                        path.to_vec(),
                        origin.mode,
                        origin.new,
                    ));
                }
            });
        }
        if !regions
            .keys()
            .any(|region| region.summarized() || region.returned.is_some())
        {
            return;
        }
        // Published indices are ordered by the shape visible to the caller.
        let mut by_shape: Vec<_> = regions
            .into_iter()
            .map(|(region, paths)| (paths, region.summarized(), region))
            .collect();
        by_shape.sort_unstable();
        let identities: BTreeMap<_, _> = by_shape
            .into_iter()
            .enumerate()
            .map(|(index, (_, summarized, region))| {
                (region, AllocationIdentity { index, summarized })
            })
            .collect();
        for value in values {
            value.transform(&mut |origin| {
                origin.return_allocation = identities.get(&origin.region).copied();
            });
        }
    }

    pub(super) fn return_allocations(values: &[Self]) -> Vec<ReturnAllocation> {
        let mut allocations = BTreeSet::new();
        for value in values {
            value.visit_nodes(&mut Vec::new(), &mut |path, node| {
                for origin in &node.roots {
                    let Some(AllocationIdentity { index, summarized }) = origin.return_allocation
                    else {
                        continue;
                    };
                    allocations.insert(ReturnAllocation {
                        path: path.to_vec(),
                        index,
                        access: origin.mode,
                        new: origin.new,
                        qualified: node.requires_new,
                        summarized,
                    });
                }
            });
        }
        allocations.into_iter().collect()
    }

    fn compact_snapshot(&mut self, local_data: impl Fn(Span) -> bool + Copy) -> bool {
        let mut plain = true;
        for member in self.members.values_mut() {
            plain &= member.compact_snapshot(local_data);
        }
        plain &= !self.requires_new
            && !self.result_fresh
            && !self.stateful_handler
            && self.task_scope.is_none()
            && self.results.is_empty()
            && self.latent_effects.is_empty()
            && self.environments.is_empty()
            && self.publications.is_empty()
            && self.invocations.is_empty()
            && self.roots.iter().all(|origin| {
                origin.mode == Access::Immutable
                    && origin.region.instance != RegionInstance::Source
                    && local_data(origin.region.source)
                    && origin.callback_result.is_none()
                    && origin.confined.is_none()
            });
        if plain && !self.roots.is_empty() {
            // A frozen, locally allocated graph cannot carry caller sources
            // or writable edges. Its root suffices for later projections.
            self.members.clear();
        }
        plain
    }

    fn size(&self) -> usize {
        1 + self.roots.len() + self.members.values().map(Self::size).sum::<usize>()
    }

    fn fold_old_allocations(&mut self, members: &mut BTreeMap<Region, Self>) {
        for member in self.members.values_mut() {
            member.fold_old_allocations(members);
        }
        if !self
            .roots
            .iter()
            .any(|root| root.region.instance == RegionInstance::PriorAllocations)
            || self
                .roots
                .iter()
                .any(|root| root.region.instance == RegionInstance::Source)
        {
            return;
        }
        let parents: BTreeSet<_> = self.roots.iter().map(|root| &root.region).collect();
        // Earlier instances can come from different branches. If a join has
        // lost the association between a parent and its fields, keep the
        // possible edges for each represented allocation.
        for (coordinate, mut member) in std::mem::take(&mut self.members) {
            member.transform(&mut |origin| origin.branches.clear());
            for parent in &parents {
                let mut slot = (*parent).clone();
                slot.selection.push(coordinate.clone());
                merge_member(members, slot, member.clone());
            }
        }
    }

    fn remember_return_graph(&self, members: &mut BTreeMap<Region, Self>, call: Span) {
        let parents: BTreeSet<_> = self
            .roots
            .iter()
            .map(|origin| &origin.region)
            .filter(|region| region.source == call && region.returned.is_some())
            .collect();
        for (coordinate, member) in &self.members {
            for parent in &parents {
                let mut slot = (*parent).clone();
                slot.selection.push(coordinate.clone());
                merge_member(members, slot, member.clone());
            }
            member.remember_return_graph(members, call);
        }
    }

    pub(super) fn has_call_graph(&self, call: Span) -> bool {
        self.origins()
            .any(|origin| origin.region.source == call && origin.region.returned.is_some())
    }

    pub(super) fn can_freeze(&self) -> bool {
        self.freezable_sources(self.requires_new)
    }

    fn freezable_sources(&self, owned: bool) -> bool {
        self.roots
            .iter()
            .all(|root| root.mode == Access::Immutable || owned && root.new)
            && self
                .members
                .values()
                .all(|member| member.freezable_sources(owned && self.environments.is_empty()))
    }

    pub(super) fn freeze(&mut self) {
        for root in &mut self.roots {
            root.fix_mode(Access::Immutable);
            root.new = false;
            root.from_variable = false;
        }
        for member in self.members.values_mut() {
            member.freeze();
        }
        self.requires_new = false;
    }

    pub(super) fn receive_binding(&mut self, access: Access) {
        for root in &mut self.roots {
            root.fix_mode(access);
            root.from_variable = false;
            if matches!(access, Access::Ref | Access::Shared) {
                root.new = false;
            }
        }
        self.requires_new = false;
    }

    pub(super) fn results(&self) -> BTreeSet<ResultOccurrence> {
        self.root_results()
            .into_iter()
            .chain(self.members.values().flat_map(Self::results))
            .collect()
    }

    pub(super) fn root_results(&self) -> BTreeSet<ResultOccurrence> {
        self.results
            .iter()
            .map(|item| item.occurrence.clone())
            .collect()
    }

    pub(super) fn has_root_result(&self) -> bool {
        !self.results.is_empty()
    }

    pub(super) fn set_variant(&mut self, variant: &str) {
        for root in &mut self.roots {
            root.variant = Some(variant.into());
        }
    }

    pub(super) fn forget_variants(&mut self) {
        self.transform(&mut |origin| origin.variant = None);
    }

    pub(super) fn known_variant(&self) -> Option<&str> {
        let variant = self.roots.first()?.variant.as_deref()?;
        self.roots
            .iter()
            .all(|root| root.variant.as_deref() == Some(variant))
            .then_some(variant)
    }

    fn stamp_results(&mut self, choices: &Choices) {
        if choices.is_empty() {
            return;
        }
        self.rewrite_results(&mut |mut item| {
            item.branches
                .extend(choices.iter().map(|(&key, &arm)| (key, arm)));
            Some(item)
        });
    }

    fn select_results(&mut self, choices: &Choices) {
        self.rewrite_results(&mut |item| compatible(&item.branches, choices).then_some(item));
    }

    fn rewrite_results(
        &mut self,
        transform: &mut impl FnMut(ResultReference) -> Option<ResultReference>,
    ) {
        self.results = std::mem::take(&mut self.results)
            .into_iter()
            .filter_map(&mut *transform)
            .collect();
        for member in self.members.values_mut() {
            member.rewrite_results(transform);
        }
    }

    fn remap_results(
        &mut self,
        carried: &BTreeMap<ResultOccurrence, ResultOccurrence>,
        age_choices: impl Fn(&mut Choices),
    ) {
        if carried.is_empty() && self.results().is_empty() {
            return;
        }
        self.rewrite_results(&mut |mut item| {
            if let Some(target) = carried.get(&item.occurrence) {
                if target.places.is_empty() {
                    return None;
                }
                item.occurrence = target.clone();
            }
            age_choices(&mut item.branches);
            Some(item)
        });
    }

    fn result_places(
        &self,
        holder: ResultHolder,
        path: &mut Vec<Coordinate>,
        results: &mut BTreeMap<ResultOccurrence, ResultOccurrence>,
    ) {
        for item in &self.results {
            if let Some(carried) = results.get_mut(&item.occurrence) {
                carried.places.insert((holder, path.clone()));
            }
        }
        for (step, member) in &self.members {
            path.push(step.clone());
            member.result_places(holder, path, results);
            path.pop();
        }
    }

    pub(super) fn joined(mut self, mut other: Self) -> Self {
        self.roots.append(&mut other.roots);
        self.roots.sort_unstable();
        self.roots.dedup();
        // Widen branch correlations before fact growth makes nested branches impractical.
        if self.roots.len() > BRANCH_LIMIT {
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
        for (owner, existing_storage) in other.publications {
            *self.publications.entry(owner).or_default() |= existing_storage;
        }
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
        self.project_schema(coordinate, mode.as_mode())
    }

    fn project_schema(&self, coordinate: Coordinate, mode: Mode) -> Self {
        if let Some(mut member) = self.known_member(&coordinate) {
            self.attenuate(&mut member);
            return member;
        }
        self.project_opaque(coordinate, mode)
    }

    fn known_member(&self, coordinate: &Coordinate) -> Option<Self> {
        self.members.get(coordinate).cloned().or_else(|| {
            (*coordinate == Coordinate::Dynamic)
                .then(|| self.members.values().cloned().reduce(Self::joined))
                .flatten()
        })
    }

    fn project_opaque(&self, coordinate: Coordinate, mode: Mode) -> Self {
        let roots: Vec<_> = self
            .roots
            .iter()
            .map(|origin| {
                let mut origin = origin.clone();
                origin.region.selection.push(coordinate.clone());
                origin.variant = None;
                origin.from_variable = false;
                if !origin.draft {
                    origin.project_mode(mode);
                    // The schema of an opaque member selection can expose authority
                    // which survived the transfer of its enclosing new object.
                    if matches!(mode, Mode::Ref | Mode::Shared | Mode::Via) {
                        origin.new = false;
                    }
                }
                origin
            })
            .collect();
        Self {
            requires_new: self.requires_new && roots.iter().all(|root| root.new),
            roots,
            ..Self::default()
        }
    }

    fn attenuate(&self, member: &mut Self) {
        member.requires_new &= self.requires_new;
        for root in &mut member.roots {
            root.from_variable = false;
            root.anchor_scopes
                .extend(self.roots.iter().flat_map(|parent| &parent.anchor_scopes));
        }
        if self.roots.iter().all(|root| !root.mode.writes()) {
            if self.roots.iter().all(|root| root.mode == Access::Immutable) {
                member.freeze();
            } else {
                member.transform(&mut |origin| {
                    origin.fix_mode(Access::Ref.project(origin.mode));
                    origin.new = false;
                });
                member.requires_new = false;
            }
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

    pub(super) fn surviving_publications(
        &self,
        owner: Span,
        caller_root: bool,
        visit: &mut impl FnMut(&Self),
    ) {
        if self
            .publications
            .get(&owner)
            .is_some_and(|&existing| caller_root || existing)
        {
            visit(self);
        } else {
            for member in self.members.values() {
                member.surviving_publications(owner, caller_root, visit);
            }
        }
    }

    pub(super) fn writers(&self) -> bool {
        !self.roots.is_empty() && self.roots.iter().all(|root| root.mode.writes())
    }

    pub(super) fn returns_borrowed_writer(&self, mode: Mode) -> bool {
        let writable_loan = |origin: &Origin| origin.call_borrow && origin.mode.writes();
        (matches!(mode, Mode::Infer | Mode::New | Mode::Shared)
            && self.roots.iter().any(writable_loan))
            || self
                .members
                .values()
                .flat_map(Self::origins)
                .any(writable_loan)
    }

    pub(super) fn detach_handed_off_paths(&mut self) {
        let ended: BTreeSet<_> = self
            .roots
            .iter()
            .flat_map(|origin| origin.dependencies.iter().copied())
            .collect();
        self.transform(&mut |origin| {
            origin.dependencies.retain(|token| !ended.contains(token));
        });
        for root in &mut self.roots {
            root.new = true;
            root.inherits_mode = false;
            root.reception.clear();
        }
        self.requires_new = true;
    }

    pub(super) fn root_dependencies(&self) -> impl Iterator<Item = Span> + '_ {
        self.roots.iter().flat_map(|origin| {
            origin
                .dependency_spans()
                .chain(std::iter::once(origin.region.source))
        })
    }
}

fn merge_member(members: &mut BTreeMap<Region, Datum>, slot: Region, member: Datum) {
    match members.entry(slot) {
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            let value = entry.get_mut();
            *value = std::mem::take(value).joined(member);
        }
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(member);
        }
    }
}

fn join_member(left: Option<Datum>, right: Datum) -> Option<Datum> {
    Some(match left {
        Some(left) => left.joined(right),
        None => right,
    })
}

#[derive(Clone, Eq, PartialEq)]
pub(super) struct Slot {
    pub decl: Span,
    pub variable: bool,
    pub mode: Mode,
    pub value: Datum,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Replacement {
    pub value: Datum,
    pub definite: bool,
}

#[derive(Clone, Default, Eq, PartialEq)]
pub(super) struct Ledger {
    pub slots: BTreeMap<Span, Slot>,
    revoked: BTreeMap<Occurrence, Revocations>,
    pub obligations: BTreeSet<ResultOccurrence>,
    pub inspected: BTreeSet<ResultOccurrence>,
    pub lost_results: BTreeSet<Span>,
    pub iteration: Vec<Datum>,
    pub holds: Vec<(Mode, Datum)>,
    pub choices: Choices,
    pub no_continuation: bool,
    replacements: BTreeMap<Region, Replacement>,
    loop_members: BTreeMap<Region, Datum>,
}

impl Ledger {
    pub(super) fn remember_return_graph(&mut self, value: &Datum, call: Span) {
        value.remember_return_graph(&mut self.loop_members, call);
    }

    pub(super) fn reset_revocations(&mut self) {
        self.revoked.clear();
    }

    pub(super) fn revoke(
        &mut self,
        token: Occurrence,
        origin: Option<&Origin>,
        trigger: Option<Revocation>,
    ) {
        let mut choices = self.choices.clone();
        if let Some(origin) = origin {
            choices.extend(origin.branches.iter().map(|(&branch, &arm)| (branch, arm)));
        }
        let alternatives = self
            .revoked
            .entry(token)
            .or_default()
            .entry(trigger)
            .or_default();
        alternatives.insert(choices);
        Self::widen_revocations(alternatives);
    }

    fn widen_revocations(alternatives: &mut BTreeSet<Choices>) {
        if alternatives.len() > BRANCH_LIMIT {
            alternatives.clear();
            alternatives.insert(Choices::new());
        }
    }

    pub(super) fn hold_conflict(&self, value: &Datum, mode: Mode) -> Option<bool> {
        if self.holds.is_empty() {
            return None;
        }
        let value = self.loop_snapshot(value);
        self.holds.iter().find_map(|(held_mode, held)| {
            conflicts(&value, mode, &self.loop_snapshot(held), *held_mode)
        })
    }

    pub(super) fn stamp(&self, value: &mut Datum) {
        value.transform(&mut |origin| {
            origin
                .branches
                .extend(self.choices.iter().map(|(&k, &v)| (k, v)));
        });
        value.stamp_results(&self.choices);
    }

    pub(super) fn take_choice(&mut self, span: Span, arm: usize) {
        let key = span.into();
        self.choices.insert(key, arm);
        let selected = Choices::from([(key, arm)]);
        for slot in self.slots.values_mut() {
            slot.value.transform(&mut |origin| {
                origin.branches.insert(key, arm);
            });
            slot.value.stamp_results(&selected);
        }
        for replacement in self.replacements.values_mut() {
            replacement.value.transform(&mut |origin| {
                origin.branches.insert(key, arm);
            });
            replacement.value.stamp_results(&selected);
        }
    }

    pub(super) fn record_result(&mut self, value: &mut Datum, span: Span) {
        let occurrence = ResultOccurrence {
            span,
            places: BTreeSet::new(),
            created_in: self.choices.clone(),
        };
        self.obligations.insert(occurrence.clone());
        value.results.insert(ResultReference {
            occurrence,
            branches: self.choices.clone(),
        });
    }

    pub(super) fn variant_paths(&self, value: &Datum) -> Vec<(Self, Datum)> {
        let paths: BTreeSet<_> = value.roots.iter().map(|root| &root.branches).collect();
        if paths.len() < 2
            || paths.len() > BRANCH_LIMIT
            || value.roots.iter().any(|root| root.variant.is_none())
            || (self.obligations.is_empty() && value.results().is_empty())
        {
            return Vec::new();
        }
        paths
            .into_iter()
            .filter(|path| compatible(path, &self.choices))
            .map(|path| {
                let mut ledger = self.clone();
                ledger
                    .choices
                    .extend(path.iter().map(|(&key, &arm)| (key, arm)));
                ledger
                    .obligations
                    .retain(|item| compatible(&item.created_in, path));
                ledger
                    .inspected
                    .retain(|item| compatible(&item.created_in, path));
                for slot in ledger.slots.values_mut() {
                    slot.value.select_results(path);
                }
                for replacement in ledger.replacements.values_mut() {
                    replacement.value.select_results(path);
                }
                for member in ledger.loop_members.values_mut() {
                    member.select_results(path);
                }
                let mut selected = value.clone();
                selected
                    .roots
                    .retain(|root| compatible(&root.branches, path));
                selected.select_results(path);
                (ledger, selected)
            })
            .collect()
    }

    pub(super) fn loop_backedge(
        &mut self,
        owner: Span,
        repeated: Span,
        entry: &Self,
        local_data: impl Fn(Span) -> bool + Copy,
    ) {
        let local = |span: Span| {
            span.file == repeated.file && span.start >= repeated.start && span.end <= repeated.end
        };
        let age = |mut occurrence: Occurrence| {
            occurrence.prior_iteration |= local(occurrence.span);
            occurrence
        };
        // Correlations within the last iteration survive the backedge. Older
        // decisions can vary independently of the branch that is about to run.
        let age_choices = |choices: &mut Choices| {
            *choices = std::mem::take(choices)
                .into_iter()
                .filter(|(key, _)| key.span != owner && (!key.prior_iteration || !local(key.span)))
                .map(|(key, arm)| (age(key), arm))
                .collect();
        };
        self.choices
            .retain(|key, _| key.span != owner && !local(key.span));
        self.iteration.truncate(entry.iteration.len());
        self.holds.truncate(entry.holds.len());
        self.slots.retain(|id, _| entry.slots.contains_key(id));
        let carried = self.rebase_results(local, age_choices);
        for value in self
            .iteration
            .iter_mut()
            .chain(self.holds.iter_mut().map(|(_, value)| value))
        {
            value.remap_results(&carried, age_choices);
        }
        let age_value = |value: &mut Datum| {
            value.compact_snapshot(local_data);
            value.remap_results(&carried, age_choices);
            value.transform(&mut |origin| {
                origin.region.age_allocation(local(origin.region.source));
                origin.dependencies = std::mem::take(&mut origin.dependencies)
                    .into_iter()
                    .map(age)
                    .collect();
                age_choices(&mut origin.branches);
            });
        };

        for slot in self.slots.values_mut() {
            age_value(&mut slot.value);
            slot.value.fold_old_allocations(&mut self.loop_members);
        }
        for (mut slot, mut member) in std::mem::take(&mut self.loop_members) {
            slot.age_allocation(local(slot.source));
            age_value(&mut member);
            member.fold_old_allocations(&mut self.loop_members);
            merge_member(&mut self.loop_members, slot, member);
        }
        for (mut region, mut update) in std::mem::take(&mut self.replacements) {
            region.age_allocation(local(region.source));
            update.definite &= !region.summarized();
            age_value(&mut update.value);
            update.value.fold_old_allocations(&mut self.loop_members);
            self.replacements
                .entry(region)
                .and_modify(|prior| {
                    prior.value = std::mem::take(&mut prior.value).joined(update.value.clone());
                    prior.definite &= update.definite;
                })
                .or_insert(update);
        }
        for (token, triggers) in std::mem::take(&mut self.revoked) {
            let archived = self.revoked.entry(age(token)).or_default();
            for (trigger, choices) in triggers {
                let combined = archived.entry(trigger).or_default();
                combined.extend(choices.into_iter().map(|mut branch| {
                    age_choices(&mut branch);
                    branch
                }));
                Self::widen_revocations(combined);
            }
        }
    }

    fn rebase_results(
        &mut self,
        local: impl Fn(Span) -> bool,
        age_choices: impl Fn(&mut Choices),
    ) -> BTreeMap<ResultOccurrence, ResultOccurrence> {
        let mut carried: BTreeMap<_, _> = self
            .obligations
            .iter()
            .filter(|item| local(item.span))
            .map(|item| {
                let mut target = item.clone();
                target.places.clear();
                age_choices(&mut target.created_in);
                (item.clone(), target)
            })
            .collect();
        if carried.is_empty() {
            return carried;
        }
        let bindings = self
            .slots
            .iter()
            .map(|(&id, slot)| (ResultHolder::Binding(id), &slot.value));
        let iterables = self
            .iteration
            .iter()
            .enumerate()
            .map(|(id, value)| (ResultHolder::Iterable(id), value));
        let handlers = self
            .holds
            .iter()
            .enumerate()
            .map(|(id, (_, value))| (ResultHolder::Handler(id), value));
        // A carried identity is determined by its surviving paths. Different
        // evaluations of one site remain distinct when held in different slots.
        for (holder, value) in bindings.chain(iterables).chain(handlers) {
            self.snapshot(value)
                .result_places(holder, &mut Vec::new(), &mut carried);
        }
        let rebase = |item: &ResultOccurrence| match carried.get(item) {
            Some(target) if target.places.is_empty() => None,
            Some(target) => Some(target.clone()),
            None => Some(item.clone()),
        };
        let pending = self.obligations.difference(&self.inspected);
        self.lost_results.extend(
            pending
                .clone()
                .filter(|item| {
                    carried
                        .get(*item)
                        .is_some_and(|result| result.places.is_empty())
                })
                .map(|item| item.span),
        );
        let pending: BTreeSet<_> = pending.filter_map(rebase).collect();
        self.obligations = self.obligations.iter().filter_map(rebase).collect();
        self.inspected = self
            .inspected
            .iter()
            .filter_map(rebase)
            .filter(|item| !pending.contains(item))
            .collect();
        carried
    }

    pub(super) fn size(&self) -> usize {
        self.slots
            .values()
            .map(|slot| slot.value.size())
            .chain(self.replacements.values().map(|update| update.value.size()))
            .chain(self.loop_members.values().map(Datum::size))
            .sum()
    }

    pub(super) fn merge_bindings(&mut self, alternatives: &[Self]) {
        let mut prior = self.clone();
        if let Some(first) = alternatives.first() {
            for (&decl, slot) in &first.slots {
                if alternatives
                    .iter()
                    .all(|branch| branch.slots.contains_key(&decl))
                {
                    prior.slots.entry(decl).or_insert_with(|| slot.clone());
                }
            }
        }
        self.merge(&prior, alternatives);
    }

    pub(super) fn continue_at_pattern(&mut self, mut paths: Vec<Self>) -> bool {
        if let Some(last) = paths.pop() {
            if paths.is_empty() {
                *self = last;
            } else {
                paths.push(last);
                self.merge_bindings(&paths);
            }
            true
        } else {
            false
        }
    }

    pub(super) fn merge(&mut self, prior: &Self, alternatives: &[Self]) {
        let alternatives: Vec<_> = alternatives
            .iter()
            .filter(|ledger| !ledger.no_continuation)
            .collect();
        self.no_continuation = prior.no_continuation || alternatives.is_empty();
        self.slots = prior.slots.clone();
        self.revoked = prior.revoked.clone();
        self.obligations.clear();
        if alternatives.is_empty() {
            self.obligations.clone_from(&prior.obligations);
        }
        self.lost_results = prior.lost_results.clone();
        for branch in &alternatives {
            for (&token, revoked) in &branch.revoked {
                let merged = self.revoked.entry(token).or_default();
                for (&trigger, alternatives) in revoked {
                    let cases = merged.entry(trigger).or_default();
                    cases.extend(alternatives.iter().cloned());
                    Self::widen_revocations(cases);
                }
            }
            self.obligations.extend(branch.obligations.iter().cloned());
            self.lost_results.extend(&branch.lost_results);
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
                .cloned()
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
        self.merge_replacements(prior, &alternatives);
        self.loop_members = if alternatives.is_empty() {
            prior.loop_members.clone()
        } else {
            let mut members = BTreeMap::new();
            for (slot, member) in alternatives.iter().flat_map(|branch| &branch.loop_members) {
                merge_member(&mut members, slot.clone(), member.clone());
            }
            members
        };
    }

    fn merge_replacements(&mut self, prior: &Self, alternatives: &[&Self]) {
        if alternatives.is_empty() {
            self.replacements.clone_from(&prior.replacements);
            return;
        }
        self.replacements = Self::join_updates(
            alternatives
                .iter()
                .map(|branch| &branch.replacements)
                .collect(),
        );
    }

    pub(super) fn join_updates(
        paths: Vec<&BTreeMap<Region, Replacement>>,
    ) -> BTreeMap<Region, Replacement> {
        let regions: BTreeSet<_> = paths.iter().flat_map(|path| path.keys()).collect();
        regions
            .into_iter()
            .filter_map(|region| {
                let entries: Vec<_> = paths.iter().filter_map(|path| path.get(region)).collect();
                let definite =
                    entries.len() == paths.len() && entries.iter().all(|entry| entry.definite);
                let value = entries
                    .into_iter()
                    .map(|entry| entry.value.clone())
                    .reduce(Datum::joined)?;
                Some((region.clone(), Replacement { value, definite }))
            })
            .collect()
    }

    pub(super) fn call_updates(
        &self,
        owner: Span,
        formals: &[Option<Span>],
        captures: &BTreeSet<Span>,
    ) -> BTreeMap<Region, Replacement> {
        self.replacements
            .iter()
            .filter(|(region, update)| {
                (formals.contains(&Some(region.source))
                    || region.selection.is_empty() && captures.contains(&region.source))
                    && update.value.publications.contains_key(&owner)
            })
            .map(|(region, update)| {
                (
                    region.clone(),
                    Replacement {
                        value: self.snapshot(&update.value),
                        definite: update.definite,
                    },
                )
            })
            .collect()
    }

    pub(super) fn replaces_slot(&self, owner: Span, decl: Span) -> bool {
        self.replacements
            .get(&Region::root(decl))
            .is_some_and(|update| update.value.publications.contains_key(&owner))
    }

    pub(super) fn replace_slot(&mut self, decl: Span, mut value: Datum, definite: bool) -> bool {
        self.stamp(&mut value);
        let Some(slot) = self.slots.get_mut(&decl) else {
            return false;
        };
        slot.value = if definite {
            value.clone()
        } else {
            std::mem::take(&mut slot.value).joined(value.clone())
        };
        self.replace_region(&Region::root(decl), &value, definite);
        true
    }

    pub(super) fn replace_member(&mut self, slot: &Datum, mut value: Datum, definite: bool) {
        self.stamp(&mut value);
        let single = slot
            .roots
            .first()
            .is_some_and(|first| slot.roots.iter().all(|root| root.region == first.region));
        for origin in &slot.roots {
            let region = &origin.region;
            let definite = definite
                && single
                && !region.summarized()
                && !region.selection.contains(&Coordinate::Dynamic);
            self.replace_region(region, &value, definite);
        }
    }

    fn replace_region(&mut self, region: &Region, value: &Datum, definite: bool) {
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

    pub(super) fn project(&self, base: &Datum, coordinate: Coordinate, mode: Access) -> Datum {
        self.project_schema(base, coordinate, mode.as_mode())
    }

    pub(super) fn project_schema(&self, base: &Datum, coordinate: Coordinate, mode: Mode) -> Datum {
        self.project_members(base, coordinate, mode, |_| true, |_| true)
    }

    fn project_members(
        &self,
        base: &Datum,
        coordinate: Coordinate,
        mode: Mode,
        follow: impl Fn(&Origin) -> bool,
        include_opaque: impl Fn(&Region) -> bool,
    ) -> Datum {
        if base.roots.is_empty() || self.replacements.is_empty() && self.loop_members.is_empty() {
            return base.project_schema(coordinate, mode);
        }
        let initial = base.known_member(&coordinate);
        let slot = base.slot_projection(coordinate.clone());
        let mut missing = Vec::new();
        let mut projected = None;
        let mut use_inline = false;
        for (root, origin) in base.roots.iter().zip(&slot.roots) {
            if !follow(root) {
                use_inline = true;
                continue;
            }
            let region = &origin.region;
            let exact = self.replacements.get(region);
            if let Some(update) = exact.filter(|update| update.definite) {
                projected = join_member(projected, update.value.clone());
                continue;
            }
            use_inline = true;
            let matches = |key: &Region| {
                key.selection.len() == region.selection.len() && key.overlaps(region)
            };
            let mut folded = false;
            for (key, member) in &self.loop_members {
                if matches(key) {
                    folded |= key == region;
                    projected = join_member(projected, member.clone());
                }
            }
            for (key, update) in &self.replacements {
                if matches(key) {
                    projected = join_member(projected, update.value.clone());
                }
            }
            if !folded && initial.is_none() && include_opaque(region) {
                missing.push(root.clone());
            }
        }
        if use_inline && let Some(initial) = initial {
            projected = join_member(projected, initial);
        }
        if let Some(value) = &mut projected {
            base.attenuate(value);
        }
        if !missing.is_empty() {
            let fallback = Datum {
                roots: missing,
                requires_new: base.requires_new,
                ..Datum::default()
            };
            projected = join_member(projected, fallback.project_opaque(coordinate, mode));
        }
        projected.unwrap_or_default()
    }

    pub(super) fn snapshot(&self, value: &Datum) -> Datum {
        if self.replacements.is_empty() && self.loop_members.is_empty() {
            return value.clone();
        }
        self.snapshot_members(value, &mut BTreeSet::new())
    }

    fn snapshot_members(&self, value: &Datum, ancestors: &mut BTreeSet<(Region, Access)>) -> Datum {
        let mut snapshot = value.clone();
        let regions: BTreeSet<_> = value
            .roots
            .iter()
            .map(|root| (root.region.clone(), root.mode))
            .filter(|root| !ancestors.contains(root))
            .collect();
        ancestors.extend(regions.iter().cloned());
        let mut coordinates: BTreeSet<_> = value.members.keys().cloned().collect();
        for key in self.replacements.keys().chain(self.loop_members.keys()) {
            for (region, _) in &regions {
                if key.overlaps(region)
                    && let Some(coordinate) = key.selection.get(region.selection.len())
                {
                    coordinates.insert(coordinate.clone());
                }
            }
        }
        for coordinate in coordinates {
            let member = self.project_members(
                value,
                coordinate.clone(),
                Mode::Mut,
                |root| regions.contains(&(root.region.clone(), root.mode)),
                // A symbolic root already represents its entry graph. During
                // a snapshot, invent a path only to reach a tracked store.
                |region| {
                    self.replacements.keys().any(|target| {
                        region.selection.len() <= target.selection.len() && region.overlaps(target)
                    })
                },
            );
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
        let results = self.loop_snapshot(datum).results();
        self.inspected.extend(results);
    }

    pub(super) fn inspect_root(&mut self, datum: &Datum) {
        self.inspected.extend(datum.root_results());
    }

    pub(super) fn loop_snapshot<'d>(&self, datum: &'d Datum) -> Cow<'d, Datum> {
        if self.loop_members.is_empty() {
            Cow::Borrowed(datum)
        } else {
            Cow::Owned(self.snapshot(datum))
        }
    }

    pub(super) fn revocations(&self, datum: &Datum) -> BTreeSet<Option<Revocation>> {
        if self.revoked.is_empty() {
            return BTreeSet::new();
        }
        self.loop_snapshot(datum)
            .origins()
            .flat_map(|origin| {
                origin
                    .dependencies
                    .iter()
                    .filter_map(|token| self.revoked.get(token))
                    .flatten()
                    .filter(|(trigger, branches)| {
                        let received_here = origin.callback_result.is_some()
                            && matches!(trigger, Some(Revocation::Callback { site, .. })
                                if *site == origin.region.source);
                        !received_here
                            && branches.iter().any(|branch| {
                                compatible(branch, &self.choices)
                                    && compatible(branch, &origin.branches)
                            })
                    })
                    .map(|(&trigger, _)| trigger)
            })
            .collect()
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
