use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

use ril_base::span::Span;
use ril_frontend::syntax::Mode;
use serde::{Deserialize, Serialize};

use super::{ArrayExtent, Input, ModeExpression, ModeStep, ReturnAllocation};

mod storage;
pub(super) use storage::{
    DeferredStorageCall, StorageAction, StorageFlow, StorageRead, StorageTarget,
};

mod conflicts;
mod datum;
mod ledger;
mod results;
mod snapshots;
pub(super) use conflicts::{AccessConflict, ConflictKind, ForwardedMode, ViaConflict, conflicts};
use datum::{join_member, merge_member};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
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

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Coordinate {
    Field(String),
    Index(String),
    Dynamic,
    MapKey,
    // Array indices at or above the given position.
    ArrayTail(usize),
}

impl Coordinate {
    fn covers(&self, step: &Self) -> bool {
        match (self, step) {
            (Self::MapKey, _) | (_, Self::MapKey) => self == step,
            (Self::Dynamic, _) => true,
            (Self::ArrayTail(start), Self::Index(index)) => {
                index.parse::<usize>().is_ok_and(|index| index >= *start)
            }
            (Self::ArrayTail(start), Self::ArrayTail(other)) => start <= other,
            _ => self == step,
        }
    }

    fn is_range(&self) -> bool {
        matches!(self, Self::Dynamic | Self::ArrayTail(_))
    }
}

pub(super) fn widen_recursive_projection(
    path: &mut Vec<Coordinate>,
    previous: &[Coordinate],
    recursive: &mut Option<Vec<Coordinate>>,
) {
    if path.len() <= previous.len() {
        return;
    }
    // A recursive traversal can extend a selection on every call. Keep the
    // common prefix and look for the final selection within the reachable graph.
    if recursive.is_none() {
        let suffix = path
            .iter()
            .rev()
            .zip(previous.iter().rev())
            .take_while(|(left, right)| left == right)
            .count();
        *recursive = Some(path.iter().skip(path.len() - suffix).cloned().collect());
    }
    let prefix = path
        .iter()
        .zip(previous)
        .take_while(|(left, right)| left == right)
        .count();
    path.truncate(prefix);
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

    fn capture_slot(source: Span) -> Self {
        let mut cell = Self::allocation(source);
        cell.selection.push(Coordinate::Index("0".into()));
        cell
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

    fn append_parent(&self) -> Option<&[Coordinate]> {
        let (member, parent) = self.selection.split_last()?;
        matches!(member, Coordinate::ArrayTail(_)).then_some(parent)
    }

    fn allocation_root(&self) -> Self {
        let mut root = self.clone();
        root.selection.clear();
        root
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
                .all(|(a, b)| a.covers(b) || b.covers(a))
    }

    pub(super) fn matches_axis(&self, projection: &Self) -> bool {
        self.source == projection.source
            && self.selection.len() == projection.selection.len()
            && self
                .selection
                .iter()
                .zip(&projection.selection)
                .all(|(axis, step)| axis.covers(step))
    }
}

pub(super) type Reception = ModeStep<Region>;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Origin {
    pub region: Region,
    pub mode: Access,
    pub inherits_mode: bool,
    pub callback_result: Option<CallbackOrigin>,
    pub storage_read: Option<StorageRead>,
    pub array_extent: Option<ArrayExtent>,
    pub snapshot_provider: Option<Span>,
    // A copied node has fresh authority. Its enclosing member's schema
    // determines access when the node is projected from the copy.
    pub clone_member: bool,
    // A functional update retains the source for opaque projections. Its
    // materialized members describe the copied graph independently.
    pub detached_snapshot: bool,
    pub return_allocation: Option<AllocationIdentity>,
    pub reception: Vec<Reception>,
    pub new: bool,
    // A marker on this expression, independent of the source's existing access.
    pub explicit_share: bool,
    // A direct read of a replaceable slot cannot anchor a ref binding.
    pub from_variable: bool,
    pub call_scoped_access: bool,
    entry_graph: Option<EntryGraph>,
    capture: Option<CaptureEntry>,
    pub dependencies: BTreeSet<Occurrence>,
    pub anchor_scopes: BTreeSet<Span>,
    pub branches: Choices,
    variant: Option<String>,
    pub confined: Option<Span>,
    pub draft: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EntryGraph {
    callable: Span,
    new_qualified: bool,
    shared_at: Option<usize>,
    via_at: Vec<Region>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct CaptureEntry {
    pub callable: Span,
    pub binding: Span,
    pub inferred: bool,
    shared: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct CapturePath {
    pub owner: Span,
    pub region: Region,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct CallbackOrigin {
    pub template: usize,
    pub cap: Option<Access>,
}

impl Origin {
    pub(super) fn can_freeze(&self, owned: bool) -> bool {
        self.mode == Access::Immutable || owned && self.new && !self.call_scoped_access
    }

    pub(super) fn enter_formal(&mut self, callable: Span, mode: Mode) {
        self.inherits_mode = mode == Mode::Via;
        self.call_scoped_access = mode == Mode::Mut;
        self.entry_graph =
            matches!(mode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via).then(|| EntryGraph {
                callable,
                new_qualified: matches!(mode, Mode::New | Mode::Via),
                shared_at: (mode == Mode::Shared).then_some(0),
                via_at: if mode == Mode::Via {
                    vec![Region::root(self.region.source)]
                } else {
                    Vec::new()
                },
            });
    }

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
            self.call_scoped_access = false;
            if let Some(entry) = &mut self.entry_graph {
                entry.shared_at = Some(self.region.selection.len());
                entry.via_at.clear();
            }
            if let Some(capture) = &mut self.capture {
                capture.shared |= self.mode.writes();
            }
        }
        if member == Mode::Via
            && self.mode.writes()
            && let Some(entry) = &mut self.entry_graph
        {
            entry.via_at.push(self.region.clone());
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

    fn shared_boundary(&self, input: &impl Fn(&Region) -> Option<Input>) -> Option<&[Coordinate]> {
        let entry = self.entry_graph.as_ref()?;
        let depth = entry
            .via_at
            .iter()
            .rev()
            .find(|axis| input(axis) == Some(Input::Shared))
            .map(|axis| axis.selection.len())
            .or(entry.shared_at)?;
        self.region.selection.get(..depth)
    }

    fn has_shared_boundary(&self) -> bool {
        self.entry_graph
            .as_ref()
            .is_some_and(|entry| entry.shared_at.is_some() || !entry.via_at.is_empty())
    }

    pub(super) fn entry_callable(&self) -> Option<Span> {
        self.entry_graph.as_ref().map(|entry| entry.callable)
    }

    pub(super) fn handed_off_entry(&self, owned: bool) -> Option<Span> {
        self.entry_graph
            .as_ref()
            .filter(|entry| {
                entry.new_qualified && owned && self.new && self.mode != Access::Immutable
            })
            .map(|entry| entry.callable)
    }

    pub(super) fn forwarded_mode(&self) -> Option<ForwardedMode> {
        if self.inherits_mode {
            Some(ForwardedMode::Axis(Region::root(self.region.source)))
        } else {
            (!self.reception.is_empty()).then(|| ForwardedMode::projection(self.reception.clone()))
        }
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
    discriminant: Option<usize>,
}

impl From<Span> for Occurrence {
    fn from(span: Span) -> Self {
        Self {
            span,
            prior_iteration: false,
            discriminant: None,
        }
    }
}

impl Occurrence {
    pub(super) fn discriminant(span: Span, index: usize) -> Self {
        Self {
            discriminant: Some(index),
            ..Self::from(span)
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ResultOccurrence {
    pub span: Span,
    part: usize,
    collection_elements: bool,
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

pub(super) fn compatible(a: &Choices, b: &Choices) -> bool {
    a.iter()
        .all(|(branch, arm)| b.get(branch).is_none_or(|other| arm == other))
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Datum {
    pub roots: Vec<Origin>,
    pub members: BTreeMap<Coordinate, Datum>,
    pub array_len: Option<usize>,
    pub map_keys: Option<Vec<Coordinate>>,
    pub(super) results: BTreeSet<ResultReference>,
    pub requires_new: bool,
    pub latent_effects: BTreeSet<String>,
    pub environments: BTreeSet<Span>,
    pub publications: BTreeMap<Span, bool>,
    // Paths in the environment at callable entry. A true entry identifies
    // the value on every incoming path, while false marks a possible source.
    pub capture_paths: BTreeMap<CapturePath, bool>,
    pub invocations: BTreeMap<Span, BTreeMap<Span, BTreeSet<Span>>>,
    // Live named captures or lexical handlers outside the member graph.
    pub live_callable_state: bool,
    pub task_scope: Option<Span>,
    pub result_fresh: bool,
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

impl ArrayExtent {
    fn meet(self, other: Self) -> Self {
        Self {
            minimum: self.minimum.min(other.minimum),
            exact: self.exact && self == other,
        }
    }
}

#[derive(Clone, Default, Eq, PartialEq)]
pub(super) struct Ledger {
    pub slots: BTreeMap<Span, Slot>,
    revoked: BTreeMap<Occurrence, Revocations>,
    obligations: BTreeSet<ResultOccurrence>,
    pub inspected: BTreeSet<ResultOccurrence>,
    // Only obligations outstanding on a subset of the incoming paths need
    // a disjunction. An absent entry leaves the ordinary obligation in force.
    pending_result_paths: BTreeMap<ResultOccurrence, BTreeSet<Choices>>,
    result_samples: BTreeMap<ResultOccurrence, BTreeSet<ResultOccurrence>>,
    pub lost_results: BTreeSet<Span>,
    pub iteration: Vec<Datum>,
    pub holds: Vec<(Mode, Datum)>,
    pub choices: Choices,
    pub no_continuation: bool,
    replacements: BTreeMap<Region, Replacement>,
    // The ordinary ledger tracks object identities. Call summaries also
    // need paths relative to the captured bindings at that call's entry.
    capture_owner: Option<Span>,
    capture_updates: BTreeMap<Region, Replacement>,
    storage_formals: Vec<Option<Span>>,
    storage_captures: BTreeSet<Span>,
    pub storage_flow: Option<StorageFlow>,
    storage_samples: BTreeMap<(Span, Vec<InvocationSite>, usize), Datum>,
    loop_members: BTreeMap<Region, Datum>,
    // Draft handles are path cursors into private working graphs. Ordinary
    // replacements in the same transfer can still update caller storage.
    drafts: BTreeMap<Region, Datum>,
    // Length evidence for array objects. Result iteration separately
    // tracks the immutable layout it needs to discharge obligations.
    array_extents: BTreeMap<Region, ArrayExtent>,
}
