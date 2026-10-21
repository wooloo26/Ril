//! Non-moving tracing arena. Handles include a generation, never an address.
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
mod channel_tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Handle(pub u64);

impl Handle {
    pub const INVALID: Self = Self(0);

    fn new(index: u32, generation: u32) -> Self {
        Self((u64::from(generation) << 32) | u64::from(index + 1))
    }

    fn index(self) -> Option<usize> {
        let low = self.0 as u32;
        (low != 0).then(|| (low - 1) as usize)
    }

    fn generation(self) -> u32 {
        (self.0 >> 32) as u32
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    File(u64),
    Child(u64),
    TaskScope(std::sync::Arc<crate::concurrent::Scope>),
    Task(std::sync::Arc<crate::concurrent::Task>),
    ParallelGroup(std::sync::Arc<crate::parallel::Group>),
    ChannelSender(std::sync::Arc<crate::channel::Sender>),
    ChannelReceiver(std::sync::Arc<crate::channel::Receiver>),
    ChannelDetached(std::sync::Arc<crate::channel::Detached>),
    NativeString(crate::native_string::NativeString),
    Path(crate::native_string::NativeString),
    RandomState(u64),
    MonotonicInstant {
        domain: u64,
        nanos: u128,
    },
    StringBuilder(String),
    BigInteger(num_bigint::BigInt),
    Unit,
    Bool(bool),
    Integer {
        value: i128,
        bits: u8,
        signed: bool,
    },
    Float {
        value: f64,
        bits: u8,
    },
    String(String),
    Bytes(crate::byte_string::Bytes),
    /// Private linear-time stream accumulation, never a source-language value.
    IoAccumulator(Vec<u8>),
    /// Immutable, non-owning position identity. This weak generation identity
    /// is deliberately not a heap edge, including when this value is copied.
    ReadPosition(Handle),
    ReadBuffer(crate::io_buffered::ReadBuffer),
    WriteBuffer(crate::io_buffered::WriteBuffer),
    Array(Vec<Handle>),
    ArrayWindow {
        backing: Handle,
        start: usize,
        len: usize,
    },
    Deque(std::collections::VecDeque<Handle>),
    PriorityHeap(crate::order::PriorityHeap),
    /// Private continuation-owned sift state; not a Ril data value.
    HeapMutation(Box<crate::order::HeapMutation>),
    Map(crate::map::OrderedMap),
    Set(crate::map::OrderedMap),
    Range {
        lower: Option<Handle>,
        upper: Option<Handle>,
        inclusive: bool,
    },
    Tuple(Vec<Handle>),
    Record(BTreeMap<String, Handle>),
    Variant {
        tag: String,
        fields: Vec<Handle>,
    },
    Closure {
        function: u64,
        environment: Handle,
    },
    CpsClosure {
        function: u64,
        environment: Handle,
    },
    BudgetClosure {
        normal: u64,
        metered: u64,
        environment: Handle,
        normal_is_cps: bool,
        metered_entry_event: bool,
    },
    CpsOperation(u64),
    RetainedClosure {
        callable: Handle,
        recipes: Vec<crate::cps::HandlerRecipe>,
    },
    CpsContinuation {
        state: crate::cps::Continuation,
        used: bool,
    },
    CpsHandlers(crate::cps::HandlerTable),
    CpsHandlerFrame(crate::cps::HandlerFrame),
    CpsResumption(crate::cps::Resumption),
    CpsStep(crate::cps::Step),
    CpsBudgetBoundary(crate::cps::BudgetBoundary),
    CpsActivation(crate::cps::Activation),
    CpsScope {
        activation: Handle,
        depth: u32,
    },
    Cell(Handle),
    /// Internal native traversal state; never exposed as a Ril value.
    Iterator {
        source: Handle,
        index: u64,
        next: Option<usize>,
        range_next: Option<Handle>,
        exhausted: bool,
    },
    Builtin(String),
    DataConstructor {
        tag: String,
        nominal: bool,
    },
    Nominal {
        tag: String,
        payload: Handle,
    },
}

impl Object {
    pub fn references(&self) -> Vec<Handle> {
        match self {
            Self::TaskScope(scope) => scope.references(),
            Self::Task(task) => task.references(),
            Self::ParallelGroup(group) => group.references(),
            Self::ChannelSender(value) => value.references(),
            Self::ChannelReceiver(value) => value.references(),
            Self::ChannelDetached(value) => value.references(),
            Self::Array(values) | Self::Tuple(values) => values.clone(),
            Self::ArrayWindow { backing, .. } => vec![*backing],
            Self::Deque(values) => values.iter().copied().collect(),
            Self::PriorityHeap(heap) => heap.references(),
            Self::HeapMutation(state) => state.references(),
            Self::Map(entries) | Self::Set(entries) => {
                entries.iter().flat_map(|(k, v)| [*k, *v]).collect()
            }
            Self::Range { lower, upper, .. } => lower.iter().chain(upper).copied().collect(),
            Self::Record(fields) => fields.values().copied().collect(),
            Self::Variant { fields, .. } => fields.clone(),
            Self::Closure { environment, .. } => vec![*environment],
            Self::CpsClosure { environment, .. } => vec![*environment],
            Self::BudgetClosure { environment, .. } => vec![*environment],
            Self::RetainedClosure { callable, recipes } => std::iter::once(*callable)
                .chain(
                    recipes
                        .iter()
                        .flat_map(|recipe| recipe.arms.values().copied()),
                )
                .collect(),
            Self::CpsContinuation { state, .. } => state.references(),
            Self::CpsHandlers(table) => table.values().copied().collect(),
            Self::CpsHandlerFrame(frame) => [frame.table, frame.parent, frame.delimiter]
                .into_iter()
                .filter(|&handle| handle != Handle::INVALID)
                .collect(),
            Self::CpsResumption(resumption) => [
                resumption.continuation,
                resumption.handlers,
                resumption.delimiter,
                resumption.activation,
            ]
            .into_iter()
            .filter(|&handle| handle != Handle::INVALID)
            .collect(),
            Self::CpsStep(step) => step.references(),
            Self::CpsBudgetBoundary(boundary) => boundary.references(),
            Self::CpsActivation(state) => [state.parent, state.handlers]
                .into_iter()
                .chain(state.cleanups.iter().copied())
                .filter(|&handle| handle != Handle::INVALID)
                .collect(),
            Self::CpsScope { activation, .. } => vec![*activation],
            Self::Cell(value) => vec![*value],
            Self::Nominal { payload, .. } => vec![*payload],
            Self::Iterator {
                source, range_next, ..
            } => std::iter::once(*source)
                .chain(range_next.iter().copied())
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Edges belonging to the stored Ril value itself. Opaque runtime resources
    /// may trace hidden queued work for GC, but that work is not part of a
    /// captured callable's environment or a transported payload's authority.
    pub(crate) fn value_references(&self) -> Vec<Handle> {
        match self {
            Self::Array(_)
            | Self::ArrayWindow { .. }
            | Self::Deque(_)
            | Self::PriorityHeap(_)
            | Self::Map(_)
            | Self::Set(_)
            | Self::Range { .. }
            | Self::Tuple(_)
            | Self::Record(_)
            | Self::Variant { .. }
            | Self::Closure { .. }
            | Self::CpsClosure { .. }
            | Self::BudgetClosure { .. }
            | Self::RetainedClosure { .. }
            | Self::Cell(_)
            | Self::Nominal { .. } => self.references(),
            _ => vec![],
        }
    }

    fn map_references(&self, mut map: impl FnMut(Handle) -> Handle) -> Self {
        match self {
            Self::Array(values) => Self::Array(values.iter().copied().map(&mut map).collect()),
            Self::ArrayWindow {
                backing,
                start,
                len,
            } => Self::ArrayWindow {
                backing: map(*backing),
                start: *start,
                len: *len,
            },
            Self::Deque(values) => Self::Deque(values.iter().copied().map(&mut map).collect()),
            Self::PriorityHeap(heap) => Self::PriorityHeap(heap.map_references(&mut map)),
            Self::Tuple(values) => Self::Tuple(values.iter().copied().map(&mut map).collect()),
            Self::Map(entries) => Self::Map(entries.map_references(&mut map)),
            Self::Set(entries) => Self::Set(entries.map_references(&mut map)),
            Self::Range {
                lower,
                upper,
                inclusive,
            } => Self::Range {
                lower: lower.map(&mut map),
                upper: upper.map(&mut map),
                inclusive: *inclusive,
            },
            Self::Record(fields) => {
                Self::Record(fields.iter().map(|(k, v)| (k.clone(), map(*v))).collect())
            }
            Self::Variant { tag, fields } => Self::Variant {
                tag: tag.clone(),
                fields: fields.iter().copied().map(&mut map).collect(),
            },
            Self::Closure {
                function,
                environment,
            } => Self::Closure {
                function: *function,
                environment: map(*environment),
            },
            Self::CpsClosure {
                function,
                environment,
            } => Self::CpsClosure {
                function: *function,
                environment: map(*environment),
            },
            Self::Cell(value) => Self::Cell(map(*value)),
            Self::BudgetClosure {
                normal,
                metered,
                environment,
                normal_is_cps,
                metered_entry_event,
            } => Self::BudgetClosure {
                normal: *normal,
                metered: *metered,
                environment: map(*environment),
                normal_is_cps: *normal_is_cps,
                metered_entry_event: *metered_entry_event,
            },
            Self::Nominal { tag, payload } => Self::Nominal {
                tag: tag.clone(),
                payload: map(*payload),
            },
            scalar => scalar.clone(),
        }
    }
}

#[derive(Debug)]
struct Slot {
    generation: u32,
    value: Option<Box<Object>>,
    marked: bool,
}

#[derive(Debug, Default)]
pub struct Heap {
    live: usize,
    slots: Vec<Slot>,
    free: Vec<u32>,
    roots: BTreeMap<u64, Handle>,
    next_root: u64,
    /// Non-owning reservations follow the shared heap across native workers.
    pub(crate) read_reservations: BTreeMap<Handle, crate::io_buffered::Binding>,
    pub(crate) read_sources: BTreeMap<Handle, BTreeSet<Handle>>,
    native_entry_aliases: BTreeMap<u64, u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapError {
    InvalidHandle,
    InvalidWindow,
    Exhausted,
    NonClonable,
}

impl Heap {
    pub fn array_elements(&self, handle: Handle) -> Result<Option<&[Handle]>, HeapError> {
        match self.get(handle)? {
            Object::Array(values) => Ok(Some(values)),
            Object::ArrayWindow {
                backing,
                start,
                len,
            } => {
                let Object::Array(values) = self.get(*backing)? else {
                    return Err(HeapError::InvalidWindow);
                };
                let end = start.checked_add(*len).ok_or(HeapError::InvalidWindow)?;
                Ok(Some(
                    values.get(*start..end).ok_or(HeapError::InvalidWindow)?,
                ))
            }
            _ => Ok(None),
        }
    }
    pub fn allocate(&mut self, value: Object) -> Result<Handle, HeapError> {
        let reservation = if let Object::ReadBuffer(buffer) = &value {
            buffer.binding.clone()
        } else {
            None
        };
        if let Some(index) = self.free.pop() {
            let slot = &mut self.slots[index as usize];
            debug_assert!(slot.value.is_none());
            slot.value = Some(Box::new(value));
            slot.marked = false;
            self.live += 1;
            let handle = Handle::new(index, slot.generation);
            self.set_read_reservation(handle, reservation);
            return Ok(handle);
        }
        let index = u32::try_from(self.slots.len()).map_err(|_| HeapError::Exhausted)?;
        if index == u32::MAX {
            return Err(HeapError::Exhausted);
        }
        self.slots.push(Slot {
            generation: 1,
            value: Some(Box::new(value)),
            marked: false,
        });
        self.live += 1;
        let handle = Handle::new(index, 1);
        self.set_read_reservation(handle, reservation);
        Ok(handle)
    }

    pub fn get(&self, handle: Handle) -> Result<&Object, HeapError> {
        let slot = self
            .slots
            .get(handle.index().ok_or(HeapError::InvalidHandle)?)
            .ok_or(HeapError::InvalidHandle)?;
        if slot.generation != handle.generation() {
            return Err(HeapError::InvalidHandle);
        }
        slot.value.as_deref().ok_or(HeapError::InvalidHandle)
    }

    pub fn get_mut(&mut self, handle: Handle) -> Result<&mut Object, HeapError> {
        let slot = self
            .slots
            .get_mut(handle.index().ok_or(HeapError::InvalidHandle)?)
            .ok_or(HeapError::InvalidHandle)?;
        if slot.generation != handle.generation() {
            return Err(HeapError::InvalidHandle);
        }
        slot.value.as_deref_mut().ok_or(HeapError::InvalidHandle)
    }

    pub fn root(&mut self, value: Handle) -> Result<u64, HeapError> {
        self.get(value)?;
        self.next_root = self.next_root.checked_add(1).ok_or(HeapError::Exhausted)?;
        self.roots.insert(self.next_root, value);
        Ok(self.next_root)
    }

    pub fn unroot(&mut self, root: u64) -> bool {
        self.roots.remove(&root).is_some()
    }

    /// The caller has stopped mutators and published all execution roots.
    pub fn collect(
        &mut self,
        execution_roots: impl IntoIterator<Item = Handle>,
    ) -> Result<usize, HeapError> {
        let mut pending: Vec<_> = self
            .roots
            .values()
            .copied()
            .chain(execution_roots)
            .collect();
        let mut marked = BTreeSet::new();
        while let Some(handle) = pending.pop() {
            if !marked.insert(handle) {
                continue;
            }
            pending.extend(self.get(handle)?.references());
        }
        for handle in marked {
            self.slots[handle.index().unwrap()].marked = true;
        }
        let mut collected = 0;
        for (index, slot) in self.slots.iter_mut().enumerate() {
            if slot.value.is_some() && !slot.marked {
                slot.value = None;
                collected += 1;
                // Never recycle a generation that could alias an old handle.
                if let Some(generation) = slot.generation.checked_add(1) {
                    slot.generation = generation;
                    self.free.push(index as u32);
                }
            }
            slot.marked = false;
        }
        self.live -= collected;
        let slots = &self.slots;
        self.read_reservations.retain(|handle, _| {
            handle.index().is_some_and(|index| {
                slots.get(index).is_some_and(|slot| {
                    slot.generation == handle.generation() && slot.value.is_some()
                })
            })
        });
        self.read_sources.retain(|handle, _| {
            handle.index().is_some_and(|index| {
                slots.get(index).is_some_and(|slot| {
                    slot.generation == handle.generation() && slot.value.is_some()
                })
            })
        });
        Ok(collected)
    }

    pub fn live_objects(&self) -> usize {
        self.live
    }

    /// Copy each source node once, preserving cycles and repeated references.
    /// Failure is checked before allocating any destination node.
    pub fn deep_clone(&mut self, root: Handle) -> Result<Handle, HeapError> {
        let mut pending = vec![root];
        let mut originals = BTreeMap::new();
        let mut window_backings = BTreeSet::new();
        while let Some(handle) = pending.pop() {
            if originals.contains_key(&handle) {
                continue;
            }
            let mut object = self.get(handle)?.clone();
            if let Object::ArrayWindow { backing, .. } = &object {
                if !window_backings.insert(*backing) {
                    return Err(HeapError::NonClonable);
                }
                object = Object::Array(
                    self.array_elements(handle)?
                        .ok_or(HeapError::InvalidWindow)?
                        .to_vec(),
                );
            }
            if let Object::Closure { environment, .. }
            | Object::CpsClosure { environment, .. }
            | Object::BudgetClosure { environment, .. } = &object
            {
                let empty = match self.get(*environment)? {
                    Object::Unit => true,
                    Object::Record(fields) => fields.is_empty(),
                    _ => false,
                };
                if !empty {
                    return Err(HeapError::NonClonable);
                }
            }
            if matches!(
                object,
                Object::Iterator { .. }
                    | Object::IoAccumulator(_)
                    | Object::HeapMutation(_)
                    | Object::File(_)
                    | Object::Child(_)
                    | Object::TaskScope(_)
                    | Object::Task(_)
                    | Object::ParallelGroup(_)
                    | Object::RetainedClosure { .. }
                    | Object::ChannelSender(_)
                    | Object::ChannelReceiver(_)
                    | Object::ChannelDetached(_)
                    | Object::CpsContinuation { .. }
                    | Object::CpsHandlers(_)
                    | Object::CpsHandlerFrame(_)
                    | Object::CpsResumption(_)
                    | Object::CpsStep(_)
                    | Object::CpsBudgetBoundary(_)
                    | Object::CpsActivation(_)
                    | Object::CpsScope { .. }
            ) {
                return Err(HeapError::NonClonable);
            }
            pending.extend(object.references());
            originals.insert(handle, object);
        }
        // Materializing one window preserves its selected graph. A second view
        // or an independently reachable backing also needs slot-sharing clone
        // semantics; source verification must keep these cases incomplete.
        if window_backings
            .iter()
            .any(|backing| originals.contains_key(backing))
        {
            return Err(HeapError::NonClonable);
        }
        let mut copies = BTreeMap::new();
        for source in originals.keys() {
            copies.insert(*source, self.allocate(Object::Unit)?);
        }
        for (source, object) in originals {
            let copied = object.map_references(|handle| copies[&handle]);
            if let Object::ReadBuffer(buffer) = &copied {
                self.set_read_reservation(copies[&source], buffer.binding.clone());
                if let Some(sources) = self.read_sources.get(&source).cloned() {
                    self.read_sources.insert(copies[&source], sources);
                }
            }
            *self.get_mut(copies[&source])? = copied;
        }
        Ok(copies[&root])
    }
    pub(crate) fn set_read_reservation(
        &mut self,
        buffer: Handle,
        binding: Option<crate::io_buffered::Binding>,
    ) {
        if let Some(binding) = binding {
            self.read_reservations.insert(buffer, binding);
        } else {
            self.read_reservations.remove(&buffer);
            self.read_sources.remove(&buffer);
        }
    }
    pub(crate) fn register_native_entries(&mut self, normal: u64, metered: u64) {
        self.native_entry_aliases.insert(metered, normal);
    }
    pub(crate) fn canonical_native_entry(&self, entry: u64) -> u64 {
        self.native_entry_aliases
            .get(&entry)
            .copied()
            .unwrap_or(entry)
    }

    /// Replace transported ticket leaves without mutating the original graph.
    /// Only ancestors of a replaced leaf are copied; every unaffected child
    /// keeps its existing identity. Placeholders preserve cycles and aliases.
    /// This method never collects: the managed caller roots the returned graph
    /// before its next allocating safepoint, while holding the shared heap gate.
    pub(crate) fn replace_ticket_graph(
        &mut self,
        root: Handle,
        replacements: &BTreeMap<Handle, Handle>,
    ) -> Result<Handle, HeapError> {
        self.get(root)?;
        if replacements.is_empty() {
            return Ok(root);
        }
        for (&before, &after) in replacements {
            if !matches!(self.get(before)?, Object::ChannelDetached(_))
                || !matches!(self.get(after)?, Object::ChannelDetached(_))
            {
                return Err(HeapError::NonClonable);
            }
        }
        let mut pending = vec![root];
        let mut originals = BTreeMap::new();
        let mut parents = BTreeMap::<Handle, Vec<Handle>>::new();
        let mut affected = BTreeSet::new();
        while let Some(handle) = pending.pop() {
            if originals.contains_key(&handle) {
                continue;
            }
            let object = self.get(handle)?.clone();
            if replacements.contains_key(&handle) {
                affected.insert(handle);
            } else {
                for child in object.value_references() {
                    parents.entry(child).or_default().push(handle);
                    pending.push(child);
                }
            }
            originals.insert(handle, object);
        }
        let mut pending: Vec<_> = affected.iter().copied().collect();
        while let Some(child) = pending.pop() {
            for &parent in parents.get(&child).into_iter().flatten() {
                if affected.insert(parent) {
                    pending.push(parent);
                }
            }
        }
        if !affected.contains(&root) {
            return Ok(root);
        }
        let mut copies = replacements.clone();
        for &source in &affected {
            if let std::collections::btree_map::Entry::Vacant(entry) = copies.entry(source) {
                entry.insert(self.allocate(Object::Unit)?);
            }
        }
        for source in affected {
            if replacements.contains_key(&source) {
                continue;
            }
            let copied = originals[&source]
                .map_references(|child| copies.get(&child).copied().unwrap_or(child));
            *self.get_mut(copies[&source])? = copied;
        }
        Ok(copies[&root])
    }

    pub fn structurally_equal(&self, left: Handle, right: Handle) -> Result<bool, HeapError> {
        let mut pending = vec![(left, right)];
        let mut visited = BTreeSet::new();
        while let Some((a, b)) = pending.pop() {
            if !visited.insert((a, b)) {
                continue;
            }
            if let (Some(a), Some(b)) = (self.array_elements(a)?, self.array_elements(b)?) {
                if a.len() != b.len() {
                    return Ok(false);
                }
                pending.extend(a.iter().copied().zip(b.iter().copied()));
                continue;
            }
            let (a, b) = (self.get(a)?, self.get(b)?);
            match (a, b) {
                (Object::Array(a), Object::Array(b)) | (Object::Tuple(a), Object::Tuple(b)) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    pending.extend(a.iter().copied().zip(b.iter().copied()));
                }
                (Object::Deque(a), Object::Deque(b)) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    pending.extend(a.iter().copied().zip(b.iter().copied()));
                }
                (Object::PriorityHeap(_), _) | (_, Object::PriorityHeap(_)) => {
                    return Err(HeapError::NonClonable);
                }
                (Object::Record(a), Object::Record(b)) => {
                    if a.keys().ne(b.keys()) {
                        return Ok(false);
                    }
                    pending.extend(a.values().copied().zip(b.values().copied()));
                }
                (Object::Map(a), Object::Map(b)) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    for (key, _, value) in a.keyed() {
                        let Some(other) = b.get(key) else {
                            return Ok(false);
                        };
                        pending.push((value, other));
                    }
                }
                (Object::Set(a), Object::Set(b)) => {
                    if a.len() != b.len() || a.keyed().any(|(key, _, _)| !b.contains(key)) {
                        return Ok(false);
                    }
                }
                (
                    Object::Range {
                        lower: a,
                        upper: b,
                        inclusive: x,
                    },
                    Object::Range {
                        lower: c,
                        upper: d,
                        inclusive: y,
                    },
                ) => {
                    if x != y || a.is_some() != c.is_some() || b.is_some() != d.is_some() {
                        return Ok(false);
                    }
                    if let (Some(a), Some(c)) = (a, c) {
                        pending.push((*a, *c));
                    }
                    if let (Some(b), Some(d)) = (b, d) {
                        pending.push((*b, *d));
                    }
                }
                (Object::Variant { tag: a, fields: x }, Object::Variant { tag: b, fields: y }) => {
                    if a != b || x.len() != y.len() {
                        return Ok(false);
                    }
                    pending.extend(x.iter().copied().zip(y.iter().copied()));
                }
                (
                    Object::Nominal { tag: a, payload: x },
                    Object::Nominal { tag: b, payload: y },
                ) => {
                    if a != b {
                        return Ok(false);
                    }
                    pending.push((*x, *y));
                }
                (Object::DataConstructor { .. }, _) | (_, Object::DataConstructor { .. }) => {
                    return Err(HeapError::NonClonable);
                }
                (Object::Closure { .. } | Object::Iterator { .. }, _)
                | (_, Object::Closure { .. } | Object::Iterator { .. }) => {
                    return Err(HeapError::NonClonable);
                }
                (
                    Object::CpsClosure { .. }
                    | Object::RetainedClosure { .. }
                    | Object::BudgetClosure { .. }
                    | Object::CpsOperation(_)
                    | Object::CpsContinuation { .. }
                    | Object::CpsHandlers(_)
                    | Object::CpsHandlerFrame(_)
                    | Object::CpsResumption(_)
                    | Object::CpsStep(_)
                    | Object::CpsBudgetBoundary(_)
                    | Object::CpsActivation(_)
                    | Object::CpsScope { .. },
                    _,
                )
                | (
                    _,
                    Object::CpsClosure { .. }
                    | Object::RetainedClosure { .. }
                    | Object::BudgetClosure { .. }
                    | Object::CpsOperation(_)
                    | Object::CpsContinuation { .. }
                    | Object::CpsHandlers(_)
                    | Object::CpsHandlerFrame(_)
                    | Object::CpsResumption(_)
                    | Object::CpsStep(_)
                    | Object::CpsBudgetBoundary(_)
                    | Object::CpsActivation(_)
                    | Object::CpsScope { .. },
                ) => return Err(HeapError::NonClonable),
                _ if a == b => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn live_accounting_survives_sweep_reuse_clone_and_failed_collection() {
        let mut heap = Heap::default();
        let first = heap.allocate(Object::Unit).unwrap();
        let retained = heap.allocate(Object::Array(vec![first])).unwrap();
        let abandoned = heap.allocate(Object::Bool(true)).unwrap();
        assert_eq!(heap.live_objects(), 3);
        assert_eq!(heap.collect([retained]).unwrap(), 1);
        assert_eq!(heap.live_objects(), 2);
        let reused = heap.allocate(Object::Bool(false)).unwrap();
        assert_ne!(reused, abandoned);
        assert_eq!(heap.live_objects(), 3);
        let copied = heap.deep_clone(retained).unwrap();
        assert_eq!(heap.live_objects(), 5);
        assert_eq!(heap.collect([abandoned]), Err(HeapError::InvalidHandle));
        assert_eq!(heap.live_objects(), 5);
        assert_eq!(heap.collect([copied]).unwrap(), 3);
        assert_eq!(heap.live_objects(), 2);
    }

    #[test]
    fn roots_keep_cycles_alive_and_stale_generations_never_revive() {
        let mut heap = Heap::default();
        let cycle = heap.allocate(Object::Array(vec![])).unwrap();
        *heap.get_mut(cycle).unwrap() = Object::Array(vec![cycle]);
        let root = heap.root(cycle).unwrap();
        assert_eq!(heap.collect([]).unwrap(), 0);
        heap.unroot(root);
        assert_eq!(heap.collect([]).unwrap(), 1);
        let reused = heap.allocate(Object::Unit).unwrap();
        assert_ne!(cycle, reused);
        assert_eq!(heap.get(cycle), Err(HeapError::InvalidHandle));
    }

    #[test]
    fn clone_preserves_internal_aliases_and_cycles_but_isolates_source() {
        let mut heap = Heap::default();
        let child = heap.allocate(Object::Array(vec![])).unwrap();
        *heap.get_mut(child).unwrap() = Object::Array(vec![child]);
        let pair = heap.allocate(Object::Tuple(vec![child, child])).unwrap();
        let copy = heap.deep_clone(pair).unwrap();
        let Object::Tuple(fields) = heap.get(copy).unwrap() else {
            panic!("tuple");
        };
        assert_eq!(fields[0], fields[1]);
        assert_ne!(fields[0], child);
        let Object::Array(back) = heap.get(fields[0]).unwrap() else {
            panic!("array");
        };
        assert_eq!(back[0], fields[0]);
        assert!(heap.structurally_equal(pair, copy).unwrap());
        assert_eq!(heap.collect([copy]).unwrap(), 2);
        assert_eq!(heap.live_objects(), 2);
    }

    #[test]
    fn equality_traverses_identical_handles_and_cycles_containing_nan() {
        let mut heap = Heap::default();
        let nan = heap
            .allocate(Object::Float {
                value: f64::NAN,
                bits: 64,
            })
            .unwrap();
        assert!(!heap.structurally_equal(nan, nan).unwrap());
        let cycle = heap.allocate(Object::Array(vec![])).unwrap();
        *heap.get_mut(cycle).unwrap() = Object::Array(vec![cycle, nan]);
        assert!(!heap.structurally_equal(cycle, cycle).unwrap());
        let copy = heap.deep_clone(cycle).unwrap();
        assert!(!heap.structurally_equal(cycle, copy).unwrap());
        *heap.get_mut(cycle).unwrap() = Object::Array(vec![cycle]);
        assert!(heap.structurally_equal(cycle, cycle).unwrap());
    }
    #[test]
    fn environment_free_functions_copy_but_retained_environments_are_not_ordinary_data() {
        let mut heap = Heap::default();
        let empty = heap.allocate(Object::Unit).unwrap();
        let function = heap
            .allocate(Object::Closure {
                function: 1,
                environment: empty,
            })
            .unwrap();
        let copy = heap.deep_clone(function).unwrap();
        let Object::Closure { environment, .. } = heap.get(copy).unwrap() else {
            panic!("function")
        };
        let copied_environment = *environment;
        assert_ne!(copied_environment, empty);
        heap.collect([copy]).unwrap();
        assert_eq!(heap.get(copied_environment).unwrap(), &Object::Unit);
        let captured = heap
            .allocate(Object::Record(
                [("value".into(), copied_environment)].into(),
            ))
            .unwrap();
        let function = heap
            .allocate(Object::Closure {
                function: 1,
                environment: captured,
            })
            .unwrap();
        assert_eq!(heap.deep_clone(function), Err(HeapError::NonClonable));
    }
}
