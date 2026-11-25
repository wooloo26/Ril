use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::ToPrimitive as _;

use crate::{
    draft::DraftNode,
    map::{RilMap, RilStr},
};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Value(pub u64);

impl Value {
    pub const UNIT: Self = Self(0);
    pub const FALSE: Self = Self(0b010);
    pub const TRUE: Self = Self(0b110);

    pub const fn boolean(value: bool) -> Self {
        if value { Self::TRUE } else { Self::FALSE }
    }

    pub fn as_bool(self) -> Option<bool> {
        match self {
            Self::TRUE => Some(true),
            Self::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    pub(crate) fn from_slot(index: usize, generation: u32) -> Self {
        let low = u32::try_from(index)
            .ok()
            .and_then(|i| i.checked_add(1))
            .and_then(|i| i.checked_shl(3))
            .unwrap_or_else(|| std::process::abort());
        Self((u64::from(generation) << 32) | u64::from(low))
    }

    #[inline]
    pub(crate) fn slot_parts(self) -> Option<(usize, u32)> {
        if self.is_immediate() {
            return None;
        }
        let low = (self.0 as u32) >> 3;
        let index = usize::try_from(low.checked_sub(1)?).ok()?;
        let generation = (self.0 >> 32) as u32;
        Some((index, generation))
    }
}

/// Intrusive Henderson stack-allocated GC root frame linked from `Runtime.gc.top_frame`.
///
/// Immediately followed in memory by `count` contiguous `Value` root slots.
#[repr(C)]
pub struct RootFrameHeader {
    pub prev: *mut RootFrameHeader,
    pub count: usize,
}

#[derive(Clone, Debug)]
pub enum Object {
    Int(BigInt),
    Scope(u64),
    Task {
        task: u64,
        scope: u64,
    },
    Sender(u64),
    ClosedSender,
    Receiver(u64),
    F64(u64),
    Str(RilStr),
    PanicInfo(String),
    Bytes(Vec<u8>),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Record(BTreeMap<String, Value>),
    Map(RilMap),
    Tag(String, Vec<Value>),
    Closure {
        function: *const u8,
        arity: u64,
        environment: Value,
        evidence: Value,
    },
    Evidence {
        parent: Value,
        operation: u64,
        handler: Value,
    },
    Draft {
        copy: Value,
    },
}

impl Object {
    pub(crate) fn visit_children(&self, mut visit: impl FnMut(Value)) {
        match self {
            Self::Array(values) | Self::Tuple(values) | Self::Tag(_, values) => {
                for &v in values {
                    visit(v);
                }
            }
            Self::Record(fields) => {
                for &v in fields.values() {
                    visit(v);
                }
            }
            Self::Map(map) => {
                for &(_, k, v) in map.entries() {
                    visit(k);
                    visit(v);
                }
            }
            Self::Closure {
                environment,
                evidence,
                ..
            } => {
                visit(*environment);
                visit(*evidence);
            }
            Self::Draft { copy } => visit(*copy),
            Self::Evidence {
                parent, handler, ..
            } => {
                visit(*parent);
                visit(*handler);
            }
            Self::Scope(_)
            | Self::Task { .. }
            | Self::Sender(_)
            | Self::ClosedSender
            | Self::Receiver(_)
            | Self::Int(_)
            | Self::F64(_)
            | Self::Str(_)
            | Self::PanicInfo(_)
            | Self::Bytes(_) => {}
        }
    }
}

struct SlotEntry {
    generation: u32,
    state: SlotState,
}

enum SlotState {
    Free { next: usize },
    Occupied { object: Object, marked: bool },
}

const FREE_END: usize = usize::MAX;

#[repr(C)]
pub struct GcRuntime {
    pub top_frame: *mut RootFrameHeader,
    slots: Vec<SlotEntry>,
    free_head: usize,
    live_count: usize,
    pub(crate) draft_nodes: BTreeMap<Value, DraftNode>,
    suspended_top_frames: BTreeMap<u64, *mut RootFrameHeader>,
    roots: BTreeMap<Value, usize>,
    #[cfg(not(miri))]
    active: u64,
    next_collection: usize,
    stress: bool,
}

impl Default for GcRuntime {
    fn default() -> Self {
        Self::new(std::env::var_os("RIL_GC_STRESS").is_some())
    }
}

impl GcRuntime {
    pub fn new(stress: bool) -> Self {
        Self {
            top_frame: std::ptr::null_mut(),
            slots: Vec::new(),
            free_head: FREE_END,
            live_count: 0,
            draft_nodes: BTreeMap::new(),
            suspended_top_frames: BTreeMap::new(),
            roots: BTreeMap::new(),
            #[cfg(not(miri))]
            active: 0,
            next_collection: 64,
            stress,
        }
    }

    #[cfg(not(miri))]
    pub(crate) fn switch_fiber(&mut self, fiber: u64) {
        if fiber != self.active {
            let next_top = self
                .suspended_top_frames
                .remove(&fiber)
                .unwrap_or(std::ptr::null_mut());
            let prev_top = std::mem::replace(&mut self.top_frame, next_top);
            if !prev_top.is_null() {
                self.suspended_top_frames.insert(self.active, prev_top);
            }
            self.active = fiber;
        }
    }

    #[cfg(not(miri))]
    pub(crate) fn clear_fiber_frames(&mut self, fiber: u64) {
        self.suspended_top_frames.remove(&fiber);
    }

    pub(crate) fn pin(&mut self, value: Value) {
        *self.roots.entry(value).or_default() += 1;
    }

    pub(crate) fn unpin(&mut self, value: Value) {
        if let Some(count) = self.roots.get_mut(&value) {
            *count -= 1;
            if *count == 0 {
                self.roots.remove(&value);
            }
        }
    }

    pub fn alloc(&mut self, object: Object) -> Value {
        // Normalize integers here so equality can compare inline values by word.
        if let Object::Int(number) = &object
            && let Some(value) = number.to_i64().and_then(Value::from_small_int)
        {
            return value;
        }
        if self.stress || self.live_count >= self.next_collection {
            let mut extra = Vec::new();
            object.visit_children(|child| extra.push(child));
            self.collect(extra);
        }
        self.alloc_rooted(object)
    }

    fn alloc_rooted(&mut self, object: Object) -> Value {
        self.live_count += 1;
        if self.free_head != FREE_END {
            let index = self.free_head;
            if let Some(entry) = self.slots.get_mut(index) {
                let next = match entry.state {
                    SlotState::Free { next } => next,
                    SlotState::Occupied { .. } => std::process::abort(),
                };
                self.free_head = next;
                entry.state = SlotState::Occupied {
                    object,
                    marked: false,
                };
                return Value::from_slot(index, entry.generation);
            }
        }
        let index = self.slots.len();
        self.slots.push(SlotEntry {
            generation: 0,
            state: SlotState::Occupied {
                object,
                marked: false,
            },
        });
        Value::from_slot(index, 0)
    }

    #[inline]
    pub fn object(&self, value: Value) -> Option<&Object> {
        let (index, generation) = value.slot_parts()?;
        match self.slots.get(index) {
            Some(SlotEntry {
                generation: slot_gen,
                state: SlotState::Occupied { object, .. },
            }) if *slot_gen == generation => Some(object),
            _ => None,
        }
    }

    #[inline]
    pub fn object_mut(&mut self, value: Value) -> Option<&mut Object> {
        let (index, generation) = value.slot_parts()?;
        match self.slots.get_mut(index) {
            Some(SlotEntry {
                generation: slot_gen,
                state: SlotState::Occupied { object, .. },
            }) if *slot_gen == generation => Some(object),
            _ => None,
        }
    }

    pub fn safepoint(&mut self) {
        if self.stress || self.live_count >= self.next_collection {
            self.collect(Vec::new());
        }
    }

    #[allow(
        unsafe_code,
        reason = "traverse intrusive stack-allocated RootFrameHeader chains published by generated code"
    )]
    fn push_stack_frames(head: *mut RootFrameHeader, pending: &mut Vec<Value>) {
        let mut cursor = head;
        while !cursor.is_null() {
            // SAFETY: every linked RootFrameHeader lives on a live active or suspended
            // fiber stack frame and is followed by `count` initialized `Value` words.
            // Use raw field reads without creating a `&RootFrameHeader` so provenance
            // over the trailing `[Value; count]` slots is preserved under Stacked Borrows.
            let (prev, count, slots) = unsafe {
                let prev = std::ptr::read(&raw const (*cursor).prev);
                let count = std::ptr::read(&raw const (*cursor).count);
                let slots_ptr = cursor.add(1).cast::<Value>();
                (prev, count, slots_ptr)
            };
            for i in 0..count {
                // SAFETY: generated prologues zero-initialize all `count` slots before linking.
                let slot = unsafe { std::ptr::read(slots.add(i)) };
                pending.push(slot);
            }
            cursor = prev;
        }
    }

    pub fn collect(&mut self, additional: Vec<Value>) {
        let mut pending: Vec<Value> = self.roots.keys().copied().chain(additional).collect();
        Self::push_stack_frames(self.top_frame, &mut pending);
        for &suspended in self.suspended_top_frames.values() {
            Self::push_stack_frames(suspended, &mut pending);
        }

        while let Some(value) = pending.pop() {
            let Some((index, generation)) = value.slot_parts() else {
                continue;
            };
            let Some(SlotEntry {
                generation: slot_gen,
                state: SlotState::Occupied { object, marked },
            }) = self.slots.get_mut(index)
            else {
                continue;
            };
            if *slot_gen == generation && !*marked {
                *marked = true;
                object.visit_children(|child| {
                    if !child.is_immediate() {
                        pending.push(child);
                    }
                });
            }
        }

        let mut surviving = 0usize;
        for index in 0..self.slots.len() {
            let Some(entry) = self.slots.get_mut(index) else {
                continue;
            };
            match &mut entry.state {
                SlotState::Occupied { marked, .. } if *marked => {
                    *marked = false;
                    surviving += 1;
                }
                SlotState::Occupied { .. } => {
                    entry.generation = entry.generation.wrapping_add(1);
                    entry.state = SlotState::Free {
                        next: self.free_head,
                    };
                    self.free_head = index;
                }
                SlotState::Free { .. } => {}
            }
        }
        self.live_count = surviving;
        if !self.draft_nodes.is_empty() {
            let slots = &self.slots;
            let is_live = |v: Value| {
                v.slot_parts()
                    .and_then(|(idx, generation)| {
                        slots.get(idx).map(|entry| {
                            entry.generation == generation
                                && matches!(entry.state, SlotState::Occupied { .. })
                        })
                    })
                    .unwrap_or(false)
            };
            self.draft_nodes
                .retain(|&value, node| is_live(value) && is_live(node.draft));
        }
        self.next_collection = self.live_count.saturating_mul(2).max(64);
    }

    pub fn live_objects(&self) -> usize {
        self.live_count
    }
}
