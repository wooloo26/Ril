use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::ToPrimitive as _;

use crate::draft::DraftNode;

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
}

/// Intrusive Henderson stack-allocated GC root frame linked from `Runtime.gc.top_frame`.
///
/// Immediately followed in memory by `count` contiguous `Value` root slots.
#[repr(C)]
pub struct RootFrameHeader {
    pub prev: *mut RootFrameHeader,
    pub count: usize,
}

/// Describes the managed words in a native object with up to 64 data words.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct TypeDesc {
    pub reference_mask: u64,
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
    Receiver(u64),
    F64(u64),
    Str(String),
    PanicInfo(String),
    Bytes(Vec<u8>),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Record(BTreeMap<String, Value>),
    Map(Vec<(Value, Value)>),
    Tag(String, Vec<Value>),
    Closure {
        function: u64,
        arity: u64,
        environment: Value,
        evidence: Value,
    },
    Evidence {
        parent: Value,
        operation: String,
        handler: Value,
    },
    Draft {
        copy: Value,
    },
    Words {
        layout: TypeDesc,
        words: Vec<Value>,
    },
}

impl Object {
    pub(crate) fn children(&self) -> Vec<Value> {
        match self {
            Self::Array(values) | Self::Tuple(values) | Self::Tag(_, values) => values.clone(),
            Self::Record(fields) => fields.values().copied().collect(),
            Self::Map(entries) => entries.iter().flat_map(|&(k, v)| [k, v]).collect(),
            Self::Closure {
                environment,
                evidence,
                ..
            } => vec![*environment, *evidence],
            Self::Draft { copy } => vec![*copy],
            Self::Evidence {
                parent, handler, ..
            } => vec![*parent, *handler],
            Self::Words { layout, words } => words
                .iter()
                .enumerate()
                .take(64)
                .filter(|(i, _)| layout.reference_mask & (1_u64 << i) != 0)
                .map(|(_, &word)| word)
                .collect(),
            Self::Scope(_)
            | Self::Task { .. }
            | Self::Sender(_)
            | Self::Receiver(_)
            | Self::Int(_)
            | Self::F64(_)
            | Self::Str(_)
            | Self::PanicInfo(_)
            | Self::Bytes(_) => Vec::new(),
        }
    }
}

#[repr(C)]
pub struct GcRuntime {
    pub top_frame: *mut RootFrameHeader,
    objects: BTreeMap<Value, Object>,
    pub(crate) draft_nodes: BTreeMap<Value, DraftNode>,
    frames: Vec<Vec<Value>>,
    suspended_frames: BTreeMap<u64, Vec<Vec<Value>>>,
    suspended_top_frames: BTreeMap<u64, *mut RootFrameHeader>,
    roots: BTreeMap<Value, usize>,
    #[cfg(not(miri))]
    active: u64,
    next: u64,
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
            objects: BTreeMap::new(),
            draft_nodes: BTreeMap::new(),
            frames: Vec::new(),
            suspended_frames: BTreeMap::new(),
            suspended_top_frames: BTreeMap::new(),
            roots: BTreeMap::new(),
            #[cfg(not(miri))]
            active: 0,
            next: 8,
            next_collection: 64,
            stress,
        }
    }

    #[cfg(not(miri))]
    pub(crate) fn switch_fiber(&mut self, fiber: u64) {
        if fiber != self.active {
            let frames = self.suspended_frames.remove(&fiber).unwrap_or_default();
            let suspended = std::mem::replace(&mut self.frames, frames);
            if !suspended.is_empty() {
                self.suspended_frames.insert(self.active, suspended);
            }
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

    pub fn push_frame(&mut self, slots: usize) {
        self.frames.push(vec![Value::UNIT; slots]);
    }

    pub fn set_root(&mut self, slot: usize, value: Value) -> bool {
        if let Some(root) = self.frames.last_mut().and_then(|frame| frame.get_mut(slot)) {
            *root = value;
            true
        } else {
            false
        }
    }

    pub fn pop_frame(&mut self) {
        self.frames.pop();
    }

    pub fn alloc(&mut self, object: Object) -> Value {
        // Normalize integers here so equality can compare inline values by word.
        if let Object::Int(number) = &object
            && let Some(value) = number.to_i64().and_then(Value::from_small_int)
        {
            return value;
        }
        if self.stress || self.objects.len() >= self.next_collection {
            self.collect(object.children());
        }
        self.alloc_rooted(object)
    }

    fn alloc_rooted(&mut self, object: Object) -> Value {
        let value = Value(self.next);
        self.next = self
            .next
            .checked_add(8)
            .unwrap_or_else(|| std::process::abort());
        self.objects.insert(value, object);
        value
    }

    pub fn object(&self, value: Value) -> Option<&Object> {
        if value.is_immediate() {
            return None;
        }
        self.objects.get(&value)
    }

    pub fn object_mut(&mut self, value: Value) -> Option<&mut Object> {
        self.objects.get_mut(&value)
    }

    pub fn safepoint(&mut self) {
        if self.stress || self.objects.len() >= self.next_collection {
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
        let mut visited = BTreeSet::new();
        let mut pending: Vec<_> = self
            .frames
            .iter()
            .flatten()
            .chain(self.suspended_frames.values().flatten().flatten())
            .copied()
            .chain(self.roots.keys().copied())
            .chain(additional)
            .collect();
        Self::push_stack_frames(self.top_frame, &mut pending);
        for &suspended in self.suspended_top_frames.values() {
            Self::push_stack_frames(suspended, &mut pending);
        }
        while let Some(value) = pending.pop() {
            if !value.is_immediate()
                && let Some(object) = self.objects.get(&value)
                && visited.insert(value)
            {
                pending.extend(object.children());
            }
        }
        self.objects.retain(|value, _| visited.contains(value));
        self.draft_nodes
            .retain(|value, node| visited.contains(value) && visited.contains(&node.draft));
        self.next_collection = self.objects.len().saturating_mul(2).max(64);
    }

    pub fn live_objects(&self) -> usize {
        self.objects.len()
    }
}
