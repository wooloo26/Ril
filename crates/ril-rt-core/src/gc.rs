use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Value(pub u64);

impl Value {
    pub const UNIT: Self = Self(0);
    pub const FALSE: Self = Self(1);
    pub const TRUE: Self = Self(2);

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
            | Self::Bytes(_) => Vec::new(),
        }
    }
}

pub struct GcRuntime {
    objects: BTreeMap<Value, Object>,
    frames: Vec<Vec<Value>>,
    suspended_frames: BTreeMap<u64, Vec<Vec<Value>>>,
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
            objects: BTreeMap::new(),
            frames: Vec::new(),
            suspended_frames: BTreeMap::new(),
            roots: BTreeMap::new(),
            #[cfg(not(miri))]
            active: 0,
            next: 3,
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
            self.active = fiber;
        }
    }

    #[cfg(not(miri))]
    pub(crate) fn pin(&mut self, value: Value) {
        *self.roots.entry(value).or_default() += 1;
    }

    #[cfg(not(miri))]
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
        if self.stress || self.objects.len() >= self.next_collection {
            self.collect(object.children());
        }
        self.alloc_rooted(object)
    }

    pub(crate) fn alloc_rooted(&mut self, object: Object) -> Value {
        let value = Value(self.next);
        self.next = self
            .next
            .checked_add(1)
            .unwrap_or_else(|| std::process::abort());
        self.objects.insert(value, object);
        value
    }

    pub fn object(&self, value: Value) -> Option<&Object> {
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
        while let Some(value) = pending.pop() {
            if let Some(object) = self.objects.get(&value)
                && visited.insert(value)
            {
                pending.extend(object.children());
            }
        }
        self.objects.retain(|value, _| visited.contains(value));
        self.next_collection = self.objects.len().saturating_mul(2).max(64);
    }

    pub fn live_objects(&self) -> usize {
        self.objects.len()
    }
}
