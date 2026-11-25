use std::ops::Deref;

use crate::{GcRuntime, Object, Value};

/// Immutable Ril string with cached UTF-8 scalar length and ASCII fast-path flag.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RilStr {
    text: String,
    scalar_len: usize,
    is_ascii: bool,
}

impl RilStr {
    pub fn new(text: String) -> Self {
        let is_ascii = text.is_ascii();
        let scalar_len = if is_ascii {
            text.len()
        } else {
            text.chars().count()
        };
        Self {
            text,
            scalar_len,
            is_ascii,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.text
    }

    pub const fn scalar_len(&self) -> usize {
        self.scalar_len
    }

    pub const fn is_ascii(&self) -> bool {
        self.is_ascii
    }

    pub fn scalar_at(&self, index: usize) -> Option<char> {
        if index >= self.scalar_len {
            return None;
        }
        if self.is_ascii {
            self.text.as_bytes().get(index).map(|&b| char::from(b))
        } else {
            self.text.chars().nth(index)
        }
    }

    pub fn slice_scalars(&self, start: usize, end: usize) -> Option<String> {
        if start > end || end > self.scalar_len {
            return None;
        }
        if self.is_ascii {
            self.text.get(start..end).map(str::to_owned)
        } else {
            Some(self.text.chars().skip(start).take(end - start).collect())
        }
    }
}

impl Deref for RilStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.text
    }
}

impl From<String> for RilStr {
    fn from(text: String) -> Self {
        Self::new(text)
    }
}

impl From<&str> for RilStr {
    fn from(text: &str) -> Self {
        Self::new(text.to_owned())
    }
}

const EMPTY_BUCKET: u32 = u32::MAX;

/// Insertion-ordered hash map (`IndexMap` layout) with O(1) lookup, O(1) insert,
/// O(1) dense positional iteration (`ril_rt_iter_at`), and bisimulation-invariant hashing.
#[derive(Clone, Debug, Default)]
pub struct RilMap {
    entries: Vec<(u64, Value, Value)>,
    table: Vec<u32>,
}

impl RilMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn entries(&self) -> &[(u64, Value, Value)] {
        &self.entries
    }

    pub fn get_entry(&self, index: usize) -> Option<(Value, Value)> {
        self.entries.get(index).map(|&(_, k, v)| (k, v))
    }

    pub fn value_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.entries.get_mut(index).map(|(_, _, v)| v)
    }

    /// Finds the dense entry index matching `hash` and `matches_key(stored_key)`.
    pub fn find_index(
        &self,
        hash: u64,
        mut matches_key: impl FnMut(Value) -> bool,
    ) -> Option<usize> {
        if self.entries.is_empty() {
            return None;
        }
        if self.table.is_empty() {
            return self
                .entries
                .iter()
                .position(|&(h, k, _)| h == hash && matches_key(k));
        }
        let mask = self.table.len() - 1;
        let mut slot = (hash as usize) & mask;
        loop {
            let bucket = *self.table.get(slot)?;
            if bucket == EMPTY_BUCKET {
                return None;
            }
            let idx = bucket as usize;
            if let Some(&(h, k, _)) = self.entries.get(idx)
                && h == hash
                && matches_key(k)
            {
                return Some(idx);
            }
            slot = (slot + 1) & mask;
        }
    }

    /// Iterates candidate dense entry indices that share `hash`.
    pub fn indices_with_hash<'a>(&'a self, hash: u64) -> HashCandidates<'a> {
        let mask = self.table.len().saturating_sub(1);
        HashCandidates {
            map: self,
            hash,
            slot: if self.table.is_empty() {
                0
            } else {
                (hash as usize) & mask
            },
            linear_pos: 0,
        }
    }

    /// Inserts a new `(hash, key, value)` entry assuming the caller verified `key` is absent.
    pub fn push_new(&mut self, hash: u64, key: Value, value: Value) {
        let idx = self.entries.len();
        self.entries.push((hash, key, value));
        if self.entries.len() > 8 || !self.table.is_empty() {
            if self.table.is_empty() || self.entries.len() * 4 >= self.table.len() * 3 {
                self.rehash();
            } else if let Ok(idx_u32) = u32::try_from(idx) {
                self.insert_bucket(hash, idx_u32);
            }
        }
    }

    /// Removes the entry at dense `index`, preserving insertion order of remaining entries.
    pub fn remove_at(&mut self, index: usize) -> Option<(Value, Value)> {
        if index >= self.entries.len() {
            return None;
        }
        let (_, key, value) = self.entries.remove(index);
        if !self.table.is_empty() {
            if self.entries.len() <= 8 {
                self.table.clear();
            } else {
                self.rehash();
            }
        }
        Some((key, value))
    }

    /// Removes all entries from the map.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.table.clear();
    }

    fn rehash(&mut self) {
        let cap = (self.entries.len() * 2).next_power_of_two().max(16);
        self.table.clear();
        self.table.resize(cap, EMPTY_BUCKET);
        let mask = cap - 1;
        for (idx, &(hash, _, _)) in self.entries.iter().enumerate() {
            let Ok(idx_u32) = u32::try_from(idx) else {
                break;
            };
            let mut slot = (hash as usize) & mask;
            while self.table.get(slot).copied() != Some(EMPTY_BUCKET) {
                slot = (slot + 1) & mask;
            }
            if let Some(cell) = self.table.get_mut(slot) {
                *cell = idx_u32;
            }
        }
    }

    fn insert_bucket(&mut self, hash: u64, idx_u32: u32) {
        let mask = self.table.len() - 1;
        let mut slot = (hash as usize) & mask;
        while self.table.get(slot).copied() != Some(EMPTY_BUCKET) {
            slot = (slot + 1) & mask;
        }
        if let Some(cell) = self.table.get_mut(slot) {
            *cell = idx_u32;
        }
    }
}

pub struct HashCandidates<'a> {
    map: &'a RilMap,
    hash: u64,
    slot: usize,
    linear_pos: usize,
}

impl Iterator for HashCandidates<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.map.table.is_empty() {
            while let Some(&(h, _, _)) = self.map.entries.get(self.linear_pos) {
                let idx = self.linear_pos;
                self.linear_pos += 1;
                if h == self.hash {
                    return Some(idx);
                }
            }
            return None;
        }
        let mask = self.map.table.len() - 1;
        loop {
            let bucket = *self.map.table.get(self.slot)?;
            if bucket == EMPTY_BUCKET {
                return None;
            }
            self.slot = (self.slot + 1) & mask;
            let idx = bucket as usize;
            if self
                .map
                .entries
                .get(idx)
                .is_some_and(|&(h, _, _)| h == self.hash)
            {
                return Some(idx);
            }
        }
    }
}

const fn mix64(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

fn hash_bytes(tag: u64, bytes: &[u8]) -> u64 {
    let mut h = mix64(tag ^ (bytes.len() as u64));
    for &b in bytes {
        h = mix64(h ^ u64::from(b));
    }
    h
}

const BISIM_MAX_DEPTH: usize = 8;
const DEPTH_SENTINEL: u64 = 0x9e37_79b9_7f4a_7c15;

impl GcRuntime {
    /// Bisimulation-invariant structural hash (`equal(a, b) => bisim_hash(a) == bisim_hash(b)`).
    ///
    /// Uses fixed-depth tree unfolding (`D = 8`) without pointer addresses or visited sets,
    /// so bisimilar cyclic graphs (e.g. a 1-node cycle and a 2-node cycle) always hash identically.
    pub fn bisim_hash(&self, value: Value) -> u64 {
        self.bisim_hash_depth(value, BISIM_MAX_DEPTH)
    }

    fn bisim_hash_depth(&self, value: Value, depth: usize) -> u64 {
        if depth == 0 {
            return DEPTH_SENTINEL;
        }
        if let Some(n) = value.small_int() {
            return mix64(0x1001_u64 ^ u64::from_ne_bytes(n.to_ne_bytes()));
        }
        match value {
            Value::UNIT => return mix64(0x1000),
            Value::FALSE => return mix64(0x1002),
            Value::TRUE => return mix64(0x1003),
            _ => {}
        }
        match self.object(value) {
            Some(Object::Int(big)) => {
                let (sign, digits) = big.to_bytes_le();
                let tag = match sign {
                    num_bigint::Sign::Minus => 0x1011,
                    num_bigint::Sign::NoSign => 0x1012,
                    num_bigint::Sign::Plus => 0x1013,
                };
                hash_bytes(tag, &digits)
            }
            Some(Object::F64(bits)) => {
                let f = f64::from_bits(*bits);
                let canonical = if f == 0.0 {
                    0.0_f64.to_bits()
                } else if f.is_nan() {
                    f64::NAN.to_bits()
                } else {
                    *bits
                };
                mix64(0x1020_u64 ^ canonical)
            }
            Some(Object::Str(s)) => hash_bytes(0x1030, s.as_bytes()),
            Some(Object::PanicInfo(s)) => hash_bytes(0x1031, s.as_bytes()),
            Some(Object::Bytes(b)) => hash_bytes(0x1040, b),
            Some(Object::Array(items)) => {
                let mut h = mix64(0x2001_u64 ^ (items.len() as u64));
                for &item in items {
                    h = mix64(h.wrapping_add(self.bisim_hash_depth(item, depth - 1)));
                }
                h
            }
            Some(Object::Tuple(items)) => {
                let mut h = mix64(0x2002_u64 ^ (items.len() as u64));
                for &item in items {
                    h = mix64(h.wrapping_add(self.bisim_hash_depth(item, depth - 1)));
                }
                h
            }
            Some(Object::Tag(name, items)) => {
                let mut h = hash_bytes(0x2003, name.as_bytes());
                h = mix64(h ^ (items.len() as u64));
                for &item in items {
                    h = mix64(h.wrapping_add(self.bisim_hash_depth(item, depth - 1)));
                }
                h
            }
            Some(Object::Record(fields)) => {
                let mut h = mix64(0x2004_u64 ^ (fields.len() as u64));
                for (name, &val) in fields {
                    let kh = hash_bytes(0x2005, name.as_bytes());
                    let vh = self.bisim_hash_depth(val, depth - 1);
                    h = mix64(h.wrapping_add(mix64(kh ^ vh)));
                }
                h
            }
            Some(Object::Map(map)) => {
                // Commutative combination over entries so map equality implies equal hash.
                let mut acc = 0_u64;
                for &(_, k, v) in map.entries() {
                    let kh = self.bisim_hash_depth(k, depth - 1);
                    let vh = self.bisim_hash_depth(v, depth - 1);
                    acc = acc.wrapping_add(mix64(kh ^ vh.rotate_left(17)));
                }
                mix64(0x2006_u64 ^ (map.len() as u64) ^ acc)
            }
            Some(Object::Set(set)) => {
                let mut acc = 0_u64;
                for &(_, k, _) in set.entries() {
                    let kh = self.bisim_hash_depth(k, depth - 1);
                    acc = acc.wrapping_add(mix64(kh ^ 0x517c_c1b7_2722_0a95));
                }
                mix64(0x2007_u64 ^ (set.len() as u64) ^ acc)
            }
            _ => mix64(0x3000),
        }
    }
}
