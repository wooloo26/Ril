use std::collections::{BTreeMap, BTreeSet};

use num_traits::ToPrimitive;

use crate::{GcRuntime, Object, Value, text};

impl GcRuntime {
    pub fn equal(&self, a: Value, b: Value) -> Result<bool, &'static str> {
        if a.is_immediate() || b.is_immediate() {
            return Ok(a == b);
        }
        self.equal_from(a, b, &mut BTreeSet::new())
    }

    fn equal_from(
        &self,
        a: Value,
        b: Value,
        seen: &mut BTreeSet<(Value, Value)>,
    ) -> Result<bool, &'static str> {
        let mut pending = vec![(a, b)];
        while let Some((a, b)) = pending.pop() {
            if a.is_immediate() || b.is_immediate() {
                if a != b {
                    return Ok(false);
                }
                continue;
            }
            if !seen.insert((a, b)) {
                continue;
            }
            match (self.object(a), self.object(b)) {
                (Some(Object::Int(a)), Some(Object::Int(b))) if a == b => {}
                (Some(Object::F64(a)), Some(Object::F64(b)))
                    if f64::from_bits(*a) == f64::from_bits(*b) => {}
                (Some(Object::Str(a)), Some(Object::Str(b))) if a == b => {}
                (Some(Object::PanicInfo(a)), Some(Object::PanicInfo(b))) if a == b => {}
                (Some(Object::Bytes(a)), Some(Object::Bytes(b))) if a == b => {}
                (Some(Object::Array(a)), Some(Object::Array(b)))
                | (Some(Object::Tuple(a)), Some(Object::Tuple(b)))
                    if a.len() == b.len() =>
                {
                    pending.extend(a.iter().copied().zip(b.iter().copied()));
                }
                (Some(Object::Tag(a, aa)), Some(Object::Tag(b, bb)))
                    if a == b && aa.len() == bb.len() =>
                {
                    pending.extend(aa.iter().copied().zip(bb.iter().copied()));
                }
                (Some(Object::Record(a)), Some(Object::Record(b))) if a.len() == b.len() => {
                    for ((k, x), (other, y)) in a.iter().zip(b) {
                        if k != other {
                            return Ok(false);
                        }
                        pending.push((*x, *y));
                    }
                }
                (Some(Object::Map(a)), Some(Object::Map(b))) if a.len() == b.len() => {
                    for &(hash, key, value) in a.entries() {
                        let mut found = false;
                        for cand_idx in b.indices_with_hash(hash) {
                            let Some((other, candidate)) = b.get_entry(cand_idx) else {
                                continue;
                            };
                            let mut trial = seen.clone();
                            if self.equal_from(key, other, &mut trial)?
                                && self.equal_from(value, candidate, &mut trial)?
                            {
                                *seen = trial;
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            return Ok(false);
                        }
                    }
                }
                (Some(Object::Set(a)), Some(Object::Set(b))) if a.len() == b.len() => {
                    for &(hash, key, _) in a.entries() {
                        let mut found = false;
                        for cand_idx in b.indices_with_hash(hash) {
                            let Some((other, _)) = b.get_entry(cand_idx) else {
                                continue;
                            };
                            let mut trial = seen.clone();
                            if self.equal_from(key, other, &mut trial)? {
                                *seen = trial;
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            return Ok(false);
                        }
                    }
                }
                (Some(Object::Closure { .. } | Object::Draft { .. }), _)
                | (_, Some(Object::Closure { .. } | Object::Draft { .. })) => {
                    return Err("object does not support equality");
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    pub fn clone_graph(&mut self, root: Value) -> Result<Value, &'static str> {
        if matches!(self.object(root), Some(Object::Closure { .. })) {
            return Err("object cannot be cloned");
        }
        self.pin(root);
        let mut copied = BTreeMap::new();
        let result = self.copy_graph(root, &mut copied);
        for value in copied.into_values() {
            self.unpin(value);
        }
        self.unpin(root);
        result
    }

    fn copy_graph(
        &mut self,
        root: Value,
        copied: &mut BTreeMap<Value, Value>,
    ) -> Result<Value, &'static str> {
        let mut pending = Vec::new();
        let root = self.queue_copy(root, copied, &mut pending)?;
        while let Some((source, target)) = pending.pop() {
            let original = self
                .object(source)
                .cloned()
                .ok_or("invalid object identity")?;
            let mut copy = |value| self.queue_copy(value, copied, &mut pending);
            let result = match original {
                Object::Array(values) => {
                    Object::Array(values.into_iter().map(copy).collect::<Result<_, _>>()?)
                }
                Object::Tuple(values) => {
                    Object::Tuple(values.into_iter().map(copy).collect::<Result<_, _>>()?)
                }
                Object::Tag(tag, values) => {
                    Object::Tag(tag, values.into_iter().map(copy).collect::<Result<_, _>>()?)
                }
                Object::Record(fields) => Object::Record(
                    fields
                        .into_iter()
                        .map(|(key, value)| Ok((key, copy(value)?)))
                        .collect::<Result<_, _>>()?,
                ),
                Object::Map(map) => {
                    let mut cloned = crate::RilMap::new();
                    for &(hash, key, value) in map.entries() {
                        let k = copy(key)?;
                        let v = copy(value)?;
                        cloned.push_new(hash, k, v);
                    }
                    Object::Map(cloned)
                }
                Object::Set(set) => {
                    let mut cloned = crate::RilMap::new();
                    for &(hash, key, _) in set.entries() {
                        let k = copy(key)?;
                        cloned.push_new(hash, k, Value::UNIT);
                    }
                    Object::Set(cloned)
                }
                _ => return Err("object cannot be cloned"),
            };
            *self.object_mut(target).ok_or("missing pinned graph copy")? = result;
        }
        Ok(root)
    }

    fn queue_copy(
        &mut self,
        value: Value,
        copied: &mut BTreeMap<Value, Value>,
        pending: &mut Vec<(Value, Value)>,
    ) -> Result<Value, &'static str> {
        if value.is_immediate() {
            return Ok(value);
        }
        if let Some(&copy) = copied.get(&value) {
            return Ok(copy);
        }
        match self.object(value).ok_or("invalid object identity")? {
            Object::Int(_)
            | Object::F64(_)
            | Object::Str(_)
            | Object::Bytes(_)
            | Object::PanicInfo(_) => Ok(value),
            // A contained callable is a value with its original immutable
            // environment and lexical dispatch evidence. Sema checks that
            // it retains no live capture or stateful handler.
            Object::Closure { .. } => Ok(value),
            Object::Array(_)
            | Object::Tuple(_)
            | Object::Tag(..)
            | Object::Record(_)
            | Object::Map(_)
            | Object::Set(_) => {
                // Pin unfinished copies until every incoming edge has been rebuilt.
                let copy = self.alloc(Object::Array(Vec::new()));
                self.pin(copy);
                copied.insert(value, copy);
                pending.push((value, copy));
                Ok(copy)
            }
            _ => Err("object cannot be cloned"),
        }
    }

    pub fn inspect(&self, value: Value) -> String {
        self.inspect_from(value, &[], Value::UNIT, &mut BTreeSet::new(), 0)
    }

    pub(crate) fn inspect_typed(&self, value: Value, plan: Value) -> String {
        let Some(Object::Array(nodes)) = self.object(plan) else {
            return self.inspect(value);
        };
        let root = nodes.get(1).copied().unwrap_or(Value::UNIT);
        self.inspect_from(value, nodes, root, &mut BTreeSet::new(), 0)
    }

    fn inspect_from(
        &self,
        value: Value,
        nodes: &[Value],
        descriptor: Value,
        active: &mut BTreeSet<Value>,
        depth: usize,
    ) -> String {
        let descriptor_handle = descriptor;
        let descriptor = self.object(descriptor_handle);
        if let Some(Object::Str(text)) = descriptor {
            return text.as_str().to_owned();
        }
        if depth > 96 {
            return "...".into();
        }
        if let Some(integer) = value.small_int() {
            return integer.to_string();
        }
        if !active.insert(value) {
            return "...".into();
        }
        let mut render = |value, index: Option<Value>| {
            let next = index
                .and_then(|index| self.integer(index))
                .and_then(|index| index.to_usize())
                .and_then(|index| nodes.get(index).copied())
                .unwrap_or(Value::UNIT);
            self.inspect_from(value, nodes, next, active, depth + 1)
        };
        let index_at = |index| match descriptor {
            Some(Object::Tuple(ids)) => ids.get(index).copied(),
            _ => None,
        };
        let field = |name: &str| match descriptor {
            Some(Object::Record(fields)) => fields.get(name).copied(),
            _ => None,
        };
        let result = match value {
            Value::UNIT => "()".into(),
            Value::TRUE => "true".into(),
            Value::FALSE => "false".into(),
            _ => match self.object(value) {
                Some(Object::Int(i)) => i.to_string(),
                Some(Object::F64(f)) => format!("{:?}", f64::from_bits(*f)),
                Some(Object::Str(value)) => text::inspect_string(value),
                Some(Object::PanicInfo(_)) => "<PanicInfo>".into(),
                Some(Object::Closure { .. }) => "<fn>".into(),
                Some(Object::Task { .. }) => "<Task>".into(),
                Some(Object::Scope(_)) => "<Scope>".into(),
                Some(Object::Sender(_) | Object::ClosedSender) => "<Sender>".into(),
                Some(Object::Receiver(_)) => "<Receiver>".into(),
                Some(Object::Draft { .. }) => "<Draft>".into(),
                Some(Object::Bytes(bytes)) => text::inspect_bytes(bytes),
                Some(Object::Array(items)) => {
                    let index = self.integer(descriptor_handle).map(|_| descriptor_handle);
                    format!(
                        "[{}]",
                        items
                            .iter()
                            .map(|&value| render(value, index))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
                Some(Object::Tuple(items)) => format!(
                    "({})",
                    items
                        .iter()
                        .enumerate()
                        .map(|(index, &value)| render(value, index_at(index)))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Record(fields)) => format!(
                    ".{{ {} }}",
                    fields
                        .iter()
                        .map(|(name, &value)| format!("{name}: {}", render(value, field(name))))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Map(map)) => format!(
                    "[{}]",
                    map.entries()
                        .iter()
                        .map(|&(_, key, value)| format!(
                            "{}: {}",
                            render(key, index_at(0)),
                            render(value, index_at(1))
                        ))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Set(set)) => {
                    let index = self.integer(descriptor_handle).map(|_| descriptor_handle);
                    format!(
                        "Set([{}])",
                        set.entries()
                            .iter()
                            .map(|&(_, key, _)| render(key, index))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
                Some(Object::Tag(tag, fields)) if fields.is_empty() => tag.clone(),
                Some(Object::Tag(tag, fields)) => {
                    let ids = match field(tag).and_then(|child| self.object(child)) {
                        Some(Object::Tuple(ids)) => ids.as_slice(),
                        _ => &[],
                    };
                    format!(
                        "{tag}({})",
                        fields
                            .iter()
                            .enumerate()
                            .map(|(index, &value)| render(value, ids.get(index).copied()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
                _ => "<object>".into(),
            },
        };
        active.remove(&value);
        result
    }
}
