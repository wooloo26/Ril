use std::collections::{BTreeMap, BTreeSet};

use crate::{GcRuntime, Object, Value, text};

impl GcRuntime {
    pub fn equal(&self, a: Value, b: Value) -> Result<bool, &'static str> {
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
            if !seen.insert((a, b)) {
                continue;
            }
            if a.0 < 3 || b.0 < 3 {
                if a != b {
                    return Ok(false);
                }
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
                    for &(key, value) in a {
                        let mut found = false;
                        for &(other, candidate) in b {
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
                Object::Map(entries) => Object::Map(
                    entries
                        .into_iter()
                        .map(|(key, value)| Ok((copy(key)?, copy(value)?)))
                        .collect::<Result<_, _>>()?,
                ),
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
        if value.0 < 3 {
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
            Object::Array(_)
            | Object::Tuple(_)
            | Object::Tag(..)
            | Object::Record(_)
            | Object::Map(_) => {
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
        self.inspect_from(value, &mut BTreeSet::new(), 0)
    }

    fn inspect_from(&self, value: Value, active: &mut BTreeSet<Value>, depth: usize) -> String {
        if depth > 96 || !active.insert(value) {
            return "...".into();
        }
        let mut render = |v| self.inspect_from(v, active, depth + 1);
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
                Some(Object::Sender(_)) => "<Sender>".into(),
                Some(Object::Receiver(_)) => "<Receiver>".into(),
                Some(Object::Draft { .. }) => "<Draft>".into(),
                Some(Object::Bytes(bytes)) => text::inspect_bytes(bytes),
                Some(Object::Array(items)) => format!(
                    "[{}]",
                    items
                        .iter()
                        .copied()
                        .map(&mut render)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Tuple(items)) => format!(
                    "({})",
                    items
                        .iter()
                        .copied()
                        .map(&mut render)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Record(fields)) => format!(
                    ".{{ {} }}",
                    fields
                        .iter()
                        .map(|(k, v)| format!("{k}: {}", render(*v)))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Map(fields)) => format!(
                    "[{}]",
                    fields
                        .iter()
                        .map(|(k, v)| format!("{}: {}", render(*k), render(*v)))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Some(Object::Tag(tag, fields)) if fields.is_empty() => tag.clone(),
                Some(Object::Tag(tag, fields)) => format!(
                    "{tag}({})",
                    fields
                        .iter()
                        .copied()
                        .map(&mut render)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                _ => "<object>".into(),
            },
        };
        active.remove(&value);
        result
    }
}
