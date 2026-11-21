use std::collections::{BTreeMap, BTreeSet};

use crate::{GcRuntime, Object, Value};

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
        if !seen.insert((a, b)) {
            return Ok(true);
        }
        if a.0 < 3 || b.0 < 3 {
            return Ok(a == b);
        }
        let equal = |a, b, seen: &mut _| self.equal_from(a, b, seen);
        Ok(match (self.object(a), self.object(b)) {
            (Some(Object::Int(a)), Some(Object::Int(b))) => a == b,
            (Some(Object::F64(a)), Some(Object::F64(b))) => {
                f64::from_bits(*a) == f64::from_bits(*b)
            }
            (Some(Object::Str(a)), Some(Object::Str(b))) => a == b,
            (Some(Object::Bytes(a)), Some(Object::Bytes(b))) => a == b,
            (Some(Object::Array(a)), Some(Object::Array(b)))
            | (Some(Object::Tuple(a)), Some(Object::Tuple(b))) => self.equal_parts(a, b, seen)?,
            (Some(Object::Tag(a, aa)), Some(Object::Tag(b, bb))) => {
                a == b && self.equal_parts(aa, bb, seen)?
            }
            (Some(Object::Record(a)), Some(Object::Record(b))) if a.len() == b.len() => {
                for ((k, x), (other, y)) in a.iter().zip(b) {
                    if k != other || !equal(*x, *y, seen)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Some(Object::Map(a)), Some(Object::Map(b))) if a.len() == b.len() => {
                for &(key, value) in a {
                    let mut found = false;
                    for &(other, candidate) in b {
                        let mut trial = seen.clone();
                        if equal(key, other, &mut trial)? && equal(value, candidate, &mut trial)? {
                            *seen = trial;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Ok(false);
                    }
                }
                true
            }
            (Some(Object::Closure { .. } | Object::Draft { .. }), _)
            | (_, Some(Object::Closure { .. } | Object::Draft { .. })) => {
                return Err("object does not support equality");
            }
            _ => false,
        })
    }

    fn equal_parts(
        &self,
        a: &[Value],
        b: &[Value],
        seen: &mut BTreeSet<(Value, Value)>,
    ) -> Result<bool, &'static str> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (&a, &b) in a.iter().zip(b) {
            if !self.equal_from(a, b, seen)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn clone_graph(&mut self, root: Value) -> Result<Value, &'static str> {
        self.clone_from(root, &mut BTreeMap::new())
    }

    fn clone_from(
        &mut self,
        from: Value,
        copied: &mut BTreeMap<Value, Value>,
    ) -> Result<Value, &'static str> {
        if from.0 < 3 {
            return Ok(from);
        }
        if let Some(copy) = copied.get(&from) {
            return Ok(*copy);
        }
        let original = self
            .object(from)
            .cloned()
            .ok_or("invalid object identity")?;
        if matches!(
            original,
            Object::Int(_) | Object::F64(_) | Object::Str(_) | Object::Bytes(_)
        ) {
            return Ok(from);
        }
        let placeholder = self.alloc_rooted(Object::Array(Vec::new()));
        copied.insert(from, placeholder);
        let mut item = |id| self.clone_from(id, copied);
        let result = match original {
            Object::Array(values) => {
                Object::Array(values.into_iter().map(item).collect::<Result<_, _>>()?)
            }
            Object::Tuple(values) => {
                Object::Tuple(values.into_iter().map(item).collect::<Result<_, _>>()?)
            }
            Object::Tag(tag, values) => {
                Object::Tag(tag, values.into_iter().map(item).collect::<Result<_, _>>()?)
            }
            Object::Record(fields) => Object::Record(
                fields
                    .into_iter()
                    .map(|(key, value)| Ok((key, item(value)?)))
                    .collect::<Result<_, _>>()?,
            ),
            Object::Map(entries) => Object::Map(
                entries
                    .into_iter()
                    .map(|(key, value)| Ok((item(key)?, item(value)?)))
                    .collect::<Result<_, _>>()?,
            ),
            _ => return Err("object cannot be cloned"),
        };
        if let Some(target) = self.object_mut(placeholder) {
            *target = result;
        }
        Ok(placeholder)
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
                Some(Object::F64(f)) => f64::from_bits(*f).to_string(),
                Some(Object::Str(text)) => format!("{text:?}"),
                Some(Object::Bytes(bytes)) => format!("bytes{bytes:?}"),
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
