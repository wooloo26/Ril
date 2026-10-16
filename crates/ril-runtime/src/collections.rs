//! Collection contracts over insertion-ordered hash storage.
use crate::{
    heap::{Handle, Object},
    map::{Key, OrderedMap},
    value::{Result, Runtime, RuntimeError},
};
impl Runtime {
    pub fn key(&self, mut value: Handle) -> Result<Key> {
        let mut wrappers = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        while let Object::Nominal { tag, payload } = self.heap.get(value)? {
            if !seen.insert(value) {
                return Err(RuntimeError::internal("cyclic nominal map key"));
            }
            wrappers.push(tag.clone());
            value = *payload;
        }
        let key = match self.heap.get(value)? {
            Object::Unit => Key::Unit,
            Object::Bool(value) => Key::Bool(*value),
            Object::Integer {
                value,
                bits,
                signed,
            } => Key::Integer(*value, *bits, *signed),
            Object::BigInteger(value) => Key::BigInteger(value.clone()),
            Object::String(value) => Key::String(value.clone()),
            Object::Bytes(value) => Key::Bytes(value.clone()),
            Object::NativeString(value) => Key::NativeString(value.clone()),
            Object::Path(value) => Key::Path(value.clone()),
            _ => {
                return Err(RuntimeError::internal(
                    "inadmissible map key reached native runtime",
                ));
            }
        };
        Ok(if wrappers.is_empty() {
            key
        } else {
            Key::Wrapper(wrappers, Box::new(key))
        })
    }
    pub fn map_set(&mut self, items: Handle, key: Handle, value: Handle) -> Result<Option<Handle>> {
        let identity = self.key(key)?;
        self.heap.get(value)?;
        match self.heap.get_mut(items)? {
            Object::Map(items) => Ok(items.set(identity, key, value)),
            _ => Err(RuntimeError::internal("expected map")),
        }
    }
    pub(crate) fn collection_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index: usize| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing collection argument"))
        };
        match name {
            "Map::from" => {
                let entries = self.sequence(arg(0)?)?;
                let result = self.allocate(Object::Map(Default::default()))?;
                for pair in entries {
                    let pair = self.sequence(pair)?;
                    if pair.len() != 2 {
                        return Err(RuntimeError::internal("map entry is not a pair"));
                    }
                    self.map_set(result, pair[0], pair[1])?;
                }
                Ok(result)
            }
            "Map::set" => {
                self.map_set(arg(0)?, arg(1)?, arg(2)?)?;
                self.unit()
            }
            "Map::get" | "Map::contains" | "Map::remove" => {
                let key = self.key(arg(1)?)?;
                let value = if name == "Map::remove" {
                    match self.heap.get_mut(arg(0)?)? {
                        Object::Map(items) => items.remove(&key),
                        _ => return Err(RuntimeError::internal("expected map")),
                    }
                } else {
                    match self.heap.get(arg(0)?)? {
                        Object::Map(items) => items.get(&key),
                        _ => return Err(RuntimeError::internal("expected map")),
                    }
                };
                if name == "Map::contains" {
                    self.boolean(value.is_some())
                } else {
                    self.variant(
                        if value.is_some() { "Some" } else { "None" },
                        value.into_iter().collect(),
                    )
                }
            }
            "Map::keys" | "Map::values" | "Map::entries" => {
                let entries = match self.heap.get(arg(0)?)? {
                    Object::Map(items) => items
                        .iter()
                        .map(|(key, value)| (*key, *value))
                        .collect::<Vec<_>>(),
                    _ => return Err(RuntimeError::internal("expected map")),
                };
                let mut values = Vec::new();
                for (key, value) in entries {
                    values.push(match name {
                        "Map::keys" => key,
                        "Map::values" => value,
                        _ => self.allocate(Object::Tuple(vec![key, value]))?,
                    });
                }
                self.allocate(Object::Array(values))
            }
            "Set::from" | "Set::of" => {
                let values = self.sequence(arg(0)?)?;
                let mut set = OrderedMap::default();
                for value in values {
                    set.set(self.key(value)?, value, value);
                }
                self.allocate(Object::Set(set))
            }
            "Set::contains" | "Set::insert" | "Set::remove" => {
                let original = arg(1)?;
                let key = self.key(original)?;
                let result = if name == "Set::contains" {
                    match self.heap.get(arg(0)?)? {
                        Object::Set(items) => items.contains(&key),
                        _ => return Err(RuntimeError::internal("expected set")),
                    }
                } else {
                    match self.heap.get_mut(arg(0)?)? {
                        Object::Set(items) => {
                            if name == "Set::insert" {
                                items.set(key, original, original).is_none()
                            } else {
                                items.remove(&key).is_some()
                            }
                        }
                        _ => return Err(RuntimeError::internal("expected set")),
                    }
                };
                self.boolean(result)
            }
            "Set::values" => {
                let values = match self.heap.get(arg(0)?)? {
                    Object::Set(items) => items.iter().map(|(key, _)| *key).collect(),
                    _ => return Err(RuntimeError::internal("expected set")),
                };
                self.allocate(Object::Array(values))
            }
            "Set::union" | "Set::intersect" | "Set::diff" => {
                let left = match self.heap.get(arg(0)?)? {
                    Object::Set(items) => items.clone(),
                    _ => return Err(RuntimeError::internal("expected set")),
                };
                let right = match self.heap.get(arg(1)?)? {
                    Object::Set(items) => items.clone(),
                    _ => return Err(RuntimeError::internal("expected set")),
                };
                let mut result = OrderedMap::default();
                for (key, original, value) in left.keyed() {
                    if name == "Set::union" || right.contains(key) == (name == "Set::intersect") {
                        result.set(key.clone(), original, value);
                    }
                }
                if name == "Set::union" {
                    for (key, original, value) in right.keyed() {
                        if !result.contains(key) {
                            result.set(key.clone(), original, value);
                        }
                    }
                }
                self.allocate(Object::Set(result))
            }
            _ => Err(RuntimeError::internal("unimplemented collection operation")),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn traversal_preserves_insertion_order_and_reads_replacements_when_visited() {
        let mut rt = Runtime::default();
        let map = rt.allocate(Object::Map(Default::default())).unwrap();
        let first = rt.string("b".into()).unwrap();
        let second = rt.string("a".into()).unwrap();
        let old = rt.int(1).unwrap();
        rt.map_set(map, first, old).unwrap();
        rt.map_set(map, second, old).unwrap();
        let cursor = rt.iterator(map).unwrap();
        rt.root(0, cursor).unwrap();
        rt.statement_end();
        rt.collect().unwrap();
        let pair = rt.iterator_item(cursor, 0).unwrap();
        assert_eq!(rt.sequence(pair).unwrap(), [first, old]);
        let replacement = rt.int(42).unwrap();
        rt.map_set(map, second, replacement).unwrap();
        let pair = rt.iterator_item(cursor, 1).unwrap();
        assert_eq!(rt.sequence(pair).unwrap(), [second, replacement]);
    }
    #[test]
    fn map_membership_equality_ignores_insertion_order_and_clone_preserves_cycles() {
        let mut runtime = Runtime::default();
        let a = runtime.string("a".into()).unwrap();
        let b = runtime.string("b".into()).unwrap();
        let first = runtime.allocate(Object::Map(Default::default())).unwrap();
        let second = runtime.allocate(Object::Map(Default::default())).unwrap();
        let one = runtime.int(1).unwrap();
        let two = runtime.int(2).unwrap();
        runtime.map_set(first, a, one).unwrap();
        runtime.map_set(first, b, two).unwrap();
        runtime.map_set(second, b, two).unwrap();
        runtime.map_set(second, a, one).unwrap();
        assert!(runtime.heap.structurally_equal(first, second).unwrap());
        runtime.map_set(first, a, first).unwrap();
        let cloned = runtime.copy(first).unwrap();
        assert!(runtime.heap.structurally_equal(first, cloned).unwrap());
        let key = runtime.key(a).unwrap();
        let Object::Map(items) = runtime.heap.get(cloned).unwrap() else {
            panic!("map");
        };
        assert_eq!(items.get(&key), Some(cloned));
    }
}
