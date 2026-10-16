//! Hash lookup with an explicit linked insertion order and reusable slots.
use crate::heap::Handle;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Key {
    Unit,
    Bool(bool),
    Integer(i128, u8, bool),
    BigInteger(num_bigint::BigInt),
    String(String),
    Bytes(crate::byte_string::Bytes),
    NativeString(crate::native_string::NativeString),
    Path(crate::native_string::NativeString),
    /// A flat nominal path keeps hashing, cloning and dropping deep keys bounded
    /// in native stack depth. Runtime construction always ends in a scalar key.
    Wrapper(Vec<String>, Box<Key>),
}
#[derive(Debug, Clone, PartialEq)]
struct Entry {
    key: Key,
    original: Handle,
    value: Handle,
    previous: Option<usize>,
    next: Option<usize>,
}
#[derive(Debug, Clone, Default, PartialEq)]
pub struct OrderedMap {
    slots: Vec<Option<Entry>>,
    free: Vec<usize>,
    index: HashMap<Key, usize>,
    head: Option<usize>,
    tail: Option<usize>,
}
impl OrderedMap {
    pub fn len(&self) -> usize {
        self.index.len()
    }
    pub fn is_empty(&self) -> bool {
        self.index.is_empty()
    }
    pub fn get(&self, key: &Key) -> Option<Handle> {
        self.index
            .get(key)
            .and_then(|index| self.slots[*index].as_ref())
            .map(|entry| entry.value)
    }
    pub fn contains(&self, key: &Key) -> bool {
        self.index.contains_key(key)
    }
    pub fn set(&mut self, key: Key, original: Handle, value: Handle) -> Option<Handle> {
        if let Some(index) = self.index.get(&key) {
            return self.slots[*index]
                .as_mut()
                .map(|entry| std::mem::replace(&mut entry.value, value));
        }
        let index = self.free.pop().unwrap_or_else(|| {
            self.slots.push(None);
            self.slots.len() - 1
        });
        self.slots[index] = Some(Entry {
            key: key.clone(),
            original,
            value,
            previous: self.tail,
            next: None,
        });
        if let Some(tail) = self.tail {
            self.slots[tail].as_mut().unwrap().next = Some(index);
        } else {
            self.head = Some(index);
        }
        self.tail = Some(index);
        self.index.insert(key, index);
        None
    }
    pub fn remove(&mut self, key: &Key) -> Option<Handle> {
        let index = self.index.remove(key)?;
        let entry = self.slots[index].take().unwrap();
        if let Some(previous) = entry.previous {
            self.slots[previous].as_mut().unwrap().next = entry.next;
        } else {
            self.head = entry.next;
        }
        if let Some(next) = entry.next {
            self.slots[next].as_mut().unwrap().previous = entry.previous;
        } else {
            self.tail = entry.previous;
        }
        self.free.push(index);
        Some(entry.value)
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            map: self,
            next: self.head,
        }
    }
    pub(crate) fn first_slot(&self) -> Option<usize> {
        self.head
    }
    pub(crate) fn slot(&self, index: usize) -> Option<(Handle, Handle, Option<usize>)> {
        self.slots
            .get(index)?
            .as_ref()
            .map(|entry| (entry.original, entry.value, entry.next))
    }
    pub fn keyed(&self) -> impl Iterator<Item = (&Key, Handle, Handle)> {
        self.iter_indices().map(|index| {
            let entry = self.slots[index].as_ref().unwrap();
            (&entry.key, entry.original, entry.value)
        })
    }
    fn iter_indices(&self) -> impl Iterator<Item = usize> + '_ {
        std::iter::successors(self.head, |index| self.slots[*index].as_ref().unwrap().next)
    }
    pub fn map_references(&self, mut map: impl FnMut(Handle) -> Handle) -> Self {
        let mut output = self.clone();
        for entry in output.slots.iter_mut().flatten() {
            entry.original = map(entry.original);
            entry.value = map(entry.value);
        }
        output
    }
}
pub struct Iter<'a> {
    map: &'a OrderedMap,
    next: Option<usize>,
}
impl<'a> Iterator for Iter<'a> {
    type Item = (&'a Handle, &'a Handle);
    fn next(&mut self) -> Option<Self::Item> {
        let index = self.next?;
        let entry = self.map.slots[index].as_ref().unwrap();
        self.next = entry.next;
        Some((&entry.original, &entry.value))
    }
}
impl<'a> IntoIterator for &'a OrderedMap {
    type Item = (&'a Handle, &'a Handle);
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn replacements_keep_position_removal_and_reinsertion_append() {
        let mut map = OrderedMap::default();
        map.set(Key::String("b".into()), Handle(1), Handle(10));
        map.set(Key::String("a".into()), Handle(2), Handle(20));
        assert_eq!(
            map.set(Key::String("b".into()), Handle(3), Handle(30)),
            Some(Handle(10))
        );
        assert_eq!(
            map.iter().map(|(_, value)| value.0).collect::<Vec<_>>(),
            [30, 20]
        );
        assert_eq!(map.remove(&Key::String("b".into())), Some(Handle(30)));
        map.set(Key::String("b".into()), Handle(4), Handle(40));
        assert_eq!(
            map.iter().map(|(_, value)| value.0).collect::<Vec<_>>(),
            [20, 40]
        );
        assert_eq!(map.slots.len(), 2);
    }
}
