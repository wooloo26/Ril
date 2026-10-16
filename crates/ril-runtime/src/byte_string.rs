//! Immutable shared byte storage. Slicing changes two offsets without copying
//! the remaining input for each partial stream transfer.
use std::{
    ops::{Deref, Range},
    sync::Arc,
};
#[derive(Clone)]
pub struct Bytes {
    backing: Arc<[u8]>,
    range: Range<usize>,
}
impl From<Vec<u8>> for Bytes {
    fn from(value: Vec<u8>) -> Self {
        let end = value.len();
        Self {
            backing: value.into(),
            range: 0..end,
        }
    }
}
impl Bytes {
    pub fn as_slice(&self) -> &[u8] {
        &self.backing[self.range.clone()]
    }
    pub fn slice(&self, range: Range<usize>) -> Option<Self> {
        self.as_slice().get(range.clone())?;
        Some(Self {
            backing: self.backing.clone(),
            range: self.range.start + range.start..self.range.start + range.end,
        })
    }
}
impl Deref for Bytes {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
impl std::fmt::Debug for Bytes {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(formatter)
    }
}
impl PartialEq for Bytes {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl Eq for Bytes {}
impl PartialOrd for Bytes {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Bytes {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}
impl std::hash::Hash for Bytes {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nested_slices_share_storage_and_use_value_equality() {
        let original = Bytes::from(vec![0, 1, 2, 3]);
        let outer = original.slice(1..4).unwrap();
        let inner = outer.slice(1..2).unwrap();
        assert!(Arc::ptr_eq(&original.backing, &inner.backing));
        assert_eq!(inner, Bytes::from(vec![2]));
        assert!(inner.slice(Range { start: 1, end: 0 }).is_none());
        drop(original);
        drop(outer);
        assert_eq!(inner.as_slice(), &[2]);
    }
}
