//! One allocation and ancestry index for evaluation frames. Frame origins are
//! receiver identities, independent of loans, results or continuation shape.
use super::{
    application_effect::EntryOrigin,
    copy_templates::InstanceId,
    effect_identity::{ClosureInvocationId, InvocationContext},
    facts::ScopeId,
};
use ril_compiler_core::ids::{ActivationEpochId, ExprId};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub enum ScopeOrigin {
    Module,
    Unresolved,
    Named(InstanceId),
    Closure(ClosureInvocationId),
    Operation(OperationEntry),
}

#[derive(Debug, Clone)]
pub struct OperationEntry {
    pub handler: usize,
    pub operation: u64,
    pub body: Option<ExprId>,
    pub parent: Option<ActivationEpochId>,
    pub caller_context: InvocationContext,
    pub context: InvocationContext,
    pub origin: EntryOrigin,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone)]
pub struct ScopeRecord {
    pub id: ScopeId,
    pub parent: Option<ScopeId>,
    pub origin: ScopeOrigin,
}

#[derive(Debug, Clone, Default)]
pub struct ScopeIndex {
    entries: BTreeMap<ScopeId, ScopeRecord>,
    next: u32,
    poisoned: bool,
}

impl ScopeIndex {
    pub fn contains(&self, id: &ScopeId) -> bool {
        self.entries.contains_key(id)
    }
    pub fn iter(&self) -> impl Iterator<Item = &ScopeId> {
        self.entries.keys()
    }
    pub fn records(&self) -> impl ExactSizeIterator<Item = &ScopeRecord> {
        self.entries.values()
    }
    pub fn get(&self, id: &ScopeId) -> Option<&ScopeRecord> {
        self.entries.get(id)
    }
    pub fn get_mut(&mut self, id: &ScopeId) -> Option<&mut ScopeRecord> {
        self.entries.get_mut(id)
    }
    pub fn remove(&mut self, id: &ScopeId) -> Option<ScopeRecord> {
        self.entries.remove(id)
    }
    pub fn parent(&self, id: &ScopeId) -> Option<&ScopeId> {
        self.entries.get(id)?.parent.as_ref()
    }
    pub fn parents(&self) -> impl Iterator<Item = (&ScopeId, &ScopeId)> {
        self.entries
            .values()
            .filter_map(|record| record.parent.as_ref().map(|parent| (&record.id, parent)))
    }
    pub fn is_poisoned(&self) -> bool {
        self.poisoned || self.entries.iter().any(|(id, record)| *id != record.id)
    }
    pub fn insert(&mut self, id: ScopeId) -> bool {
        if let Some(next) = id.0.checked_add(1) {
            self.next = self.next.max(next);
        } else {
            self.poisoned = true;
        }
        if self.entries.contains_key(&id) {
            return false;
        }
        self.entries.insert(
            id,
            ScopeRecord {
                id,
                parent: None,
                origin: if id == ScopeId(0) {
                    ScopeOrigin::Module
                } else {
                    ScopeOrigin::Unresolved
                },
            },
        );
        true
    }
    pub fn set_parent(&mut self, child: ScopeId, parent: ScopeId) -> Option<ScopeId> {
        if let Some(record) = self.entries.get_mut(&child) {
            record.parent.replace(parent)
        } else {
            self.poisoned = true;
            None
        }
    }
    pub(crate) fn set_origin(&mut self, id: ScopeId, origin: ScopeOrigin) {
        if let Some(record) = self.entries.get_mut(&id) {
            record.origin = origin;
        } else {
            self.poisoned = true;
        }
    }
    pub(crate) fn allocate(&mut self) -> Option<ScopeId> {
        if self.poisoned || self.entries.len() >= 1_000_000 {
            self.poisoned = true;
            return None;
        }
        let id = ScopeId(self.next);
        self.insert(id).then_some(id)
    }
}

impl Extend<ScopeId> for ScopeIndex {
    fn extend<T: IntoIterator<Item = ScopeId>>(&mut self, iter: T) {
        for id in iter {
            self.insert(id);
        }
    }
}
impl FromIterator<ScopeId> for ScopeIndex {
    fn from_iter<T: IntoIterator<Item = ScopeId>>(iter: T) -> Self {
        let mut result = Self::default();
        result.extend(iter);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn allocation_and_ancestry_share_one_identity_space() {
        let mut scopes: ScopeIndex = [ScopeId(0)].into_iter().collect();
        let child = scopes.allocate().unwrap();
        assert_eq!(child, ScopeId(1));
        scopes.set_parent(child, ScopeId(0));
        scopes.set_origin(child, ScopeOrigin::Named(InstanceId(3)));
        let record = scopes.get(&child).unwrap();
        assert!(matches!(record.origin, ScopeOrigin::Named(InstanceId(3))));
        assert_eq!(record.parent, Some(ScopeId(0)));
        assert_eq!(
            scopes.iter().copied().collect::<Vec<_>>(),
            [ScopeId(0), child]
        );
        assert_eq!(scopes.parents().count(), 1);
        assert!(!scopes.is_poisoned());
    }
    #[test]
    fn a_parent_link_cannot_allocate_or_authorize_an_unborn_scope() {
        let mut scopes: ScopeIndex = [ScopeId(0)].into_iter().collect();
        scopes.set_parent(ScopeId(7), ScopeId(0));
        assert!(!scopes.contains(&ScopeId(7)));
        assert!(scopes.is_poisoned());
        assert!(scopes.allocate().is_none());
    }
}
