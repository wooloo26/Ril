//! Lexically captured type interpretation, independent of active control flow.
//!
//! A frozen environment is a single immutable contract. Captured type, key and
//! row identities cannot be restored independently or borrowed from a caller.
use super::{
    model::{Env, StaticCoordinate, Ty},
    record_bounds::BoundRowSelection,
    source_types::TypeSourceSelection,
};
use ril_compiler_core::ids::BoundRowId;
use std::{
    collections::BTreeMap,
    ops::{Deref, DerefMut},
    sync::{
        Arc, Weak,
        atomic::{AtomicU64, Ordering},
    },
};

static NEXT_ENVIRONMENT: AtomicU64 = AtomicU64::new(1);

/// An opaque immutable capture identity. Equal contents in another capture do
/// not authorize substituting that capture's lexical declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FrozenEnvId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FrozenTypeEnvId(u64);

#[derive(Debug, Clone, Default)]
pub struct StaticEnvironment {
    pub generic_context: BTreeMap<String, String>,
    pub generic_substitutions: BTreeMap<String, Ty>,
    pub generic_sources: BTreeMap<String, Arc<TypeSourceSelection>>,
    pub static_key_arguments: BTreeMap<String, StaticCoordinate>,
    pub bound_row_context: BTreeMap<String, BoundRowId>,
    pub bound_row_selections: BTreeMap<BoundRowId, Arc<BoundRowSelection>>,
}

impl PartialEq for StaticEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.generic_context == other.generic_context
            && self.generic_substitutions == other.generic_substitutions
            && self.generic_sources == other.generic_sources
            && self.static_key_arguments == other.static_key_arguments
            && self.bound_row_context == other.bound_row_context
            && self.same_row_choices(other)
    }
}
impl Eq for StaticEnvironment {}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypingEnvironment {
    pub types: StaticEnvironment,
    /// Actual lexical binding identities used by named capability bounds.
    pub contract_bindings: Env,
}

impl Deref for TypingEnvironment {
    type Target = StaticEnvironment;
    fn deref(&self) -> &Self::Target {
        &self.types
    }
}
impl DerefMut for TypingEnvironment {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.types
    }
}
impl TypingEnvironment {
    pub fn contract_bindings(&self) -> &Env {
        &self.contract_bindings
    }
}

/// The identity and immutable interpretation live in the same owned object.
#[derive(Debug)]
pub(crate) struct FrozenStaticEnvironment {
    id: FrozenTypeEnvId,
    data: StaticEnvironment,
}

impl StaticEnvironment {
    fn same_row_choices(&self, original: &Self) -> bool {
        self.bound_row_selections.len() == original.bound_row_selections.len()
            && self.bound_row_selections.iter().all(|(id, selection)| {
                original
                    .bound_row_selections
                    .get(id)
                    .is_some_and(|other| Arc::ptr_eq(selection, other))
            })
    }

    fn reusable_with(&self, original: &Self) -> bool {
        // Equality of erased selections cannot identify an actual argument.
        // Shared complete Source handles retain that argument's interpretation.
        self.generic_substitutions
            .keys()
            .all(|id| self.generic_sources.contains_key(id))
            && self.generic_context == original.generic_context
            && self.generic_substitutions == original.generic_substitutions
            && self.static_key_arguments == original.static_key_arguments
            && self.bound_row_context == original.bound_row_context
            && self.same_row_choices(original)
            && self.generic_sources.len() == original.generic_sources.len()
            && self.generic_sources.iter().all(|(name, source)| {
                original
                    .generic_sources
                    .get(name)
                    .is_some_and(|other| Arc::ptr_eq(source, other))
            })
    }
}

impl TypingEnvironment {
    pub fn freeze(self) -> FrozenEnvironment {
        self.freeze_reusing_types(None)
    }

    pub(crate) fn freeze_reusing_types(
        self,
        previous: Option<Arc<FrozenStaticEnvironment>>,
    ) -> FrozenEnvironment {
        let id = NEXT_ENVIRONMENT
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("frozen typing environment identity exhausted");
        FrozenEnvironment {
            id: FrozenEnvId(id),
            types: previous
                .filter(|previous| self.types.reusable_with(&previous.data))
                .unwrap_or_else(|| {
                    Arc::new(FrozenStaticEnvironment {
                        id: FrozenTypeEnvId(id),
                        data: self.types,
                    })
                }),
            bindings: Arc::new(self.contract_bindings),
            poisoned: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FrozenEnvironment {
    id: FrozenEnvId,
    types: Arc<FrozenStaticEnvironment>,
    bindings: Arc<Env>,
    poisoned: bool,
}

impl Default for FrozenEnvironment {
    fn default() -> Self {
        TypingEnvironment::default().freeze()
    }
}

impl PartialEq for FrozenEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.poisoned == other.poisoned
            && self.types.data == other.types.data
            && self.bindings == other.bindings
    }
}
impl Eq for FrozenEnvironment {}

impl Deref for FrozenEnvironment {
    type Target = StaticEnvironment;
    fn deref(&self) -> &Self::Target {
        &self.types.data
    }
}

impl FrozenEnvironment {
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    pub(crate) fn poisoned() -> Self {
        Self {
            poisoned: true,
            ..Self::default()
        }
    }

    pub(crate) fn is_shared(&self) -> bool {
        Arc::strong_count(&self.types) != 1 || Arc::strong_count(&self.bindings) != 1
    }

    pub fn id(&self) -> FrozenEnvId {
        self.id
    }

    pub fn type_id(&self) -> FrozenTypeEnvId {
        self.types.id
    }

    pub fn contract_bindings(&self) -> &Env {
        &self.bindings
    }

    pub(crate) fn weak_types(&self) -> Weak<FrozenStaticEnvironment> {
        Arc::downgrade(&self.types)
    }

    pub(crate) fn same_types(&self, other: &Self) -> bool {
        !self.poisoned && !other.poisoned && Arc::ptr_eq(&self.types, &other.types)
    }

    /// Explicit derivation creates a new contract; existing captures stay fixed.
    pub fn thaw(&self) -> TypingEnvironment {
        TypingEnvironment {
            types: self.types.data.clone(),
            contract_bindings: (*self.bindings).clone(),
        }
    }

    pub fn with_contract_bindings(&self, bindings: Env) -> Self {
        if self.poisoned {
            return self.clone();
        }
        let id = NEXT_ENVIRONMENT
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("frozen typing environment identity exhausted");
        Self {
            id: FrozenEnvId(id),
            types: self.types.clone(),
            bindings: Arc::new(bindings),
            poisoned: false,
        }
    }

    pub(crate) fn into_typing_environment(self) -> TypingEnvironment {
        let types = match Arc::try_unwrap(self.types) {
            Ok(types) => types.data,
            Err(types) => types.data.clone(),
        };
        TypingEnvironment {
            types,
            contract_bindings: Arc::unwrap_or_clone(self.bindings),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cloned_handles_share_identity_but_equal_new_captures_do_not() {
        let original = TypingEnvironment::default().freeze();
        assert_eq!(original.id(), original.clone().id());
        let independent = TypingEnvironment::default().freeze();
        assert_eq!(original, independent);
        assert_ne!(original.id(), independent.id());
        assert!(!original.same_types(&independent));
        let derived = original.with_contract_bindings(BTreeMap::from([("value".into(), 7)]));
        assert_ne!(original.id(), derived.id());
        assert!(original.same_types(&derived));
        assert!(original.contract_bindings().is_empty());
        assert_eq!(derived.contract_bindings().get("value"), Some(&7));
    }
}
