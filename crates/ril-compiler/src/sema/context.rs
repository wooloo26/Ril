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
    ops::Deref,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

static NEXT_ENVIRONMENT: AtomicU64 = AtomicU64::new(1);

/// An opaque immutable capture identity. Equal contents in another capture do
/// not authorize substituting that capture's lexical declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FrozenEnvId(u64);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypingEnvironment {
    pub generic_context: BTreeMap<String, String>,
    pub generic_substitutions: BTreeMap<String, Ty>,
    pub generic_sources: BTreeMap<String, Arc<TypeSourceSelection>>,
    pub static_key_arguments: BTreeMap<String, StaticCoordinate>,
    pub bound_row_context: BTreeMap<String, BoundRowId>,
    pub bound_row_selections: BTreeMap<BoundRowId, BoundRowSelection>,
    /// Actual lexical binding identities used by named capability bounds.
    pub contract_bindings: Env,
}

impl TypingEnvironment {
    pub fn freeze(self) -> FrozenEnvironment {
        let id = NEXT_ENVIRONMENT
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("frozen typing environment identity exhausted");
        FrozenEnvironment {
            id: FrozenEnvId(id),
            environment: Arc::new(self),
            poisoned: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FrozenEnvironment {
    id: FrozenEnvId,
    environment: Arc<TypingEnvironment>,
    poisoned: bool,
}

impl Default for FrozenEnvironment {
    fn default() -> Self {
        TypingEnvironment::default().freeze()
    }
}

impl PartialEq for FrozenEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.poisoned == other.poisoned && self.environment == other.environment
    }
}
impl Eq for FrozenEnvironment {}

impl Deref for FrozenEnvironment {
    type Target = TypingEnvironment;
    fn deref(&self) -> &Self::Target {
        &self.environment
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
        Arc::strong_count(&self.environment) != 1
    }

    pub fn id(&self) -> FrozenEnvId {
        self.id
    }

    /// Explicit derivation creates a new contract; existing captures stay fixed.
    pub fn thaw(&self) -> TypingEnvironment {
        (*self.environment).clone()
    }

    pub fn with_contract_bindings(&self, bindings: Env) -> Self {
        if self.poisoned {
            return self.clone();
        }
        let mut derived = self.thaw();
        derived.contract_bindings = bindings;
        derived.freeze()
    }

    pub(crate) fn into_typing_environment(self) -> TypingEnvironment {
        Arc::unwrap_or_clone(self.environment)
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
        let derived = original.with_contract_bindings(BTreeMap::from([("value".into(), 7)]));
        assert_ne!(original.id(), derived.id());
        assert!(original.contract_bindings.is_empty());
        assert_eq!(derived.contract_bindings.get("value"), Some(&7));
    }
}
