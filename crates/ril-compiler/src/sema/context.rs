//! Lexically captured type interpretation, independent of active control flow.
//!
//! A frozen environment is a single immutable contract. Captured type, key and
//! row identities cannot be restored independently or borrowed from a caller.
use super::{
    model::{Env, SourceTypeWitness, StaticCoordinate, Ty},
    record_bounds::BoundRowSelection,
};
use ril_compiler_core::ids::BoundRowId;
use std::{collections::BTreeMap, ops::Deref, sync::Arc};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypingEnvironment {
    pub generic_context: BTreeMap<String, String>,
    pub generic_substitutions: BTreeMap<String, Ty>,
    pub generic_type_witnesses: BTreeMap<String, Arc<SourceTypeWitness>>,
    pub static_key_arguments: BTreeMap<String, StaticCoordinate>,
    pub bound_row_context: BTreeMap<String, BoundRowId>,
    pub bound_row_selections: BTreeMap<BoundRowId, BoundRowSelection>,
    /// Actual lexical binding identities used by named capability bounds.
    pub contract_bindings: Env,
}

impl TypingEnvironment {
    pub fn freeze(self) -> FrozenEnvironment {
        FrozenEnvironment(Arc::new(self))
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FrozenEnvironment(Arc<TypingEnvironment>);

impl Deref for FrozenEnvironment {
    type Target = TypingEnvironment;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FrozenEnvironment {
    /// Explicit derivation creates a new contract; existing captures stay fixed.
    pub fn thaw(&self) -> TypingEnvironment {
        (*self.0).clone()
    }

    pub fn with_contract_bindings(&self, bindings: Env) -> Self {
        let mut derived = self.thaw();
        derived.contract_bindings = bindings;
        derived.freeze()
    }

    pub(crate) fn into_typing_environment(self) -> TypingEnvironment {
        Arc::unwrap_or_clone(self.0)
    }
}
