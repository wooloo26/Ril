//! Original primitive source contracts, attached to physical observations.
//! The raw annotations remain available for explanation. They are not a
//! closed source witness or a proof that a receiving bound is satisfied.
use super::{effect_identity::InvocationContext, model::BindingId};
use ril_compiler_core::diagnostic::CauseId;
use ril_syntax::ast::TypeExpr;
use std::collections::BTreeSet;
use std::sync::OnceLock;

/// Intrinsic declarations are interpreted in one canonical namespace. This
/// environment never captures a user's lexical bindings or static selections.
pub(crate) fn catalog_environment() -> &'static super::context::FrozenEnvironment {
    static CATALOG: OnceLock<super::context::FrozenEnvironment> = OnceLock::new();
    CATALOG.get_or_init(Default::default)
}

pub(crate) fn is_catalog_environment(environment: &super::context::FrozenEnvironment) -> bool {
    !environment.is_poisoned()
        && environment.id() == catalog_environment().id()
        && environment.generic_context.is_empty()
        && environment.generic_substitutions.is_empty()
        && environment.generic_sources.is_empty()
        && environment.static_key_arguments.is_empty()
        && environment.bound_row_context.is_empty()
        && environment.bound_row_selections.is_empty()
        && environment.contract_bindings.is_empty()
}

/// Candidate interface only. Original declaration/occurrence validation still
/// establishes identity. A published monomorphic view keeps its own interface.
pub(crate) fn generic_reference(
    value: &super::model::Value,
) -> Option<ril_compiler_core::builtin_calls::GenericBuiltin> {
    use super::model::{Callable, Ty};
    if value.signature.is_some() || value.ty != Ty::Unknown {
        return None;
    }
    let [Callable::Builtin(name)] = value.callables.as_slice() else {
        return None;
    };
    ril_compiler_core::builtin_calls::GenericBuiltin::lookup(name)
}

pub(crate) fn parameter_labels(value: &super::model::Value, fallback: usize) -> Vec<Option<&str>> {
    if let Some(parameters) = &value.signature {
        crate::hir::application::parameter_labels(parameters)
    } else if let Some(id) = generic_reference(value) {
        super::source_types::polymorphic::parameter_labels(id)
    } else {
        vec![None; fallback]
    }
}

/// A closed declaration reference can retain universal variables without
/// inventing a monomorphic TypeExpr from the later receiving context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinDeclaration {
    Syntax(TypeExpr),
    Generic(ril_compiler_core::builtin_calls::GenericBuiltin),
}

impl BuiltinDeclaration {
    pub fn syntax(&self) -> Option<&TypeExpr> {
        match self {
            Self::Syntax(syntax) => Some(syntax),
            Self::Generic(_) => None,
        }
    }
    pub fn syntax_mut(&mut self) -> Option<&mut TypeExpr> {
        match self {
            Self::Syntax(syntax) => Some(syntax),
            Self::Generic(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BuiltinSourceObservation {
    pub expression: usize,
    pub context: InvocationContext,
    pub identity: String,
    pub full_header: BuiltinDeclaration,
    pub environment: super::context::FrozenEnvironment,
    pub concrete_effects: BTreeSet<String>,
    pub written_formals: BTreeSet<u32>,
    pub captures: BTreeSet<BindingId>,
    pub cause: CauseId,
}
