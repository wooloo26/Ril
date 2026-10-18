//! Canonical effect identity is independent of source spelling and display names.
use ril_compiler_core::{ids::DefinitionId, source::Span};
use ril_syntax::ast::ParameterMode;
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StaticBinderSort {
    Type,
}

/// Closed leaves come only from ordinary static normalization. Composite nodes
/// retain source information which the value-level `Ty` deliberately erases.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgumentKey {
    Closed(String),
    Binder {
        identity: String,
        sort: StaticBinderSort,
    },
    Name {
        name: String,
        arguments: Vec<Self>,
    },
    Array {
        length: Option<String>,
        element: Box<Self>,
    },
    Map {
        key: Box<Self>,
        value: Box<Self>,
    },
    Tuple(Vec<Self>),
    Record {
        fields: Vec<(String, bool, Self)>,
        row: Option<Box<Self>>,
    },
    Callable {
        parameters: Vec<(ParameterMode, Self)>,
        result: Box<Self>,
        annotations: Vec<String>,
    },
}
impl ArgumentKey {
    pub fn is_closed(&self) -> bool {
        match self {
            Self::Closed(_) => true,
            Self::Binder { .. } => false,
            Self::Name { arguments, .. } | Self::Tuple(arguments) => {
                arguments.iter().all(Self::is_closed)
            }
            Self::Array { element, .. } => element.is_closed(),
            Self::Map { key, value } => key.is_closed() && value.is_closed(),
            Self::Record { fields, row } => {
                fields.iter().all(|(_, _, value)| value.is_closed())
                    && row.as_ref().is_none_or(|row| row.is_closed())
            }
            Self::Callable {
                parameters, result, ..
            } => parameters.iter().all(|(_, value)| value.is_closed()) && result.is_closed(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectInstanceKey {
    pub declaration: Span,
    pub name: String,
    pub arguments: Vec<ArgumentKey>,
}
impl EffectInstanceKey {
    pub fn is_closed(&self) -> bool {
        self.arguments.iter().all(ArgumentKey::is_closed)
    }
}

#[derive(Debug, Clone)]
pub struct EffectInstance {
    pub key: EffectInstanceKey,
    pub name: String,
    pub operations: BTreeSet<u64>,
    pub sites: BTreeSet<(u32, u32, u32)>,
}

/// An observation is not yet a specialization certificate. Missing static
/// arguments stay explicit; operation and callback dependencies are never lost.
#[derive(Debug, Clone)]
pub struct EffectInvocation {
    pub invocation: Option<super::copy_templates::InstanceId>,
    pub budget_validation: bool,
    pub function: DefinitionId,
    pub site: Span,
    pub arguments: Vec<StaticArgumentWitness>,
    pub captured_arguments: Vec<StaticArgumentWitness>,
    pub unresolved_captured_binders: BTreeSet<String>,
    pub operations: BTreeSet<u64>,
    pub callbacks: Vec<CallbackInvocation>,
    pub unresolved: BTreeSet<u32>,
    pub verifying: bool,
}

#[derive(Debug, Clone)]
pub struct StaticArgumentWitness {
    pub definition: DefinitionId,
    pub index: u32,
    pub binder: String,
    pub key: Option<ArgumentKey>,
    pub syntax: Option<ril_syntax::ast::TypeExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InvocationContext {
    pub invocation: Option<super::copy_templates::InstanceId>,
    pub owner: Option<ril_compiler_core::ids::CallableOwner>,
    pub closure: Option<usize>,
    pub closure_invocation: Option<ClosureInvocationId>,
    pub budget_validation: bool,
    pub default_use: Option<super::default_uses::DefaultUseId>,
}

#[derive(Debug, Clone)]
pub struct InvocationExpression {
    pub context: InvocationContext,
    /// Index in SemanticFacts.expressions, preserving the complete Value.
    pub expression: usize,
    /// Present only for this actual argument root emission in its caller
    /// context. Repeated source spans do not identify argument occurrences.
    pub argument_of: Option<(super::copy_contract::CopyCallEventId, u32)>,
}

#[derive(Debug, Clone)]
pub struct InvocationCall {
    pub invocation: super::copy_templates::InstanceId,
    pub caller_owner: Option<ril_compiler_core::ids::CallableOwner>,
    pub caller_closure: Option<usize>,
    pub caller_closure_invocation: Option<ClosureInvocationId>,
    pub default_use: Option<super::default_uses::DefaultUseId>,
}

pub use ril_compiler_core::ids::ClosureInvocationId;

#[derive(Debug, Clone)]
pub struct ClosureInvocation {
    pub id: ClosureInvocationId,
    pub source_event: Option<super::copy_contract::CopyCallEventId>,
    pub caller_activation: super::facts::ScopeId,
    /// Actual entered closure frame, distinct from its caller and creation.
    pub activation: Option<super::facts::ScopeId>,
    /// Actual semantic closure object, not its shared source ClosureSiteId.
    pub closure: usize,
    pub parent_named: Option<super::copy_templates::InstanceId>,
    pub parent_closure: Option<ClosureInvocationId>,
    pub caller_owner: Option<ril_compiler_core::ids::CallableOwner>,
    pub site: Span,
    pub probe: bool,
    /// A known nonpositive budget checks its action but never enters it.
    pub budget_validation: bool,
    pub status: super::copy_contract::CopyInvocationStatus,
}

#[derive(Debug, Clone)]
pub struct InvocationWitness {
    pub context: InvocationContext,
    pub span: Span,
    pub kind: InvocationWitnessKind,
}

#[derive(Debug, Clone)]
pub enum InvocationWitnessKind {
    NumericSelection(super::numeric_selection::NumericSelection),
    ContextualType(super::model::Ty),
    ImplicitUnwrap(super::ImplicitUnwrap),
    VariantProjection(super::VariantProjection),
    StaticKey(usize),
    Budget(super::BudgetProof),
    Handler(usize),
    RetainedHandler(super::model::RetainedHandlerFact),
}

#[derive(Debug, Clone)]
pub struct CallbackInvocation {
    pub site: Span,
    pub owner: Option<ril_compiler_core::ids::CallableOwner>,
    pub parameter_bindings: BTreeSet<super::model::BindingId>,
    pub targets: Vec<super::model::Callable>,
}
