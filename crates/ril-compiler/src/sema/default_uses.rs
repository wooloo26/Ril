//! A default evaluation belongs to one application event, before body entry.
use super::{
    copy_contract::{CopyCallEventId, CopyInvocationStatus, CopyValueSnapshot},
    copy_templates::InstanceId,
    effect_identity::{InvocationContext, StaticArgumentWitness},
};
pub use crate::hir::application::EvaluationRole;
use ril_compiler_core::{
    ids::{CallableOwner, DefinitionId},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefaultUseId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefaultOrigin {
    Call(CopyCallEventId),
    DeclarationProbe,
    InvocationFallback(InstanceId),
}

#[derive(Debug, Clone)]
pub struct DefaultUse {
    pub id: DefaultUseId,
    pub origin: DefaultOrigin,
    pub target: Option<DefinitionId>,
    pub parameter: u32,
    pub caller: InvocationContext,
    pub owner: Option<CallableOwner>,
    pub span: Span,
    pub arguments: Vec<StaticArgumentWitness>,
    pub captured_arguments: Vec<StaticArgumentWitness>,
    pub unresolved_captured_binders: BTreeSet<String>,
    /// Normal evaluation is necessary but never certifies body entry by itself.
    pub evaluation_complete: bool,
    pub status: CopyInvocationStatus,
    pub entered: Vec<InstanceId>,
    pub result: Option<CopyValueSnapshot>,
    /// The real root emission, in this receipt's default-use context. This
    /// cannot be recovered later by searching for a matching span or cause.
    pub result_expression: Option<usize>,
    /// Epoch of that actual result snapshot, before later arguments/defaults.
    /// A missing or partial result supplies no body-entry proof.
    pub result_allocation_epoch: Option<usize>,
}

/// Link a prepared default to the existing callable-entry packet which used
/// it. This checks identity only; completion and body evidence are checked by
/// their owning analyses. An equal value or equal span is not the same input.
pub(crate) fn closure_entry_uses(
    default: &DefaultUse,
    call: &super::effect_identity::ClosureInvocation,
    closure: &super::model::ClosureInfo,
) -> bool {
    let DefaultOrigin::Call(event) = default.origin else {
        return false;
    };
    let Some(argument) = call.entry.arguments.get(default.parameter as usize) else {
        return false;
    };
    let birth = argument.packet.birth_coordinates();
    default.target.is_none()
        && default.evaluation_complete
        && default.owner.is_some()
        && default.owner == closure.site.map(CallableOwner::Lambda)
        && matches!(&call.entry.origin, super::application_effect::EntryOrigin::Application(actual) if *actual == event)
        && call.entry.caller_context == default.caller
        && default.result_expression.is_some()
        && birth.observation == default.result_expression
        && birth.context
            == Some(InvocationContext {
                owner: default.owner,
                default_use: Some(default.id),
                ..default.caller
            })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentSource {
    Supplied,
    Default(DefaultUseId),
    Missing,
}

/// The original supplied operand observation; this is not a receiving cast.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SuppliedArgument {
    pub expression: usize,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ApplicationEvaluation {
    pub role: EvaluationRole,
    pub observation: SuppliedArgument,
}

#[derive(Debug, Clone)]
pub struct CallArguments {
    pub source_event: CopyCallEventId,
    pub target: Option<DefinitionId>,
    /// Exact evaluated prefix, including the callee's own root and epoch.
    /// It survives an abrupt piped operand even when no callee was evaluated.
    pub evaluated: Vec<ApplicationEvaluation>,
    /// Mapping to parameter slots exists only after the actual callee is known.
    /// False requires empty slots/supplied; it does not erase evaluated work.
    pub slots_bound: bool,
    pub slots: Vec<ArgumentSource>,
    /// Actual parameter slot after the original public label/position mapping.
    /// Missing observations cannot be replaced by equal-span/value searches.
    pub supplied: BTreeMap<u32, SuppliedArgument>,
    pub evaluation_complete: bool,
}
