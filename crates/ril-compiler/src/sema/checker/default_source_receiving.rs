//! Declaration defaults receive a source type before any descriptor rewrite.
//! Their root emission is owned by a DefaultUse, never a hypothetical Call.
use super::*;
use crate::sema::{
    copy_contract::CopyInvocationStatus,
    default_uses::{DefaultOrigin, DefaultUseId},
    source_reception::{self, SchemaSensitivity, Target},
    source_types::{SourceTypesError, WorkLimit},
};

pub(super) struct DeclaredDefault<'a> {
    pub function: DefinitionId,
    pub parameter: u32,
    pub receipt: DefaultUseId,
    pub syntax: &'a Expr,
    pub target: Option<&'a Target>,
}

impl Checker {
    pub(super) fn check_declared_default_source(
        &mut self,
        request: DeclaredDefault<'_>,
        value: &Value,
        frame: &Frame,
    ) -> bool {
        let mut caller = self.invocation_context(frame.callable_owner);
        let active = self.default_use_stack.last().copied();
        caller.default_use = self.default_use_stack.iter().rev().nth(1).copied();
        let original = (|| {
            let function = self
                .functions
                .iter()
                .find(|function| function.definition == request.function)?;
            let parameter = function.syntax.parameters.get(request.parameter as usize)?;
            if parameter.default.as_ref()? != request.syntax {
                return None;
            }
            let receipt = self.default_uses.get(request.receipt.0 as usize)?;
            if receipt.id != request.receipt
                || receipt.origin != DefaultOrigin::DeclarationProbe
                || receipt.target != Some(request.function)
                || receipt.parameter != request.parameter
                || receipt.owner != Some(CallableOwner::Function(request.function))
                || frame.callable_owner != receipt.owner
                || receipt.caller != caller
                || active != Some(receipt.id)
                || receipt.span != request.syntax.span
                || !receipt.entered.is_empty()
                || matches!(
                    receipt.status,
                    CopyInvocationStatus::Rejected | CopyInvocationStatus::Unsupported
                )
            {
                return None;
            }
            let token = receipt.result_expression?;
            let observed = self.application_effect.expressions.get(token)?;
            let emission = self.application_effect.contexts.get(token)?;
            let snapshot = receipt.result.as_ref()?;
            let epoch = receipt.result_allocation_epoch?;
            let mut context = caller;
            context.default_use = Some(receipt.id);
            if emission.expression != token
                || emission.context != context
                || request.syntax.hir_id.is_none()
                || observed.source_id != request.syntax.hir_id
                || observed.value != snapshot.value
                || &snapshot.value != value
                || epoch != self.recency_moves.len()
                || receipt.evaluation_complete != (value.ty != Ty::Never)
            {
                return None;
            }
            Some(observed.value.clone())
        })();
        let Some(original) = original else {
            self.unsupported(
                request.syntax.span,
                "declaration default lacks its original owned root, context or snapshot",
            );
            return false;
        };
        // Bottom supplies no normally returned value and no body-entry proof.
        // The receipt remains incomplete; all ordinary type checks still run.
        if value.ty == Ty::Never {
            return true;
        }
        let Some(target) = request.target else {
            return true;
        };
        if target.sensitivity == SchemaSensitivity::NotRequired {
            return true;
        }
        let mut work = WorkLimit::new(16384);
        let answer = (|| {
            if target.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            let mut remaining = work.remaining();
            let fresh = source_reception::construction(request.syntax, &mut remaining)
                .ok_or(SourceTypesError::BudgetExceeded)?;
            work.charge(work.remaining() - remaining)?;
            match self.original_source_receiving_schema(
                &original,
                request.syntax,
                frame,
                &mut work,
            )? {
                Some((actual, environment)) => {
                    if environment.is_poisoned() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    target.receive_schema(&actual, Some(&fresh), &mut work)
                }
                None => target
                    .schema
                    .as_ref()
                    .ok_or(SourceTypesError::Unresolved)?
                    .empty_context(&fresh, &mut work)?
                    .ok_or(SourceTypesError::Unresolved),
            }
        })();
        match answer {
            Ok(true) => true,
            Ok(false) => {
                self.error(
                    "E0301",
                    request.syntax.span,
                    "original declaration default source does not fit its parameter",
                    [value.cause],
                );
                false
            }
            Err(error) => {
                self.unsupported(
                    request.syntax.span,
                    format!("declaration default requires its complete original receiving source: {error}"),
                );
                false
            }
        }
    }
}
