//! Declaration defaults receive a source type before any descriptor rewrite.
//! Their root emission is owned by a DefaultUse, never a hypothetical Call.
use super::*;
use crate::sema::{
    copy_contract::CopyInvocationStatus,
    default_uses::{DefaultOrigin, DefaultUseId},
    source_reception::{self, Construction, SchemaSensitivity, Target},
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
            let observed = self.expression_facts.get(token)?;
            let emission = self.invocation_expressions.get(token)?;
            let snapshot = receipt.result.as_ref()?;
            let epoch = receipt.result_allocation_epoch?;
            let mut context = caller;
            context.default_use = Some(receipt.id);
            if emission.expression != token
                || emission.context != context
                || observed.span != request.syntax.span
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
        let answer = target.key.as_ref().and_then(|expected| {
            let fresh = source_reception::construction(request.syntax, &mut 4096)?;
            match self.original_source_receiving_key(&original, request.syntax, frame) {
                Some(actual) => {
                    source_reception::compatible(expected, &actual, Some(&fresh), &mut 4096)
                }
                None => empty_default(expected, &fresh),
            }
        });
        match answer {
            Some(true) => true,
            Some(false) => {
                self.error(
                    "E0301",
                    request.syntax.span,
                    "original declaration default source does not fit its parameter",
                    [value.cause],
                );
                false
            }
            None => {
                self.unsupported(
                    request.syntax.span,
                    "declaration default requires its complete original receiving source",
                );
                false
            }
        }
    }
}

fn empty_default(
    expected: &crate::sema::effect_identity::ArgumentKey,
    fresh: &Construction,
) -> Option<bool> {
    use crate::sema::effect_identity::ArgumentKey;
    let (ArgumentKey::Array { length, element }, Construction::Array(items)) = (expected, fresh)
    else {
        return None;
    };
    if !items.is_empty() {
        return None;
    }
    source_reception::complete(element, &mut 4096)?;
    Some(
        length
            .as_ref()
            .is_none_or(|length| length == "const(int:0)"),
    )
}
