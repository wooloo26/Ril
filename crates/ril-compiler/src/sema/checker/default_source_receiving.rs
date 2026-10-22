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

fn original_default_value(
    birth: &Value,
    birth_epoch: usize,
    completion: &Value,
    completion_epoch: usize,
    received: &Value,
    moves: &[(NodeId, NodeId)],
    work: &mut usize,
) -> Result<Value, SourceTypesError> {
    let completed = crate::sema::evaluated::transport_value_at(
        birth,
        moves,
        birth_epoch,
        completion_epoch,
        work,
    )?;
    if !crate::sema::evaluated::same_birth_value(&completed, completion, work)? {
        return Err(SourceTypesError::Unresolved);
    }
    let current = crate::sema::evaluated::transport_value_at(
        completion,
        moves,
        completion_epoch,
        moves.len(),
        work,
    )?;
    if !crate::sema::evaluated::same_birth_value(&current, received, work)? {
        return Err(SourceTypesError::Unresolved);
    }
    // Source reconstruction keeps the actual birth descriptor. Comparing a
    // later, transported copy never rewrites that historical observation.
    crate::sema::evaluated::transport_value_at(birth, moves, birth_epoch, birth_epoch, work)
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
        let emission = self
            .default_uses
            .get(request.receipt.0 as usize)
            .and_then(|receipt| receipt.result_expression)
            .and_then(|token| self.application_effect.contexts.get(token))
            .map(|emission| (emission.expression, emission.context));
        let functions = &self.functions;
        let receipts = &self.default_uses;
        let hir = &self.semantic_hir;
        let moves = &self.recency_moves;
        let original = self.application_effect.with_evaluation_work(
            |expressions, evaluations, activations, work| {
                *work = work
                    .checked_sub(functions.len())
                    .and_then(|remaining| remaining.checked_sub(12))
                    .ok_or(SourceTypesError::BudgetExceeded)?;
                let function = functions
                    .iter()
                    .find(|function| function.definition == request.function)
                    .ok_or(SourceTypesError::MissingNode)?;
                let parameter = function
                    .syntax
                    .parameters
                    .get(request.parameter as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                crate::static_eval::charge_parameter_syntax_clone(parameter, work)
                    .ok_or(SourceTypesError::BudgetExceeded)?;
                if parameter
                    .default
                    .as_ref()
                    .ok_or(SourceTypesError::MissingNode)?
                    != request.syntax
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let receipt = receipts
                    .get(request.receipt.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                if receipt.id != request.receipt
                    || receipt.origin != DefaultOrigin::DeclarationProbe
                    || receipt.target != Some(request.function)
                    || receipt.parameter != request.parameter
                    || receipt.owner != Some(CallableOwner::Function(request.function))
                    || frame.callable_owner != receipt.owner
                    || receipt.caller != caller
                    || active != Some(receipt.id)
                    || !receipt.entered.is_empty()
                    || matches!(
                        receipt.status,
                        CopyInvocationStatus::Rejected | CopyInvocationStatus::Unsupported
                    )
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let token = receipt
                    .result_expression
                    .ok_or(SourceTypesError::MissingNode)?;
                let observed = expressions
                    .get(token)
                    .ok_or(SourceTypesError::MissingNode)?;
                let evaluation = evaluations
                    .get(token)
                    .ok_or(SourceTypesError::MissingNode)?;
                let identity = evaluation.identity.ok_or(SourceTypesError::MissingNode)?;
                let activation = activations
                    .get(identity.activation.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                let snapshot = receipt
                    .result
                    .as_ref()
                    .ok_or(SourceTypesError::MissingNode)?;
                let epoch = receipt
                    .result_allocation_epoch
                    .ok_or(SourceTypesError::MissingNode)?;
                let source = request.syntax.hir_id.ok_or(SourceTypesError::MissingNode)?;
                let original = hir
                    .expression(source)
                    .ok_or(SourceTypesError::MissingNode)?;
                let kind = if matches!(
                    original.kind,
                    crate::hir::nodes::ExprKind::Control {
                        operation: ControlOperation::Resume,
                        ..
                    }
                ) {
                    crate::sema::application_effect::ActivationKind::ControlTransfer
                } else {
                    crate::sema::application_effect::ActivationKind::Expression
                };
                let mut context = caller;
                context.default_use = Some(receipt.id);
                if emission != Some((token, context))
                    || observed.source_id != Some(source)
                    || evaluation.id.0 as usize != token
                    || identity.source != source
                    || evaluation.context != context
                    || evaluation.scope != frame.owner
                    || observed.allocation_epoch != evaluation.allocation_epoch
                    || activation.id != identity.activation
                    || activation.source != Some(source)
                    || activation.kind != kind
                    || activation.context != context
                    || activation.scope != frame.owner
                    || activation.result != Some(evaluation.id)
                    || activation.start_expression > token
                    || activation
                        .end_expression
                        .is_none_or(|end| end <= token || end > expressions.len())
                    || receipt.evaluation_complete != (snapshot.value.ty != Ty::Never)
                {
                    return Err(SourceTypesError::Unresolved);
                }
                original_default_value(
                    &observed.value,
                    evaluation.allocation_epoch,
                    &snapshot.value,
                    epoch,
                    value,
                    moves,
                    work,
                )
            },
        );
        let original = match original {
            Ok(original) => original,
            Err(error) => {
                self.unsupported(
                    request.syntax.span,
                    format!("declaration default lacks its original owned root, context or snapshot: {error}"),
                );
                return false;
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::ids::OptionalTagId;

    fn value(outer: u32, inner: u32) -> Value {
        let element = Ty::Array(Box::new(Ty::Int("int".into())));
        let mut payload = Value::reference(element.clone(), NodeId(inner), CauseId(1));
        payload.permission = Permission::Read;
        payload.participants = [Participant::Loan(LoanId(2))].into();
        let mut value =
            Value::reference(Ty::Optional(Box::new(element)), NodeId(outer), CauseId(0));
        value.permission = Permission::Read;
        value.participants = [Participant::Loan(LoanId(2))].into();
        value.results = [3].into();
        value.must_results = [3].into();
        value.option_tag = Some(true);
        value.option_identity = Some(OptionalTagId(4));
        value.option_payload = Some(Box::new(payload));
        value
    }

    const MOVES: [(NodeId, NodeId); 4] = [
        (NodeId(1), NodeId(6)),
        (NodeId(2), NodeId(7)),
        (NodeId(6), NodeId(8)),
        (NodeId(7), NodeId(9)),
    ];

    #[test]
    fn default_completion_preserves_birth_through_both_recorded_epochs() {
        let birth = value(1, 2);
        let completion = value(6, 7);
        let received = value(8, 9);
        let original =
            original_default_value(&birth, 0, &completion, 2, &received, &MOVES, &mut 4096)
                .unwrap();
        assert_eq!(original, birth);
        assert_eq!(birth.origins.nodes, BTreeSet::from([NodeId(1)]));
        assert_eq!(completion.origins.nodes, BTreeSet::from([NodeId(6)]));
        assert_eq!(
            original.option_payload.as_ref().unwrap().origins.nodes,
            BTreeSet::from([NodeId(2)])
        );
        assert_eq!(original.permission, Permission::Read);
        assert_eq!(
            original.participants,
            BTreeSet::from([Participant::Loan(LoanId(2))])
        );
        assert_eq!(original.results, BTreeSet::from([3]));
        assert_eq!(original.option_identity, Some(OptionalTagId(4)));
    }

    #[test]
    fn default_completion_cannot_relabel_an_old_snapshot_or_change_its_duties() {
        let birth = value(1, 2);
        let completion = value(6, 7);
        let received = value(8, 9);
        for mutation in 0..6 {
            let mut changed = completion.clone();
            match mutation {
                0 => changed = birth.clone(),
                1 => changed.permission = Permission::Write,
                2 => changed.participants.clear(),
                3 => changed.results.clear(),
                4 => changed.option_identity = Some(OptionalTagId(5)),
                5 => changed.marker = true,
                _ => unreachable!(),
            }
            assert!(matches!(
                original_default_value(&birth, 0, &changed, 2, &received, &MOVES, &mut 4096),
                Err(SourceTypesError::Unresolved)
            ));
        }
        let mut changed = received.clone();
        changed.permission = Permission::Write;
        assert!(matches!(
            original_default_value(&birth, 0, &completion, 2, &changed, &MOVES, &mut 4096),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn default_completion_requires_ordered_available_epochs_and_work() {
        let birth = value(1, 2);
        let completion = value(6, 7);
        let received = value(8, 9);
        for (birth_epoch, completion_epoch) in [(3, 2), (0, 5), (5, 5)] {
            assert!(matches!(
                original_default_value(
                    &birth,
                    birth_epoch,
                    &completion,
                    completion_epoch,
                    &received,
                    &MOVES,
                    &mut 4096,
                ),
                Err(SourceTypesError::Unresolved)
            ));
        }
        assert!(matches!(
            original_default_value(&birth, 0, &completion, 2, &received, &MOVES, &mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }
}
