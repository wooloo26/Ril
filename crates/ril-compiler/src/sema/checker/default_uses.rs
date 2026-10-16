//! Defaults run in their own lexical/static environment before body entry.
//! The call event is passed explicitly; the body consumes that event once.
use super::super::{
    copy_contract::CopyInvocationStatus,
    default_uses::{DefaultOrigin, DefaultUse, DefaultUseId},
};
use super::*;

impl Checker {
    pub(super) fn fail_default_uses(&mut self, rejected: bool) {
        for id in &self.default_use_stack {
            let status = &mut self.default_uses[id.0 as usize].status;
            if rejected {
                *status = CopyInvocationStatus::Rejected;
            } else if *status != CopyInvocationStatus::Rejected {
                *status = CopyInvocationStatus::Unsupported;
            }
        }
    }

    pub(super) fn evaluate_default(
        &mut self,
        target: Option<usize>,
        parameter: usize,
        syntax: &Expr,
        origin: DefaultOrigin,
        caller: super::super::effect_identity::InvocationContext,
        frame: &mut Frame,
    ) -> (DefaultUseId, Value) {
        let info = target.map(|id| self.functions[id].clone());
        let selected = info
            .as_ref()
            .map(|info| self.static_arguments_for(info, syntax.span))
            .unwrap_or_default();
        let id = DefaultUseId(self.default_uses.len() as u32);
        self.default_uses.push(DefaultUse {
            id,
            origin,
            target: info.as_ref().map(|info| info.definition),
            parameter: parameter as u32,
            caller,
            owner: frame.callable_owner,
            span: syntax.span,
            arguments: selected.arguments,
            captured_arguments: selected.captured_arguments,
            unresolved_captured_binders: selected.unresolved_captured_binders,
            evaluation_complete: false,
            status: CopyInvocationStatus::Incomplete,
            entered: vec![],
            result: None,
            result_expression: None,
            result_allocation_epoch: None,
        });
        self.default_use_stack.push(id);
        let expected = info
            .as_ref()
            .and_then(|info| info.syntax.parameters.get(parameter))
            .and_then(|parameter| parameter.ty.as_ref())
            .map(|syntax| self.ty(syntax));
        let (value, result_expression) =
            self.expression_expected_observed(syntax, frame, expected.as_ref());
        self.check_default_purity(&value, syntax.span, frame);
        assert_eq!(self.default_use_stack.pop(), Some(id));
        let result = self.copy_value_snapshot(&value);
        let result_allocation_epoch = self.recency_moves.len();
        let record = &mut self.default_uses[id.0 as usize];
        record.evaluation_complete = value.ty != Ty::Never && result_expression.is_some();
        record.result = Some(result);
        record.result_expression = result_expression;
        record.result_allocation_epoch = Some(result_allocation_epoch);
        (id, value)
    }

    pub(super) fn check_default_purity(&mut self, value: &Value, span: Span, frame: &Frame) {
        if !frame.obligations.effects.is_empty()
            || !frame.obligations.named.is_empty()
            || frame.obligations.parameter_write
            || value.mutable_environment
            || value.observer_environment
        {
            self.error(
                "E0409",
                span,
                "default expressions must be pure and immutable",
                [value.cause],
            );
        }
    }

    pub(super) fn finish_default_invocation(&mut self) {
        let Some(id) = self.copy_invocation_stack.last().copied() else {
            return;
        };
        let invocation = &self.copy_invocations[id.0 as usize];
        let Some(selected) = self
            .effect_invocations
            .iter()
            .rev()
            .find(|call| call.invocation == Some(id))
        else {
            return;
        };
        let equivalent =
            |left: &[super::super::effect_identity::StaticArgumentWitness],
             right: &[super::super::effect_identity::StaticArgumentWitness]| {
                left.len() == right.len()
                    && left.iter().zip(right).all(|(a, b)| {
                        a.definition == b.definition
                            && a.index == b.index
                            && a.key.is_some()
                            && a.key == b.key
                            && a.syntax.is_some()
                            && b.syntax.is_some()
                    })
            };
        for record in &mut self.default_uses {
            let matches = match record.origin {
                DefaultOrigin::Call(event) => invocation.source_event == Some(event),
                DefaultOrigin::InvocationFallback(call) => call == id,
                DefaultOrigin::DeclarationProbe => false,
            };
            if !matches || record.target != Some(invocation.target) || !record.evaluation_complete {
                continue;
            }
            if !record.entered.contains(&id) {
                record.entered.push(id);
            }
            if record.status == CopyInvocationStatus::Incomplete
                && equivalent(&record.arguments, &selected.arguments)
                && equivalent(&record.captured_arguments, &selected.captured_arguments)
                && record.unresolved_captured_binders.is_empty()
                && selected.unresolved_captured_binders.is_empty()
            {
                record.status = invocation.status;
            }
        }
    }
}
