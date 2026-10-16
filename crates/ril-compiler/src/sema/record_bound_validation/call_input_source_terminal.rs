//! A small Source proof of absent normal entry, never a hypothetical body.
//! Other terminal expressions retain their independent obligations.
use super::*;
use crate::sema::{
    copy_contract::CopyCallEvent, default_uses::ArgumentSource, effect_identity::InvocationContext,
    model::Callable,
};
use ril_syntax::ast::{ParameterMode, PatternKind};

impl Replay<'_> {
    pub(super) fn call_input_terminal_operand(
        &self,
        event: &CopyCallEvent,
        source: &Expr,
        context: InvocationContext,
    ) -> Check<bool> {
        let ExprKind::Call { arguments, .. } = &source.kind else {
            return Ok(false);
        };
        let Some(target) = event.target else {
            return Ok(false);
        };
        let function = self.function(target)?;
        if !function.syntax.generics.is_empty()
            || function.syntax.parameters.len() != 1
            || function.syntax.parameters[0].mode != ParameterMode::Read
            || arguments.len() != 1
            || arguments[0].mode != ParameterMode::Read
        {
            return Ok(false);
        }
        let operand = &arguments[0].value;
        let ExprKind::Call {
            callee,
            arguments: panic_arguments,
        } = &operand.kind
        else {
            return Ok(false);
        };
        let canonical = match &callee.kind {
            ExprKind::Name(name) => matches!(name.as_str(), "panic" | "Prelude::panic"),
            ExprKind::Path(path) => path == &["Prelude", "panic"],
            _ => false,
        };
        if !canonical
            || self.facts.operations.contains_key("panic")
            || self.facts.operations.contains_key("Prelude::panic")
            || panic_arguments.len() != 1
            || panic_arguments[0].mode != ParameterMode::Read
            || panic_arguments[0].label.is_some()
            || !matches!(
                panic_arguments[0].value.kind,
                ExprKind::Literal(Literal::String(_) | Literal::RawString(_))
            )
        {
            return Ok(false);
        }
        require(
            self.facts.copy_call_events.len() <= LIMIT && self.facts.call_arguments.len() <= LIMIT,
            "terminal Source proof exceeds its event admission",
        )?;
        let outer_callee = event
            .callee_expression
            .ok_or_else(|| "terminal outer call lost its actual callee".to_owned())?;
        let public = self
            .facts
            .expressions
            .get(outer_callee)
            .and_then(|value| value.value.signature.as_ref())
            .ok_or_else(|| "terminal call lost its original public signature".to_owned())?;
        require(
            public.len() == 1 && public[0].mode == ParameterMode::Read,
            "terminal call changed its public arity or mode",
        )?;
        if let Some(label) = &arguments[0].label {
            require(
                matches!(&public[0].pattern.kind, PatternKind::Name(name) if name == label),
                "terminal operand has an invalid public label",
            )?;
        }
        let token = self.terminal_operand_token(event, operand, context, false)?;
        require(
            self.facts.expressions[token].value.ty == Ty::Never,
            "terminal outer operand still has a normal result",
        )?;
        let candidates: Vec<_> = self
            .facts
            .copy_call_events
            .iter()
            .filter(|inner| {
                inner.matches_source(operand)
                    && inner.owner == context.owner
                    && inner.parent == context.invocation
                    && inner
                        .callee_expression
                        .is_some_and(|index| outer_callee < index && index < token)
                    && self.facts.invocation_expressions.iter().any(|row| {
                        Some(row.expression) == inner.callee_expression && row.context == context
                    })
            })
            .collect();
        let [inner] = candidates.as_slice() else {
            return Err("terminal operand lacks its unique actual intrinsic call".into());
        };
        let callee_token = inner.callee_expression.unwrap();
        let observed = self
            .facts
            .expressions
            .get(callee_token)
            .ok_or_else(|| "terminal intrinsic callee is outside its arena".to_owned())?;
        require(
            inner.target.is_none()
                && observed.source_id.is_some()
                && observed.source_id == callee.hir_id
                && observed.value.sources.is_empty()
                && matches!(observed.value.callables.as_slice(), [Callable::Builtin(name)]
                if matches!(name.as_str(), "panic" | "Prelude::panic")),
            "terminal Source is not the actual unshadowed panic intrinsic",
        )?;
        let message =
            self.terminal_operand_token(inner, &panic_arguments[0].value, context, true)?;
        require(
            callee_token < message
                && message < token
                && self.facts.expressions[message].value.ty == Ty::Str,
            "terminal intrinsic message lost its literal evaluation",
        )?;
        Ok(true)
    }

    fn terminal_operand_token(
        &self,
        event: &CopyCallEvent,
        syntax: &Expr,
        context: InvocationContext,
        complete: bool,
    ) -> Check<usize> {
        let preparations: Vec<_> = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id)
            .collect();
        let [preparation] = preparations.as_slice() else {
            return Err("terminal operand lacks its unique actual preparation".into());
        };
        require(
            preparation.target == event.target
                && preparation.evaluation_complete == complete
                && preparation.slots == [ArgumentSource::Supplied]
                && preparation.supplied.len() == 1,
            "terminal preparation changed its source, arity or outcome",
        )?;
        let supplied = preparation
            .supplied
            .get(&0)
            .ok_or_else(|| "terminal preparation lost its real supplied root".to_owned())?;
        let observed = self
            .facts
            .expressions
            .get(supplied.expression)
            .ok_or_else(|| "terminal supplied root is outside its arena".to_owned())?;
        require(
            supplied.allocation_epoch <= self.facts.allocation_history.len()
                && observed.source_id.is_some()
                && observed.source_id == syntax.hir_id
                && self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|row| {
                        row.expression == supplied.expression
                            && row.context == context
                            && row.argument_of == Some((event.id, 0))
                    })
                    .count()
                    == 1,
            "terminal root belongs to another operand or invocation",
        )?;
        Ok(supplied.expression)
    }
}
