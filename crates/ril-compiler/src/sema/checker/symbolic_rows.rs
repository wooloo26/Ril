//! Unknown callable bounds describe possible use, separately from actual
//! concrete state. Every use retains its original callee occurrence.
use super::*;
use crate::sema::application_effect::EntryOrigin;
use ril_compiler_core::ids::EvaluationOccurrenceId;

fn named_constraint(
    bound: &CallableBound,
    target: BindingId,
    required: Mode,
    bindings: &[BindingInfo],
) -> (bool, bool, bool) {
    let (mut state, mut named, mut allows) = (false, false, false);
    for annotation in &bound.annotations {
        if annotation.kind != AnnotationKind::Capability {
            continue;
        }
        state = true;
        let text = annotation.text.trim();
        if text == "&closure" {
            allows |= bindings
                .get(target)
                .is_some_and(|binding| binding.owner != ScopeId(0));
        }
        let Some(inner) = text
            .strip_prefix("&{")
            .and_then(|text| text.strip_suffix('}'))
        else {
            continue;
        };
        for item in inner.split(',').map(str::trim) {
            if item == "closure" || item.starts_with("closure ") {
                continue;
            }
            let (mode, name) = if let Some(name) = item.strip_prefix("^mut ") {
                (Mode::Retain, name.trim())
            } else if let Some(name) = item.strip_prefix("mut ") {
                (Mode::Write, name.trim())
            } else {
                (Mode::Read, item)
            };
            if bound.source.is_some()
                && !bound.typing_environment.is_poisoned()
                && bound.typing_environment.contract_bindings.get(name) == Some(&target)
            {
                named = true;
                allows |= mode >= required;
            }
        }
    }
    (state, named, allows)
}

impl Checker {
    pub(super) fn record_symbolic_row_use(
        &self,
        callee: &Value,
        origin: &EntryOrigin,
        frame: &mut Frame,
    ) {
        let observed = match origin {
            EntryOrigin::Application(id) => self
                .copy_call_events
                .get(id.0 as usize)
                .and_then(|event| event.callee_expression)
                .map(|id| EvaluationOccurrenceId(id as u32)),
            // Generated callbacks need their own entered-origin proof before
            // they can justify a declaration row. A projected value alone
            // supplies no evidence that its callback was actually entered.
            _ => None,
        };
        let Some(observed) = observed else { return };
        if self
            .application_effect
            .contexts
            .get(observed.0 as usize)
            .is_none_or(|row| row.context.budget_validation)
        {
            return;
        }
        let Some(original) = self.application_effect.expressions.get(observed.0 as usize) else {
            return;
        };
        if original.value.callable_bounds == callee.callable_bounds
            && original
                .value
                .callables
                .iter()
                .any(|code| matches!(code, Callable::Symbolic(..)))
            && original.value.callback_parameters.iter().any(|id| {
                self.bindings
                    .get(*id)
                    .is_some_and(|binding| binding.parameter)
            })
        {
            frame.obligations.symbolic_uses.insert(observed);
        }
    }

    pub(super) fn symbolic_named_use(
        &self,
        obligations: &Obligations,
        target: BindingId,
        required: Mode,
    ) -> bool {
        obligations.symbolic_uses.iter().any(|observed| {
            let Some(value) = self.application_effect.expressions.get(observed.0 as usize) else {
                return false;
            };
            if self
                .application_effect
                .contexts
                .get(observed.0 as usize)
                .is_none_or(|row| row.context.budget_validation)
            {
                return false;
            }
            let mut named = false;
            for bound in &value.value.callable_bounds {
                let (state, explicit, allows) =
                    named_constraint(bound, target, required, &self.bindings);
                named |= explicit;
                if state && !allows {
                    return false;
                }
            }
            named
        })
    }
}
