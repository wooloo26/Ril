//! Dynamic closure calls keep their object and creation ancestry independently
//! of shared lexical sites. This evidence does not execute a latent body twice.
use super::super::{
    copy_contract::CopyInvocationStatus,
    effect_identity::{ClosureInvocation, ClosureInvocationId},
};
use super::*;

impl Checker {
    pub(super) fn invoke_closure(
        &mut self,
        id: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        caller: &mut Frame,
    ) -> Value {
        self.invoke_recorded_closure(id, args, span, caller, false)
    }

    pub(super) fn invoke_closure_probe(
        &mut self,
        id: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        caller: &mut Frame,
    ) -> Value {
        self.invoke_recorded_closure(id, args, span, caller, true)
    }

    fn invoke_recorded_closure(
        &mut self,
        closure: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        site: Span,
        caller: &mut Frame,
        probe: bool,
    ) -> Value {
        let id = ClosureInvocationId(self.closure_invocations.len() as u32);
        let parent_closure = self.closure_invocation_stack.last().copied();
        let probe = probe
            || parent_closure
                .is_some_and(|parent| self.closure_invocations[parent.0 as usize].probe);
        self.closure_invocations.push(ClosureInvocation {
            id,
            source_event: (!probe)
                .then(|| self.channel_source_event(caller))
                .flatten(),
            caller_activation: caller.owner,
            activation: None,
            closure,
            parent_named: self.copy_invocation_stack.last().copied(),
            parent_closure,
            caller_owner: caller.callable_owner,
            site,
            probe,
            budget_validation: self.budget_validation_depth > 0,
            status: CopyInvocationStatus::Incomplete,
        });
        self.closure_invocation_stack.push(id);
        let result = self.invoke_closure_unrecorded(closure, args, site, caller);
        assert_eq!(self.closure_invocation_stack.pop(), Some(id));
        result
    }

    pub(super) fn complete_closure_invocation(&mut self) {
        if let Some(id) = self.closure_invocation_stack.last() {
            let status = &mut self.closure_invocations[id.0 as usize].status;
            if *status == CopyInvocationStatus::Incomplete {
                *status = CopyInvocationStatus::Completed;
            }
        }
    }

    pub(super) fn fail_closure_invocations(&mut self, rejected: bool) {
        for id in &self.closure_invocation_stack {
            let status = &mut self.closure_invocations[id.0 as usize].status;
            if rejected {
                *status = CopyInvocationStatus::Rejected;
            } else if *status != CopyInvocationStatus::Rejected {
                *status = CopyInvocationStatus::Unsupported;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repeated_diagnostics_do_not_leave_a_later_closure_call_completed() {
        let parsed = ril_syntax::parse(
            "fn example(){let callback=\\number:int->number+true;let first=callback(1);let second=callback(2)}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        assert!(checker.closure_invocations.len() >= 3);
        assert!(
            checker
                .closure_invocations
                .iter()
                .all(|call| call.status == CopyInvocationStatus::Rejected)
        );
        assert!(checker.closure_invocation_stack.is_empty());
    }
}
