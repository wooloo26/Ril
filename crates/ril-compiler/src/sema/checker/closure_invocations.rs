//! Dynamic closure calls keep their object and creation ancestry independently
//! of shared lexical sites. This evidence does not execute a latent body twice.
use super::super::{
    copy_contract::CopyInvocationStatus,
    effect_identity::{ClosureInvocation, ClosureInvocationId},
};
use super::*;
use crate::sema::application_effect::{CallableEntry, EntryOrigin};
use crate::sema::source_reception;

struct ClosureCallContext<'a> {
    caller: &'a mut Frame,
    result_source: Option<source_reception::Target>,
}

impl Checker {
    pub(super) fn invoke_closure_packets_from(
        &mut self,
        id: usize,
        args: std::sync::Arc<Vec<crate::sema::application_effect::EntryArgument>>,
        callee: Option<std::sync::Arc<EvaluatedValue>>,
        span: Span,
        caller: &mut Frame,
        origin: EntryOrigin,
    ) -> Value {
        self.invoke_recorded_closure(
            id,
            args,
            callee,
            span,
            ClosureCallContext {
                caller,
                result_source: None,
            },
            origin,
        )
    }

    pub(super) fn invoke_closure_probe(
        &mut self,
        id: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        caller: &mut Frame,
        result_source: Option<source_reception::Target>,
    ) -> Value {
        let args = match self.uncaptured_entry_arguments(args) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("closure probe input admission: {error}"));
                return Value::scalar(Ty::Unknown, None, CauseId(0));
            }
        };
        self.invoke_recorded_closure(
            id,
            args,
            None,
            span,
            ClosureCallContext {
                caller,
                result_source,
            },
            EntryOrigin::DeclarationProbe,
        )
    }

    pub(super) fn invoke_closure_signature(
        &mut self,
        id: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        caller: &mut Frame,
        source: std::sync::Arc<crate::sema::application_effect::SignatureProbeSource>,
    ) -> Value {
        let args = match self.uncaptured_entry_arguments(args) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("closure signature input admission: {error}"));
                return Value::scalar(Ty::Unknown, None, CauseId(0));
            }
        };
        self.invoke_recorded_closure(
            id,
            args,
            None,
            span,
            ClosureCallContext {
                caller,
                result_source: None,
            },
            EntryOrigin::SignatureProbe(source),
        )
    }

    fn invoke_recorded_closure(
        &mut self,
        closure: usize,
        args: std::sync::Arc<Vec<crate::sema::application_effect::EntryArgument>>,
        callee: Option<std::sync::Arc<EvaluatedValue>>,
        site: Span,
        context: ClosureCallContext<'_>,
        origin: EntryOrigin,
    ) -> Value {
        let ClosureCallContext {
            caller,
            mut result_source,
        } = context;
        let parent_closure = self.closure_invocation_stack.last().copied();
        let probe = matches!(
            origin,
            EntryOrigin::DeclarationProbe | EntryOrigin::SignatureProbe(_)
        ) || parent_closure
            .is_some_and(|parent| self.closure_invocations[parent.0 as usize].probe);
        if !self.application_effect.admit(1 + args.len()) {
            self.unsupported(site, "callable input recording exhausted its work bound");
            return Value::scalar(Ty::Unknown, None, CauseId(0));
        }
        let arguments = match self.freeze_entry_arguments(&args) {
            Ok(arguments) => arguments,
            Err(error) => {
                self.unsupported(site, format!("closure entry admission: {error}"));
                return Value::scalar(Ty::Unknown, None, CauseId(0));
            }
        };
        let callee = match self.freeze_entry_callee(callee, site) {
            Ok(callee) => callee,
            Err(error) => {
                self.unsupported(site, format!("closure entry callee admission: {error}"));
                return Value::scalar(Ty::Unknown, None, CauseId(0));
            }
        };
        if result_source.is_none()
            && !probe
            && self
                .lambda_contract(closure)
                .is_some_and(|contract| contract.return_type.is_none())
            && let Some(packet) = &callee
            && (packet.birth_coordinates().observation.is_some()
                || matches!(origin, EntryOrigin::Application(_)))
        {
            match self.packet_callable_result_target(packet, site) {
                Ok(target) => result_source = target,
                Err(error) => {
                    self.unsupported(site, format!("closure callee result Source: {error}"));
                    return Value::scalar(Ty::Unknown, None, CauseId(0));
                }
            }
        }
        let entry = CallableEntry {
            callee,
            parent: self.application_effect.current_activation(),
            caller_context: self.invocation_context(caller.callable_owner),
            origin,
            allocation_epoch: self.recency_moves.len(),
            arguments: arguments.clone(),
        };
        let id = ClosureInvocationId(self.closure_invocations.len() as u32);
        self.closure_invocations.push(ClosureInvocation {
            id,
            summary: None,
            entry,
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
        let result =
            self.invoke_closure_unrecorded(closure, &arguments, site, caller, result_source);
        assert_eq!(self.closure_invocation_stack.pop(), Some(id));
        result
    }

    pub(super) fn complete_closure_invocation(&mut self) {
        if let Some(id) = self.closure_invocation_stack.last().copied() {
            let status = &mut self.closure_invocations[id.0 as usize].status;
            if *status == CopyInvocationStatus::Incomplete {
                *status = CopyInvocationStatus::Completed;
            }
            if !matches!(
                self.closure_invocations[id.0 as usize].entry.origin,
                EntryOrigin::Application(_)
            ) {
                return;
            }
            if !self
                .default_uses
                .len()
                .checked_mul(16)
                .is_some_and(|cost| self.application_effect.admit(cost))
            {
                let span = self.closure_invocations[id.0 as usize].site;
                self.unsupported(
                    span,
                    "default closure entry completion exceeds its work bound",
                );
                return;
            }
            let call = &self.closure_invocations[id.0 as usize];
            let closure = &self.closures[call.closure];
            for default in &mut self.default_uses {
                if super::super::default_uses::closure_entry_uses(default, call, closure) {
                    default.status = match (default.status, call.status) {
                        (CopyInvocationStatus::Rejected, _)
                        | (_, CopyInvocationStatus::Rejected) => CopyInvocationStatus::Rejected,
                        (CopyInvocationStatus::Unsupported, _)
                        | (_, CopyInvocationStatus::Unsupported) => {
                            CopyInvocationStatus::Unsupported
                        }
                        (_, status) => status,
                    };
                }
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
