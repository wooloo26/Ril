//! Invocation-specific copy evidence. Records remain separate at identical
//! source spans, and early returns cannot leave behind a successful certificate.
use super::super::{copy_contract::*, copy_templates::InstanceId};
use super::*;

impl Checker {
    pub(super) fn finish_copy_templates(&mut self) {
        use super::super::{copy_template_closure as closure, copy_templates as domain};
        let owners = closure::template_owners(&self.copy_boundaries, &self.copy_invocations);
        if owners.is_empty() {
            return;
        }
        let mut templates = BTreeMap::new();
        for &owner in &owners {
            let public = self.functions.iter().any(|info| {
                info.definition == owner && info.syntax.visibility == Visibility::Public
            });
            let escaped = self
                .copy_references
                .iter()
                .any(|reference| reference.target == owner && reference.direct_call.is_none());
            let calls: Vec<_> = self
                .copy_invocations
                .iter()
                .filter(|call| !call.declaration_probe && call.target == owner)
                .collect();
            let indirect = calls.iter().any(|call| !call.direct);
            let sites = calls
                .iter()
                .map(|call| domain::Site {
                    owner: call.caller,
                    target: owner,
                    source: (call.span.file.0, call.span.start, call.span.end),
                })
                .collect();
            let mut dependencies = BTreeSet::new();
            for probe in self
                .copy_invocations
                .iter()
                .filter(|call| call.declaration_probe && call.target == owner)
            {
                for call in self
                    .copy_invocations
                    .iter()
                    .filter(|call| !call.declaration_probe && owners.contains(&call.target))
                {
                    if self.copy_executed_within(probe.id, call.id) {
                        dependencies.insert(call.target);
                    }
                }
            }
            templates.insert(
                owner,
                domain::Template {
                    public,
                    escaped: escaped || indirect,
                    sites,
                    dependencies,
                },
            );
        }
        let result = closure::instances(
            &templates,
            &self.copy_boundaries,
            &self.copy_invocations,
            &self.copy_call_events,
            &self.resource_clones,
        )
        .and_then(|actual| {
            domain::close(&templates, &actual.actual)
                .map(|certificate| (certificate, actual.discharges))
                .map_err(|error| format!("{error:?}"))
        });
        match result {
            Ok((certificate, discharges)) => {
                self.copy_template_closure = Some(CopyTemplateClosure {
                    templates,
                    certificate,
                    discharges,
                })
            }
            Err(reason) => {
                let span = self
                    .copy_boundaries
                    .iter()
                    .find(|boundary| boundary.template)
                    .unwrap()
                    .span;
                let callable = self.copy_boundaries.iter().any(|boundary| {
                    boundary.template
                        && boundary.constituents.iter().any(|part| {
                            matches!(
                            part.qualification,
                            super::super::copy_eligibility::Constituent::Deferred(
                                super::super::copy_eligibility::AbstractMember::CallableEnvironment
                            )
                        )
                        })
                });
                self.unsupported(span,format!("{}copy template requires every private direct call instance and consumer proof: {reason}",if callable {"callable environment "}else{"generic or row "}));
            }
        }
    }
    pub(super) fn record_copy_references(&mut self, value: &Value, span: Span, frame: &Frame) {
        for callable in &value.callables {
            if let Callable::Named(index) = callable {
                self.copy_references.push(CopyReference {
                    id: CopyReferenceId(self.copy_references.len() as u32),
                    expression: self.application_effect.expressions.len(),
                    owner: frame.callable_owner,
                    parent: self.copy_invocation_stack.last().copied(),
                    target: self.functions[*index].definition,
                    span,
                    direct_call: None,
                });
            }
        }
    }

    pub(super) fn reserve_copy_call_event(
        &mut self,
        call: &Expr,
        frame: &Frame,
    ) -> CopyCallEventId {
        let id = CopyCallEventId(self.copy_call_events.len() as u32);
        self.copy_call_events.push(CopyCallEvent {
            id,
            source_id: call.hir_id,
            callee_expression: None,
            result_expression: None,
            owner: frame.callable_owner,
            parent: self.copy_invocation_stack.last().copied(),
            span: call.span,
            target: None,
            direct: false,
            copy_operation: None,
            references: vec![],
        });
        id
    }

    pub(super) fn complete_copy_call_callee(
        &mut self,
        id: CopyCallEventId,
        syntax: &Expr,
        value: &Value,
        reference_start: usize,
        callee_expression: Option<usize>,
        frame: &Frame,
    ) {
        let parent = self.copy_invocation_stack.last().copied();
        let target = match value.callables.as_slice() {
            [Callable::Named(index)] => Some(self.functions[*index].definition),
            _ => None,
        };
        let mut parts = 1;
        let mut base = syntax;
        while let ExprKind::Generic { base: inner, .. } = &base.kind {
            parts += 1;
            base = inner;
        }
        let name = match &base.kind {
            ExprKind::Name(name) => Some(name.clone()),
            ExprKind::Path(path) => Some(path.join("::")),
            _ => None,
        };
        let references = &mut self.copy_references[reference_start..];
        // This interval belongs only to this callee evaluation, never a prior
        // equal-span expression. A direct Name/Generic chain evaluates exactly
        // one matching callable expression per layer; unexpected nested uses
        // fail closed instead of inheriting directness.
        let direct = target.is_some()
            && matches!(value.callables.as_slice(), [Callable::Named(index)]
                if name.as_ref() == Some(&self.functions[*index].syntax.name))
            && references.len() == parts
            && references.iter().all(|reference| {
                Some(reference.target) == target
                    && reference.owner == frame.callable_owner
                    && reference.parent == parent
                    && reference.direct_call.is_none()
            });
        if direct {
            for reference in references.iter_mut() {
                reference.direct_call = Some(id);
            }
        }
        let event = &mut self.copy_call_events[id.0 as usize];
        event.callee_expression = callee_expression;
        event.target = target;
        event.direct = direct;
        event.copy_operation = match value.callables.as_slice() {
            [Callable::Builtin(name)] if matches!(name.as_str(), "clone" | "Prelude::clone") => {
                Some(CopyMode::Mutable)
            }
            [Callable::Builtin(name)]
                if matches!(name.as_str(), "clone_immut" | "Prelude::clone_immut") =>
            {
                Some(CopyMode::Immutable)
            }
            _ => None,
        };
        event.references = references.iter().map(|reference| reference.id).collect();
    }

    fn copy_executed_within(&self, root: InstanceId, mut child: InstanceId) -> bool {
        loop {
            if child == root {
                return true;
            }
            let invocation = &self.copy_invocations[child.0 as usize];
            if invocation.declaration_probe {
                return false;
            }
            let Some(parent) = invocation.parent else {
                return false;
            };
            child = parent;
        }
    }
    pub(super) fn copy_value_snapshot(&self, value: &Value) -> CopyValueSnapshot {
        let (nodes, relations) = self.copy_graph_snapshot(value);
        CopyValueSnapshot {
            value: value.clone(),
            nodes,
            relations,
        }
    }

    pub(super) fn complete_copy_invocation(&mut self) {
        if let Some(id) = self.copy_invocation_stack.last() {
            let status = &mut self.copy_invocations[id.0 as usize].status;
            if *status == CopyInvocationStatus::Incomplete {
                *status = CopyInvocationStatus::Completed;
            }
        }
    }

    pub(super) fn fail_copy_invocations(&mut self, rejected: bool) {
        // Diagnostics may be deduplicated by source span. Each actual call
        // still failed and must not borrow another instance's successful row.
        for id in &self.copy_invocation_stack {
            let status = &mut self.copy_invocations[id.0 as usize].status;
            if rejected {
                *status = CopyInvocationStatus::Rejected;
            } else if *status != CopyInvocationStatus::Rejected {
                *status = CopyInvocationStatus::Unsupported;
            }
        }
    }

    pub(super) fn invoke_named(
        &mut self,
        id: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        caller: Option<&mut Frame>,
        verifying: bool,
    ) -> Value {
        use crate::sema::application_effect::EntryOrigin;
        let origin = if verifying {
            EntryOrigin::DeclarationProbe
        } else {
            caller
                .as_ref()
                .and_then(|frame| frame.copy_call_event)
                .map(EntryOrigin::Application)
                .unwrap_or(EntryOrigin::Unresolved)
        };
        self.invoke_named_from(id, args, span, caller, origin)
    }

    pub(super) fn invoke_named_from(
        &mut self,
        id: usize,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        mut caller: Option<&mut Frame>,
        origin: crate::sema::application_effect::EntryOrigin,
    ) -> Value {
        use crate::sema::application_effect::{CallableEntry, EntryOrigin};
        let verifying = origin == EntryOrigin::DeclarationProbe;
        if !self.application_effect.admit(1 + args.len()) {
            self.unsupported(
                span,
                "named callable input recording exhausted its work bound",
            );
            return Value::scalar(Ty::Unknown, None, CauseId(0));
        }
        let supplied_event = caller
            .as_deref_mut()
            .and_then(|frame| frame.copy_call_event.take());
        let source_event = match origin {
            EntryOrigin::Application(id) if supplied_event == Some(id) => Some(id),
            _ => None,
        };
        let caller_owner = caller.as_ref().and_then(|frame| frame.callable_owner);
        let target = self.functions[id].definition;
        let direct = source_event
            .and_then(|event| self.copy_call_events.get(event.0 as usize))
            .is_some_and(|event| {
                event.direct
                    && event.target == Some(target)
                    && event.owner == caller_owner
                    && event.parent == self.copy_invocation_stack.last().copied()
                    && event.span == span
            });
        let instance = InstanceId(self.copy_invocations.len() as u32);
        let mut boundaries = BTreeSet::new();
        let arguments = args
            .iter()
            .map(|(mode, value, _)| {
                boundaries.extend(self.pending_copy_dependencies(value));
                let mode = match mode {
                    ParameterMode::Read => Mode::Read,
                    ParameterMode::Mut => Mode::Write,
                    ParameterMode::SharedMut => Mode::Retain,
                };
                (mode, self.copy_value_snapshot(value))
            })
            .collect();
        self.copy_invocations.push(CopyInvocation {
            id: instance,
            entry: CallableEntry {
                parent: self.application_effect.current_activation(),
                caller_context: self.invocation_context(caller_owner),
                origin,
                allocation_epoch: self.recency_moves.len(),
                arguments,
            },
            parent: self.copy_invocation_stack.last().copied(),
            caller: caller.as_ref().and_then(|frame| frame.definition),
            caller_owner,
            caller_activation: caller.as_ref().map(|frame| frame.owner),
            target,
            span,
            declaration_probe: verifying,
            direct,
            source_event,
            boundaries,
            result: None,
            resource_copies: vec![],
            status: CopyInvocationStatus::Incomplete,
        });
        self.copy_invocation_stack.push(instance);
        let diagnostics = self.diagnostics.len();
        let unsupported = self.unsupported.len();
        let boundary_start = self.copy_boundaries.len();
        let result = self.invoke_named_unrecorded(id, args, span, caller, verifying);
        assert_eq!(self.copy_invocation_stack.pop(), Some(instance));
        let returned = self.copy_value_snapshot(&result);
        let dependencies = self.pending_copy_dependencies(&result);
        let executed: Vec<_> = self.copy_boundaries[boundary_start..]
            .iter()
            .filter(|boundary| {
                boundary
                    .invocation
                    .is_some_and(|id| self.copy_executed_within(instance, id))
            })
            .map(|boundary| boundary.id)
            .collect();
        let record = &mut self.copy_invocations[instance.0 as usize];
        record.result = Some(returned);
        record.boundaries.extend(dependencies);
        record.boundaries.extend(executed);
        if self.diagnostics[diagnostics..]
            .iter()
            .any(|diagnostic| diagnostic.severity == Severity::Error)
        {
            record.status = CopyInvocationStatus::Rejected;
        } else if self.unsupported.len() != unsupported
            && record.status != CopyInvocationStatus::Rejected
        {
            record.status = CopyInvocationStatus::Unsupported;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn failed_or_unresolved_invocations_never_keep_a_completed_status() {
        for (source, expected) in [
            (
                "fn bad()->int{missing}\nfn example(){let _=bad()}",
                CopyInvocationStatus::Rejected,
            ),
            (
                "fn bad()->int{bad()}\nfn example(){let _=bad()}",
                CopyInvocationStatus::Unsupported,
            ),
        ] {
            let syntax = ril_syntax::parse(source);
            assert!(syntax.is_ok());
            let mut checker = Checker::new(FileId(0));
            checker.run(&syntax.program);
            let target = checker
                .functions
                .iter()
                .find(|function| function.syntax.name == "bad")
                .unwrap()
                .definition;
            let records: Vec<_> = checker
                .copy_invocations
                .iter()
                .filter(|record| record.target == target)
                .collect();
            assert!(!records.is_empty());
            assert!(
                records.iter().all(|record| record.status == expected),
                "{source}: {records:?}"
            );
            assert!(checker.copy_invocation_stack.is_empty());
        }
    }

    #[test]
    fn one_success_at_a_shared_helper_site_does_not_hide_repeated_resource_failures() {
        let source = "fn duplicate<T>(source:T)->T{clone(source)}\nfn forward<T>(source:T)->T{duplicate(source)}\nfn example(file:File::Handle){let _=forward(1);let _=forward(file);let _=forward(file);let _=forward(2)}";
        let syntax = ril_syntax::parse(source);
        assert!(syntax.is_ok());
        let mut checker = Checker::new(FileId(0));
        checker.run(&syntax.program);
        let target = checker
            .functions
            .iter()
            .find(|function| function.syntax.name == "duplicate")
            .unwrap()
            .definition;
        let calls: Vec<_> = checker
            .copy_invocations
            .iter()
            .filter(|call| !call.declaration_probe && call.target == target)
            .collect();
        let good: Vec<_> = calls
            .iter()
            .filter(|call| matches!(call.entry.arguments[0].1.value.ty, Ty::Int(_)))
            .collect();
        let bad: Vec<_> = calls
            .iter()
            .filter(|call| call.entry.arguments[0].1.value.ty == Ty::Named("File::Handle".into()))
            .collect();
        assert_eq!((good.len(), bad.len()), (2, 2));
        assert!(
            good.iter()
                .all(|call| call.status == CopyInvocationStatus::Completed)
        );
        assert!(
            bad.iter()
                .all(|call| call.status == CopyInvocationStatus::Rejected)
        );
        assert!(calls.iter().all(|call| call.span == good[0].span));
        assert_ne!(bad[0].id, bad[1].id);
    }
}
