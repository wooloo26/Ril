use super::*;
use crate::sema::application_effect::{EntryArgument, EntryOrigin};
use crate::sema::source_reception;
use crate::sema::source_types::SourceTypesError;
use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum AnnotationCheck {
    Declaration,
    Invocation,
}

impl Checker {
    pub(super) fn invoke_generated_values(
        &mut self,
        callee: &Value,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        // A generated callback is not the enclosing written application's
        // parameter list. Only the packet-native application entry may claim it.
        let origin = crate::sema::application_effect::EntryOrigin::Unresolved;
        self.invoke_generated_values_from(callee, args, span, frame, origin)
    }

    pub(super) fn invoke_generated_values_from(
        &mut self,
        callee: &Value,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        frame: &mut Frame,
        origin: crate::sema::application_effect::EntryOrigin,
    ) -> Value {
        let epoch = self.recency_moves.len();
        if !self.application_effect.admit(2) {
            self.unsupported(span, "generated callee wrapper admission exhausted");
            return Value::scalar(Ty::Unknown, None, CauseId(0));
        }
        let callee = match self
            .application_effect
            .with_work(|work| crate::sema::evaluated::transport_value_at(callee, &[], 0, 0, work))
        {
            Ok(value) => Arc::new(EvaluatedValue::new(value, epoch)),
            Err(error) => {
                self.unsupported(span, format!("generated callee admission: {error}"));
                return Value::scalar(Ty::Unknown, None, CauseId(0));
            }
        };
        self.invoke_generated_arguments_from(callee, args, span, frame, origin)
    }

    pub(super) fn invoke_generated_arguments_from(
        &mut self,
        callee: Arc<EvaluatedValue>,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        frame: &mut Frame,
        origin: EntryOrigin,
    ) -> Value {
        let args = match self.uncaptured_entry_arguments(args) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("generated input admission: {error}"));
                return Value::scalar(Ty::Unknown, None, CauseId(0));
            }
        };
        self.invoke_packets_from(callee, args, span, frame, origin)
            .into_current(&self.recency_moves)
    }

    pub(super) fn invoke_application_packet(
        &mut self,
        callee: Arc<EvaluatedValue>,
        args: Arc<Vec<EntryArgument>>,
        event: crate::sema::copy_contract::CopyCallEventId,
        span: Span,
        frame: &mut Frame,
    ) -> EvaluatedValue {
        self.invoke_packets_from(callee, args, span, frame, EntryOrigin::Application(event))
    }

    pub(super) fn invoke_packets_from(
        &mut self,
        callee: Arc<EvaluatedValue>,
        args: Arc<Vec<EntryArgument>>,
        span: Span,
        frame: &mut Frame,
        origin: EntryOrigin,
    ) -> EvaluatedValue {
        self.invoke_target_packets_from(callee, args, span, frame, origin, None)
    }

    pub(super) fn invoke_target_packets_from(
        &mut self,
        callee: Arc<EvaluatedValue>,
        args: Arc<Vec<EntryArgument>>,
        span: Span,
        frame: &mut Frame,
        origin: EntryOrigin,
        target: Option<&Callable>,
    ) -> EvaluatedValue {
        let current = match self.read_evaluation_packet(&callee, span) {
            Ok(value) => value,
            Err(error) => {
                self.unsupported(span, format!("callee packet admission: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        self.require_recorded_public_call_inputs(&current, span, frame);
        let Some(origin) = self.application_effect.enter_call(origin) else {
            self.unsupported(span, "call entry budget exhausted before invocation");
            return EvaluatedValue::unobserved(
                Value::scalar(Ty::Unknown, None, CauseId(0)),
                self.recency_moves.len(),
                false,
            );
        };
        let result = self.invoke_packets_unrecorded(callee, args, span, frame, &origin, target);
        self.application_effect.leave_call(&origin);
        result
    }
    fn invoke_packets_unrecorded(
        &mut self,
        callee_packet: Arc<EvaluatedValue>,
        argument_packets: Arc<Vec<EntryArgument>>,
        span: Span,
        frame: &mut Frame,
        origin: &crate::sema::application_effect::EntryOrigin,
        target: Option<&Callable>,
    ) -> EvaluatedValue {
        // The syntax token belongs to this invocation only. Builtin/closure
        // callbacks and signature probes must not inherit a caller's token.
        let copy_call_event = frame.copy_call_event.take();
        let saved_callee = match self.resolve_named_callee_packet(&callee_packet, span) {
            Ok(packet) => packet,
            Err(error) => {
                self.unsupported(span, format!("named callee packet admission: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        let resolved_callee = match self.read_evaluation_packet(&saved_callee, span) {
            Ok(value) => value,
            Err(error) => {
                self.unsupported(span, format!("callee packet read: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        let callee = &resolved_callee;
        let args = match self.entry_values(&argument_packets) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("input packet read: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        if !callee.callback_parameters.is_empty() {
            self.effect_callback_uses
                .push(super::super::effect_identity::CallbackInvocation {
                    site: span,
                    owner: frame.callable_owner,
                    parameter_bindings: callee.callback_parameters.clone(),
                    targets: callee.callables.clone(),
                });
        }
        if callee
            .variant_tag
            .as_ref()
            .and_then(|name| self.constructors.get(name))
            .is_some_and(|constructor| !constructor.has_payload)
        {
            self.error(
                "E0353",
                span,
                "a nullary constructor tag is data and cannot be called",
                [callee.cause],
            );
            return EvaluatedValue::new(self.unit(span), self.recency_moves.len());
        }
        if matches!(
            self.expanded(&callee.ty, &mut BTreeSet::new()),
            Ty::Optional(_)
        ) {
            self.error(
                "E0310",
                span,
                "optional callable requires a proven Some refinement before invocation",
                [callee.cause],
            );
            return EvaluatedValue::new(self.unit(span), self.recency_moves.len());
        }
        if callee.ty == Ty::Never {
            return self
                .clone_evaluation_packet(&saved_callee, span)
                .unwrap_or_else(|_| {
                    EvaluatedValue::unobserved(callee.clone(), self.recency_moves.len(), false)
                });
        }
        if !matches!(
            self.expanded_at(&callee.ty, span.file),
            Ty::Callable(..) | Ty::Unknown
        ) && !callee.callables.is_empty()
        {
            self.error(
                "E0338",
                span,
                "the public value type does not expose a callable representation",
                [callee.cause],
            );
            return EvaluatedValue::new(self.unit(span), self.recency_moves.len());
        }
        if let Some((_, value, _)) = args.iter().find(|(_, value, _)| value.ty == Ty::Never) {
            return EvaluatedValue::new(value.clone(), self.recency_moves.len());
        }
        if target.is_none() && self.foreign_callback_depth > 0 && callee.callables.len() > 1 {
            return self.invoke_foreign_target_packets(
                &saved_callee,
                argument_packets,
                span,
                frame,
                origin,
            );
        }
        let previous_callback = frame.callback_call;
        frame.callback_call = callee
            .callback_parameters
            .iter()
            .any(|id| frame.anonymous || self.bindings[*id].owner == frame.owner);
        if let Some(parameters) = &callee.signature {
            for ((mode, value, arg_span), parameter) in args.iter().zip(&parameters.parameters) {
                if *mode != parameter.mode {
                    self.error(
                        if *mode != ParameterMode::Read && parameter.mode != ParameterMode::Read {
                            "E0406"
                        } else {
                            "E0405"
                        },
                        *arg_span,
                        "callable argument mode mismatch",
                        [value.cause],
                    );
                }
            }
        }
        if callee.mutable_environment && callee.permission != Permission::Write {
            self.error(
                "E0520",
                span,
                "mutable captured environment requires a writable callable handle",
                [callee.cause],
            );
        }
        if callee.mutable_environment {
            self.access(callee, None, Mode::Write, span, frame);
        }
        let mut results = Vec::new();
        for callable in &callee.callables {
            if target.is_some_and(|target| target != callable) {
                continue;
            }
            let current_callee = match self.read_evaluation_packet(&saved_callee, span) {
                Ok(value) => value,
                Err(error) => {
                    self.unsupported(span, format!("target callee transport: {error}"));
                    break;
                }
            };
            let callee = &current_callee;
            let args = match self.entry_values(&argument_packets) {
                Ok(args) => args,
                Err(error) => {
                    self.unsupported(span, format!("target input transport: {error}"));
                    break;
                }
            };
            let foreign_exit_epoch = self.explanations.causes.len() as u32;
            self.budget_invoke(callable, span);
            let overlay = self.captured_loan_overlay(callable, callee);
            self.completed_invocation = None;
            let value = match callable {
                Callable::Constructor(name) => {
                    let value = self.invoke_constructor(name, &args, span, copy_call_event, frame);
                    let mut packet = EvaluatedValue::new(value, self.recency_moves.len());
                    if let Some(view) = self.constructors.get(name).and_then(|info| info.source)
                        && let Err(error) =
                            packet.set_current_type(super::super::evaluated::CapturedSource::Known(
                                super::super::evaluated::SourceRef {
                                    view,
                                    original: None,
                                },
                            ))
                    {
                        self.unsupported(
                            span,
                            format!("constructor result type is unavailable: {error}"),
                        );
                        packet.fail_current_source(error);
                    }
                    packet
                }
                Callable::Named(..) => {
                    frame.copy_call_event = copy_call_event;
                    if let Some(origin) = self.application_effect.snapshot_origin(origin) {
                        self.invoke_named_packets_from(
                            callable,
                            argument_packets.clone(),
                            Some(saved_callee.clone()),
                            span,
                            Some(frame),
                            origin,
                        )
                    } else {
                        self.unsupported(span, "callable origin cloning exhausted its work bound");
                        EvaluatedValue::unobserved(
                            Value::scalar(Ty::Unknown, None, CauseId(0)),
                            self.recency_moves.len(),
                            false,
                        )
                    }
                }
                Callable::Builtin(name) => {
                    let value = if concurrent::is_builtin(name) {
                        let mut intrinsic = frame.clone();
                        intrinsic.obligations = Obligations::default();
                        intrinsic.locals.clear();
                        intrinsic.returned.clear();
                        let value = self
                            .concurrent_builtin(callee, name, &args, span, &mut intrinsic)
                            .expect("recognized structured operation has a semantic contract");
                        self.complete_intrinsic_summary(&intrinsic);
                        if frame.callback_call {
                            intrinsic.obligations.concrete_effects.clear();
                            intrinsic.obligations.concrete.clear();
                        }
                        frame.obligations.include(&intrinsic.obligations, false);
                        value
                    } else if standard::builtin_callable_signature(name, span).is_some()
                        || (standard::storage_callable(name) && callee.signature.is_some())
                    {
                        let mut intrinsic = frame.clone();
                        intrinsic.obligations = Obligations::default();
                        intrinsic.locals.clear();
                        intrinsic.returned.clear();
                        let value =
                            self.transfer_builtin(callee, name, args.clone(), span, &mut intrinsic);
                        self.complete_intrinsic_summary(&intrinsic);
                        if frame.callback_call {
                            intrinsic.obligations.concrete_effects.clear();
                            intrinsic.obligations.concrete.clear();
                        }
                        frame.obligations.include(&intrinsic.obligations, true);
                        value
                    } else {
                        self.transfer_builtin(callee, name, args.clone(), span, frame)
                    };
                    EvaluatedValue::new(value, self.recency_moves.len())
                }
                Callable::Closure(id) => {
                    if let Some(origin) = self.application_effect.snapshot_origin(origin) {
                        self.invoke_closure_packets_from(
                            *id,
                            argument_packets.clone(),
                            Some(saved_callee.clone()),
                            span,
                            frame,
                            origin,
                        )
                    } else {
                        self.unsupported(span, "callable origin cloning exhausted its work bound");
                        EvaluatedValue::unobserved(
                            Value::scalar(Ty::Unknown, None, CauseId(0)),
                            self.recency_moves.len(),
                            false,
                        )
                    }
                }
                Callable::Symbolic(index, path) => {
                    self.unknown_window_callback(callee, span);
                    if self.has_window(callee)
                        || args.iter().any(|(_, value, _)| self.has_window(value))
                    {
                        self.unsupported(
                            span,
                            "an unknown callable requires a window lifetime and escape summary",
                        );
                    }
                    if !callee.scoped.is_empty()
                        || args.iter().any(|(_, value, _)| {
                            !value.scoped.is_empty()
                                || !self
                                    .heap
                                    .reachable(value.origins.nodes.iter().copied())
                                    .is_disjoint(&self.active_drafts)
                        })
                    {
                        self.unsupported(span,"an unknown callable cannot prove confinement of scoped or derived authority");
                    }
                    let exposed_inputs = std::iter::once(callee.clone())
                        .chain(args.iter().map(|(_, value, _)| value.clone()))
                        .collect::<Vec<_>>();
                    self.invalidate_unknown_callback_refinements(&exposed_inputs, frame.owner);
                    frame.obligations.symbolic = true;
                    self.record_symbolic_row_use(callee, origin, frame);
                    for (mode, value, arg_span) in &args {
                        if *mode != ParameterMode::Read {
                            self.access(value, None, Mode::Write, *arg_span, frame);
                        }
                    }
                    let ty = if let Ty::Callable(_, result) =
                        self.expanded(&callee.ty, &mut BTreeSet::new())
                    {
                        *result
                    } else {
                        Ty::Unknown
                    };
                    let mut value = self.formal_value(ty, *index, span, &mut BTreeSet::new());
                    self.produced_symbolic_results(&mut value, span, frame.owner);
                    if !value.origins.nodes.is_empty() {
                        value.permission = Permission::Read;
                        value.construction = false;
                        for (_, arg, _) in &args {
                            value.origins.nodes.extend(&arg.origins.nodes);
                            value.scoped.extend(&arg.scoped);
                            value.results.extend(&arg.results);
                            value.callback_parameters.extend(&arg.callback_parameters);
                        }
                    }
                    let _ = path;
                    self.project_evaluated_value(
                        &saved_callee,
                        super::super::source_types::SourcePath::CallableResult,
                        value,
                        span,
                    )
                }
            };
            self.restore_foreign_exit_overlays(&overlay, foreign_exit_epoch);
            self.restore_captured_loan_overlay(overlay);
            if !callee.callable_bounds.is_empty() {
                if let Some(obligations) = self.completed_summary().cloned()
                    && let Some(owner) = obligations.activation
                {
                    self.check_callable_bounds(callee, callable, owner, &obligations, span);
                } else if !matches!(callable, Callable::Symbolic(..)) {
                    self.unsupported(
                        span,
                        "bounded callable invocation requires a complete invocation summary",
                    );
                }
            }
            let current_callee = match self.read_evaluation_packet(&saved_callee, span) {
                Ok(value) => value,
                Err(error) => {
                    self.unsupported(span, format!("callee return transport: {error}"));
                    break;
                }
            };
            let value = value.transform_value(|value| {
                let value =
                    self.apply_callable_returns(&current_callee, callable, value, span, frame);
                (value, self.recency_moves.len())
            });
            results.push(value);
        }
        frame.callback_call = previous_callback;
        if results.is_empty() {
            self.error("E0338", span, "value is not callable", [callee.cause]);
            return EvaluatedValue::unobserved(
                Value::scalar(Ty::Unknown, None, callee.cause),
                self.recency_moves.len(),
                false,
            );
        }
        let mut result = results.remove(0);
        if let Err(error) = self.prepare_evaluation_packet(&mut result, span) {
            result.fail_current_source(error);
        }
        for other in results {
            let mut other = other;
            self.receive_boundary_type(&mut other, &mut result, span);
            let cause = self.cause(
                CauseKind::BranchJoin,
                span,
                "possible callable targets",
                [result.value.cause, other.value.cause],
            );
            result.value = result.value.join(&other.value, self.choice(), cause);
        }
        let args = match self.entry_values(&argument_packets) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("final input transport: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        result.transform_value(|mut value| {
        let input_pending = args
            .iter()
            .flat_map(|(_, value, _)| self.pending_result_binders(value))
            .collect::<BTreeSet<_>>();
        let remaining = self.unresolved_inference_metas(input_pending);
        let mut output_names = BTreeSet::new();
        value.ty.generic_names(&mut output_names);
        let output_pending = self.pending_result_binders(&value);
        let mut lost = BTreeSet::new();
        for identity in remaining {
            if output_names.contains(&identity) || output_pending.contains(&identity) {
                value.pending_inference.insert(identity);
            } else {
                lost.insert(identity);
            }
        }
        if !lost.is_empty() && value.ty != Ty::Never {
            self.error("E0344",span,"call arguments contain unresolved result type variables with no determining context",[value.cause]);
        }
        value.requires_inference |= !value.pending_inference.is_empty();
        if value.ty != Ty::Never
            && args
                .iter()
                .any(|(_, value, _)| self.unresolved_empty_map_keys(value))
            && !self.unresolved_empty_map_keys(&value)
        {
            if value.ty.scalar() {
                self.error(
                    "E0344",
                    span,
                    "call arguments contain an empty-map key class without a determining context",
                    [value.cause],
                );
            } else {
                self.unsupported(span,"empty-map key inference through this callable result requires an explicit type context");
            }
        }
        self.remember_constructor_carrier(callee, &value, copy_call_event, frame);
        (value, self.recency_moves.len())
        })
    }
    pub(super) fn invocation_summary(
        &self,
        id: usize,
        frame: &Frame,
        returned_nodes: &BTreeSet<NodeId>,
    ) -> super::super::summary::InvocationSummary {
        let mut summary = super::super::summary::InvocationSummary {
            activation: Some(frame.owner),
            context: Some(self.invocation_context(frame.callable_owner)),
            channel_messages: self.channel_invocation_messages(frame.owner),
            ..super::super::summary::InvocationSummary::from_obligations(&frame.obligations)
        };
        summary.escaped_origins = returned_nodes.clone();
        if frame.obligations.symbolic {
            summary.unresolved.insert(id as u32);
        }
        summary
    }

    pub(super) fn invoke_named_unrecorded(
        &mut self,
        id: usize,
        input_packets: Arc<Vec<EntryArgument>>,
        span: Span,
        mut caller: Option<&mut Frame>,
        verifying: bool,
    ) -> EvaluatedValue {
        let mut args = match self.entry_values(&input_packets) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("named formal packet admission: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        let arguments_recency = self.recency_moves.len();
        let effect_callback_epoch = self.effect_callback_uses.len();
        if let Some(invocation) = self.copy_invocation_stack.last().copied() {
            self.invocation_calls
                .push(super::super::effect_identity::InvocationCall {
                    invocation,
                    caller_owner: caller.as_ref().and_then(|frame| frame.callable_owner),
                    caller_closure: self
                        .closure_invocation_stack
                        .last()
                        .map(|id| self.closure_invocations[id.0 as usize].closure),
                    caller_closure_invocation: self.closure_invocation_stack.last().copied(),
                    default_use: self.default_use_stack.last().copied(),
                });
        }
        let foreign_exit_epoch = self.explanations.causes.len() as u32;
        if self.call_stack.len() >= 64 {
            self.unsupported(span, "named invocation traversal resource budget exhausted");
            return EvaluatedValue::unobserved(
                Value::scalar(Ty::Unknown, None, CauseId(0)),
                self.recency_moves.len(),
                false,
            );
        }
        self.check_named_initialization(id);
        let info = self.functions[id].clone();
        let function = &info.syntax;
        if verifying {
            self.widen_definition_environment(&info.lexical);
        }
        let previous_typing = self.generic_scope(id);
        let binders: BTreeSet<_> = function
            .generics
            .iter()
            .filter_map(|parameter| {
                self.type_source
                    .environment
                    .generic_context
                    .get(&parameter.name)
                    .cloned()
            })
            .collect();
        for binder in &binders {
            self.type_source
                .environment
                .generic_substitutions
                .remove(binder);
            self.type_source.environment.generic_sources.remove(binder);
            self.type_source
                .environment
                .static_key_arguments
                .remove(binder);
        }
        let previous_universal = self.universal;
        self.universal = verifying
            || (previous_universal && info.owner.is_some() && function.generics.is_empty());
        let explicit = (!verifying)
            .then(|| self.named_instance_for_invocation(&info))
            .flatten();
        // Preserve the genuine unselected templates before seeding a prefix.
        let raw_templates = explicit.as_ref().map(|_| {
            function
                .parameters
                .iter()
                .map(|parameter| {
                    parameter.ty.as_ref().map(|syntax| {
                        let ty = self.ty(syntax);
                        self.call_inference_type(&ty)
                    })
                })
                .collect()
        });
        if let Some(prepared) = &explicit {
            self.seed_named_instance(prepared);
        }
        let (mut missing_inference, argument_templates) = if verifying {
            (BTreeSet::new(), Vec::new())
        } else {
            self.infer_named_arguments(
                function,
                &args,
                &binders,
                raw_templates,
                explicit.as_deref(),
            )
        };
        if let Some(prepared) = &explicit {
            self.finish_named_instance_inference(prepared, span);
        }
        let source_event = self
            .copy_invocation_stack
            .last()
            .and_then(|id| self.copy_invocations.get(id.0 as usize))
            .and_then(|call| call.source_event);
        let mut input_sources_valid = vec![true; function.parameters.len()];
        if !verifying {
            if let Some(caller) = &caller {
                self.check_record_bound_application(
                    id,
                    &args,
                    &argument_templates,
                    self.invocation_context(Some(CallableOwner::Function(info.definition))),
                    caller.owner,
                    span,
                );
                // Complete structural inputs may determine another owned Type
                // parameter absent from the ordinary value template. Recompute
                // missing arguments only after that transactional bound check.
                missing_inference.retain(|binder| {
                    !self
                        .type_source
                        .environment
                        .generic_substitutions
                        .contains_key(binder)
                });
            } else if self
                .record_bounds
                .iter()
                .any(|bound| bound.definition == info.definition)
            {
                self.unsupported(
                    span,
                    "generic record-bound application requires its actual caller activation",
                );
            }
            // Structural input dependencies must be fully selected before a
            // prepared numeric instance can be compared and frozen.
            for (index, argument) in input_packets.iter().enumerate() {
                if let Some(valid) = input_sources_valid.get_mut(index) {
                    *valid = self.check_named_input_source(
                        &info,
                        index,
                        &argument.packet,
                        source_event,
                        argument.span,
                    );
                }
            }
            if input_sources_valid.iter().all(|valid| *valid) {
                self.validate_numeric_application(&info, span);
            } else if let Some(event) = self
                .copy_invocation_stack
                .last()
                .and_then(|id| self.copy_invocations.get(id.0 as usize))
                .and_then(|call| call.source_event)
                && let Some(application) = self.numeric.applications.get_mut(&event)
            {
                application.phase = crate::sema::numeric_selection::ApplicationPhase::Invalid;
            }
        }
        if self.call_stack.contains(&id) {
            if let Some(caller) = caller.as_mut()
                && let Some(value) = self.instantiate_recursive(
                    id,
                    &args,
                    span,
                    caller,
                    verifying,
                    effect_callback_epoch,
                )
            {
                self.restore_typing_environment(previous_typing);
                self.universal = previous_universal;
                self.complete_copy_invocation();
                self.finish_default_invocation();
                return EvaluatedValue::new(value, self.recency_moves.len());
            }
            self.unsupported(span, "recursive return and heap-shape summary fixed point");
            let ty = function
                .return_type
                .as_ref()
                .map(|t| self.ty(t))
                .unwrap_or(Ty::Unit);
            let value = self.formal_value(ty, id as u32, span, &mut BTreeSet::new());
            self.restore_typing_environment(previous_typing);
            self.universal = previous_universal;
            return EvaluatedValue::new(value, self.recency_moves.len());
        }
        let env = info.lexical.clone();
        let mut frame = self.frame(env, false);
        frame.definition = Some(info.definition);
        frame.callable_owner = Some(CallableOwner::Function(info.definition));
        if let Some(&invocation) = self.copy_invocation_stack.last() {
            self.scopes.set_origin(
                frame.owner,
                crate::sema::scopes::ScopeOrigin::Named(invocation),
            );
        }
        if let Some(caller) = &caller {
            self.scopes.set_parent(frame.owner, caller.owner);
        }
        frame.expected_return = Some(
            function
                .return_type
                .as_ref()
                .map(|ty| self.ty(ty))
                .unwrap_or(Ty::Unit),
        );
        if !verifying {
            let mut result_binders = BTreeSet::new();
            frame
                .expected_return
                .as_ref()
                .unwrap()
                .generic_names(&mut result_binders);
            if missing_inference
                .iter()
                .any(|identity| !result_binders.contains(identity))
            {
                self.error(
                    "E0344",
                    span,
                    "generic arguments are not determined by input values or the result context",
                    [],
                );
            }
        }
        let previous_loop_depth = self.loop_depth;
        self.loop_depth = 0;
        self.scope_names
            .insert(frame.owner, Some(function.name.clone()));
        self.call_stack.push(id);
        if args.len() > function.parameters.len()
            || args.len()
                < function
                    .parameters
                    .iter()
                    .filter(|p| p.default.is_none())
                    .count()
        {
            self.error("E0404", span, "wrong number of arguments", []);
        }
        let mut loan_origins = Vec::new();
        let mut local_loans = BTreeMap::new();
        let mut received_arguments = Vec::new();
        let mut exchange_arguments = Vec::new();
        macro_rules! admit_formal_packet {
            ($result:expr, $at:expr) => {
                match $result {
                    Ok(packet) => packet,
                    Err(error) => {
                        let at = $at;
                        self.unsupported(
                            at,
                            format!("formal evaluation packet admission: {error}"),
                        );
                        let mut failed = Value::scalar(Ty::Unknown, None, CauseId(0));
                        self.flush_handler_obligations(&mut frame);
                        self.end_invocation_loans(&mut failed, &frame, &local_loans, at);
                        if let Some(caller) = caller.as_mut() {
                            caller.obligations.include(&frame.obligations, true);
                        }
                        for binding in &frame.locals {
                            self.bindings[*binding].alive = false;
                        }
                        self.call_stack.pop();
                        self.loop_depth = previous_loop_depth;
                        self.restore_typing_environment(previous_typing);
                        self.universal = previous_universal;
                        return EvaluatedValue::unobserved(failed, self.recency_moves.len(), false);
                    }
                }
            };
        }
        for (index, param) in function.parameters.iter().enumerate() {
            if matches!(
                param.pattern.kind,
                PatternKind::Mode {
                    mode: BindingMode::Var | BindingMode::VarMut,
                    ..
                }
            ) {
                self.error(
                    "E0403",
                    param.span,
                    "var bindings are prohibited in function parameters",
                    [],
                );
            }
            let (mode, mut held, arg_span) = if let Some(arg) = input_packets.get(index) {
                let mut packet = admit_formal_packet!(
                    self.clone_evaluation_packet(&arg.packet, arg.span),
                    arg.span
                );
                admit_formal_packet!(
                    self.prepare_evaluation_packet(&mut packet, arg.span),
                    arg.span
                );
                (arg.mode, packet, arg.span)
            } else if let Some(default) = &param.default {
                let invocation = *self
                    .copy_invocation_stack
                    .last()
                    .expect("named invocation identity");
                let context = self.invocation_context(frame.callable_owner);
                let mut default_receipt = None;
                let default_result = (|| {
                    let (use_id, packet) = self.evaluate_default(
                        Some(id),
                        index,
                        default,
                        super::super::default_uses::DefaultOrigin::InvocationFallback(invocation),
                        context,
                        &mut frame,
                    )?;
                    default_receipt = Some(use_id);
                    if let Some(event) = source_event {
                        let original = self.clone_evaluation_packet(&packet, default.span)?;
                        self.record_default_call_input_source(
                            event,
                            index,
                            use_id,
                            default,
                            &frame,
                            std::sync::Arc::new(original),
                        );
                    }
                    Ok::<_, SourceTypesError>(packet)
                })();
                let packet = match default_result {
                    Ok(packet) => packet,
                    Err(error) => {
                        if let Some(id) = default_receipt {
                            self.default_uses[id.0 as usize].status =
                                super::super::copy_contract::CopyInvocationStatus::Unsupported;
                        }
                        self.unsupported(
                            default.span,
                            format!("default packet admission: {error}"),
                        );
                        let mut failed = Value::scalar(Ty::Unknown, None, CauseId(0));
                        self.flush_handler_obligations(&mut frame);
                        self.end_invocation_loans(&mut failed, &frame, &local_loans, default.span);
                        if let Some(caller) = caller.as_mut() {
                            caller.obligations.include(&frame.obligations, true);
                        }
                        for binding in &frame.locals {
                            self.bindings[*binding].alive = false;
                        }
                        self.call_stack.pop();
                        self.loop_depth = previous_loop_depth;
                        self.restore_typing_environment(previous_typing);
                        self.universal = previous_universal;
                        // Admission failure leaves Result duties unresolved;
                        // it supplies neither an inspection nor a return.
                        return EvaluatedValue::unobserved(failed, self.recency_moves.len(), false);
                    }
                };
                if !verifying {
                    input_sources_valid[index] = self.check_named_input_source(
                        &info,
                        index,
                        &packet,
                        source_event,
                        default.span,
                    );
                }
                (ParameterMode::Read, packet, default.span)
            } else {
                let ty = param.ty.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unknown);
                (
                    param.mode,
                    {
                        let value =
                            self.formal_value(ty, index as u32, param.span, &mut BTreeSet::new());
                        EvaluatedValue::new(value, self.recency_moves.len())
                    },
                    param.span,
                )
            };
            if held.value.ty == Ty::Never {
                // No body entry certificate exists when an implicit application
                // stops in a default. Keep this path explicit until its caller
                // supplies an application event for native fallback lowering.
                self.unsupported(
                    arg_span,
                    "implicit application exits during a default before body entry",
                );
                self.flush_handler_obligations(&mut frame);
                self.finish_results(frame.owner, &held.value);
                if let Some(caller) = caller.as_mut() {
                    caller.obligations.include(&frame.obligations, true);
                }
                for binding in &frame.locals {
                    self.bindings[*binding].alive = false;
                }
                self.call_stack.pop();
                self.loop_depth = previous_loop_depth;
                self.restore_typing_environment(previous_typing);
                self.universal = previous_universal;
                return held;
            }
            if mode != param.mode {
                self.error(
                    if mode != ParameterMode::Read && param.mode != ParameterMode::Read {
                        "E0406"
                    } else {
                        "E0405"
                    },
                    arg_span,
                    "argument mode must match the parameter mode",
                    [held.value.cause],
                );
            }
            if input_sources_valid[index]
                && let Some(syntax) = &param.ty
            {
                if let Ty::StaticKey(identity) = self.ty(syntax) {
                    held.invalidate_current_source();
                    held.value.ty = Ty::StaticKey(identity);
                }
                self.set_contract_environment(&frame.env);
                admit_formal_packet!(
                    self.prepare_evaluation_packet(&mut held, arg_span),
                    arg_span
                );
                held.invalidate_current_source();
                self.ascribe_signature(&mut held.value, syntax);
                admit_formal_packet!(
                    self.prepare_evaluation_packet(&mut held, arg_span),
                    arg_span
                );
                self.check_storage_shape(&held.value, syntax, &mut frame);
                let ty = self.ty(syntax);
                admit_formal_packet!(
                    self.prepare_evaluation_packet(&mut held, arg_span),
                    arg_span
                );
                self.constrain_collection_type(&held.value, &ty, arg_span);
                self.require_type(&held.value, &ty, arg_span);
                let mut generics = BTreeSet::new();
                generic_names(&ty, &mut generics);
                if generics.is_empty() {
                    held.value.ty = ty;
                }
            }
            admit_formal_packet!(
                self.prepare_evaluation_packet(&mut held, arg_span),
                arg_span
            );
            let forwarded = held.value.sources.clone();
            // Defaults are evaluated before read reception just like explicit
            // arguments. Preserve their original construction witness for the
            // immutable external exchange judgment.
            exchange_arguments.push(admit_formal_packet!(
                self.clone_evaluation_packet(&held, arg_span),
                arg_span
            ));
            let binding_mode = if param.mode == ParameterMode::Read {
                BindingMode::Let
            } else {
                BindingMode::LetMut
            };
            if param.mode != ParameterMode::Read && held.value.permission != Permission::Write {
                self.error(
                    "E0520",
                    arg_span,
                    "mutable argument has no writable authority",
                    [held.value.cause],
                );
            }
            held.invalidate_current_source();
            let value = &mut held.value;
            if param.mode == ParameterMode::Read {
                value.permission = Permission::Read;
                value.construction = false;
            } else {
                if param.mode == ParameterMode::SharedMut && value.temporary {
                    self.unsupported(
                        arg_span,
                        "a retained parameter cannot extend a temporary loan",
                    );
                }
                value.temporary |= param.mode == ParameterMode::Mut;
                let loan = LoanId(self.next_loan);
                self.next_loan += 1;
                self.loan_parents.insert(loan, value.participants.clone());
                local_loans.insert(loan, value.participants.clone());
                self.start_invocation_loan(
                    loan,
                    value,
                    &frame,
                    index,
                    param.mode == ParameterMode::SharedMut,
                    arg_span,
                );
                value.participants = [Participant::Loan(loan)].into();
                loan_origins.push(value.origins.clone());
            }
            let start = frame.locals.len();
            let mut received_packet =
                admit_formal_packet!(self.clone_evaluation_packet(&held, arg_span), arg_span);
            let mut received =
                admit_formal_packet!(self.read_evaluation_packet(&held, arg_span), arg_span);
            let mut received_epoch = received_packet.current_epoch();
            admit_formal_packet!(
                self.bind_parameter_packet(&param.pattern, binding_mode, held, &mut frame),
                arg_span
            );
            for &binding in &frame.locals[start..] {
                self.bindings[binding].forwarded = forwarded.clone();
                received
                    .callback_parameters
                    .extend(&self.bindings[binding].value.callback_parameters);
            }
            if let [binding] = &frame.locals[start..] {
                received = self.bindings[*binding].value.clone();
                received_epoch = self.recency_moves.len();
            }
            self.record_received_closures(&received, &mut frame);
            let moves = &self.recency_moves;
            received = admit_formal_packet!(
                self.application_effect.with_work(|work| {
                    crate::sema::evaluated::transport_value_at(
                        &received,
                        moves,
                        received_epoch,
                        moves.len(),
                        work,
                    )
                }),
                arg_span
            );
            admit_formal_packet!(
                self.prepare_evaluation_packet(&mut received_packet, arg_span),
                arg_span
            );
            received_packet.value = received;
            received_packet.invalidate_current_source();
            received_arguments.push(received_packet);
            if verifying {
                self.record_static_key_parameter(param, function.span, index, &frame);
            }
        }
        let retained =
            self.begin_retained_handlers(&Callable::Named(id, None), &info.handler_context, &frame);
        let foreign_body_before = (self.foreign_callback_depth > 0).then(|| self.snapshot_flow());
        let declared_body_boundary = function.body.as_ref().map(|_| self.next_boundary);
        let exchange_arguments = exchange_arguments
            .into_iter()
            .map(|value| self.consume_evaluation_packet(value, span))
            .collect::<Result<Vec<_>, _>>();
        let exchange_arguments = admit_formal_packet!(exchange_arguments, span);
        let received_arguments = received_arguments
            .into_iter()
            .map(|value| self.consume_evaluation_packet(value, span))
            .collect::<Result<Vec<_>, _>>();
        let received_arguments = admit_formal_packet!(received_arguments, span);
        let expected_return = frame.expected_return.clone();
        self.set_contract_environment(&frame.env);
        let frozen_return_source = function
            .return_type
            .as_ref()
            .map(|syntax| self.freeze_source_receiving_target(syntax));
        frame.expected_return_source = frozen_return_source.clone();
        let mut result = if let Some(body) = &function.body {
            self.block_expected_source(
                body,
                &mut frame,
                expected_return.as_ref(),
                frozen_return_source.as_ref(),
            )
        } else if self.declaration_files.contains(&function.span.file.0) {
            self.check_external_invocation(
                function,
                &exchange_arguments,
                &received_arguments,
                span,
                &mut frame,
            );
            for annotation in &function.annotations {
                if annotation.kind == AnnotationKind::Effect {
                    frame.obligations.effects.extend(
                        annotation
                            .text
                            .trim_start_matches('@')
                            .trim_matches(['{', '}'])
                            .split(['+', ','])
                            .map(str::trim)
                            .filter(|s| !s.is_empty())
                            .map(str::to_owned),
                    );
                } else if annotation.text != "&{}" {
                    self.unsupported(annotation.span,"foreign capability contract requires an explicit verified resource operation");
                }
            }
            let ty = function
                .return_type
                .as_ref()
                .map(|t| self.ty(t))
                .unwrap_or(Ty::Unit);
            let value = self.external_formal_value(
                ty,
                id as u32,
                function.return_type.as_ref(),
                span,
                &mut frame,
            );
            EvaluatedValue::unobserved(value, self.recency_moves.len(), true)
        } else {
            self.unsupported(function.span, "foreign function contract");
            EvaluatedValue::unobserved(self.unit(span), self.recency_moves.len(), false)
        };
        if let Some(before) = &foreign_body_before {
            self.finish_foreign_returns(before, &mut frame, &mut result, span, foreign_exit_epoch);
        }
        self.flush_handler_obligations(&mut frame);
        self.check_deep_uncertainty(&result.value, span);
        self.finish_results(frame.owner, &result.value);
        for mut returned in frame.returned.clone() {
            self.transport_evaluation_packet(&mut returned, span);
            if result.value.ty == Ty::Never {
                result = returned;
            } else {
                self.receive_boundary_type(&mut returned, &mut result, function.span);
                let cause = self.cause(
                    CauseKind::BranchJoin,
                    span,
                    "explicit return alternatives",
                    [result.value.cause, returned.value.cause],
                );
                result.value = result.value.join(&returned.value, self.choice(), cause);
            }
        }
        self.finish_retained_handlers(retained, &mut frame, &mut result, span);
        let mut output = result.transform_value(|mut result| {
            if let Some(expected) = &function.return_type {
                self.set_contract_environment(&frame.env);
                if frame.return_source_valid {
                    self.ascribe_signature(&mut result, expected);
                    self.check_storage_shape(&result, expected, &mut frame);
                }
                let expected = self.ty(expected);
                if frame.return_source_valid {
                    self.constrain_collection_type(&result, &expected, function.span);
                }
                self.require_type(&result, &expected, function.span);
                if result.ty != Ty::Never
                    && let Some(boundary) = declared_body_boundary
                {
                    // A zero-budget/abort path may infer only None's payload hole.
                    // The declared result constrains this function body's answer,
                    // including its retained handler definition, after ordinary
                    // return checking. Nested block answers remain independent.
                    let answer = join_type_holes(
                        &self.expanded(&result.ty, &mut BTreeSet::new()),
                        &self.expanded(&expected, &mut BTreeSet::new()),
                    );
                    self.record_handler_answer(boundary, &answer);
                }
                let mut result_generics = BTreeSet::new();
                generic_names(&expected, &mut result_generics);
                let mut inputs = BTreeSet::new();
                for parameter in &function.parameters {
                    if let Some(ty) = &parameter.ty {
                        let ty = self.ty(ty);
                        generic_names(&ty, &mut inputs);
                    }
                }
                let pending: BTreeSet<_> = missing_inference
                    .iter()
                    .cloned()
                    .chain(
                        result_generics
                            .iter()
                            .filter(|name| binders.contains(*name) && !inputs.contains(*name))
                            .cloned(),
                    )
                    .collect();
                if result.ty == Ty::Never && !verifying && !pending.is_empty() {
                    // Abrupt control cannot determine a declaration's unselected
                    // static arguments. Preserve their actual invocation variables
                    // so a context-free receiver still diagnoses E0344.
                    for identity in &pending {
                        let meta = format!("{identity}:invocation:{}", frame.owner.0);
                        self.inference_metas.insert(meta.clone());
                        result.pending_inference.insert(meta);
                    }
                    result.requires_inference = true;
                }
                if result.ty != Ty::Never {
                    result.ty = expected.clone();
                    if !verifying && !pending.is_empty() {
                        result.pending_inference.extend(pending.iter().cloned());
                        let instantiated: BTreeMap<_, _> = pending
                            .iter()
                            .map(|identity| {
                                (
                                    identity.clone(),
                                    Ty::Generic(format!("{identity}:invocation:{}", frame.owner.0)),
                                )
                            })
                            .collect();
                        let selected =
                            super::types::substitute_inferred_type(&expected, &instantiated);
                        for ty in instantiated.values() {
                            if let Ty::Generic(identity) = ty {
                                self.inference_metas.insert(identity.clone());
                            }
                        }
                        self.contextual_result_inference(&mut result, &selected, function.span);
                        for (_, meta) in instantiated {
                            let Ty::Generic(identity) = meta else {
                                unreachable!()
                            };
                            result.pending_inference.insert(identity);
                        }
                        result.requires_inference = true;
                    }
                }
            } else if result.ty != Ty::Unit && result.ty != Ty::Never {
                self.error(
                    "E0301",
                    function.span,
                    "function without result annotation must return unit",
                    [result.cause],
                );
            }
            let returned_nodes = self.heap.reachable(result.origins.nodes.iter().copied());
            for (_, argument, _) in &mut args {
                self.transport_value_since(argument, arguments_recency);
            }
            if result.temporary {
                result.permission = Permission::Read;
                result.construction = false;
            }
            if self.functions.iter().any(|function| {
                function
                    .environment
                    .is_some_and(|node| returned_nodes.contains(&node))
                    && function
                        .captures
                        .iter()
                        .any(|binding| self.bindings[*binding].value.temporary)
            }) {
                self.unsupported(
                    function.span,
                    "escaping named callable cannot retain a temporary parameter loan",
                );
            }
            if self.closures.iter().any(|closure| {
                returned_nodes.contains(&closure.node)
                    && closure
                        .captures
                        .iter()
                        .any(|binding| self.bindings[*binding].value.temporary)
            }) {
                self.unsupported(
                    function.span,
                    "escaping callable cannot retain a temporary parameter loan",
                );
            }
            for (index, param) in function.parameters.iter().enumerate() {
                if param.mode == ParameterMode::SharedMut
                    && let Some((_, arg, _)) = args.get(index)
                    && !returned_nodes.is_disjoint(&arg.origins.nodes)
                {
                    frame.obligations.retention = true;
                    result.retention_result = true;
                    for source in &arg.origins.nodes {
                        let bindings: Vec<_> = frame
                            .locals
                            .iter()
                            .copied()
                            .filter(|id| {
                                self.bindings[*id].parameter
                                    && self.bindings[*id].value.origins.nodes.contains(source)
                            })
                            .collect();
                        for binding in bindings {
                            self.mark_write(binding);
                        }
                    }
                    for source in &arg.sources {
                        self.mark_write(*source);
                    }
                }
            }
            self.record_closure_exposure(
                &result,
                &frame,
                super::super::closure_exclusivity::ExposureKind::Returned,
                span,
            );
            self.escape_obligations(&result, &mut frame);
            self.record_callable_local_effects(false, id, &frame, &result);
            self.record_retained_handlers(
                Callable::Named(id, None),
                &info.handler_context,
                &frame.obligations.selected_handlers,
                &result,
                frame.owner,
                function.span,
            );
            self.record_returned_handler_context(
                Callable::Named(id, None),
                &info.handler_context,
                &result,
                &frame,
                span,
            );
            frame.obligations.handler_environment |=
                self.has_retained_handlers(&Callable::Named(id, None));
            for access in &mut frame.obligations.accesses {
                access.transport(&self.recency_moves);
            }
            self.check_exclusivity(&frame.obligations.accesses, span);
            if function.body.is_some() {
                self.check_annotations(
                    function,
                    &frame,
                    info.owner,
                    if verifying {
                        AnnotationCheck::Declaration
                    } else {
                        AnnotationCheck::Invocation
                    },
                );
            }
            let summary = self.invocation_summary(id, &frame, &returned_nodes);
            if verifying {
                let returned = self.expanded(&result.ty, &mut BTreeSet::new());
                let declared = self.expanded(
                    frame.expected_return.as_ref().unwrap_or(&Ty::Unit),
                    &mut BTreeSet::new(),
                );
                self.definition_checks.push(super::super::DefinitionCheck {
                    function: id,
                    span: function.span,
                    declared,
                    returned,
                    invocation: summary.clone(),
                });
            }
            self.record_effect_invocation(&info, span, &summary, verifying, effect_callback_epoch);
            let summary = self.retain_invocation_summary(summary);
            self.unwind_foreign_abort_exits(
                frame.owner,
                &frame.locals,
                &local_loans,
                foreign_exit_epoch,
            );
            self.completed_invocation =
                Some(super::contracts::CompletedInvocation::Recorded(summary));
            for &binding in &frame.locals {
                self.check_authority_use(binding);
                self.bindings[binding].alive = false;
            }
            if self.is_private_fresh(&result) {
                result.construction = true;
                result.publication = Publication::Unpublished;
                result.permission = Permission::Write;
            }
            self.export_conditional_result_family(&mut result, frame.owner, span);
            result.through_return = true;
            result.unsuffixed_numeric = false;
            result.static_coordinate = None;
            result.sources.clear();
            result.cause = self.cause(
                CauseKind::Call,
                span,
                format!("return from {} preserves provenance", function.name),
                [result.cause],
            );
            if let Some(caller) = caller.as_mut() {
                caller
                    .obligations
                    .copy_boundaries
                    .extend(&frame.obligations.copy_boundaries);
                caller.obligations.handler_environment |= frame.obligations.handler_environment;
                caller
                    .obligations
                    .performed_operations
                    .extend(&frame.obligations.performed_operations);
                caller
                    .obligations
                    .selected_handlers
                    .extend(&frame.obligations.selected_handlers);
                self.transfer_results(&result, frame.owner, caller.owner);
                let forwarded_callback = args.iter().any(|(_, value, _)| {
                    value
                        .callback_parameters
                        .iter()
                        .any(|binding| self.bindings[*binding].owner == caller.owner)
                });
                for (&binding, &mode) in &frame.obligations.named {
                    if self.bindings[binding].owner == caller.owner
                        && self.bindings[binding].parameter
                        && mode != Mode::Read
                    {
                        caller.obligations.parameter_write = true;
                    }
                    if self.bindings[binding].owner != caller.owner && self.bindings[binding].alive
                    {
                        caller
                            .obligations
                            .named
                            .entry(binding)
                            .and_modify(|m| *m = (*m).max(mode))
                            .or_insert(mode);
                        if !caller.callback_call
                            && (!forwarded_callback
                                || frame.obligations.concrete.contains_key(&binding))
                        {
                            caller
                                .obligations
                                .concrete
                                .entry(binding)
                                .and_modify(|m| *m = (*m).max(mode))
                                .or_insert(mode);
                        }
                    }
                }
                caller
                    .obligations
                    .effects
                    .extend(frame.obligations.effects.iter().cloned());
                caller.obligations.symbolic |= frame.obligations.symbolic;
                caller
                    .obligations
                    .symbolic_uses
                    .extend(&frame.obligations.symbolic_uses);
                if !caller.callback_call {
                    caller.obligations.concrete_effects.extend(
                        if forwarded_callback {
                            frame.obligations.concrete_effects.iter()
                        } else {
                            frame.obligations.effects.iter()
                        }
                        .cloned(),
                    );
                }
                // Access through a callee's loan is a suspended forwarding path,
                // while ambient paths retain their own participant identities.
                for mut access in frame.obligations.accesses.iter().cloned() {
                    access.participants = super::recursive_calls::normalize_participants(
                        &access.participants,
                        &local_loans,
                    );
                    caller.obligations.accesses.push(access);
                }
                for &source in args
                    .iter()
                    .filter(|(mode, _, _)| *mode != ParameterMode::Read)
                    .flat_map(|(_, v, _)| v.sources.iter())
                {
                    if self.bindings[source].parameter && self.bindings[source].write_used {
                        caller.obligations.parameter_write = true;
                    }
                }
            }
            if caller.is_none() {
                self.transfer_results(&result, frame.owner, ScopeId(u32::MAX));
            }
            self.end_invocation_loans(&mut result, &frame, &local_loans, span);
            self.call_stack.pop();
            result.participants =
                super::recursive_calls::normalize_participants(&result.participants, &local_loans);
            self.loop_depth = previous_loop_depth;
            self.restore_typing_environment(previous_typing);
            self.universal = previous_universal;
            let _ = (loan_origins, verifying);
            result.unsuffixed_numeric = false;
            result.static_coordinate = None;
            self.complete_copy_invocation();
            self.finish_default_invocation();
            (result, self.recency_moves.len())
        });
        if output.source_valid
            && let Some(target) = &frozen_return_source
        {
            self.record_received_type(&mut output, target, span);
        }
        output
    }
    /// Select each binder once for the whole invocation. A later argument is
    /// checked against that selection; it cannot independently rename T.
    pub(super) fn infer_named_arguments(
        &mut self,
        function: &Function,
        args: &[(ParameterMode, Value, Span)],
        binders: &BTreeSet<String>,
        raw_templates: Option<Vec<Option<Ty>>>,
        explicit: Option<&NamedInstance>,
    ) -> (BTreeSet<String>, Vec<Option<Ty>>) {
        if function.generics.is_empty() {
            return (BTreeSet::new(), Vec::new());
        }
        let binders: BTreeSet<_> = binders
            .iter()
            .filter(|identity| !self.generic_key_bounds.contains_key(*identity))
            .cloned()
            .collect();
        let templates: Vec<_> = raw_templates.unwrap_or_else(|| {
            function
                .parameters
                .iter()
                .map(|parameter| {
                    parameter.ty.as_ref().map(|syntax| {
                        let ty = self.ty(syntax);
                        self.call_inference_type(&ty)
                    })
                })
                .collect()
        });
        let mut selected: BTreeMap<_, _> = explicit
            .into_iter()
            .flat_map(|prepared| prepared.selections.iter())
            .map(|selection| (selection.binder.clone(), selection.ty.clone()))
            .collect();
        // A numeric literal is still contextual. Nonliteral evidence such as
        // the i8 second argument in choose(1, 2i8) selects its type first.
        for provisional in [false, true] {
            for ((_, value, span), template) in args.iter().zip(&templates) {
                if value.unsuffixed_numeric != provisional {
                    continue;
                }
                let Some(template) = template else { continue };
                let mut mentioned = BTreeSet::new();
                generic_names(template, &mut mentioned);
                if mentioned.is_disjoint(&binders) {
                    continue;
                }
                let mut actual = self.source_value_inference_type(value);
                if provisional {
                    self.type_source
                        .environment
                        .generic_substitutions
                        .extend(selected.clone());
                    if let Ty::Generic(identity) = template
                        && let Some(ty) = selected.get(identity)
                        && matches!(
                            (&actual, ty),
                            (Ty::Int(_), Ty::Int(_)) | (Ty::Float(_), Ty::Float(_))
                        )
                    {
                        actual = ty.clone();
                    }
                }
                if !super::types::unify_call_types(template, &actual, &binders, &mut selected) {
                    self.error(
                        "E0301",
                        *span,
                        "arguments require inconsistent instantiations of a generic parameter",
                        [value.cause],
                    );
                }
            }
        }
        let missing = binders
            .iter()
            .filter(|binder| !selected.contains_key(*binder))
            .cloned()
            .collect();
        // An unused explicit Type already has a complete source descriptor.
        // Inputs mentioning it still participate in the full schema comparison.
        let explicit_binders: BTreeSet<_> = explicit
            .into_iter()
            .flat_map(|prepared| {
                prepared
                    .selections
                    .iter()
                    .map(|selection| selection.binder.clone())
            })
            .collect();
        let mut mentioned = BTreeSet::new();
        for template in templates.iter().flatten() {
            template.generic_names(&mut mentioned);
        }
        let schema_selected: BTreeMap<_, _> = selected
            .iter()
            .filter(|(binder, _)| {
                !explicit_binders.contains(*binder) || mentioned.contains(*binder)
            })
            .map(|(binder, ty)| (binder.clone(), ty.clone()))
            .collect();
        self.select_generic_source_types(&templates, args, &binders, &schema_selected, explicit);
        self.type_source
            .environment
            .generic_substitutions
            .extend(selected);
        self.infer_static_keys_and_bounds(function, args, &templates);
        (missing, templates)
    }
    fn infer_static_keys_and_bounds(
        &mut self,
        function: &Function,
        args: &[(ParameterMode, Value, Span)],
        templates: &[Option<Ty>],
    ) {
        for ((_, value, span), template) in args.iter().zip(templates) {
            let Some(Ty::StaticKey(identity)) = template else {
                continue;
            };
            let coordinate_type = self.call_inference_type(&value.ty);
            if !matches!(&coordinate_type, Ty::Str | Ty::StaticKey(_))
                && !matches!(&coordinate_type,Ty::Int(name)if name=="int")
            {
                if coordinate_type == Ty::Unknown {
                    self.unsupported(*span, "static key argument type is unresolved");
                } else {
                    self.error(
                        "E0323",
                        *span,
                        "static coordinates require the matching string or int sort",
                        [value.cause],
                    );
                }
                continue;
            }
            let coordinate = value.static_coordinate.clone().or_else(|| {
                if let Ty::StaticKey(source) = &value.ty {
                    self.type_source
                        .environment
                        .static_key_arguments
                        .get(source)
                        .cloned()
                } else {
                    None
                }
            });
            let Some(coordinate) = coordinate else {
                if matches!(value.ty, Ty::StaticKey(_)) {
                    self.unsupported(
                        *span,
                        "symbolic static-key forwarding requires a binder equality proof",
                    );
                } else {
                    self.error(
                        "E0814",
                        *span,
                        "a keyof parameter requires a static coordinate argument",
                        [value.cause],
                    );
                }
                continue;
            };
            if let Some(previous) = self
                .type_source
                .environment
                .static_key_arguments
                .get(identity)
                && previous != &coordinate
            {
                self.error(
                    "E0323",
                    *span,
                    "one static key binder has inconsistent coordinate arguments",
                    [value.cause],
                );
                continue;
            }
            if let Some(base) = self.static_key_bound_type(identity) {
                if matches!(base, Ty::Generic(_) | Ty::Unknown) {
                    self.unsupported(*span,"static-key membership requires a concrete receiver or an implied symbolic constraint");
                } else if self.static_type_projection(&base, &coordinate).is_none() {
                    self.error(
                        "E0323",
                        *span,
                        "coordinate is not a member of the inferred keyof receiver",
                        [value.cause],
                    );
                } else {
                    let cause = self.cause(
                        CauseKind::Source,
                        *span,
                        "inferred static coordinate belongs to the selected receiver type",
                        [value.cause],
                    );
                    self.expression_witness(
                        *span,
                        super::super::effect_identity::InvocationWitnessKind::StaticKey(
                            self.static_key_checks.len(),
                        ),
                    );
                    self.static_key_checks.push(super::super::StaticKeyCheck {
                        binder: identity.clone(),
                        argument: *span,
                        receiver: base,
                        coordinate: coordinate.clone(),
                        cause,
                    });
                }
            }
            self.type_source
                .environment
                .static_key_arguments
                .insert(identity.clone(), coordinate);
        }
        for generic in &function.generics {
            let Some(bound) = &generic.bound else {
                continue;
            };
            if matches!(bound.kind, TypeKind::KeyOf(_)) {
                continue;
            }
            if matches!(&bound.kind,TypeKind::Name{path,arguments}if path==&["Type".to_owned()]&&arguments.is_empty())
            {
                continue;
            }
            let Some(identity) = self
                .type_source
                .environment
                .generic_context
                .get(&generic.name)
                .cloned()
            else {
                continue;
            };
            // Structural bounds use the application-wide row equation and
            // complete source keys above. Keep legacy handling for constraints
            // which have not produced a verified structural declaration.
            if self.record_bounds_by_binder.contains_key(&identity) {
                continue;
            }
            let Some(actual) = self
                .type_source
                .environment
                .generic_substitutions
                .get(&identity)
                .cloned()
            else {
                continue;
            };
            let TypeKind::Record { fields, row } = &bound.kind else {
                self.unsupported(
                    bound.span,
                    "generic bound implication is not implemented for this constraint",
                );
                continue;
            };
            let actual = self.call_inference_type(&actual);
            let Ty::Record(actual_fields) = actual else {
                if matches!(actual, Ty::Generic(_)) {
                    self.unsupported(
                        bound.span,
                        "symbolic record-bound implication requires the caller binder's constraint",
                    );
                } else {
                    self.error(
                        "E0301",
                        bound.span,
                        "generic argument does not satisfy the required record shape",
                        [],
                    );
                }
                continue;
            };
            if row.is_none() && fields.len() != actual_fields.len() {
                self.error("E0301", bound.span, "generic record bound is closed", []);
            }
            for field in fields {
                let expected = self.ty(&field.ty);
                if actual_fields.get(&field.name).is_none_or(|(mutable, ty)| {
                    *mutable != field.mutable || !self.compatible(ty, &expected)
                }) {
                    self.error(
                        "E0301",
                        field.span,
                        "generic argument does not satisfy a bound field",
                        [],
                    );
                }
            }
        }
    }
    pub(super) fn invoke_closure_unrecorded(
        &mut self,
        id: usize,
        input_packets: &[EntryArgument],
        span: Span,
        caller: &mut Frame,
        contextual_return_source: Option<source_reception::Target>,
    ) -> EvaluatedValue {
        let args = match self.entry_values(input_packets) {
            Ok(args) => args,
            Err(error) => {
                self.unsupported(span, format!("closure formal packet admission: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        let arguments_recency = self.recency_moves.len();
        let foreign_exit_epoch = self.explanations.causes.len() as u32;
        if self.analysis_depth >= 64 {
            self.unsupported(
                span,
                "anonymous invocation traversal resource budget exhausted",
            );
            return EvaluatedValue::unobserved(
                Value::scalar(Ty::Unknown, None, CauseId(0)),
                self.recency_moves.len(),
                false,
            );
        }
        let closure = self.closures[id].clone();
        let previous_typing = self.capture_typing_environment();
        if let Some(environment) = self
            .lambda_contract(id)
            .map(|contract| contract.typing_environment.clone())
        {
            self.restore_typing_environment(environment);
        }
        let previous_loop_depth = self.loop_depth;
        self.loop_depth = 0;
        let mut frame = self.frame(closure.lexical.clone(), true);
        frame.callable_owner = closure.site.map(CallableOwner::Lambda);
        // Parameter Source headers belong to the closure declaration. Adding
        // runtime formal bindings must not mint a different interpretation of
        // the same lexical UIDs for each activation.
        frame.input_environment = Some(closure.contract.typing_environment.clone());
        if let Some(id) = self.closure_invocation_stack.last().copied() {
            self.scopes
                .set_origin(frame.owner, crate::sema::scopes::ScopeOrigin::Closure(id));
            let invocation = &mut self.closure_invocations[id.0 as usize];
            if invocation
                .activation
                .is_some_and(|activation| activation != frame.owner)
            {
                self.unsupported(
                    span,
                    "closure invocation already belongs to a different activation",
                );
            } else {
                invocation.activation = Some(frame.owner);
            }
        }
        self.scopes.set_parent(frame.owner, caller.owner);
        frame.expected_return = self
            .lambda_contract(id)
            .and_then(|contract| contract.return_type.clone())
            .map(|syntax| self.ty(&syntax));
        if frame.expected_return.is_none() && self.concurrent_scope_callback(id) {
            frame.expected_return = Some(Ty::Result(
                Box::new(Ty::Unknown),
                Box::new(Ty::Named("Concurrent::TaskFault".into())),
            ));
        }
        if args.iter().all(|(_, value, _)| value.ty != Ty::Unknown)
            && args.len() == closure.parameters.len()
        {
            self.checked_closures.insert(id);
        }
        if args.len() != closure.parameters.len() {
            self.error("E0404", span, "wrong number of closure arguments", []);
        }
        let mut local_loans = BTreeMap::new();
        macro_rules! admit_closure_packet {
            ($result:expr, $at:expr) => {
                match $result {
                    Ok(value) => value,
                    Err(error) => {
                        let at = $at;
                        self.unsupported(at, format!("closure formal packet admission: {error}"));
                        let mut failed = Value::scalar(Ty::Unknown, None, CauseId(0));
                        self.flush_handler_obligations(&mut frame);
                        self.end_invocation_loans(&mut failed, &frame, &local_loans, at);
                        caller.obligations.include(&frame.obligations, true);
                        for binding in &frame.locals {
                            self.bindings[*binding].alive = false;
                        }
                        self.loop_depth = previous_loop_depth;
                        self.restore_typing_environment(previous_typing);
                        return EvaluatedValue::unobserved(failed, self.recency_moves.len(), false);
                    }
                }
            };
        }
        for (index, param) in closure.parameters.iter().enumerate() {
            if let Some(argument) = input_packets.get(index) {
                let (mode, arg_span) = (argument.mode, argument.span);
                let mut held = admit_closure_packet!(
                    self.clone_evaluation_packet(&argument.packet, arg_span),
                    arg_span
                );
                admit_closure_packet!(
                    self.prepare_evaluation_packet(&mut held, arg_span),
                    arg_span
                );
                if mode != param.mode {
                    self.error(
                        "E0405",
                        arg_span,
                        "closure argument mode mismatch",
                        [held.value.cause],
                    );
                }
                if let Some(ty) = &param.ty {
                    held.invalidate_current_source();
                    self.ascribe_signature(&mut held.value, ty);
                    admit_closure_packet!(
                        self.prepare_evaluation_packet(&mut held, arg_span),
                        arg_span
                    );
                    self.check_storage_shape(&held.value, ty, &mut frame);
                    let ty = self.ty(ty);
                    admit_closure_packet!(
                        self.prepare_evaluation_packet(&mut held, arg_span),
                        arg_span
                    );
                    self.require_type(&held.value, &ty, arg_span);
                    let mut generics = BTreeSet::new();
                    generic_names(&ty, &mut generics);
                    if generics.is_empty() {
                        held.value.ty = ty;
                    }
                }
                admit_closure_packet!(
                    self.prepare_evaluation_packet(&mut held, arg_span),
                    arg_span
                );
                let forwarded = held.value.sources.clone();
                self.record_received_closures(&held.value, &mut frame);
                held.invalidate_current_source();
                let value = &mut held.value;
                if mode == ParameterMode::Read {
                    value.permission = Permission::Read;
                    value.construction = false;
                } else {
                    if value.permission != Permission::Write {
                        self.error(
                            "E0520",
                            arg_span,
                            "mutable anonymous argument has no writable authority",
                            [value.cause],
                        );
                    }
                    if mode == ParameterMode::SharedMut && value.temporary {
                        self.unsupported(
                            arg_span,
                            "a retained anonymous parameter cannot extend a temporary loan",
                        );
                    }
                    value.temporary |= mode == ParameterMode::Mut;
                    let loan = LoanId(self.next_loan);
                    self.next_loan += 1;
                    self.loan_parents.insert(loan, value.participants.clone());
                    local_loans.insert(loan, value.participants.clone());
                    self.start_invocation_loan(
                        loan,
                        value,
                        &frame,
                        index,
                        mode == ParameterMode::SharedMut,
                        arg_span,
                    );
                    value.participants = [Participant::Loan(loan)].into();
                }
                let start = frame.locals.len();
                admit_closure_packet!(
                    self.bind_parameter_packet(
                        &param.pattern,
                        if mode == ParameterMode::Read {
                            BindingMode::Let
                        } else {
                            BindingMode::LetMut
                        },
                        held,
                        &mut frame,
                    ),
                    arg_span
                );
                for &binding in &frame.locals[start..] {
                    self.bindings[binding].forwarded = forwarded.clone();
                }
                let owner = self
                    .lambda_contract(id)
                    .map(|contract| contract.span)
                    .unwrap_or(closure.body.span);
                self.record_static_key_parameter(param, owner, index, &frame);
            }
        }
        // A literal certified as the immediate body of Concurrent::scope runs
        // in its caller's dynamic extent. An abort still targets that caller's
        // handler boundary; an already-created callable keeps its own recipe.
        let immediate_scope = self.immediate_scope_closures.contains(&id)
            && closure
                .handler_context
                .iter()
                .all(|handler| self.active_handlers.contains(handler));
        let retained = if immediate_scope {
            None
        } else {
            self.begin_retained_handlers(&Callable::Closure(id), &closure.handler_context, &frame)
        };
        let foreign_body_before = (self.foreign_callback_depth > 0).then(|| self.snapshot_flow());
        let return_syntax = self
            .lambda_contract(id)
            .and_then(|contract| contract.return_type.clone());
        self.set_contract_environment(&frame.env);
        let mut frozen_return_source = return_syntax
            .as_ref()
            .map(|syntax| self.freeze_source_receiving_target(syntax));
        if frozen_return_source.is_none() {
            match self.signature_closure_return_target(id, span) {
                Ok(target) => frozen_return_source = target,
                Err(error) => self.unsupported(
                    span,
                    format!("closure result context lost its original Source: {error}"),
                ),
            }
        }
        if frozen_return_source.is_none() {
            frozen_return_source = contextual_return_source;
        }
        if frame.expected_return.is_none()
            && let Some(target) = &frozen_return_source
            && let Some(syntax) = &target.syntax
        {
            frame.expected_return = Some(
                self.with_typing_environment(&target.environment, |checker| checker.ty(syntax)),
            );
        }
        frame.expected_return_source = frozen_return_source.clone();
        let expected_return = frame.expected_return.clone();
        let mut result = self.expression_expected_source(
            &closure.body,
            &mut frame,
            expected_return.as_ref(),
            frozen_return_source.as_ref(),
        );
        if let Some(before) = &foreign_body_before {
            self.finish_foreign_returns(before, &mut frame, &mut result, span, foreign_exit_epoch);
        }
        self.flush_handler_obligations(&mut frame);
        self.finish_results(frame.owner, &result.value);
        for mut returned in frame.returned.clone() {
            self.transport_evaluation_packet(&mut returned, span);
            if result.value.ty == Ty::Never {
                result = returned;
            } else {
                self.receive_boundary_type(&mut returned, &mut result, span);
                let cause = self.cause(
                    CauseKind::BranchJoin,
                    span,
                    "anonymous returns retain every continuing result path",
                    [result.value.cause, returned.value.cause],
                );
                result.value = result.value.join(&returned.value, self.choice(), cause);
            }
        }
        self.finish_retained_handlers(retained, &mut frame, &mut result, span);
        let mut type_work = self.application_effect.lease_work(32768);
        let result_type = self.owned_result_type(&result, type_work.work());
        let returned_work = self.application_effect.return_work(type_work);
        let result_type = result_type.and_then(|result| returned_work.map(|()| result));
        let mut output = result.transform_value(|mut result| {
            self.flush_handler_obligations(&mut frame);
            if result.temporary {
                result.permission = Permission::Read;
                result.construction = false;
            }
            let returned_nodes = self.heap.reachable(result.origins.nodes.iter().copied());
            for (parameter, (_, argument, _)) in closure.parameters.iter().zip(args) {
                if parameter.mode != ParameterMode::SharedMut {
                    continue;
                }
                let moves = &self.recency_moves[arguments_recency..];
                let cost = argument
                    .origins
                    .nodes
                    .len()
                    .checked_mul(moves.len().saturating_add(1));
                if !cost.is_some_and(|cost| self.application_effect.admit(cost)) {
                    self.unsupported(span, "retained input transport exhausted its work bound");
                    break;
                }
                let mut origins = argument.origins.nodes.clone();
                for &(recent, older) in moves {
                    if origins.remove(&recent) {
                        origins.insert(older);
                    }
                }
                if !returned_nodes.is_disjoint(&origins) {
                    result.retention_result = true;
                    frame.obligations.retention = true;
                    for binding in &frame.locals {
                        if self.bindings[*binding].parameter
                            && !self.bindings[*binding]
                                .value
                                .origins
                                .nodes
                                .is_disjoint(&origins)
                        {
                            self.mark_write(*binding);
                        }
                    }
                    for source in &argument.sources {
                        self.mark_write(*source);
                    }
                }
            }
            self.record_closure_exposure(
                &result,
                &frame,
                super::super::closure_exclusivity::ExposureKind::Returned,
                span,
            );
            self.escape_obligations(&result, &mut frame);
            self.record_callable_local_effects(true, id, &frame, &result);
            self.check_deep_uncertainty(&result, span);
            if !immediate_scope {
                self.record_retained_handlers(
                    Callable::Closure(id),
                    &closure.handler_context,
                    &frame.obligations.selected_handlers,
                    &result,
                    frame.owner,
                    span,
                );
                self.record_returned_handler_context(
                    Callable::Closure(id),
                    &closure.handler_context,
                    &result,
                    &frame,
                    span,
                );
            }
            frame.obligations.handler_environment |=
                self.has_retained_handlers(&Callable::Closure(id));
            self.check_lambda_contract(id, &frame, &mut result, span);
            self.remember_closure_source(id, result_type, &frame);
            // Check before local loans are projected back to their caller roots.
            // Captured paths and separate parameters remain independent access
            // participants during this invocation, as for named callables.
            // A signature/latent probe has fresh hypothetical parameters; it keeps
            // these accesses as obligations but has no actual argument relation.
            let probe = self
                .closure_invocation_stack
                .last()
                .is_some_and(|id| self.closure_invocations[id.0 as usize].probe);
            self.record_closure_exclusivity(id, &frame, span, probe);
            self.unwind_foreign_abort_exits(
                frame.owner,
                &frame.locals,
                &local_loans,
                foreign_exit_epoch,
            );
            let summary = self.invocation_summary(id, &frame, &returned_nodes);
            let summary = self.retain_invocation_summary(summary);
            self.completed_invocation =
                Some(super::contracts::CompletedInvocation::Recorded(summary));
            self.export_conditional_result_family(&mut result, frame.owner, span);
            self.end_invocation_loans(&mut result, &frame, &local_loans, span);
            self.transfer_results(&result, frame.owner, caller.owner);
            let formal_environment = closure.captures.iter().any(|binding| {
                self.bindings[*binding]
                    .value
                    .callback_parameters
                    .iter()
                    .any(|parameter| self.bindings[*parameter].owner == caller.owner)
            });
            for (&binding, &mode) in &frame.obligations.named {
                if self.bindings[binding].owner == caller.owner
                    && self.bindings[binding].parameter
                    && mode != Mode::Read
                {
                    caller.obligations.parameter_write = true;
                }
                if self.bindings[binding].owner != caller.owner && self.bindings[binding].alive {
                    caller
                        .obligations
                        .named
                        .entry(binding)
                        .and_modify(|m| *m = (*m).max(mode))
                        .or_insert(mode);
                    if !caller.callback_call
                        && (!formal_environment
                            || frame.obligations.concrete.contains_key(&binding))
                    {
                        caller
                            .obligations
                            .concrete
                            .entry(binding)
                            .and_modify(|m| *m = (*m).max(mode))
                            .or_insert(mode);
                        if frame.obligations.direct.contains_key(&binding) {
                            caller
                                .obligations
                                .direct
                                .entry(binding)
                                .and_modify(|m| *m = (*m).max(mode))
                                .or_insert(mode);
                        }
                    }
                }
            }
            if !caller.callback_call {
                caller.obligations.concrete_effects.extend(
                    if formal_environment {
                        frame.obligations.concrete_effects.iter()
                    } else {
                        frame.obligations.effects.iter()
                    }
                    .cloned(),
                );
            }
            caller
                .obligations
                .copy_boundaries
                .extend(&frame.obligations.copy_boundaries);
            caller.obligations.handler_environment |= frame.obligations.handler_environment;
            caller.obligations.effects.extend(frame.obligations.effects);
            caller
                .obligations
                .performed_operations
                .extend(frame.obligations.performed_operations);
            caller
                .obligations
                .selected_handlers
                .extend(frame.obligations.selected_handlers);
            caller.obligations.symbolic |= frame.obligations.symbolic;
            caller
                .obligations
                .symbolic_uses
                .extend(&frame.obligations.symbolic_uses);
            for mut access in frame.obligations.accesses {
                access.participants = super::recursive_calls::normalize_participants(
                    &access.participants,
                    &local_loans,
                );
                caller.obligations.accesses.push(access);
            }
            for binding in frame.locals {
                self.check_authority_use(binding);
                self.bindings[binding].alive = false;
            }
            self.loop_depth = previous_loop_depth;
            result.sources.clear();
            result.participants =
                super::recursive_calls::normalize_participants(&result.participants, &local_loans);
            result.through_return = true;
            result.unsuffixed_numeric = false;
            result.static_coordinate = None;
            self.restore_typing_environment(previous_typing);
            self.complete_closure_invocation();
            (result, self.recency_moves.len())
        });
        if output.source_valid
            && let Some(target) = &frozen_return_source
        {
            self.record_received_type(&mut output, target, span);
        }
        output
    }
    fn record_static_key_parameter(
        &mut self,
        parameter: &Parameter,
        owner: Span,
        index: usize,
        frame: &Frame,
    ) {
        let Some((binder, name)) = self.static_key_carrier(parameter) else {
            return;
        };
        let Some(&binding) = frame.env.get(&name) else {
            return;
        };
        if !self.bindings[binding].parameter || self.bindings[binding].owner != frame.owner {
            self.unsupported(
                parameter.span,
                "static-key carrier is not this invocation's parameter binding",
            );
            return;
        }
        if self.static_key_parameters.iter().any(|proof| {
            proof.binder == binder
                && proof.owner == owner
                && proof.parameter == index as u32
                && proof.name == name
        }) {
            return;
        }
        let cause = self.cause(
            CauseKind::Source,
            parameter.span,
            "runtime parameter carries its declared static coordinate binder",
            [self.bindings[binding].value.cause],
        );
        self.static_key_parameters
            .push(super::super::StaticKeyParameter {
                binder,
                owner,
                parameter: index as u32,
                name,
                cause,
            });
    }
    pub(super) fn record_inference_resolution(
        &mut self,
        binder: &str,
        selected: &Ty,
        site: Span,
        origin: CauseId,
    ) -> CauseId {
        let cause = self.cause(
            CauseKind::Source,
            site,
            "result context selects a producing invocation's owned type variable",
            [origin],
        );
        self.inference_resolutions
            .push(super::super::InferenceResolution {
                binder: binder.into(),
                selected: selected.clone(),
                site,
                origin,
                cause,
            });
        cause
    }
    fn is_private_fresh(&self, value: &Value) -> bool {
        self.pending_copy_dependencies(value).is_empty()
            && value.permission == Permission::Write
            && value.publication != Publication::Immutable
            && !value.origins.nodes.is_empty()
            && !self.has_writer(value)
            && !value.mutable_environment
            && !value.observer_environment
            && self
                .heap
                .reachable(value.origins.nodes.iter().copied())
                .iter()
                .all(|node| {
                    matches!(
                        self.heap.nodes[node.0 as usize].kind,
                        OriginKind::Fresh(_) | OriginKind::Older(_)
                    )
                })
    }
    pub(super) fn verify_local_definitions(&mut self, start: usize, parent: &Frame) {
        let budget = std::mem::take(&mut self.budget_coverage);
        let end = self.functions.len();
        for id in start..end {
            let function = self.functions[id].syntax.clone();
            if self.functions[id].owner != Some(parent.owner)
                || !self
                    .checked_definitions
                    .insert(self.functions[id].definition)
            {
                continue;
            }
            self.ensure_named_environment(id);
            let previous_typing = self.generic_scope(id);
            let preview = self.snapshot_flow();
            let active = std::mem::replace(
                &mut self.active_handlers,
                self.functions[id].handler_context.clone(),
            );
            self.validate_defaults(id, parent.env.clone());
            let mut arguments = Vec::new();
            for (index, parameter) in function.parameters.iter().enumerate() {
                let ty = parameter
                    .ty
                    .as_ref()
                    .map(|ty| self.ty(ty))
                    .unwrap_or(Ty::Unknown);
                let mut value =
                    self.formal_value(ty, index as u32, parameter.span, &mut BTreeSet::new());
                if parameter.mode != ParameterMode::Read && !self.formal_is_immutable(&value.ty) {
                    value.permission = Permission::Write;
                }
                if let Some(syntax) = &parameter.ty {
                    let mut shape_frame = parent.clone();
                    self.promise_array_shape(&value, syntax, &mut shape_frame);
                }
                let mut schema_frame = parent.clone();
                self.register_formal_record_schema(id, index as u32, &value, &mut schema_frame);
                arguments.push((parameter.mode, value, parameter.span));
            }
            for a in 0..arguments.len() {
                for b in a + 1..arguments.len() {
                    if arguments[a].0 == ParameterMode::Mut || arguments[b].0 == ParameterMode::Mut
                    {
                        let left = self
                            .heap
                            .reachable(arguments[a].1.origins.nodes.iter().copied());
                        let right = self
                            .heap
                            .reachable(arguments[b].1.origins.nodes.iter().copied());
                        for x in &left {
                            for y in &right {
                                self.heap.set_relation(*x, *y, Relation::DISJOINT);
                            }
                        }
                    }
                }
            }
            let _ = self.invoke_named_declaration_probe(id, arguments, function.span);
            self.restore_definition_state(&preview);
            self.active_handlers = active;
            self.restore_typing_environment(previous_typing);
        }
        self.budget_coverage = budget;
    }
    fn record_received_closures(&self, value: &Value, frame: &mut Frame) {
        for callable in self.graph_callables(value) {
            if let Callable::Closure(id) = callable {
                frame
                    .received_closures
                    .entry(id)
                    .or_insert((self.closures[id].node, value.cause));
            }
        }
    }

    pub(super) fn escape_obligations(&mut self, result: &Value, frame: &mut Frame) {
        if !self.pending_copy_dependencies(result).is_empty()
            && self
                .graph_callables(result)
                .iter()
                .any(|callable| match callable {
                    Callable::Closure(id) => !self.closures[*id].captures.is_empty(),
                    Callable::Named(id, _) => !self.functions[*id].captures.is_empty(),
                    _ => false,
                })
            && let Some(id) = self.pending_copy_dependencies(result).first()
        {
            let span = self.copy_boundaries[id.0 as usize].span;
            self.require_copy_dependencies(
                result,
                span,
                "escaping an environment that retains conditional copy output",
            );
        }
        frame
            .obligations
            .copy_boundaries
            .extend(self.pending_copy_dependencies(result));
        let span = self
            .call_stack
            .last()
            .map(|id| self.functions[*id].syntax.span)
            .unwrap_or(Span {
                file: self.file,
                start: 0,
                end: 0,
            });
        self.check_deep_uncertainty(result, span);
        self.publish_named_environments(result);
        let reachable = self.heap.reachable(result.origins.nodes.iter().copied());
        let mut exposed: BTreeMap<NodeId, usize> = BTreeMap::new();
        let mut exposed_bindings: BTreeMap<BindingId, usize> = BTreeMap::new();
        let mut declaration_work = self.application_effect.lease_work(4_000_000);
        let mut declaration_error = None;
        for (id, closure) in self.closures.iter().enumerate() {
            if reachable.contains(&closure.node)
                && (!closure.captures.is_empty()
                    || self.has_retained_handlers(&Callable::Closure(id)))
            {
                if self.scope_is_within(closure.owner, frame.owner) {
                    frame.obligations.capture = true;
                }
                for binding in &closure.captures {
                    let binding_id = *binding;
                    let binding = &self.bindings[binding_id];
                    let mode = if closure.writes.contains(&binding_id) {
                        Mode::Retain
                    } else {
                        Mode::Read
                    };
                    let declaration = match self
                        .original_named_declaration(binding_id, declaration_work.work())
                    {
                        Ok(declaration) => declaration.is_some(),
                        Err(error) => {
                            declaration_error = Some(error);
                            false
                        }
                    };
                    if !frame.received_closures.contains_key(&id)
                        && !self.scope_is_within(binding.owner, frame.owner)
                        && !declaration
                    {
                        frame
                            .obligations
                            .named
                            .entry(binding_id)
                            .and_modify(|old| *old = (*old).max(mode))
                            .or_insert(mode);
                        frame
                            .obligations
                            .concrete
                            .entry(binding_id)
                            .and_modify(|old| *old = (*old).max(mode))
                            .or_insert(mode);
                        frame
                            .obligations
                            .direct
                            .entry(binding_id)
                            .and_modify(|old| *old = (*old).max(mode))
                            .or_insert(mode);
                    }
                    if closure.writes.contains(&binding_id)
                        && self.scope_is_within(binding.owner, frame.owner)
                    {
                        *exposed_bindings.entry(binding_id).or_default() += 1;
                    }
                    if binding.mode.is_mutable() || binding.mode.is_reassignable() {
                        for node in &binding.value.origins.nodes {
                            *exposed.entry(*node).or_default() += 1;
                        }
                    }
                }
            }
        }
        let returned = self.application_effect.return_work(declaration_work);
        if let Some(error) = declaration_error.or_else(|| returned.err()) {
            self.unsupported(
                span,
                format!("escaping capture declaration identity: {error}"),
            );
        }
        for callable in self.graph_callables(result) {
            let Callable::Named(id, _) = callable else {
                continue;
            };
            let info = self.functions[id].clone();
            if info.captures.is_empty() && !self.has_retained_handlers(&Callable::Named(id, None)) {
                continue;
            }
            if info
                .owner
                .is_some_and(|owner| self.scope_is_within(owner, frame.owner))
            {
                frame.obligations.capture = true;
            }
            for binding in info.captures {
                if info.writes.contains(&binding)
                    && self.scope_is_within(self.bindings[binding].owner, frame.owner)
                {
                    *exposed_bindings.entry(binding).or_default() += 1;
                }
                if self.bindings[binding].mode.is_mutable()
                    || self.bindings[binding].mode.is_reassignable()
                {
                    for node in &self.bindings[binding].value.origins.nodes {
                        *exposed.entry(*node).or_default() += 1;
                    }
                }
            }
        }
        if exposed_bindings.values().any(|count| *count > 1) {
            frame.obligations.retention = true;
        }
        for (count_node, count) in exposed {
            let direct = self.fields.iter().any(|((parent, slot), value)| {
                reachable.contains(parent)
                    && !matches!(slot, Slot::Capture(_))
                    && value.origins.nodes.contains(&count_node)
            });
            if count > 1 || direct {
                frame.obligations.retention = true;
            }
        }
    }
    pub(super) fn check_exclusivity(&mut self, accesses: &[AccessFact], span: Span) {
        let accesses = self.current_accesses(accesses);
        for (a_index, a) in accesses.iter().enumerate() {
            for b in &accesses[a_index + 1..] {
                if a.mode != Mode::Write && b.mode != Mode::Write {
                    continue;
                }
                if a.participants.is_empty()
                    || b.participants.is_empty()
                    || (a.participants.len() == 1 && a.participants == b.participants)
                {
                    continue;
                }
                let has_loan = a
                    .participants
                    .iter()
                    .chain(&b.participants)
                    .any(|p| matches!(p, Participant::Loan(_)));
                if !has_loan {
                    continue;
                }
                let slot_disjoint = match (&a.slot, &b.slot) {
                    (Some(a), Some(b)) => {
                        a != b
                            && !matches!(a, Slot::AnyIndex | Slot::RowTail(_))
                            && !matches!(b, Slot::AnyIndex | Slot::RowTail(_))
                    }
                    _ => false,
                };
                if !slot_disjoint && !self.origins_disjoint(&a.origins, &b.origins) {
                    let a_writes = accesses.iter().any(|access| {
                        access.mode != Mode::Read
                            && !access.participants.is_disjoint(&a.participants)
                    });
                    let b_writes = accesses.iter().any(|access| {
                        access.mode != Mode::Read
                            && !access.participants.is_disjoint(&b.participants)
                    });
                    self.error(
                        if a_writes && b_writes {
                            "E0523"
                        } else {
                            "E0524"
                        },
                        span,
                        "independent access participants have possibly overlapping storage origins",
                        [a.cause, b.cause],
                    );
                    return;
                }
            }
        }
    }
    pub(super) fn check_annotations(
        &mut self,
        function: &Function,
        frame: &Frame,
        enclosing: Option<ScopeId>,
        checking: AnnotationCheck,
    ) {
        let mut declared = BTreeMap::new();
        let mut providers = Vec::new();
        let mut effects = BTreeSet::new();
        let (mut mut_cap, mut retained_cap, mut capture_cap, mut closed_state, mut closed_effect) =
            (false, false, false, false, false);
        let higher_order = function.parameters.iter().any(|p| {
            p.ty.as_ref().is_some_and(|t| {
                matches!(
                    self.expanded(&self.ty_readonly_public(t), &mut BTreeSet::new()),
                    Ty::Callable(..)
                )
            })
        }) || function.return_type.as_ref().is_some_and(|t| {
            matches!(
                self.expanded(&self.ty_readonly_public(t), &mut BTreeSet::new()),
                Ty::Callable(..)
            )
        });
        for annotation in &function.annotations {
            let text = annotation.text.trim();
            if annotation.kind == AnnotationKind::Effect {
                if text
                    .trim_start_matches('@')
                    .trim_matches(['{', '}'])
                    .split(['+', ','])
                    .any(|effect| effect.trim().trim_start_matches("Prelude::") == "Parallel")
                {
                    self.error(
                        "E0620",
                        annotation.span,
                        "Parallel is not an effect annotation",
                        [],
                    );
                }
                if text == "@{}" {
                    closed_effect = true;
                } else {
                    effects.extend(self.effect_row(annotation));
                }
                continue;
            }
            match text {
                "&mut" => mut_cap = true,
                "&^mut" => retained_cap = true,
                "&capture" => capture_cap = true,
                "&{}" => closed_state = true,
                "&closure" => self.error(
                    "E0534",
                    annotation.span,
                    "named definitions must declare concrete capture sources",
                    [],
                ),
                _ if text.starts_with("&{") => {
                    let Some(group) = super::contracts::state_group(text) else {
                        self.error("E0538", annotation.span, "malformed state group", []);
                        continue;
                    };
                    let captured = group.capture_owner.is_some();
                    let header = group.capture_owner.unwrap_or("");
                    let mut owner = None;
                    for super::contracts::StateItem { mode, name } in group.items() {
                        let Some(&binding) = frame.env.get(name) else {
                            self.error(
                                "E0204",
                                annotation.span,
                                format!("unknown state source {name}"),
                                [],
                            );
                            continue;
                        };
                        let actual_owner = self.bindings[binding].owner;
                        if captured {
                            if actual_owner == ScopeId(0) || actual_owner == frame.owner {
                                self.error("E0538",annotation.span,"capture group source must belong to an enclosing callable layer",[]);
                            }
                            if owner.is_some_and(|previous| previous != actual_owner) {
                                self.error(
                                    "E0538",
                                    annotation.span,
                                    "one capture group cannot merge different callable layers",
                                    [],
                                );
                            }
                            owner = Some(actual_owner);
                            let owner_name = self.scope_names.get(&actual_owner).cloned().flatten();
                            if header.is_empty()
                                && owner_name.is_some()
                                && enclosing.is_some_and(|parent| parent != actual_owner)
                            {
                                self.error(
                                    "E0538",
                                    annotation.span,
                                    "farther named capture requires an explicit owner",
                                    [],
                                );
                            }
                            if !header.is_empty() && owner_name.as_deref() != Some(header) {
                                self.error("E0538",annotation.span,"explicit capture owner does not match the resolved binding's layer",[]);
                            }
                        } else if actual_owner != ScopeId(0)
                            || self.bindings[binding]
                                .value
                                .callables
                                .iter()
                                .any(|c| matches!(c, Callable::Named(..)))
                        {
                            self.error(
                                "E0538",
                                annotation.span,
                                "global state group requires a module storage binding",
                                [],
                            );
                        }
                        declared
                            .entry(binding)
                            .and_modify(|old: &mut Mode| *old = (*old).max(mode))
                            .or_insert(mode);
                    }
                    if captured && owner.is_none() {
                        self.error(
                            "E0538",
                            annotation.span,
                            "capture group requires a source binding",
                            [],
                        );
                    }
                }
                _ => {
                    let name = text.trim_start_matches('&');
                    if let Some(&binding) = frame.env.get(name) {
                        match self.original_named_declaration_with_work(binding) {
                            Ok(Some(provider)) => providers.push(provider),
                            Ok(None) => {
                                self.error(
                                    "E0539",
                                    annotation.span,
                                    "a callable value alias is not a state contract provider",
                                    [],
                                );
                            }
                            Err(error) => self.unsupported(
                                annotation.span,
                                format!("contract provider declaration identity: {error}"),
                            ),
                        }
                    } else {
                        self.error(
                            "E0204",
                            annotation.span,
                            format!("unknown contract provider {name}"),
                            [],
                        );
                    }
                }
            }
        }
        if (closed_state || closed_effect) && !higher_order {
            self.error(
                "E0542",
                function.span,
                "empty rows require a higher-order signature",
                [],
            );
        }
        if closed_state
            && (!frame.obligations.named.is_empty()
                || frame.obligations.parameter_write
                || frame.obligations.capture
                || frame.obligations.handler_environment
                || frame.obligations.retention)
        {
            self.error(
                "E0534",
                function.span,
                "closed capability row has concrete invocation obligations",
                [],
            );
        }
        if closed_effect && !frame.obligations.effects.is_empty() {
            self.error(
                "E0534",
                function.span,
                "closed effect row has residual operations",
                [],
            );
        }
        for (&binding, &required) in &frame.obligations.concrete {
            let covered = declared.get(&binding).is_some_and(|mode| *mode >= required)
                || (!frame.obligations.direct.contains_key(&binding)
                    && providers
                        .iter()
                        .any(|provider| self.provider_covers(*provider, binding, required)));
            if !covered && !closed_state {
                self.error(
                    "E0510",
                    function.span,
                    format!(
                        "undeclared concrete state access to {}",
                        self.bindings[binding].name
                    ),
                    [self.bindings[binding].value.cause],
                );
            }
        }
        if frame.obligations.parameter_write && !mut_cap && !retained_cap && !closed_state {
            self.error(
                "E0510",
                function.span,
                "borrowed parameter mutation requires &mut",
                [],
            );
        }
        if frame.obligations.retention && !retained_cap && !closed_state {
            self.error(
                "E0510",
                function.span,
                "surviving independent writable sharing requires &^mut",
                [],
            );
        }
        if frame.obligations.capture && !capture_cap && !closed_state {
            self.error(
                "E0510",
                function.span,
                "new surviving lexical environment requires &capture",
                [],
            );
        }
        for effect in &frame.obligations.concrete_effects {
            if !effects.contains(effect) && !closed_effect {
                self.error(
                    "E0612",
                    function.span,
                    format!("undeclared residual effect {effect}"),
                    [],
                );
            }
        }
        // Minimality belongs to the declaration's conservative body check.
        // A selected call may exclude a branch that uses this capability;
        // its remaining obligations must still fit the declared upper bound.
        for (&binding, &mode) in &declared {
            if checking == AnnotationCheck::Declaration
                && frame
                    .obligations
                    .named
                    .get(&binding)
                    .is_none_or(|required| *required < mode)
                && !self.symbolic_named_use(&frame.obligations, binding, mode)
            {
                self.error(
                    "E0529",
                    function.span,
                    "concrete state capability exceeds actual use",
                    [],
                );
            }
        }
        if checking == AnnotationCheck::Declaration
            && ((mut_cap && !frame.obligations.parameter_write)
                || (retained_cap && !frame.obligations.retention)
                || (capture_cap && !frame.obligations.capture))
        {
            self.error(
                "E0529",
                function.span,
                "concrete capability exceeds actual use",
                [],
            );
        }
        for provider in providers {
            if checking == AnnotationCheck::Declaration
                && !frame
                    .obligations
                    .named
                    .iter()
                    .any(|(&binding, &mode)| self.provider_covers(provider, binding, mode))
            {
                self.error(
                    "E0529",
                    function.span,
                    "provider reference covers no inherited named state",
                    [],
                );
            }
        }
    }
    fn provider_covers(&self, provider: usize, binding: BindingId, required: Mode) -> bool {
        let info = &self.functions[provider];
        let name = &self.bindings[binding].name;
        info.syntax
            .annotations
            .iter()
            .filter(|a| a.kind == AnnotationKind::Capability && a.text.starts_with("&{"))
            .filter_map(|annotation| super::contracts::state_group(annotation.text.trim()))
            .any(|group| {
                group
                    .items()
                    .any(|item| item.name == name && item.mode >= required)
            })
    }
    fn ty_readonly_public(&self, syntax: &TypeExpr) -> Ty {
        match &syntax.kind {
            TypeKind::Name { path, .. } => Ty::Named(path.join("::")),
            TypeKind::Callable {
                parameters, result, ..
            } => Ty::Callable(
                parameters.iter().map(|_| Ty::Unknown).collect(),
                Box::new(
                    result
                        .as_ref()
                        .map(|t| self.ty_readonly_public(t))
                        .unwrap_or(Ty::Unit),
                ),
            ),
            _ => Ty::Unknown,
        }
    }
    pub(super) fn builtin(
        &mut self,
        name: &str,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        if name == "Div::budget" {
            return self.finite_budget(&args, span, frame);
        }
        if self.operations.contains_key(name) {
            return self.perform_operation(name, &args, span, frame);
        }

        if matches!(
            name,
            "assert" | "panic" | "len" | "clone" | "clone_immut" | "inner"
        ) {
            for (mode, value, arg_span) in &args {
                if *mode != ParameterMode::Read {
                    self.error(
                        "E0405",
                        *arg_span,
                        "this primitive borrows its argument read-only",
                        [value.cause],
                    );
                }
            }
        }
        if let Some(value) = self.standard_builtin(name, &args, span, frame) {
            return value;
        }
        match name {
            "inner" => {
                if args.len() != 1 {
                    self.error("E0314", span, "inner requires one nominal wrapper", []);
                }
                args.first()
                    .map(|(_, value, _)| self.nominal_inner(value, span, frame))
                    .unwrap_or_else(|| self.unit(span))
            }
            "assert" => {
                if !(1..=2).contains(&args.len()) {
                    self.error(
                        "E0314",
                        span,
                        "assert requires a condition and an optional message",
                        [],
                    );
                }
                if let Some((_, message, _)) = args.get(1) {
                    self.require_type(message, &Ty::Str, span);
                }
                if let Some((_, value, _)) = args.first() {
                    self.require_type(value, &Ty::Bool, span);
                } else {
                    self.error("E0404", span, "assert requires a condition", []);
                }
                self.unit(span)
            }
            "panic" => {
                if args.len() != 1 {
                    self.error("E0314", span, "panic requires exactly one message", []);
                }
                if let Some((_, message, _)) = args.first() {
                    self.require_type(message, &Ty::Str, span);
                }
                let mut value = self.unit(span);
                value.ty = Ty::Never;
                value.abnormal = true;
                value
            }
            "len" => {
                if let Some((_, value, _)) = args.first() {
                    self.access(value, None, Mode::Read, span, frame);
                }
                if args.len() != 1 {
                    self.error("E0314", span, "len requires exactly one collection", []);
                }
                if let Some((_, value, _)) = args.first()
                    && !matches!(
                        self.expanded_at(&value.ty, span.file),
                        Ty::Str | Ty::Bytes | Ty::Array(_) | Ty::Set(_) | Ty::Map(..)
                    )
                {
                    self.error(
                        "E0301",
                        span,
                        "len requires text, bytes, or an admitted collection",
                        [value.cause],
                    );
                }
                let cause = self.cause(
                    CauseKind::Source,
                    span,
                    "collection length",
                    args.first().map(|a| a.1.cause),
                );
                Value::scalar(Ty::Int("int".into()), None, cause)
            }
            "clone" | "clone_immut" => {
                if let Some((_, value, _)) = args.first() {
                    self.concurrent_copy_boundary(value, span);
                    if name == "clone"
                        && let Some(cloned) = self.concurrent_clone_sender(value, span, frame)
                    {
                        return cloned;
                    }
                    self.deep_read(value, span, frame);
                    let accesses = frame.obligations.accesses.len();
                    let returned = frame.returned.len();
                    let result = self.clone_value(value, span, frame, name == "clone_immut");
                    self.transport_frame_prefix(frame, accesses, returned);
                    result
                } else {
                    self.error("E0404", span, "clone requires a value", []);
                    self.unit(span)
                }
            }
            "Array::push" | "Array::insert" | "Map::set" => {
                let Some((mode, target, _)) = args.first() else {
                    self.error("E0404", span, "storage operation requires a receiver", []);
                    return self.unit(span);
                };
                if *mode != ParameterMode::Mut {
                    self.error(
                        "E0405",
                        span,
                        "storage receiver requires mut",
                        [target.cause],
                    );
                }
                if target.permission != Permission::Write {
                    self.error(
                        "E0520",
                        span,
                        "storage receiver is read-only",
                        [target.cause],
                    );
                }
                for active in &self.active_iterations {
                    if !self.origins_disjoint(active, &target.origins) {
                        self.error(
                            "E0526",
                            span,
                            "structural mutation invalidates active iteration",
                            [target.cause],
                        );
                        break;
                    }
                }
                self.access(target, None, Mode::Write, span, frame);
                if let Some((mode, inserted, insert_span)) = args.last() {
                    let mut inserted = inserted.clone();
                    if *mode == ParameterMode::SharedMut {
                        if inserted.temporary {
                            self.unsupported(
                                *insert_span,
                                "retained storage cannot extend a temporary loan",
                            );
                        }
                        if inserted.permission != Permission::Write {
                            self.error(
                                "E0520",
                                *insert_span,
                                "retained insertion has no write authority",
                                [inserted.cause],
                            );
                        }
                        for &source in &inserted.sources {
                            self.use_binding(source, Mode::Retain, frame);
                        }
                        if inserted
                            .sources
                            .iter()
                            .any(|id| self.bindings[*id].parameter)
                        {
                            frame.obligations.retention = true;
                        }
                    } else if inserted.construction {
                        if inserted.internal_aliases && !inserted.marker {
                            self.error(
                                "E0510",
                                *insert_span,
                                "internally shared writable copy requires ^mut",
                                [inserted.cause],
                            );
                        }
                        inserted.publication = Publication::Live;
                        inserted.construction = false;
                    } else {
                        inserted.permission = Permission::Read;
                    }
                    for node in &target.origins.nodes {
                        let slot = Slot::Index(
                            self.fields
                                .keys()
                                .filter(|(parent, _)| parent == node)
                                .count() as i64,
                        );
                        self.store_field(*node, slot, inserted.clone());
                    }
                }
                self.unit(span)
            }
            "Array::truncate" => {
                if let Some((mode, target, _)) = args.first() {
                    if *mode != ParameterMode::Mut {
                        self.error("E0405", span, "truncate receiver requires mut", []);
                    }
                    if target.permission != Permission::Write {
                        self.error(
                            "E0520",
                            span,
                            "truncate receiver is read-only",
                            [target.cause],
                        );
                    }
                    self.access(target, None, Mode::Write, span, frame);
                }
                self.unit(span)
            }
            "Some" => {
                let payload = self.constructor_payload(&args, span, frame);
                self.standard_option(payload, Some(true), span, frame.owner)
            }
            "Ok" | "Err" => {
                let payload = self.constructor_payload(&args, span, frame);
                self.make_result(name == "Ok", payload, span, frame.owner)
            }
            "None" => {
                let mut value = self.unit(span);
                value.ty = Ty::Optional(Box::new(Ty::Unknown));
                value.constant = None;
                value
            }
            _ => {
                if self.operations.contains_key(name) {
                    return self.perform_operation(name, &args, span, frame);
                }
                if let Some((family, operation)) = name.split_once("::")
                    && let Some(effect) = self.effects.get(family).cloned()
                    && let Some(declaration) =
                        effect.operations.iter().find(|op| op.name == operation)
                {
                    frame.obligations.effects.insert(family.into());
                    frame.obligations.concrete_effects.insert(family.into());
                    let ty = declaration
                        .return_type
                        .as_ref()
                        .map(|t| self.ty(t))
                        .unwrap_or(Ty::Unit);
                    return self.formal_value(ty, span.start, span, &mut BTreeSet::new());
                }
                self.unsupported(span, format!("builtin {name}"));
                Value::scalar(
                    Ty::Unknown,
                    None,
                    self.cause(
                        CauseKind::MissingProof,
                        span,
                        "resolved builtin has no implemented result contract",
                        [],
                    ),
                )
            }
        }
    }
    pub(super) fn constructor_payload(
        &mut self,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let mut values = Vec::new();
        for (mode, value, arg_span) in args {
            let mut value = value.clone();
            if *mode == ParameterMode::Mut {
                self.error(
                    "E0405",
                    *arg_span,
                    "a constructor cannot retain a temporary mut argument",
                    [value.cause],
                );
            }
            if *mode == ParameterMode::SharedMut {
                if value.permission != Permission::Write {
                    self.error(
                        "E0520",
                        *arg_span,
                        "retained constructor argument has no write authority",
                        [value.cause],
                    );
                }
                if value.temporary {
                    self.unsupported(*arg_span, "constructor cannot extend a temporary loan");
                }
                for source in &value.sources {
                    self.use_binding(*source, Mode::Retain, frame);
                }
                value.marker = true;
            }
            values.push(value);
        }
        match values.len() {
            0 => self.unit(span),
            1 => values.pop().unwrap(),
            _ => {
                let values_recency = self.recency_moves.len();
                let node = self.allocate_owned(span, 0x2000_0000, frame.owner);
                let mut tuple = Value::reference(
                    Ty::Tuple(values.iter().map(|value| value.ty.clone()).collect()),
                    node,
                    self.heap.nodes[node.0 as usize].cause,
                );
                for (index, mut value) in values.into_iter().enumerate() {
                    self.transport_value_since(&mut value, values_recency);
                    tuple.numeric.include(&value.numeric);
                    tuple.results.extend(&value.results);
                    tuple.must_results.extend(&value.must_results);
                    tuple.scoped.extend(&value.scoped);
                    tuple.callback_parameters.extend(&value.callback_parameters);
                    tuple.internal_aliases |= value.permission == Permission::Write
                        && !value.construction
                        && self.has_writer(&value)
                        && !value.marker;
                    tuple.mutable_environment |= value.mutable_environment;
                    tuple.observer_environment |= value.observer_environment;
                    self.store_field(node, Slot::Tuple(index as u32), value);
                }
                tuple
            }
        }
    }
    pub(super) fn clone_value_unrecorded(
        &mut self,
        source: &Value,
        span: Span,
        owner: ScopeId,
        immutable: bool,
        resource_eligibility: bool,
    ) -> Value {
        if self.has_unresolved_row(source) {
            self.unsupported(span, "copying an open row requires complete resource, environment and Result multiplicity facts");
            return source.clone();
        }
        if self.has_window(source) {
            self.unsupported(span,"copying windows requires preservation of mixed backing and selected-element graph aliases");
        }
        if !resource_eligibility && self.contains_resource(source) {
            self.error("E0530",span,"resources and scoped authority cannot be copied without an explicit resource contract",[source.cause]);
        }
        if self.equality_has_generic(&source.ty) {
            self.unsupported(span,"generic copy eligibility is not established for every possible instance, including retained environments and resources");
        }
        let reachable = self.heap.reachable(source.origins.nodes.iter().copied());
        if self.fields.iter().any(|((node, _), field)| {
            reachable.contains(node) && !field.results.is_subset(&source.results)
        }) {
            self.unsupported(span,"copying nested Result data requires complete carrier membership and multiplicity facts");
        }
        let closures = self.graph_callables(source);
        let captured = closures.iter().any(|callable| match callable {
            Callable::Closure(id) => !self.closures[*id].captures.is_empty(),
            Callable::Named(id, _) => !self.functions[*id].captures.is_empty(),
            _ => false,
        });
        if closures
            .iter()
            .any(|callable| matches!(callable, Callable::Symbolic(..)))
        {
            self.unsupported(
                span,
                "copy eligibility of an abstract callable environment is not established",
            );
        }
        if source.mutable_environment || source.observer_environment || captured {
            self.error(
                "E0530",
                span,
                "captured live or mutable environments cannot be cloned",
                [source.cause],
            );
        }
        if source.origins.nodes.is_empty() {
            let mut value = source.clone();
            value.unsuffixed_numeric = false;
            value.literal_number = false;
            value.static_coordinate = None;
            value.scoped.clear();
            self.copy_result_duties(&mut value, span, owner);
            return value;
        }
        if let Some(value) = self.canonical_ordinary_clone(source, span, owner, immutable) {
            return value;
        }
        if reachable
            .iter()
            .any(|node| self.heap.relation(*node, *node).equal != Condition::TRUE)
        {
            self.unsupported(span,"copying a summarized nonordinary graph requires its own resource, Result, environment or row transfer proof");
            return source.clone();
        }
        let mut copies = BTreeMap::new();
        for node in &reachable {
            let copy = self.allocate(
                span,
                self.loop_allocation_context(owner)
                    .0
                    .wrapping_mul(65537)
                    .wrapping_add(node.0),
                owner,
            );
            copies.insert(*node, copy);
            if let Some(ty) = self.storage_types.get(node).cloned() {
                self.storage_types.insert(copy, ty);
            }
            if let Some(length) = self.array_lengths.get(node).copied() {
                self.array_lengths.insert(copy, length);
            }
            if self.fixed_arrays.contains(node) {
                self.fixed_arrays.insert(copy);
            }
        }
        let original_fields = self.fields.clone();
        let mut frozen_roots = BTreeSet::new();
        self.immutable_clone_roots(source, false, &mut frozen_roots);
        for ((node, _), value) in &original_fields {
            if reachable.contains(node) {
                self.immutable_clone_roots(value, true, &mut frozen_roots);
            }
        }
        let frozen = self.heap.reachable(frozen_roots);
        let mut internal = self.clone_relations(&copies);
        let mut counts: BTreeMap<_, usize> = source.origins.nodes.iter().map(|n| (*n, 1)).collect();
        for ((node, slot), mut value) in original_fields {
            if let Some(&copy) = copies.get(&node) {
                for origin in &value.origins.nodes {
                    *counts.entry(*origin).or_insert(0usize) += 1;
                }
                super::copy::rewrite_clone(&mut value, &copies, &frozen, immutable);
                self.store_field(copy, slot, value);
            }
        }
        internal |= counts.values().any(|count| *count > 1);
        let mut result = source.clone();
        result.ty = match (&source.ty, immutable) {
            (Ty::Immutable(inner), false) => (*inner.clone()).clone(),
            (Ty::Immutable(_), true) => source.ty.clone(),
            (_, true) => Ty::Immutable(Box::new(source.ty.clone())),
            _ => source.ty.clone(),
        };
        self.adapt_copy_source_type(source, &mut result, immutable);
        let immutable_output = immutable || self.formal_is_immutable(&result.ty);
        super::copy::rewrite_clone(&mut result, &copies, &frozen, immutable_output);
        result.internal_aliases = internal;
        result.sources.clear();
        result.scoped.clear();
        result.participants.clear();
        result.marker = false;
        result.through_return = false;
        result.cause = self.cause(
            CauseKind::Allocation,
            span,
            "deep clone isolates storage and preserves internal graph aliases",
            [source.cause],
        );
        result.unsuffixed_numeric = false;
        result.static_coordinate = None;
        result.literal_number = false;
        let duties = self.copy_result_duties(&mut result, span, owner);
        let cloned: BTreeSet<_> = copies.values().copied().collect();
        for ((node, _), value) in &mut self.fields {
            if cloned.contains(node) {
                super::results::remap_results(value, &duties);
            }
        }
        result
    }
    pub(super) fn derive_value(
        &mut self,
        mut input: EvaluatedValue,
        recipe: &Expr,
        span: Span,
        frame: &mut Frame,
    ) -> EvaluatedValue {
        self.transport_evaluation_packet(&mut input, span);
        let source_observation = input.observation;
        let mut source = input.value.clone();
        if source.publication != Publication::Immutable
            && source.construction
            && self.construction_can_publish(&source)
        {
            self.check_deep_uncertainty(&source, span);
            source.permission = Permission::Read;
            source.publication = Publication::Immutable;
            source.construction = false;
            source.marker = false;
            source.retention_result = false;
            source.cause = self.cause(CauseKind::Restriction, span,
                "closed construction is received as immutable data before deriving its isolated draft", [source.cause]);
        }
        if self.contains_resource(&source)
            || source.publication != Publication::Immutable
            || self.has_writer(&source)
            || source.mutable_environment
            || source.observer_environment
        {
            self.error(
                "E0536",
                span,
                "derive requires immutable ordinary data",
                [source.cause],
            );
        }
        let accesses = frame.obligations.accesses.len();
        let returned = frame.returned.len();
        let copy = crate::sema::copy_contract::CopyBoundaryId(self.copy_boundaries.len() as u32);
        let draft = self.clone_value(&source, span, frame, false);
        self.transport_frame_prefix(frame, accesses, returned);
        let mut draft = EvaluatedValue::new(draft, self.recency_moves.len());
        let recipe = Arc::new(self.expression_source_packet(recipe, frame, None, None));
        let callee_observation = recipe.observation;
        let previous = self.active_drafts.clone();
        self.active_drafts.extend(
            self.heap.reachable(
                draft
                    .current(&self.recency_moves)
                    .origins
                    .nodes
                    .iter()
                    .copied(),
            ),
        );
        use crate::sema::application_effect::{EntryOrigin, InputOrigin};
        use ril_compiler_core::ids::EvaluationOccurrenceId;
        let origin = match (
            self.application_effect.current_activation(),
            source_observation,
            callee_observation,
        ) {
            (Some(anchor), Some(input), Some(callee)) if self.application_effect.admit(2) => {
                EntryOrigin::Generated {
                    anchor,
                    callee: EvaluationOccurrenceId(callee as u32),
                    inputs: vec![InputOrigin::Copied {
                        observation: EvaluationOccurrenceId(input as u32),
                        boundary: copy,
                    }],
                }
            }
            _ => {
                self.unsupported(
                    span,
                    "generated invocation lacks its actual input/callee evaluations",
                );
                EntryOrigin::Unresolved
            }
        };
        let answer = self.invoke_generated_arguments_from(
            recipe,
            vec![(ParameterMode::Mut, draft.current(&self.recency_moves), span)],
            span,
            frame,
            origin,
        );
        if !self
            .heap
            .reachable(answer.origins.nodes.iter().copied())
            .is_disjoint(&self.active_drafts)
        {
            self.error(
                "E0607",
                span,
                "derive draft cannot escape through the recipe result",
                [answer.cause],
            );
        }
        self.active_drafts = previous;
        let draft = draft.into_current(&self.recency_moves);
        self.require_type(&answer, &Ty::Unit, span);
        if answer.ty == Ty::Never {
            return EvaluatedValue::unobserved(
                answer,
                self.recency_moves.len(),
                input.source_valid,
            );
        }
        self.check_deep_uncertainty(&draft, span);
        if self.has_writer(&draft) || self.contains_resource(&draft) {
            self.error(
                "E0536",
                span,
                "derived publication must remain ordinary data without an outside writer",
                [draft.cause],
            );
        }
        let mut result = draft;
        result.ty = source.ty;
        result.permission = Permission::Read;
        result.publication = Publication::Immutable;
        result.construction = false;
        result.internal_aliases = false;
        result.marker = false;
        let mut output =
            EvaluatedValue::unobserved(result, self.recency_moves.len(), input.source_valid);
        self.inherit_result_type(&mut output, &input, span);
        output
    }
    pub(super) fn construction_can_publish(&self, source: &Value) -> bool {
        if !self.pending_copy_dependencies(source).is_empty() {
            return false;
        }
        fn qualified(value: &Value) -> bool {
            if value.publication == Publication::Immutable {
                return true;
            }
            if value.mutable_environment || value.observer_environment {
                return false;
            }
            if !value.origins.nodes.is_empty() && !value.construction {
                return false;
            }
            [
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            .all(|payload| qualified(payload))
        }
        if !self.resource_free(source) || self.has_writer(source) || !qualified(source) {
            return false;
        }
        let reachable = self.heap.reachable(source.origins.nodes.iter().copied());
        self.fields
            .iter()
            .all(|((node, _), value)| !reachable.contains(node) || qualified(value))
    }
    pub(super) fn validate_defaults(&mut self, id: usize, env: Env) {
        let function = self.functions[id].syntax.clone();
        let previous_universal = self.universal;
        self.universal = true;
        let mut frame = self.frame(env, true);
        frame.callable_owner = Some(CallableOwner::Function(self.functions[id].definition));
        if function.body.is_none() && self.declaration_files.contains(&function.span.file.0) {
            for generic in &function.generics {
                if generic.name.chars().next().is_some_and(char::is_lowercase)
                    && let Some(bound) = &generic.bound
                {
                    let ty = self.ty(bound);
                    if ty.scalar() {
                        let cause = self.cause(
                            CauseKind::Source,
                            generic.span,
                            "immutable static value parameter",
                            [],
                        );
                        let value = Value::scalar(ty, None, cause);
                        let binding = self.bind_name(
                            &generic.name,
                            BindingMode::Let,
                            value,
                            generic.span,
                            &mut frame,
                            false,
                        );
                        self.static_value_bindings.insert(binding);
                    }
                }
            }
        }
        let mut earlier = BTreeSet::new();
        let all: BTreeSet<_> = function
            .parameters
            .iter()
            .filter_map(|p| {
                if let PatternKind::Name(name) = &p.pattern.kind {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect();
        for (index, parameter) in function.parameters.iter().enumerate() {
            if let Some(default) = &parameter.default {
                if parameter.mode != ParameterMode::Read {
                    self.error(
                        "E0404",
                        default.span,
                        "mutable parameters cannot have defaults",
                        [],
                    );
                }
                let mut names = BTreeSet::new();
                super::expressions::collect_names(default, &mut names);
                if names
                    .iter()
                    .any(|name| all.contains(name) && !earlier.contains(name))
                {
                    self.error(
                        "E0408",
                        default.span,
                        "default refers to itself or a later parameter",
                        [],
                    );
                }
                self.set_contract_environment(&frame.env);
                let caller = self.invocation_context(frame.callable_owner);
                let packet = self.evaluate_default(
                    Some(id),
                    index,
                    default,
                    super::super::default_uses::DefaultOrigin::DeclarationProbe,
                    caller,
                    &mut frame,
                );
                let (use_id, packet) = match packet {
                    Ok(packet) => packet,
                    Err(error) => {
                        self.unsupported(
                            default.span,
                            format!("default probe packet admission: {error}"),
                        );
                        break;
                    }
                };
                let source_valid = packet.source_valid;
                let mut value = match self.consume_evaluation_packet(packet, default.span) {
                    Ok(value) => value,
                    Err(error) => {
                        self.default_uses[use_id.0 as usize].status =
                            super::super::copy_contract::CopyInvocationStatus::Unsupported;
                        self.unsupported(
                            default.span,
                            format!("default probe packet admission: {error}"),
                        );
                        break;
                    }
                };
                self.default_use_stack.push(use_id);
                if let Some(ty) = &parameter.ty {
                    self.set_contract_environment(&frame.env);
                    if source_valid {
                        self.ascribe_signature(&mut value, ty);
                        self.check_storage_shape(&value, ty, &mut frame);
                    }
                    let ty = self.ty(ty);
                    self.require_type(&value, &ty, default.span);
                }
                // This declaration-only evaluation supplies its result to a
                // hypothetical parameter receiver. It must not leave an
                // orphan producer before the next independent default probe.
                self.finish_results(frame.owner, &value);
                assert_eq!(self.default_use_stack.pop(), Some(use_id));
            }
            let ty = parameter
                .ty
                .as_ref()
                .map(|t| self.ty(t))
                .unwrap_or(Ty::Unknown);
            let mut value =
                self.formal_value(ty, index as u32, parameter.span, &mut BTreeSet::new());
            if let Some(syntax) = &parameter.ty {
                // This is a declaration-only hypothetical earlier formal,
                // never an actual argument or a computed default result.
                self.ascribe_signature(&mut value, syntax);
                self.promise_array_shape(&value, syntax, &mut frame);
            }
            self.bind_pattern(
                &parameter.pattern,
                BindingMode::Let,
                value,
                &mut frame,
                true,
            );
            if let PatternKind::Name(name) = &parameter.pattern.kind {
                earlier.insert(name.clone());
            }
        }
        for binding in frame.locals {
            self.bindings[binding].alive = false;
        }
        self.universal = previous_universal;
    }
}

pub(super) fn generic_names(ty: &Ty, names: &mut BTreeSet<String>) {
    ty.generic_names(names);
}
