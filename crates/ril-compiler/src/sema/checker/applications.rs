//! One application evaluator for ordinary calls and pipelines. Source order,
//! physical observations and parameter binding are independent stages.
use super::*;
use crate::hir::application::{ApplicationKind, AstApplication, EvaluationRole};
use crate::sema::source_types::SourceTypesError;
use crate::sema::{
    application_effect::EntryArgument,
    copy_contract::CopyCallEventId,
    default_uses::{ApplicationEvaluation, ArgumentSource, CallArguments, SuppliedArgument},
};

type HeldArgument = (ParameterMode, EvaluatedValue, Span);
type FrozenArgument = (ParameterMode, std::sync::Arc<EvaluatedValue>, Span);

#[derive(Clone, Copy)]
struct ApplicationSite {
    event: CopyCallEventId,
    preparation: usize,
    arity: usize,
}

pub(super) struct EvaluatedOperand {
    pub(super) role: EvaluationRole,
    pub(super) value: std::sync::Arc<EvaluatedValue>,
}

impl Checker {
    pub(super) fn prepare_evaluation_packet(
        &mut self,
        packet: &mut EvaluatedValue,
        span: Span,
    ) -> Result<(), SourceTypesError> {
        let moves = &self.recency_moves;
        let result = self
            .application_effect
            .with_work(|work| packet.transport_checked(moves, work));
        if let Err(error) = &result {
            self.unsupported(
                span,
                format!("evaluation packet transport admission: {error}"),
            );
        }
        result
    }

    pub(super) fn consume_evaluation_packet(
        &mut self,
        mut packet: EvaluatedValue,
        span: Span,
    ) -> Result<Value, SourceTypesError> {
        self.prepare_evaluation_packet(&mut packet, span)?;
        Ok(packet.value)
    }

    pub(super) fn evaluate_application(
        &mut self,
        application: &AstApplication<'_>,
        expected: Option<&Ty>,
        source: Option<&crate::sema::source_reception::Target>,
        frame: &mut Frame,
    ) -> (Value, CopyCallEventId) {
        let event = self.reserve_copy_call_event(application.root, frame);
        if !self
            .application_effect
            .admit(self.immediate_scope_arguments.len())
        {
            self.unsupported(
                application.span,
                "application scope-context admission exhausted",
            );
            return (Value::scalar(Ty::Unknown, None, CauseId(0)), event);
        }
        let original_scope_arguments = self.immediate_scope_arguments.clone();
        let preparation = self.call_arguments.len();
        let result = self.evaluate_application_packet(application, expected, source, frame, event);
        self.immediate_scope_arguments = original_scope_arguments;
        match result {
            Ok(result) => result,
            Err(error) => {
                if let Some(prepared) = self.call_arguments.get_mut(preparation)
                    && prepared.source_event == event
                {
                    prepared.evaluation_complete = false;
                }
                if let Some(numeric) = self.numeric.applications.get_mut(&event) {
                    numeric.phase = crate::sema::numeric_selection::ApplicationPhase::Invalid;
                }
                self.unsupported(
                    application.span,
                    format!("application packet could not be transported: {error}"),
                );
                (Value::scalar(Ty::Unknown, None, CauseId(0)), event)
            }
        }
    }

    fn evaluate_application_packet(
        &mut self,
        application: &AstApplication<'_>,
        expected: Option<&Ty>,
        source: Option<&crate::sema::source_reception::Target>,
        frame: &mut Frame,
        event: CopyCallEventId,
    ) -> Result<(Value, CopyCallEventId), SourceTypesError> {
        let mut site = ApplicationSite {
            event,
            preparation: self.call_arguments.len(),
            arity: application.operands.len(),
        };
        if !self.application_effect.admit(
            application
                .operands
                .len()
                .checked_add(1)
                .ok_or(SourceTypesError::BudgetExceeded)?,
        ) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        self.call_arguments.push(CallArguments {
            source_event: event,
            target: None,
            evaluated: vec![],
            slots_bound: false,
            slots: vec![],
            supplied: BTreeMap::new(),
            evaluation_complete: false,
        });
        if !self
            .application_effect
            .admit(self.immediate_scope_arguments.len())
        {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let original_scope_arguments = self.immediate_scope_arguments.clone();
        let mut callee = None::<std::sync::Arc<EvaluatedValue>>;
        let mut evaluated = Vec::<EvaluatedOperand>::new();
        let mut contexts = vec![None; application.operands.len()];
        let mut source_contexts = Vec::new();
        let mut mapping = Vec::new();
        let mut nullary_none = false;
        let mut generic = None;
        let Some(root) = application.root.hir_id else {
            self.unsupported(
                application.span,
                "application cursor has no original HIR root",
            );
            return Ok((self.unit(application.span), event));
        };
        let mut cursor = match self.application_effect.with_work(|work| {
            crate::hir::execution::ApplicationCursor::new(&self.semantic_hir, root, work)
        }) {
            Ok(cursor) => cursor,
            Err(error) => {
                self.unsupported(application.span, format!("application cursor: {error}"));
                return Ok((self.unit(application.span), event));
            }
        };
        loop {
            let child = match self
                .application_effect
                .with_work(|work| cursor.pending(work))
            {
                Ok(Some(child)) => child,
                Ok(None) => break,
                Err(error) => {
                    self.unsupported(application.span, format!("application cursor: {error}"));
                    return Ok((self.unit(application.span), event));
                }
            };
            let role = child.role;
            let syntax = application
                .expression(role)
                .expect("application role exists");
            if syntax.hir_id != Some(child.expression) {
                self.unsupported(
                    syntax.span,
                    "application AST child differs from its original HIR cursor",
                );
                return Ok((self.unit(application.span), event));
            }
            let packet = if role == EvaluationRole::Callee {
                nullary_none = match &syntax.kind {
                    ExprKind::Name(name) => {
                        name == "Prelude::None" || (name == "None" && !frame.env.contains_key(name))
                    }
                    ExprKind::Path(path) => path == &["Prelude".to_owned(), "None".to_owned()],
                    _ => false,
                };
                let reference_start = self.copy_references.len();
                let packet = self.expression_source_packet(syntax, frame, None, None);
                let observation = packet.observation;
                let value = packet.value();
                self.append_application_evaluation(application, site, role, &packet, frame);
                self.complete_copy_call_callee(
                    event,
                    syntax,
                    value,
                    reference_start,
                    observation,
                    frame,
                );
                self.call_arguments[site.preparation].target =
                    self.copy_call_events[event.0 as usize].target;
                if value.ty != Ty::Never {
                    generic = if let Some(id) =
                        crate::sema::builtin_sources::generic_reference(value)
                    {
                        let result = self.application_effect.with_work(|remaining| {
                            let mut work = crate::sema::source_types::WorkLimit::new(*remaining);
                            let result = work
                                .charge(3)
                                .and_then(|()| {
                                    packet
                                        .current_source(
                                            crate::sema::source_types_ref::SourceTypesRef::Live(
                                                self.type_source.storage.live_types(),
                                            ),
                                            &mut work,
                                        )
                                        .map(|source| source.into_known())
                                })
                                .and_then(|source| {
                                    source
                                        .map(|(schema, environment)| {
                                            if environment.is_poisoned() {
                                                return Err(SourceTypesError::Unresolved);
                                            }
                                            schema.is_generic_builtin(id, &mut work)
                                        })
                                        .transpose()
                                });
                            *remaining = work.remaining();
                            result
                        });
                        match result {
                            Ok(Some(true)) => Some(id),
                            Ok(_) => None,
                            Err(error) => {
                                self.unsupported(syntax.span, format!("generic callee lost its original Source declaration: {error}"));
                                None
                            }
                        }
                    } else {
                        None
                    };
                    let labels = if let Some(parameters) = &value.signature {
                        crate::hir::application::parameter_labels(&parameters.parameters)
                    } else if let Some(id) = generic {
                        crate::sema::source_types::polymorphic::parameter_labels(id)
                    } else {
                        vec![None; application.operands.len()]
                    };
                    site.arity = labels.len();
                    mapping = crate::hir::application::bind_slots(
                        &labels,
                        application.operands.iter().map(|argument| argument.label),
                    );
                    if application.kind == ApplicationKind::Call {
                        source_contexts = self.call_argument_source_contexts(value, event);
                        if application.operands.len() == 1
                            && let [Callable::Builtin(name)] = value.callables.as_slice()
                            && let Some(constructor) =
                                ril_compiler_core::builtin_calls::PayloadConstructor::lookup(name)
                            && let Some(target) = source
                        {
                            match super::source_receiving::constructor_payload_target(target, constructor.projection(), application.operands[0].span) {
                                Ok(Some(target)) => source_contexts = vec![Some(target)],
                                Ok(None) => {},
                                Err(error) => self.unsupported(application.span, format!("constructor operand context could not be projected: {error}")),
                            }
                        }
                        contexts = self.numeric_argument_contexts(
                            value,
                            &application.operands,
                            super::numeric_application::NumericInputContext {
                                event,
                                expected_result: expected,
                                span: application.span,
                                frozen: None,
                            },
                            frame,
                        );
                        if let Some(id) = generic {
                            contexts = self.primitive_numeric_contexts(
                                id,
                                &application.operands,
                                &mapping,
                                super::numeric_application::PrimitiveNumericPrefix {
                                    event,
                                    preparation: site.preparation,
                                    packets: &evaluated,
                                },
                                frame,
                            );
                        }
                        if matches!(value.callables.as_slice(), [Callable::Builtin(name)] if name == "Concurrent::scope")
                        {
                            for (operand, slot) in application.operands.iter().zip(&mapping) {
                                if matches!(operand.expression.kind, ExprKind::Lambda { .. })
                                    && let Ok(slot) = slot
                                {
                                    self.immediate_scope_arguments.insert((event, *slot as u32));
                                }
                            }
                        }
                    }
                }
                let packet = std::sync::Arc::new(packet);
                callee = Some(packet.clone());
                packet
            } else {
                let operand = application.operand(role).expect("actual operand");
                if operand.mode != ParameterMode::Read
                    && !matches!(
                        syntax.kind,
                        ExprKind::Name(_) | ExprKind::Field { .. } | ExprKind::Index { .. }
                    )
                {
                    self.error(
                        "E0410",
                        operand.span,
                        "mutable argument requires an addressable target",
                        [],
                    );
                }
                let index = evaluated.len();
                let expected = contexts.get(index).and_then(Option::as_ref);
                let slot = mapping
                    .get(index)
                    .and_then(|slot| slot.as_ref().ok())
                    .copied();
                let marker =
                    slot.map(|slot| self.begin_source_argument(event, slot, syntax, frame));
                let deferred = expected.is_none()
                    && super::numeric_pending::candidate(syntax)
                    && (application.kind == ApplicationKind::Pipeline
                        || generic.is_some()
                        || self.numeric.applications.contains_key(&event));
                self.numeric.deferred_depth += usize::from(deferred);
                let observation = self.expression_source_packet(
                    syntax,
                    frame,
                    expected,
                    slot.and_then(|slot| source_contexts.get(slot))
                        .and_then(Option::as_ref),
                );
                self.numeric.deferred_depth -= usize::from(deferred);
                if let Some(marker) = marker {
                    self.end_source_argument(marker);
                }
                self.append_application_evaluation(application, site, role, &observation, frame);
                let packet = std::sync::Arc::new(observation);
                evaluated.push(EvaluatedOperand {
                    role,
                    value: packet.clone(),
                });
                packet
            };
            let value = &packet.value;
            if value.ty == Ty::Never || packet.observation.is_none() {
                if let Some(callee) = callee
                    .as_mut()
                    .map(|callee| self.read_evaluation_packet(callee, application.span))
                    .transpose()?
                    && callee.ty != Ty::Never
                {
                    let _ = self.bind_application_operands(
                        application,
                        site,
                        &mapping,
                        &evaluated,
                        frame,
                    )?;
                }
                let mut prefix: Vec<_> = evaluated
                    .into_iter()
                    .map(|held| {
                        let operand = application
                            .operand(held.role)
                            .expect("actual prefix operand");
                        Ok((
                            operand.mode,
                            self.read_evaluation_packet(&held.value, operand.span)?,
                            operand.span,
                        ))
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                if value.ty == Ty::Never && role == EvaluationRole::Callee {
                    // A callee may be the abrupt tail after numeric piped inputs.
                    prefix.push((
                        ParameterMode::Read,
                        self.read_evaluation_packet(&packet, syntax.span)?,
                        syntax.span,
                    ));
                }
                self.finish_numeric_arguments(event, &mut prefix)?;
                self.immediate_scope_arguments = original_scope_arguments;
                match self
                    .application_effect
                    .with_work(|work| cursor.later_children(work))
                {
                    Ok(children) => {
                        for later in children {
                            self.preview_expression(
                                application
                                    .expression(later.role)
                                    .expect("remaining application role"),
                                frame,
                            );
                        }
                    }
                    Err(error) => self.unsupported(
                        application.span,
                        format!("application preview cursor: {error}"),
                    ),
                }
                return Ok((self.read_evaluation_packet(&packet, syntax.span)?, event));
            }
            if let Err(error) = self
                .application_effect
                .with_work(|work| cursor.complete(child, work))
            {
                self.unsupported(
                    application.span,
                    format!("application child completion: {error}"),
                );
                return Ok((self.unit(application.span), event));
            }
        }
        self.immediate_scope_arguments = original_scope_arguments;
        let Some(callee_packet) = callee else {
            self.unsupported(
                application.span,
                "application has no actual callee evaluation",
            );
            return Ok((self.unit(application.span), event));
        };
        let callee = self.read_evaluation_packet(&callee_packet, application.span)?;
        if let Some(id) = generic {
            contexts = self.primitive_numeric_contexts(
                id,
                &application.operands,
                &mapping,
                super::numeric_application::PrimitiveNumericPrefix {
                    event,
                    preparation: site.preparation,
                    packets: &evaluated,
                },
                frame,
            );
        } else if application.kind == ApplicationKind::Pipeline {
            let frozen: Vec<_> = evaluated
                .iter_mut()
                .map(|held| {
                    let operand = application.operand(held.role).expect("actual operand");
                    Ok((
                        operand.mode,
                        self.read_evaluation_packet(&held.value, operand.span)?,
                        operand.span,
                    ))
                })
                .collect::<Result<_, SourceTypesError>>()?;
            contexts = self.numeric_argument_contexts(
                &callee,
                &application.operands,
                super::numeric_application::NumericInputContext {
                    event,
                    expected_result: expected,
                    span: application.span,
                    frozen: Some(&frozen),
                },
                frame,
            );
        }
        let mut slots =
            self.bind_application_operands(application, site, &mapping, &evaluated, frame)?;
        // A failed label/position mapping has no parameter environment. Keep
        // the physical prefix, but never evaluate defaults or enter a body
        // using the partial local slots from this rejected preparation.
        if !self.call_arguments[site.preparation].slots_bound {
            self.numeric.applications.remove(&event);
            self.window_future_expressions(&[], frame);
            return Ok((self.unit(application.span), event));
        }
        self.solve_numeric_slots(event, &mut slots)?;
        // Non-generic interfaces and builtins may have no prepared numeric row.
        // Select only the already evaluated holes; no expression runs again.
        for (index, mapped) in mapping.iter().enumerate() {
            let Ok(slot) = mapped else { continue };
            let Some((_, held, _)) = slots.get_mut(*slot).and_then(Option::as_mut) else {
                continue;
            };
            if !matches!(held.value.ty, Ty::NumericHole(_)) {
                continue;
            }
            if let Ty::NumericHole(id) = held.value.ty {
                let expected = contexts
                    .get(index)
                    .and_then(Option::as_ref)
                    .filter(|ty| super::numeric::numeric_type(ty).is_some())
                    .cloned();
                let expected = match expected {
                    Some(expected) => expected,
                    None => self
                        .numeric_preference(id)?
                        .unwrap_or_else(|| Ty::Int("int".into())),
                };
                self.select_numeric_packet(held, &expected, application.span)?;
            }
        }
        let slots = slots
            .into_iter()
            .enumerate()
            .map(|(slot, held)| {
                held.map(|(mode, packet, span)| {
                    let packet = std::sync::Arc::new(packet);
                    if packet.numeric_source_derivation().is_some() {
                        self.publish_numeric_call_input(
                            site.event,
                            site.preparation,
                            slot,
                            packet.clone(),
                            frame,
                        )?;
                    }
                    Ok((mode, packet, span))
                })
                .transpose()
            })
            .collect::<Result<Vec<_>, SourceTypesError>>()?;
        let args = if callee.signature.is_some() {
            self.finish_application_slots(application, &callee, site, slots, frame)?
        } else {
            let mut args: Vec<_> = slots
                .into_iter()
                .flatten()
                .map(|(mode, packet, span)| EntryArgument {
                    mode,
                    packet,
                    span,
                    heap: None,
                })
                .collect();
            self.call_arguments[site.preparation].evaluation_complete =
                self.call_arguments[site.preparation].slots_bound
                    && self.call_arguments[site.preparation].supplied.len()
                        == application.operands.len();
            self.check_public_call_input_sources(&callee, application.callee, event, frame);
            self.finish_numeric_entry_arguments(event, &mut args)?;
            args
        };
        self.window_future_expressions(&[], frame);
        if nullary_none {
            self.error(
                "E0353",
                application.span,
                "the None tag is data and cannot be called",
                [callee.cause],
            );
            return Ok((self.unit(application.span), event));
        }
        let asserted = !callee.callables.is_empty() && callee.callables.iter().all(|target|
            matches!(target, Callable::Builtin(name) if matches!(name.as_str(), "assert" | "Prelude::assert")));
        let condition = if asserted {
            args.first()
                .map(|argument| self.read_evaluation_packet(&argument.packet, argument.span))
                .transpose()?
        } else {
            None
        };
        if let Err(error) = self
            .application_effect
            .with_work(|work| cursor.reduce(work))
        {
            self.unsupported(application.span, format!("application reduction: {error}"));
            return Ok((self.unit(application.span), event));
        }
        let previous_call = frame.copy_call_event.replace(event);
        let output = self.invoke_application_packet(
            callee_packet,
            std::sync::Arc::new(args),
            event,
            application.span,
            frame,
        );
        frame.copy_call_event = previous_call;
        if output.ty != Ty::Never
            && let Some(condition) = condition
        {
            self.inspect_condition_value(&condition, true, application.span);
        }
        Ok((output, event))
    }

    fn append_application_evaluation(
        &mut self,
        application: &AstApplication<'_>,
        site: ApplicationSite,
        role: EvaluationRole,
        packet: &EvaluatedValue,
        frame: &Frame,
    ) {
        let Some(expression) = packet.observation else {
            return;
        };
        let context = self.invocation_context(frame.callable_owner);
        let syntax = application
            .expression(role)
            .expect("actual evaluation role");
        let valid = self
            .application_effect
            .expressions
            .get(expression)
            .is_some_and(|fact| {
                fact.source_id.is_some()
                    && fact.source_id == syntax.hir_id
                    && fact.allocation_epoch == packet.allocation_epoch
            })
            && self
                .application_effect
                .contexts
                .get(expression)
                .is_some_and(|row| row.expression == expression && row.context == context)
            && application
                .evaluation_order()
                .nth(self.call_arguments[site.preparation].evaluated.len())
                == Some(role);
        if !valid {
            self.unsupported(
                syntax.span,
                "application evaluation lost its actual prefix observation",
            );
            return;
        }
        self.call_arguments[site.preparation]
            .evaluated
            .push(ApplicationEvaluation {
                role,
                observation: SuppliedArgument {
                    expression,
                    allocation_epoch: packet.allocation_epoch,
                },
            });
    }

    fn bind_application_operands(
        &mut self,
        application: &AstApplication<'_>,
        site: ApplicationSite,
        mapping: &[Result<usize, &'static str>],
        evaluated: &[EvaluatedOperand],
        frame: &Frame,
    ) -> Result<Vec<Option<HeldArgument>>, SourceTypesError> {
        if !self.application_effect.admit(site.arity) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let mut slots = vec![None; site.arity];
        let mut valid = true;
        for (index, held) in evaluated.iter().enumerate() {
            let operand = application
                .operand(held.role)
                .expect("actual bound operand");
            let slot = mapping.get(index).copied().unwrap_or(Err("E0314"));
            let Ok(slot) = slot else {
                self.error(
                    slot.unwrap_err(),
                    operand.span,
                    "argument does not name an available unbound parameter",
                    [],
                );
                valid = false;
                continue;
            };
            if !self.bind_call_input_source(site.event, held.role, slot, held.value.clone(), frame)
            {
                self.unsupported(
                    operand.span,
                    "application operand lost its frozen Source before slot binding",
                );
                valid = false;
            }
            let packet = self.clone_evaluation_packet(&held.value, operand.span)?;
            slots[slot] = Some((operand.mode, packet, operand.span));
        }
        let supplied = self.call_supplied_observations(site.event);
        let preparation = &mut self.call_arguments[site.preparation];
        preparation.slots_bound = valid;
        if valid {
            preparation.slots = slots
                .iter()
                .map(|slot| {
                    if slot.is_some() {
                        ArgumentSource::Supplied
                    } else {
                        ArgumentSource::Missing
                    }
                })
                .collect();
            preparation.supplied = supplied;
        }
        Ok(slots)
    }

    fn finish_application_slots(
        &mut self,
        application: &AstApplication<'_>,
        callee: &Value,
        site: ApplicationSite,
        mut slots: Vec<Option<FrozenArgument>>,
        frame: &mut Frame,
    ) -> Result<Vec<EntryArgument>, SourceTypesError> {
        let ApplicationSite {
            event: source_event,
            preparation,
            ..
        } = site;
        let (span, callee_syntax) = (application.span, application.callee);
        let parameters = callee
            .signature
            .as_ref()
            .map(|signature| &signature.parameters)
            .expect("default-capable public signature");
        let target = match callee.callables.as_slice() {
            [Callable::Named(id, _)] => Some(*id),
            _ => None,
        };
        let caller_context = self.invocation_context(frame.callable_owner);
        let has_default = parameters
            .iter()
            .enumerate()
            .any(|(index, parameter)| slots[index].is_none() && parameter.default.is_some());
        let previous_typing = self.capture_typing_environment();
        let mut defaults_frame = None;
        let result = (|| {
            // Supplied packets enter the real callee directly. A synthetic
            // parameter environment is needed only to evaluate omitted defaults.
            if !has_default && slots.iter().all(Option::is_some) {
                return Ok(slots.into_iter().flatten().collect::<Vec<_>>());
            }
            if has_default && let Some(id) = target {
                let info = self.functions[id].clone();
                self.generic_scope(id);
                let binders: BTreeSet<_> = info
                    .syntax
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
                let explicit = self.named_instance_for_event(source_event, info.definition);
                let mut supplied = info.syntax.clone();
                supplied.parameters = supplied
                    .parameters
                    .into_iter()
                    .enumerate()
                    .filter_map(|(index, parameter)| {
                        slots
                            .get(index)
                            .is_some_and(Option::is_some)
                            .then_some(parameter)
                    })
                    .collect();
                let actual: Vec<_> = slots
                    .iter()
                    .flatten()
                    .map(|(mode, value, span)| {
                        Ok((*mode, self.read_evaluation_packet(value, *span)?, *span))
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                let raw_templates = explicit.as_ref().map(|_| {
                    supplied
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
                self.infer_named_arguments(
                    &supplied,
                    &actual,
                    &binders,
                    raw_templates,
                    explicit.as_deref(),
                );
                if let Some(prepared) = &explicit {
                    self.finish_named_instance_inference(prepared, span);
                }
            }
            if has_default && let [Callable::Closure(id)] = callee.callables.as_slice() {
                if let Some(environment) = self
                    .lambda_contract(*id)
                    .map(|contract| contract.typing_environment.clone())
                {
                    self.restore_typing_environment(environment);
                } else {
                    self.unsupported(span, "default lambda has no frozen declaration environment");
                }
            }
            let environment = match callee.callables.as_slice() {
                [Callable::Named(id, _)] => self.functions[*id].lexical.clone(),
                [Callable::Closure(id)] => self.closures[*id].lexical.clone(),
                _ => frame.env.clone(),
            };
            defaults_frame = Some(self.frame(environment, true));
            let defaults = defaults_frame.as_mut().expect("default frame was created");
            self.scopes.set_parent(defaults.owner, frame.owner);
            defaults.callable_owner = match callee.callables.as_slice() {
                [Callable::Named(id, _)] => {
                    Some(CallableOwner::Function(self.functions[*id].definition))
                }
                [Callable::Closure(id)] => self.closures[*id].site.map(CallableOwner::Lambda),
                _ => None,
            };
            let mut result = Vec::new();
            for (index, parameter) in parameters.iter().enumerate() {
                let value = if let Some(value) = slots[index].take() {
                    value
                } else if let Some(default) = &parameter.default {
                    let (use_id, packet) = self.evaluate_default(
                        target,
                        index,
                        default,
                        super::super::default_uses::DefaultOrigin::Call(source_event),
                        caller_context,
                        defaults,
                    )?;
                    self.call_arguments[preparation].slots[index] =
                        super::super::default_uses::ArgumentSource::Default(use_id);
                    let packet = std::sync::Arc::new(packet);
                    self.record_default_call_input_source(
                        source_event,
                        index,
                        use_id,
                        default,
                        defaults,
                        packet.clone(),
                    );
                    (parameter.mode, packet, default.span)
                } else {
                    self.error(
                        "E0314",
                        span,
                        "missing required callable argument",
                        [callee.cause],
                    );
                    let ty = parameter
                        .ty
                        .as_ref()
                        .map(|t| self.ty(t))
                        .unwrap_or(Ty::Unknown);
                    (
                        parameter.mode,
                        {
                            let value =
                                self.formal_value(ty, index as u32, span, &mut BTreeSet::new());
                            std::sync::Arc::new(EvaluatedValue::new(
                                value,
                                self.recency_moves.len(),
                            ))
                        },
                        span,
                    )
                };
                if value.1.value.ty == Ty::Never {
                    result.push(value);
                    break;
                }
                let mut received = self.clone_evaluation_packet(&value.1, value.2)?;
                if has_default
                    && target.is_some()
                    && let Some(ty) = &parameter.ty
                {
                    let info = self.functions[target.unwrap()].clone();
                    self.prepare_evaluation_packet(&mut received, value.2)?;
                    let source_valid = self.check_named_input_source(
                        &info,
                        index,
                        &received,
                        Some(source_event),
                        value.2,
                    );
                    self.set_contract_environment(&defaults.env);
                    if source_valid {
                        self.prepare_evaluation_packet(&mut received, value.2)?;
                        received.invalidate_current_source();
                        self.ascribe_signature(&mut received.value, ty);
                        let expected = self.ty(ty);
                        self.prepare_evaluation_packet(&mut received, value.2)?;
                        self.require_type(&received.value, &expected, value.2);
                        self.check_storage_shape(&received.value, ty, defaults);
                        self.prepare_evaluation_packet(&mut received, value.2)?;
                        if self.literal_shape_compatible(&received.value, &expected) {
                            received.value.ty = expected;
                        }
                    }
                }
                self.bind_parameter_packet(
                    &parameter.pattern,
                    BindingMode::Let,
                    received,
                    defaults,
                )?;
                result.push(value);
            }
            // Producers created by actual defaults belong to the application.
            // Transport their duties unchanged; supplying an argument must never
            // borrow an inspection performed by an omitted default in another call.
            for (_, value, value_span) in &result {
                let current = self.read_evaluation_packet(value, *value_span)?;
                self.transfer_results(&current, defaults.owner, frame.owner);
            }
            if let Some((_, exit, _)) = result
                .iter()
                .find(|(_, value, _)| value.value.ty == Ty::Never)
            {
                let current = self.read_evaluation_packet(exit, span)?;
                self.finish_results(defaults.owner, &current);
            } else {
                let unit = self.unit(span);
                self.finish_results(defaults.owner, &unit);
            }
            Ok::<_, SourceTypesError>(result)
        })();
        if let Some(defaults) = defaults_frame {
            for binding in defaults.locals {
                self.bindings[binding].alive = false;
            }
            frame.obligations.include(&defaults.obligations, true);
        }
        self.restore_typing_environment(previous_typing);
        let result = result?;
        self.call_arguments[preparation].evaluation_complete = self.call_arguments[preparation]
            .slots_bound
            && self.call_arguments[preparation].supplied.len()
                == self.call_arguments[preparation]
                    .evaluated
                    .iter()
                    .filter(|evaluation| evaluation.role != EvaluationRole::Callee)
                    .count()
            && result.len() == parameters.len()
            && result
                .iter()
                .all(|(_, value, _)| value.value.ty != Ty::Never);
        self.check_public_call_input_sources(callee, callee_syntax, source_event, frame);
        let mut result = result
            .into_iter()
            .map(|(mode, packet, span)| EntryArgument {
                mode,
                packet,
                span,
                heap: None,
            })
            .collect::<Vec<_>>();
        self.finish_numeric_entry_arguments(source_event, &mut result)?;
        Ok(result)
    }
}
