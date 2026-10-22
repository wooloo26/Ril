//! One application evaluator for ordinary calls and pipelines. Source order,
//! physical observations and parameter binding are independent stages.
use super::*;
use crate::hir::application::{ApplicationKind, AstApplication, EvaluationRole};
use crate::sema::{
    copy_contract::CopyCallEventId,
    default_uses::{ApplicationEvaluation, ArgumentSource, CallArguments, SuppliedArgument},
};

type HeldArgument = (ParameterMode, EvaluatedValue, Span);

#[derive(Clone, Copy)]
struct ApplicationSite {
    event: CopyCallEventId,
    preparation: usize,
    arity: usize,
}

struct EvaluatedOperand {
    role: EvaluationRole,
    value: EvaluatedValue,
}

impl Checker {
    pub(super) fn evaluate_application(
        &mut self,
        application: &AstApplication<'_>,
        expected: Option<&Ty>,
        frame: &mut Frame,
    ) -> (Value, CopyCallEventId) {
        let event = self.reserve_copy_call_event(application.root, frame);
        let mut site = ApplicationSite {
            event,
            preparation: self.call_arguments.len(),
            arity: application.operands.len(),
        };
        self.call_arguments.push(CallArguments {
            source_event: event,
            target: None,
            evaluated: vec![],
            slots_bound: false,
            slots: vec![],
            supplied: BTreeMap::new(),
            evaluation_complete: false,
        });
        let original_scope_arguments = self.immediate_scope_arguments.clone();
        let mut callee = None::<EvaluatedValue>;
        let mut evaluated = Vec::<EvaluatedOperand>::new();
        let mut contexts = vec![None; application.operands.len()];
        let mut source_contexts = Vec::new();
        let mut mapping = Vec::new();
        let mut nullary_none = false;
        let mut generic = None;
        let order: Vec<_> = application.evaluation_order().collect();
        for (position, role) in order.iter().copied().enumerate() {
            let syntax = application
                .expression(role)
                .expect("application role exists");
            let (value, observation) = if role == EvaluationRole::Callee {
                nullary_none = match &syntax.kind {
                    ExprKind::Name(name) => {
                        name == "Prelude::None" || (name == "None" && !frame.env.contains_key(name))
                    }
                    ExprKind::Path(path) => path == &["Prelude".to_owned(), "None".to_owned()],
                    _ => false,
                };
                let reference_start = self.copy_references.len();
                let window = self.begin_explicit_named_callee(syntax, frame);
                let (value, observation) = self.expression_observed(syntax, frame);
                let explicit = self.end_explicit_named_callee(window, observation);
                self.append_application_evaluation(application, site, role, observation, frame);
                self.complete_copy_call_callee(
                    event,
                    syntax,
                    &value,
                    reference_start,
                    observation,
                    frame,
                );
                self.call_arguments[site.preparation].target =
                    self.copy_call_events[event.0 as usize].target;
                self.seal_explicit_named_callee(explicit, event, frame);
                if value.ty != Ty::Never {
                    generic = if let Some(id) =
                        crate::sema::builtin_sources::generic_reference(&value)
                    {
                        let mut work = crate::sema::source_types::WorkLimit::new(16384);
                        match self.original_source_receiving_schema(&value, syntax, frame, &mut work)
                            .and_then(|source| source.map(|(schema, environment)| {
                                if environment.is_poisoned() { return Err(crate::sema::source_types::SourceTypesError::Unresolved); }
                                schema.is_generic_builtin(id, &mut work)
                            }).transpose())
                        {
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
                        crate::hir::application::parameter_labels(parameters)
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
                        source_contexts = self.call_argument_source_contexts(&value, event);
                        contexts = self.numeric_argument_contexts(
                            &value,
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
                                event,
                                &application.operands,
                                &mapping,
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
                callee = Some(EvaluatedValue::new(value.clone(), self.recency_moves.len()));
                (value, observation)
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
                let observation = self.expression_expected_source(
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
                self.append_application_evaluation(
                    application,
                    site,
                    role,
                    observation.observation,
                    frame,
                );
                self.capture_call_input_source(event, role, syntax, observation.observation, frame);
                evaluated.push(EvaluatedOperand {
                    role,
                    value: EvaluatedValue::new(observation.value.clone(), self.recency_moves.len()),
                });
                (observation.value, observation.observation)
            };
            if value.ty == Ty::Never || observation.is_none() {
                if let Some(callee) = callee
                    .as_mut()
                    .map(|callee| callee.current(&self.recency_moves))
                    && callee.ty != Ty::Never
                {
                    let _ = self.bind_application_operands(
                        application,
                        site,
                        &mapping,
                        &evaluated,
                        frame,
                    );
                }
                let mut prefix: Vec<_> = evaluated
                    .into_iter()
                    .map(|held| {
                        let operand = application
                            .operand(held.role)
                            .expect("actual prefix operand");
                        (
                            operand.mode,
                            held.value.into_current(&self.recency_moves),
                            operand.span,
                        )
                    })
                    .collect();
                if value.ty == Ty::Never {
                    // A callee may be the abrupt tail after numeric piped inputs.
                    prefix.push((ParameterMode::Read, value.clone(), syntax.span));
                }
                self.finish_numeric_arguments(event, &mut prefix);
                self.immediate_scope_arguments = original_scope_arguments;
                for later in &order[position + 1..] {
                    self.preview_expression(
                        application
                            .expression(*later)
                            .expect("remaining application role"),
                        frame,
                    );
                }
                return (value, event);
            }
        }
        self.immediate_scope_arguments = original_scope_arguments;
        let Some(callee) = callee.map(|callee| callee.into_current(&self.recency_moves)) else {
            self.unsupported(
                application.span,
                "application has no actual callee evaluation",
            );
            return (self.unit(application.span), event);
        };
        if let Some(id) = generic {
            contexts =
                self.primitive_numeric_contexts(id, event, &application.operands, &mapping, frame);
        } else if application.kind == ApplicationKind::Pipeline {
            let frozen: Vec<_> = evaluated
                .iter_mut()
                .map(|held| {
                    let operand = application.operand(held.role).expect("actual operand");
                    (
                        operand.mode,
                        held.value.current(&self.recency_moves),
                        operand.span,
                    )
                })
                .collect();
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
            self.bind_application_operands(application, site, &mapping, &evaluated, frame);
        // A failed label/position mapping has no parameter environment. Keep
        // the physical prefix, but never evaluate defaults or enter a body
        // using the partial local slots from this rejected preparation.
        if !self.call_arguments[site.preparation].slots_bound {
            self.numeric.applications.remove(&event);
            self.window_future_expressions(&[], frame);
            return (self.unit(application.span), event);
        }
        self.solve_numeric_slots(event, &mut slots);
        // Non-generic interfaces and builtins may have no prepared numeric row.
        // Select only the already evaluated holes; no expression runs again.
        for (index, mapped) in mapping.iter().enumerate() {
            let Ok(slot) = mapped else { continue };
            let Some((_, held, _)) = slots.get_mut(*slot).and_then(Option::as_mut) else {
                continue;
            };
            let value = held.current_mut(&self.recency_moves);
            if let Ty::NumericHole(id) = value.ty {
                let expected = contexts
                    .get(index)
                    .and_then(Option::as_ref)
                    .filter(|ty| super::numeric::numeric_type(ty).is_some())
                    .cloned()
                    .or_else(|| self.numeric_preference(id))
                    .unwrap_or_else(|| Ty::Int("int".into()));
                self.commit_numeric_value(value, &expected);
            }
        }
        let args = if callee.signature.is_some() {
            self.finish_application_slots(application, &callee, site, slots, frame)
        } else {
            let mut args: Vec<_> = slots
                .into_iter()
                .flatten()
                .map(|(mode, held, span)| (mode, held.into_current(&self.recency_moves), span))
                .collect();
            self.call_arguments[site.preparation].evaluation_complete =
                self.call_arguments[site.preparation].slots_bound
                    && self.call_arguments[site.preparation].supplied.len()
                        == application.operands.len();
            self.check_public_call_input_sources(&callee, application.callee, event, frame);
            self.finish_numeric_arguments(event, &mut args);
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
            return (self.unit(application.span), event);
        }
        let asserted = !callee.callables.is_empty() && callee.callables.iter().all(|target|
            matches!(target, Callable::Builtin(name) if matches!(name.as_str(), "assert" | "Prelude::assert")));
        let condition = asserted
            .then(|| args.first().map(|(_, value, _)| value.clone()))
            .flatten();
        let previous_call = frame.copy_call_event.replace(event);
        let output = self.invoke(&callee, args, application.span, frame);
        frame.copy_call_event = previous_call;
        if output.ty != Ty::Never
            && let Some(condition) = condition
        {
            self.inspect_condition_value(&condition, true, application.span);
        }
        (output, event)
    }

    fn append_application_evaluation(
        &mut self,
        application: &AstApplication<'_>,
        site: ApplicationSite,
        role: EvaluationRole,
        observed: Option<usize>,
        frame: &Frame,
    ) {
        let Some(expression) = observed else {
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
            .is_some_and(|fact| fact.source_id.is_some() && fact.source_id == syntax.hir_id)
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
                    allocation_epoch: self.recency_moves.len(),
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
    ) -> Vec<Option<HeldArgument>> {
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
            if !self.bind_call_input_source(site.event, held.role, slot, frame) {
                self.unsupported(
                    operand.span,
                    "application operand lost its frozen Source before slot binding",
                );
                valid = false;
            }
            slots[slot] = Some((operand.mode, held.value.clone(), operand.span));
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
        slots
    }

    fn finish_application_slots(
        &mut self,
        application: &AstApplication<'_>,
        callee: &Value,
        site: ApplicationSite,
        mut slots: Vec<Option<HeldArgument>>,
        frame: &mut Frame,
    ) -> Vec<(ParameterMode, Value, Span)> {
        let ApplicationSite {
            event: source_event,
            preparation,
            ..
        } = site;
        let (span, callee_syntax) = (application.span, application.callee);
        let parameters = callee
            .signature
            .as_ref()
            .expect("default-capable public signature");
        let target = match callee.callables.as_slice() {
            [Callable::Named(id)] => Some(*id),
            _ => None,
        };
        let caller_context = self.invocation_context(frame.callable_owner);
        let has_default = parameters
            .iter()
            .enumerate()
            .any(|(index, parameter)| slots[index].is_none() && parameter.default.is_some());
        let previous_typing = self.capture_typing_environment();
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
            let explicit = self.explicit_named_for_event(source_event, info.definition);
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
                .iter_mut()
                .flatten()
                .map(|(mode, value, span)| (*mode, value.current(&self.recency_moves), *span))
                .collect();
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
                self.seed_explicit_named(prepared);
            }
            self.infer_named_arguments(
                &supplied,
                &actual,
                &binders,
                raw_templates,
                explicit.as_ref(),
            );
            if let Some(prepared) = &explicit {
                self.finish_explicit_named_inference(prepared, span);
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
            [Callable::Named(id)] => self.functions[*id].lexical.clone(),
            [Callable::Closure(id)] => self.closures[*id].lexical.clone(),
            _ => frame.env.clone(),
        };
        let mut defaults = self.frame(environment, true);
        self.scopes.set_parent(defaults.owner, frame.owner);
        defaults.callable_owner = match callee.callables.as_slice() {
            [Callable::Named(id)] => Some(CallableOwner::Function(self.functions[*id].definition)),
            [Callable::Closure(id)] => self.closures[*id].site.map(CallableOwner::Lambda),
            _ => None,
        };
        let mut result = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            let mut value = if let Some(value) = slots[index].take() {
                value
            } else if let Some(default) = &parameter.default {
                let (use_id, value) = self.evaluate_default(
                    target,
                    index,
                    default,
                    super::super::default_uses::DefaultOrigin::Call(source_event),
                    caller_context,
                    &mut defaults,
                );
                self.call_arguments[preparation].slots[index] =
                    super::super::default_uses::ArgumentSource::Default(use_id);
                self.record_default_call_input_source(
                    source_event,
                    index,
                    use_id,
                    default,
                    &defaults,
                );
                (
                    parameter.mode,
                    EvaluatedValue::new(value, self.recency_moves.len()),
                    default.span,
                )
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
                        let value = self.formal_value(ty, index as u32, span, &mut BTreeSet::new());
                        EvaluatedValue::new(value, self.recency_moves.len())
                    },
                    span,
                )
            };
            if value.1.current(&self.recency_moves).ty == Ty::Never {
                result.push(value);
                break;
            }
            let mut received = value.1.clone();
            if has_default
                && target.is_some()
                && let Some(ty) = &parameter.ty
            {
                let info = self.functions[target.unwrap()].clone();
                let source_valid = self.check_named_input_source(
                    &info,
                    index,
                    &received.current(&self.recency_moves),
                    Some(source_event),
                    value.2,
                );
                self.set_contract_environment(&defaults.env);
                if source_valid {
                    self.ascribe_signature(received.current_mut(&self.recency_moves), ty);
                    let expected = self.ty(ty);
                    self.require_type(&received.current(&self.recency_moves), &expected, value.2);
                    self.check_storage_shape(
                        &received.current(&self.recency_moves),
                        ty,
                        &mut defaults,
                    );
                    if self
                        .literal_shape_compatible(&received.current(&self.recency_moves), &expected)
                    {
                        received.current_mut(&self.recency_moves).ty = expected;
                    }
                }
            }
            self.bind_pattern(
                &parameter.pattern,
                BindingMode::Let,
                received.into_current(&self.recency_moves),
                &mut defaults,
                true,
            );
            result.push(value);
        }
        // Producers created by actual defaults belong to the application.
        // Transport their duties unchanged; supplying an argument must never
        // borrow an inspection performed by an omitted default in another call.
        for (_, value, _) in &mut result {
            self.transfer_results(
                &value.current(&self.recency_moves),
                defaults.owner,
                frame.owner,
            );
        }
        let exit = result
            .iter_mut()
            .map(|(_, value, _)| value.current(&self.recency_moves))
            .find(|value| value.ty == Ty::Never)
            .unwrap_or_else(|| self.unit(span));
        self.finish_results(defaults.owner, &exit);
        for binding in defaults.locals {
            self.bindings[binding].alive = false;
        }
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
                .iter_mut()
                .all(|(_, value, _)| value.current(&self.recency_moves).ty != Ty::Never);
        frame.obligations.include(&defaults.obligations, true);
        self.restore_typing_environment(previous_typing);
        self.check_public_call_input_sources(callee, callee_syntax, source_event, frame);
        let mut result = result
            .into_iter()
            .map(|(mode, value, span)| (mode, value.into_current(&self.recency_moves), span))
            .collect::<Vec<_>>();
        self.finish_numeric_arguments(source_event, &mut result);
        result
    }
}
