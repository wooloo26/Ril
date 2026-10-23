//! Single-visit combinators preserve payload identities and merge both possible
//! execution states. Inspecting an input never inspects a newly produced Result.
use super::*;

pub(super) fn is_variant_builtin(name: &str) -> bool {
    matches!(
        name,
        "Options::map"
            | "Options::and_then"
            | "Options::unwrap_or"
            | "Options::unwrap_or_else"
            | "Options::expect"
            | "Results::map"
            | "Results::map_err"
            | "Results::and_then"
            | "Results::recover"
            | "Results::expect"
    )
}

impl Checker {
    pub(super) fn standard_variant_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_variant_builtin(name) {
            return None;
        }
        if args.len() != 2 {
            self.error(
                "E0314",
                span,
                "variant combinator requires two arguments",
                [],
            );
            return Some(self.unit(span));
        }
        let (_, source, source_span) = &args[0];
        if args[0].0 != ParameterMode::Read {
            self.error(
                "E0405",
                *source_span,
                "variant subject is read-only",
                [source.cause],
            );
        }
        let callback = !matches!(
            name,
            "Options::unwrap_or" | "Options::expect" | "Results::expect"
        );
        if args[1].0 == ParameterMode::SharedMut || (!callback && args[1].0 != ParameterMode::Read)
        {
            self.error(
                "E0405",
                args[1].2,
                "variant argument mode mismatch",
                [args[1].1.cause],
            );
        }
        if name.starts_with("Options::") {
            let Ty::Optional(inner) = self.expanded(&source.ty, &mut BTreeSet::new()) else {
                self.error(
                    "E0301",
                    *source_span,
                    "Options operation requires Option data",
                    [source.cause],
                );
                return Some(self.unit(span));
            };
            let mut payload = source
                .option_payload
                .as_ref()
                .map_or_else(|| source.clone(), |payload| *payload.clone());
            payload.ty = (*inner).clone();
            payload.permission = payload.permission.meet(source.permission);
            if payload.ty.scalar() {
                payload.origins = Origins::default();
                payload.participants.clear();
                payload.temporary = false;
            }
            self.standard_borrowed_variant_payload(&mut payload);
            return Some(
                self.standard_option_operation(name, source, payload, &args[1], span, frame),
            );
        }
        let Ty::Result(ok, error) = self.expanded(&source.ty, &mut BTreeSet::new()) else {
            self.error(
                "E0301",
                *source_span,
                "Results operation requires Result data",
                [source.cause],
            );
            return Some(self.unit(span));
        };
        self.inspect_result(source);
        let mut success_payload = self.result_payload(source, true, span, frame);
        let mut error_payload = self.result_payload(source, false, span, frame);
        self.standard_borrowed_variant_payload(&mut success_payload);
        self.standard_borrowed_variant_payload(&mut error_payload);
        Some(self.standard_result_operation(
            name,
            source,
            success_payload,
            error_payload,
            *ok,
            *error,
            &args[1],
            span,
            frame,
        ))
    }
    fn standard_borrowed_variant_payload(&self, value: &mut Value) {
        if !value.origins.nodes.is_empty() {
            value.permission = Permission::Read;
            value.construction = false;
            value.marker = false;
        }
    }
    fn standard_option_operation(
        &mut self,
        name: &str,
        source: &Value,
        payload: Value,
        argument: &(ParameterMode, Value, Span),
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let inner = payload.ty.clone();
        let before = self.snapshot_flow();
        let obligations = frame.obligations.clone();
        let (mut skipped, execute) = if matches!(
            name,
            "Options::unwrap_or" | "Options::unwrap_or_else" | "Options::expect"
        ) {
            (payload.clone(), source.option_tag.map(|tag| !tag))
        } else {
            self.discharge_absent_results(source, span);
            (self.standard_none(inner.clone(), span), source.option_tag)
        };
        let skipped_state = self.snapshot_flow();
        self.restore_preview(&before);
        let executed = match name {
            "Options::expect" => {
                self.require_type(&argument.1, &Ty::Str, argument.2);
                self.standard_abnormal(span)
            }
            "Options::unwrap_or" => {
                self.require_type(&argument.1, &inner, argument.2);
                self.discharge_absent_results(source, span);
                let mut fallback = argument.1.clone();
                self.standard_borrowed_variant_payload(&mut fallback);
                fallback
            }
            "Options::unwrap_or_else" => {
                self.discharge_absent_results(source, span);
                let returned = self.standard_invoke_callback(argument, vec![], span, frame);
                self.require_type(&returned, &inner, span);
                returned
            }
            "Options::map" => {
                let returned = self.standard_invoke_callback(argument, vec![payload], span, frame);
                skipped.ty = Ty::Optional(Box::new(returned.ty.clone()));
                if returned.ty == Ty::Never {
                    returned
                } else {
                    self.standard_option(returned, Some(true), span, frame.owner)
                }
            }
            "Options::and_then" => {
                let returned = self.standard_invoke_callback(argument, vec![payload], span, frame);
                if !matches!(returned.ty, Ty::Optional(_) | Ty::Never) {
                    self.error(
                        "E0301",
                        span,
                        "Options::and_then callback must return Option",
                        [returned.cause],
                    );
                }
                skipped.ty = if returned.ty == Ty::Never {
                    Ty::Optional(Box::new(Ty::Never))
                } else {
                    returned.ty.clone()
                };
                returned
            }
            _ => unreachable!(),
        };
        match execute {
            Some(true) => executed,
            Some(false) => {
                self.restore_preview(&skipped_state);
                frame.obligations = obligations;
                skipped
            }
            None => self.branch_flow(&before, &skipped_state, &skipped, &executed, span),
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn standard_result_operation(
        &mut self,
        name: &str,
        source: &Value,
        success_payload: Value,
        error_payload: Value,
        ok: Ty,
        error: Ty,
        argument: &(ParameterMode, Value, Span),
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let produces = matches!(
            name,
            "Results::map" | "Results::map_err" | "Results::and_then"
        );
        let unit = self.unit(span);
        let template = produces.then(|| self.make_result(true, unit, span, frame.owner));
        let before = self.snapshot_flow();
        let obligations = frame.obligations.clone();
        let on_error = matches!(
            name,
            "Results::map_err" | "Results::recover" | "Results::expect"
        );
        let execute = source
            .result_tag
            .map(|tag| if on_error { !tag } else { tag });
        let mut skipped = if let Some(template) = &template {
            self.standard_result_branch(
                template,
                if on_error {
                    success_payload.clone()
                } else {
                    error_payload.clone()
                },
                on_error,
                ok.clone(),
                error.clone(),
            )
        } else {
            success_payload.clone()
        };
        let skipped_state = self.snapshot_flow();
        let executed = match name {
            "Results::expect" => {
                self.require_type(&argument.1, &Ty::Str, argument.2);
                self.standard_abnormal(span)
            }
            "Results::recover" => {
                let returned =
                    self.standard_invoke_callback(argument, vec![error_payload], span, frame);
                self.require_type(&returned, &ok, span);
                returned
            }
            "Results::map" => {
                let returned =
                    self.standard_invoke_callback(argument, vec![success_payload], span, frame);
                skipped.ty = Ty::Result(Box::new(returned.ty.clone()), Box::new(error.clone()));
                if returned.ty == Ty::Never {
                    returned
                } else {
                    self.standard_result_branch(
                        template.as_ref().unwrap(),
                        returned.clone(),
                        true,
                        returned.ty,
                        error,
                    )
                }
            }
            "Results::map_err" => {
                let returned =
                    self.standard_invoke_callback(argument, vec![error_payload], span, frame);
                skipped.ty = Ty::Result(Box::new(ok.clone()), Box::new(returned.ty.clone()));
                if returned.ty == Ty::Never {
                    returned
                } else {
                    self.standard_result_branch(
                        template.as_ref().unwrap(),
                        returned.clone(),
                        false,
                        ok,
                        returned.ty,
                    )
                }
            }
            "Results::and_then" => {
                let mut returned =
                    self.standard_invoke_callback(argument, vec![success_payload], span, frame);
                if let Ty::Result(result, actual_error) = &returned.ty {
                    if !self.compatible(actual_error, &error) {
                        self.error(
                            "E0301",
                            span,
                            "Results::and_then callback error type differs",
                            [returned.cause],
                        );
                    }
                    returned.ty = Ty::Result(result.clone(), Box::new(error.clone()));
                    skipped.ty = returned.ty.clone();
                    let outer = &template.as_ref().unwrap().outer_results;
                    returned.results.extend(outer);
                    returned.outer_results.extend(outer);
                    returned.must_results.extend(outer);
                    returned.must_outer_results.extend(outer);
                } else if returned.ty != Ty::Never {
                    self.error(
                        "E0301",
                        span,
                        "Results::and_then callback must return Result",
                        [returned.cause],
                    );
                }
                returned
            }
            _ => unreachable!(),
        };
        match execute {
            Some(true) => executed,
            Some(false) => {
                self.restore_preview(&skipped_state);
                frame.obligations = obligations;
                skipped
            }
            None => self.branch_flow(&before, &skipped_state, &skipped, &executed, span),
        }
    }
    fn standard_none(&mut self, inner: Ty, span: Span) -> Value {
        let mut value = self.unit(span);
        value.ty = Ty::Optional(Box::new(inner));
        value.constant = None;
        value.static_coordinate = None;
        value.option_tag = Some(false);
        value
    }
    fn standard_abnormal(&mut self, span: Span) -> Value {
        let mut value = self.unit(span);
        value.ty = Ty::Never;
        value.abnormal = true;
        value
    }
    fn standard_result_branch(
        &self,
        template: &Value,
        payload: Value,
        success: bool,
        ok: Ty,
        error: Ty,
    ) -> Value {
        let mut value = payload.clone();
        value.source_type_witness = None;
        value.ty = Ty::Result(Box::new(ok), Box::new(error));
        value.condition_inspections = Default::default();
        value.constant = None;
        value.static_coordinate = None;
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value.results.extend(&template.outer_results);
        value.must_results.extend(&template.must_outer_results);
        value.outer_results = template.outer_results.clone();
        value.must_outer_results = template.must_outer_results.clone();
        value.result_tag = Some(success);
        value.result_success = success.then(|| Box::new(payload.clone()));
        value.result_error = (!success).then(|| Box::new(payload.clone()));
        value.result_payload = Some(Box::new(payload));
        value.option_tag = None;
        value.option_payload = None;
        value.option_identity = None;
        value.callables.clear();
        value.callable_bounds.clear();
        value.callable_returns.clear();
        value.signature = None;
        value.variant_tag = None;
        value.variant_payload = None;
        value.variant_witnesses.clear();
        value
    }
    fn standard_invoke_callback(
        &mut self,
        argument: &(ParameterMode, Value, Span),
        mut arguments: Vec<Value>,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let (mode, callback, callback_span) = argument;
        let mut callback = callback.clone();
        if let Ty::Callable(parameters, _) = self.expanded(&callback.ty, &mut BTreeSet::new()) {
            for (value, parameter) in arguments.iter_mut().zip(parameters) {
                if value.ty == Ty::Unknown && !unknown_type(&parameter) {
                    value.ty = parameter;
                    if value.ty.scalar() {
                        value.origins = Origins::default();
                        value.participants.clear();
                        value.temporary = false;
                    }
                }
            }
        }
        if *mode == ParameterMode::Read {
            callback.permission = Permission::Read;
        } else if *mode == ParameterMode::Mut {
            if callback.permission != Permission::Write {
                self.error(
                    "E0520",
                    *callback_span,
                    "mutable callback has no write authority",
                    [callback.cause],
                );
            }
            self.access(&callback, None, Mode::Write, *callback_span, frame);
        }
        self.invoke_generated_values(
            &callback,
            arguments
                .into_iter()
                .map(|value| (ParameterMode::Read, value, span))
                .collect(),
            span,
            frame,
        )
    }
}
