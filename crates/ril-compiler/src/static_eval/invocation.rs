//! Static tail calls use an explicit invocation loop, not the host call stack.
//! The caller's return-shape contracts remain pending until the final value.
use super::*;

pub(super) struct TailInvocation {
    pub callable: StaticCallable,
    pub arguments: Vec<application::StaticArgument>,
    pub site: Span,
}

struct ReturnShape {
    syntax: TypeExpr,
    source_syntax: Option<TypeExpr>,
    environment: environments::Environment,
}

impl Evaluator {
    pub(super) fn invoke_static(
        &mut self,
        callable: StaticCallable,
        arguments: Vec<application::StaticArgument>,
    ) -> Result<StaticValue> {
        if self.call_depth + self.type_depth >= 64 {
            return Err(Failure::Unsupported(
                "non-tail static invocation exceeds the interpreter stack allowance".into(),
            ));
        }
        let saved = self.capture_environment()?;
        let saved_returns = self.tail_returns;
        let saved_types = self.tail_types;
        let saved_result_site = self.result_site;
        let saved_numeric_return = self.numeric_return.take();
        let saved_loops = std::mem::take(&mut self.loop_frames);
        self.tail_types = false;
        self.call_depth += 1;
        let result = self.invoke_static_loop(callable, arguments);
        self.call_depth -= 1;
        self.install_environment(saved);
        self.tail_returns = saved_returns;
        self.tail_types = saved_types;
        self.result_site = saved_result_site;
        self.numeric_return = saved_numeric_return;
        self.loop_frames = saved_loops;
        match result {
            Err(Failure::Loop(_)) => Err(Failure::Diagnostic(
                "E0707",
                "loop control cannot cross a static callable boundary".into(),
            )),
            other => other,
        }
    }

    fn invoke_static_loop(
        &mut self,
        mut callable: StaticCallable,
        mut arguments: Vec<application::StaticArgument>,
    ) -> Result<StaticValue> {
        let mut returns = Vec::<ReturnShape>::new();
        let mut meta_result = false;
        loop {
            self.charge()?;
            self.loop_frames.clear();
            self.tail_returns = false;
            let result = match callable {
                StaticCallable::Prepared(prepared) => {
                    meta_result = true;
                    self.install_environment(self.copy_environment(&prepared.environment)?);
                    let function = self.functions.get(&prepared.name).ok_or_else(|| {
                        Failure::Unsupported("prepared static declaration is unavailable".into())
                    })?;
                    clone_work::function(&self.budget, function)?;
                    let function = function.clone();
                    let signature = &prepared.signature;
                    if let Some(result) = &signature.result {
                        clone_work::type_syntax(&self.budget, result)?;
                    }
                    self.numeric_return = signature.result.clone();
                    let result = match self.bind_parameters_from_signature(
                        &signature.parameters,
                        &prepared.raw_signature.parameters,
                        arguments,
                    ) {
                        Err(failure) => Err(failure),
                        Ok(()) => {
                            self.budget.event(budget::Event::FunctionEntry)?;
                            let Some(body) = &function.body else {
                                return Err(Failure::Diagnostic(
                                    "E0810",
                                    "bodyless definition has no static implementation".into(),
                                ));
                            };
                            self.tail_returns = true;
                            let body = record_contexts::block(
                                body,
                                prepared.raw_signature.result.as_ref(),
                            );
                            self.block_expected(&body, true, prepared.raw_signature.result.as_ref())
                        }
                    };
                    if matches!(
                        result,
                        Ok(_) | Err(Failure::Return(_) | Failure::TailCall(_))
                    ) && let Some(syntax) = signature
                        .result
                        .as_ref()
                        .filter(|syntax| needs_shape(syntax))
                    {
                        clone_work::type_syntax(&self.budget, syntax)?;
                        returns.push(ReturnShape {
                            syntax: syntax.clone(),
                            source_syntax: prepared.raw_signature.result.clone(),
                            environment: self.capture_environment()?,
                        });
                    }
                    result
                }
                StaticCallable::View(view) => {
                    let application::CallableView {
                        target,
                        signature,
                        captured,
                    } = *view;
                    self.install_environment(captured);
                    let TypeKind::Callable {
                        parameters, result, ..
                    } = &signature.kind
                    else {
                        return Err(Failure::Unsupported(
                            "static callable view lost its signature".into(),
                        ));
                    };
                    let descriptors = parameters
                        .iter()
                        .map(application::ParameterSpec::from)
                        .collect::<Vec<_>>();
                    let plan = application::StaticApplicationPlan::new(
                        &descriptors,
                        arguments.iter().map(|argument| argument.label.clone()),
                    )?;
                    let mut supplied = arguments.into_iter().map(Some).collect::<Vec<_>>();
                    let mut prepared = Vec::new();
                    for (parameter, slot) in parameters.iter().zip(plan.slots) {
                        let application::ArgumentSlot::Explicit(index) = slot else {
                            return Err(Failure::Unsupported(
                                "a callable type view cannot supply declaration defaults".into(),
                            ));
                        };
                        let mut value = supplied[index]
                            .take()
                            .expect("unique static view slot")
                            .value;
                        if let Some(ty) = &parameter.ty {
                            value = self.ascribe_application_value(value, ty)?;
                        }
                        prepared.push(value.into());
                    }
                    if let Some(syntax) = result.as_deref() {
                        returns.push(ReturnShape {
                            syntax: syntax.clone(),
                            source_syntax: None,
                            environment: self.capture_environment()?,
                        });
                    }
                    callable = *target;
                    arguments = prepared;
                    continue;
                }
                StaticCallable::Builtin(name) => {
                    if arguments.iter().any(|argument| argument.label.is_some()) {
                        return Err(Failure::Unsupported(
                            "static builtin labelled application requires its listed signature"
                                .into(),
                        ));
                    }
                    self.static_builtin(
                        &name,
                        arguments
                            .into_iter()
                            .map(|argument| argument.value)
                            .collect(),
                    )
                }
                StaticCallable::Named { name, captured } => {
                    meta_result = true;
                    let function = self.functions.get(&name).ok_or_else(|| {
                        Failure::Unsupported("static callable declaration is unavailable".into())
                    })?;
                    clone_work::function(&self.budget, function)?;
                    let function = function.clone();
                    if !function.generics.is_empty() {
                        let caller = self.capture_environment()?;
                        let declaration = self.declaration_environment(captured)?;
                        self.type_application_sequence = self
                            .type_application_sequence
                            .checked_add(1)
                            .ok_or_else(|| {
                                Failure::Unsupported(
                                    "static type application activation identity exhausted".into(),
                                )
                            })?;
                        let types = typing::runtime_applications::infer_named_type_arguments(
                            self,
                            &function,
                            &declaration,
                            &caller,
                            &arguments,
                            None,
                            self.type_application_sequence,
                        )?;
                        callable = self.prepare_named(&name, captured, &types)?;
                        continue;
                    }
                    // A named function never inherits its caller's local names.
                    self.install_environment(self.declaration_environment(captured)?);
                    let signature = self.static_signature(&function)?;
                    self.numeric_return = signature.result.clone();
                    let result = match self.bind_parameters_from_signature(
                        &signature.parameters,
                        &function.parameters,
                        arguments,
                    ) {
                        Err(failure) => Err(failure),
                        Ok(()) => {
                            self.budget.event(budget::Event::FunctionEntry)?;
                            let Some(body) = &function.body else {
                                return Err(Failure::Diagnostic(
                                    "E0810",
                                    "foreign declarations have no static implementation".into(),
                                ));
                            };
                            self.tail_returns = true;
                            let body = record_contexts::block(body, function.return_type.as_ref());
                            self.block_expected(&body, true, function.return_type.as_ref())
                        }
                    };
                    if matches!(
                        result,
                        Ok(_) | Err(Failure::Return(_) | Failure::TailCall(_))
                    ) && let Some(syntax) = signature.result.filter(needs_shape)
                    {
                        returns.push(ReturnShape {
                            syntax,
                            source_syntax: function.return_type.clone(),
                            environment: self.capture_environment()?,
                        });
                    }
                    result
                }
                StaticCallable::Lambda {
                    parameters,
                    return_type,
                    body,
                    captured,
                } => {
                    self.install_environment(captured);
                    self.numeric_return = return_type.as_deref().cloned();
                    match self.bind_parameters(&parameters, arguments) {
                        Err(failure) => Err(failure),
                        Ok(()) => {
                            self.budget.event(budget::Event::FunctionEntry)?;
                            self.tail_returns = true;
                            self.expression_expected(&body, true, return_type.as_deref())
                        }
                    }
                }
            };
            let result = match result {
                Err(Failure::Return(value)) => Ok(*value),
                other => other,
            };
            match result {
                Err(Failure::TailCall(next)) => {
                    self.result_site = Some(next.site);
                    callable = next.callable;
                    arguments = next.arguments;
                }
                Ok(mut value) => {
                    if meta_result && contains_type_value(&value) {
                        return Err(Failure::Diagnostic(
                            "E0812",
                            "meta functions cannot return type values".into(),
                        ));
                    }
                    self.tail_returns = false;
                    for contract in returns.into_iter().rev() {
                        self.install_environment(contract.environment);
                        self.retain_constant_shape(&value, &contract.syntax)?;
                        value = self.ascribe_application_value_from_resolved(
                            value,
                            contract.source_syntax.as_ref().unwrap_or(&contract.syntax),
                            &contract.syntax,
                        )?;
                    }
                    return Ok(value);
                }
                Err(failure) => return Err(failure),
            }
        }
    }
}

fn needs_shape(ty: &TypeExpr) -> bool {
    match &ty.kind {
        TypeKind::Tuple(items) if items.is_empty() => false,
        TypeKind::Name { path, arguments } if arguments.is_empty() => {
            let name = path.join("::");
            !primitive_type(name.strip_prefix("Prelude::").unwrap_or(&name))
        }
        _ => true,
    }
}
