//! Explicit iterators retain actual step environments. No adapter invocation
//! is inferred from a descriptor's effect row or from its visible function type.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdapterKind {
    Indexed,
    Map,
    Filter,
    Take,
}

#[derive(Debug, Clone)]
pub struct StepFact {
    pub identity: String,
    pub closure: usize,
    pub kind: AdapterKind,
    pub state: Ty,
    pub item: Ty,
    pub span: Span,
    pub cause: CauseId,
}

pub(super) fn builtin(name: &str) -> bool {
    matches!(
        name,
        "Iter::indexed"
            | "Iter::cursor"
            | "Iter::pull"
            | "Iter::map"
            | "Iter::filter"
            | "Iter::take"
            | "Iter::collect"
            | "Iter::fold"
    )
}

impl Checker {
    fn iter_step_parts(&self, ty: &Ty) -> Option<(Ty, Ty)> {
        let Ty::Applied {
            constructor,
            arguments,
        } = self.call_inference_type(ty)
        else {
            return None;
        };
        if constructor != "Iter::Step" || arguments.len() != 2 {
            return None;
        }
        let data = |argument: &TypeArgument| match argument {
            TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => Some(*ty.clone()),
            _ => None,
        };
        Some((data(&arguments[0])?, data(&arguments[1])?))
    }
    fn iter_step_value(
        &mut self,
        present: bool,
        item: Option<Value>,
        state: Value,
        item_ty: &Ty,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let owner = self.iter_step_type(&state.ty, item_ty, span);
        let tag = if present {
            "Iter::Step::Yielded"
        } else {
            "Iter::Step::Done"
        };
        let name = self
            .constructors
            .iter()
            .find(|(_, constructor)| constructor.owner == owner && constructor.tag == tag)
            .map(|(name, _)| name.clone());
        let Some(name) = name else {
            self.unsupported(span, "iterator step has no complete constructor instance");
            return self.unit(span);
        };
        if let Some(item) = item {
            self.invoke_constructor(
                &name,
                &[
                    (ParameterMode::Read, item, span),
                    (ParameterMode::Read, state, span),
                ],
                span,
                None,
                frame,
            )
        } else {
            self.constructor_name(&name, span, frame)
                .unwrap_or_else(|| self.unit(span))
        }
    }
    pub(super) fn iter_private_name(&mut self, name: &str, span: Span) -> Option<Value> {
        let fact = self.iter_steps.get(name)?.clone();
        let closure = self.closures[fact.closure].clone();
        let mut inputs = vec![fact.state.clone()];
        inputs.extend(
            closure
                .captures
                .iter()
                .map(|id| self.bindings[*id].value.ty.clone()),
        );
        let result = self.iter_step_type(&fact.state, &fact.item, span);
        let mut value = Value::scalar(Ty::Callable(inputs, Box::new(result)), None, fact.cause);
        value.callables.push(Callable::Builtin(name.into()));
        Some(value)
    }
    pub(super) fn iter_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if let Some(fact) = self.iter_steps.get(name).cloned() {
            return Some(self.iter_transition(&fact, args, span, frame));
        }
        if !builtin(name) {
            return None;
        }
        let count = match name {
            "Iter::indexed" | "Iter::cursor" => 1,
            "Iter::fold" => 4,
            _ => 2,
        };
        if args.len() != count {
            self.error(
                "E0314",
                span,
                "explicit iterator argument count mismatch",
                [],
            );
            return Some(self.unit(span));
        }
        for (index, (mode, value, argument_span)) in args.iter().enumerate() {
            let expected = if name == "Iter::pull" && index == 0 {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected {
                self.error(
                    "E0405",
                    *argument_span,
                    "explicit iterator argument mode mismatch",
                    [value.cause],
                );
            }
        }
        Some(match name {
            "Iter::indexed" => {
                let items = &args[0].1;
                let Ty::Array(item) = self.collection_type(items) else {
                    self.error("E0301", span, "indexed requires an array", [items.cause]);
                    return Some(self.unit(span));
                };
                if !items.results.is_empty() || self.iter_type_has_results(&item) {
                    self.unsupported(
                        span,
                        "indexed Result membership requires transition-indexed producer coverage",
                    );
                }
                self.iter_source(
                    AdapterKind::Indexed,
                    Ty::Int("int".into()),
                    *item,
                    vec![items.clone()],
                    span,
                    frame,
                )
            }
            "Iter::cursor" => {
                let state = args[0].1.clone();
                let node = self.allocate_owned(span, 0, frame.owner);
                let cause = self.heap.nodes[node.0 as usize].cause;
                let mut cursor = Value::reference(
                    Ty::Record(
                        [
                            ("state".into(), (true, state.ty.clone())),
                            ("ended".into(), (true, Ty::Bool)),
                        ]
                        .into(),
                    ),
                    node,
                    cause,
                );
                cursor.results = state.results.clone();
                cursor.must_results = state.must_results.clone();
                cursor.scoped = state.scoped.clone();
                self.store_field(node, Slot::Field("state".into()), state);
                self.store_field(
                    node,
                    Slot::Field("ended".into()),
                    Value::scalar(Ty::Bool, Some(Constant::Bool(false)), cause),
                );
                cursor
            }
            "Iter::pull" => self.iter_pull(&args[0].1, &args[1].1, span, frame),
            "Iter::collect" | "Iter::fold" => self.iter_traverse(name, args, span, frame),
            "Iter::map" | "Iter::filter" | "Iter::take" => {
                let source = &args[0].1;
                let step = self.project(source, Slot::Field("step".into()), span, frame, true);
                let Ty::Callable(inputs, result) = self.call_inference_type(&step.ty) else {
                    self.error(
                        "E0301",
                        span,
                        "adapter requires a source with a real step callable",
                        [step.cause],
                    );
                    return Some(self.unit(span));
                };
                let Some((state, item)) = self.iter_step_parts(&result) else {
                    self.error(
                        "E0301",
                        span,
                        "source step must return Iter::Step<S,T>",
                        [step.cause],
                    );
                    return Some(self.unit(span));
                };
                if inputs.len() != 1 || !self.compatible(&inputs[0], &state) {
                    self.error(
                        "E0301",
                        span,
                        "source step input and successor state differ",
                        [step.cause],
                    );
                }
                if step.mutable_environment {
                    self.error(
                        "E0520",
                        span,
                        "adapters cannot retain a mutable step environment",
                        [step.cause],
                    );
                }
                if name == "Iter::take" {
                    self.require_type(&args[1].1, &Ty::Int("int".into()), args[1].2);
                    if matches!(args[1].1.constant,Some(Constant::Integer(value))if value<0) {
                        let mut never = self.unit(span);
                        never.ty = Ty::Never;
                        never.abnormal = true;
                        never
                    } else {
                        self.iter_source(
                            AdapterKind::Take,
                            Ty::Tuple(vec![state, Ty::Int("int".into())]),
                            item,
                            vec![source.clone(), args[1].1.clone()],
                            span,
                            frame,
                        )
                    }
                } else {
                    let mut callback = args[1].1.clone();
                    callback.permission = Permission::Read;
                    if callback.mutable_environment {
                        self.error(
                            "E0520",
                            args[1].2,
                            "iterator adapters retain only read-only callback handles",
                            [callback.cause],
                        );
                    }
                    if callback.signature.as_ref().is_some_and(|parameters| {
                        parameters.len() != 1 || parameters[0].mode != ParameterMode::Read
                    }) {
                        self.error(
                            "E0407",
                            span,
                            "iterator adapter callback requires one read-only item",
                            [callback.cause],
                        );
                    }
                    let input = self.formal_value(item.clone(), 0, span, &mut BTreeSet::new());
                    let inferred = self.iter_preview_callback(
                        &callback,
                        vec![(ParameterMode::Read, input, span)],
                        span,
                        frame,
                    );
                    callback.ty = Ty::Callable(vec![item.clone()], Box::new(inferred.ty.clone()));
                    let kind = if name == "Iter::map" {
                        AdapterKind::Map
                    } else {
                        AdapterKind::Filter
                    };
                    let output = if name == "Iter::filter" {
                        self.require_type(&inferred, &Ty::Bool, span);
                        item
                    } else {
                        inferred.ty
                    };
                    self.iter_source(
                        kind,
                        state,
                        output,
                        vec![source.clone(), callback],
                        span,
                        frame,
                    )
                }
            }
            _ => {
                self.unsupported(
                    span,
                    "explicit iterator adapter or repeated transfer is not implemented",
                );
                self.unit(span)
            }
        })
    }
    fn iter_preview_callback(
        &mut self,
        callback: &Value,
        args: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        caller: &Frame,
    ) -> Value {
        let before = self.snapshot_flow();
        let completed = self.completed_invocation.clone();
        let budgets = std::mem::take(&mut self.budget_coverage);
        let mut preview = self.frame(caller.env.clone(), true);
        let result = self.invoke(callback, args, span, &mut preview);
        self.restore_preview(&before);
        self.completed_invocation = completed;
        self.budget_coverage = budgets;
        result
    }

    fn iter_source_signature(
        &mut self,
        source: &Value,
        span: Span,
        frame: &mut Frame,
    ) -> Option<(Value, Ty, Ty)> {
        let mut step = self.project(source, Slot::Field("step".into()), span, frame, true);
        step.permission = Permission::Read;
        if step.mutable_environment {
            self.error(
                "E0520",
                span,
                "explicit iteration retains only read-only step handles",
                [step.cause],
            );
        }
        if step.signature.as_ref().is_some_and(|parameters| {
            parameters.len() != 1 || parameters[0].mode != ParameterMode::Read
        }) {
            self.error(
                "E0407",
                span,
                "source step requires one read-only state",
                [step.cause],
            );
        }
        let Ty::Callable(inputs, result) = self.call_inference_type(&step.ty) else {
            self.error("E0301", span, "source step must be callable", [step.cause]);
            return None;
        };
        let Some((state, item)) = self.iter_step_parts(&result) else {
            self.error(
                "E0301",
                span,
                "source step must return Iter::Step<S,T>",
                [step.cause],
            );
            return None;
        };
        if inputs.len() != 1 || !self.compatible(&inputs[0], &state) {
            self.error(
                "E0301",
                span,
                "source step input and successor state differ",
                [step.cause],
            );
            return None;
        }
        Some((step, state, item))
    }

    fn iter_yielded_parts(
        &mut self,
        response: &Value,
        span: Span,
        frame: &mut Frame,
    ) -> Option<(Value, Value)> {
        let payload =
            self.constructor_pattern_payload(response, "Iter::Step::Yielded", span, frame)?;
        let item = self.project(&payload, Slot::Tuple(0), span, frame, true);
        let successor = self.project(&payload, Slot::Tuple(1), span, frame, true);
        Some((item, successor))
    }

    fn iter_regular_state(&self, old: &Value, new: &Value) -> bool {
        fn scalar_product(checker: &Checker, ty: &Ty, depth: usize) -> bool {
            if depth > 64 {
                return false;
            }
            match checker.representation_graph_type(ty) {
                ty if ty.scalar() => true,
                Ty::Immutable(inner) => scalar_product(checker, &inner, depth + 1),
                Ty::Tuple(items) => items
                    .iter()
                    .all(|ty| scalar_product(checker, ty, depth + 1)),
                Ty::Record(fields) => fields
                    .values()
                    .all(|(_, ty)| scalar_product(checker, ty, depth + 1)),
                ty => checker.constructor_scalar_type(&ty) == Some(true),
            }
        }
        old.origins.nodes == new.origins.nodes
            || (scalar_product(self, &old.ty, 0)
                && scalar_product(self, &new.ty, 0)
                && old.results.is_empty()
                && new.results.is_empty()
                && old.scoped.is_empty()
                && new.scoped.is_empty()
                && old.callables.is_empty()
                && new.callables.is_empty())
    }

    fn iter_traverse(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let Some((step, state_ty, item_ty)) = self.iter_source_signature(&args[1].1, span, frame)
        else {
            return self.unit(span);
        };
        self.require_type(&args[0].1, &state_ty, args[0].2);
        if self.iter_type_has_results(&state_ty) || self.iter_type_has_results(&item_ty) {
            self.unsupported(
                span,
                "iterator traversal requires transition-indexed Result membership coverage",
            );
        }
        let fold = name == "Iter::fold";
        let mut accumulator = if fold {
            args[2].1.clone()
        } else {
            self.unit(span)
        };
        let callback = fold.then(|| {
            let mut callback = args[3].1.clone();
            callback.permission = Permission::Read;
            if callback.mutable_environment {
                self.error(
                    "E0520",
                    args[3].2,
                    "fold requires a read-only callback handle",
                    [callback.cause],
                );
            }
            if callback.signature.as_ref().is_some_and(|parameters| {
                parameters.len() != 2
                    || parameters
                        .iter()
                        .any(|parameter| parameter.mode != ParameterMode::Read)
            }) {
                self.error(
                    "E0407",
                    args[3].2,
                    "fold callback requires read-only accumulator and item",
                    [callback.cause],
                );
            }
            let input = self.formal_value(item_ty.clone(), 1, span, &mut BTreeSet::new());
            let returned = self.iter_preview_callback(
                &callback,
                vec![
                    (ParameterMode::Read, accumulator.clone(), span),
                    (ParameterMode::Read, input, span),
                ],
                span,
                frame,
            );
            self.require_type(&returned, &accumulator.ty, span);
            callback
        });
        let mut state = args[0].1.clone();
        let mut collected = Vec::new();
        // Exact finite prefixes preserve known empty/aborting transitions. A
        // changing or unknown tail is analyzed as an arbitrary repetition.
        for iteration in 0..33 {
            let summary = iteration == 32;
            let mut invocation = vec![
                (ParameterMode::Read, state.clone(), span),
                (ParameterMode::Read, accumulator.clone(), span),
            ];
            let repeated = summary.then(|| self.begin_repeated_callback(&mut invocation, frame));
            state = invocation[0].1.clone();
            accumulator = invocation[1].1.clone();
            let response = self.invoke(
                &step,
                vec![(ParameterMode::Read, state.clone(), span)],
                span,
                frame,
            );
            if response.ty == Ty::Never {
                if let Some(repeated) = repeated {
                    self.finish_repeated_callback(repeated, span);
                }
                return response;
            }
            if response.variant_tag.as_deref() == Some("Iter::Step::Done") {
                if let Some(repeated) = repeated {
                    self.finish_repeated_callback(repeated, span);
                }
                return if fold {
                    accumulator
                } else {
                    self.standard_array_with_children(item_ty, collected, span, frame.owner)
                };
            }
            let before_yield = self.snapshot_flow();
            let Some((mut item, successor)) = self.iter_yielded_parts(&response, span, frame)
            else {
                if let Some(repeated) = repeated {
                    self.finish_aborted_repeated_callback(repeated, span);
                }
                return self.unit(span);
            };
            self.require_type(&successor, &state_ty, span);
            self.require_type(&item, &item_ty, span);
            if !item.results.is_empty() || !successor.results.is_empty() {
                self.unsupported(
                    span,
                    "iterator traversal cannot discard or merge uninspected Result families",
                );
            }
            self.standard_read_handle(&mut item);
            let previous_accumulator = accumulator.clone();
            if let Some(callback) = &callback {
                accumulator = self.invoke(
                    callback,
                    vec![
                        (ParameterMode::Read, accumulator, span),
                        (ParameterMode::Read, item, span),
                    ],
                    span,
                    frame,
                );
                self.require_type(&accumulator, &args[2].1.ty, span);
            } else {
                collected.push(item);
            }
            if response.variant_tag.is_none() {
                let executed = accumulator.clone();
                accumulator = self.conditional_flow(
                    &before_yield,
                    &previous_accumulator,
                    &executed,
                    None,
                    span,
                );
                if executed.ty == Ty::Never {
                    if let Some(repeated) = repeated {
                        self.finish_repeated_callback(repeated, span);
                    }
                    return accumulator;
                }
            } else if accumulator.ty == Ty::Never {
                if let Some(repeated) = repeated {
                    self.finish_repeated_callback(repeated, span);
                }
                return accumulator;
            }
            if let Some(repeated) = repeated {
                if !self.iter_regular_state(&state, &successor)
                    || (fold && !self.iter_regular_state(&previous_accumulator, &accumulator))
                {
                    self.unsupported(span, "iterator repetition changes a reference state without a regular transfer proof");
                }
                self.finish_repeated_callback(repeated, span);
                if fold {
                    return previous_accumulator.join(
                        &accumulator,
                        self.choice(),
                        accumulator.cause,
                    );
                }
                return self.standard_array_with_children(item_ty, collected, span, frame.owner);
            }
            state = successor;
            if response.variant_tag.is_none() {
                // Force the next transition into the widened repeated tail.
                let before_tail = self.snapshot_flow();
                let skipped = accumulator.clone();
                let mut tail = vec![
                    (ParameterMode::Read, state.clone(), span),
                    (ParameterMode::Read, accumulator.clone(), span),
                ];
                let repeated = self.begin_repeated_callback(&mut tail, frame);
                let response = self.invoke(&step, vec![tail[0].clone()], span, frame);
                let mut tail_aborts = response.ty == Ty::Never;
                if response.ty != Ty::Never
                    && response.variant_tag.as_deref() != Some("Iter::Step::Done")
                    && let Some((mut item, successor)) =
                        self.iter_yielded_parts(&response, span, frame)
                {
                    if !self.iter_regular_state(&tail[0].1, &successor) {
                        self.unsupported(
                            span,
                            "iterator repeated successor requires a regular reference transfer",
                        );
                    }
                    if !item.results.is_empty() || !successor.results.is_empty() {
                        self.unsupported(
                            span,
                            "iterator repeated transition requires Result family coverage",
                        );
                    }
                    self.standard_read_handle(&mut item);
                    if let Some(callback) = &callback {
                        let returned = self.invoke(
                            callback,
                            vec![tail[1].clone(), (ParameterMode::Read, item, span)],
                            span,
                            frame,
                        );
                        self.require_type(&returned, &args[2].1.ty, span);
                        if returned.ty != Ty::Never
                            && !self.iter_regular_state(&tail[1].1, &returned)
                        {
                            self.unsupported(
                                span,
                                "iterator fold accumulator requires a regular reference transfer",
                            );
                        }
                        tail_aborts = returned.ty == Ty::Never && response.variant_tag.is_some();
                        if returned.ty != Ty::Never {
                            accumulator =
                                accumulator.join(&returned, self.choice(), returned.cause);
                        }
                    } else {
                        collected.push(item);
                    }
                }
                self.finish_repeated_callback(repeated, span);
                let executed = if tail_aborts {
                    let mut never = self.unit(span);
                    never.ty = Ty::Never;
                    never.abnormal = true;
                    never
                } else {
                    accumulator.clone()
                };
                accumulator = self.conditional_flow(&before_tail, &skipped, &executed, None, span);
                return if fold {
                    accumulator
                } else {
                    self.standard_array_with_children(item_ty, collected, span, frame.owner)
                };
            }
        }
        unreachable!()
    }

    fn iter_type_has_results(&self, ty: &Ty) -> bool {
        match self.call_inference_type(ty) {
            Ty::Result(..)
            | Ty::Generic(_)
            | Ty::Projection { .. }
            | Ty::OpenRecord { .. }
            | Ty::Unknown => true,
            Ty::Array(a) | Ty::Set(a) | Ty::Optional(a) | Ty::Immutable(a) => {
                self.iter_type_has_results(&a)
            }
            Ty::Tuple(items) => items.iter().any(|ty| self.iter_type_has_results(ty)),
            Ty::Record(fields) => fields
                .values()
                .any(|(_, ty)| self.iter_type_has_results(ty)),
            Ty::Map(a, b) => self.iter_type_has_results(&a) || self.iter_type_has_results(&b),
            Ty::Applied { .. } => true,
            _ => false,
        }
    }

    fn iter_source(
        &mut self,
        kind: AdapterKind,
        state: Ty,
        item: Ty,
        captures: Vec<Value>,
        span: Span,
        caller: &mut Frame,
    ) -> Value {
        let origin_context = self.invocation_context(caller.callable_owner);
        let Some(origin_event) = self.copy_operation_events.last().copied().flatten() else {
            self.unsupported(
                span,
                "generated iterator source requires its actual adapter Call event",
            );
            return self.unit(span);
        };
        let Some((state_syntax, item_syntax)) =
            self.iter_argument_syntax(&state, span, 0)
                .and_then(|state| normalize_closed_source_syntax(&state, &self.types, self.layout))
                .zip(self.iter_argument_syntax(&item, span, 0).and_then(|item| {
                    normalize_closed_source_syntax(&item, &self.types, self.layout)
                }))
        else {
            self.unsupported(
                span,
                "iterator state has no complete non-erasing parameter schema",
            );
            return self.unit(span);
        };
        let result_ty = self.iter_step_type(&state, &item, span);
        let mut environment = self.frame(caller.env.clone(), true);
        self.scope_parents.insert(environment.owner, caller.owner);
        let mut capture_ids = BTreeSet::new();
        for (index, value) in captures.into_iter().enumerate() {
            let mode = if value.publication == Publication::Immutable || value.construction {
                BindingMode::Let
            } else {
                BindingMode::View
            };
            let name = format!("ril__iter_capture_{index}");
            let id = self.bind_name(&name, mode, value, span, &mut environment, false);
            capture_ids.insert(id);
        }
        let identity = format!("ril__iter_step_{}", environment.owner.0);
        let node = self.allocate_owned(span, 0, environment.owner);
        let cause = self.cause(
            CauseKind::Capture,
            span,
            "iterator step retains its actual read-only environment",
            [],
        );
        let closure = self.closures.len();
        let Ok(ordinal) = u32::try_from(self.generated_sources.len()) else {
            self.unsupported(span, "generated source identity space is exhausted");
            return self.unit(span);
        };
        let generated_id = crate::sema::generated_sources::GeneratedSourceId(ordinal);
        let Some(syntax) = super::generated_sources::iterator_syntax(
            generated_id.0,
            &identity,
            &state_syntax,
            &item_syntax,
            capture_ids.len(),
        ) else {
            self.unsupported(
                span,
                "generated iterator source exceeds its canonical syntax budget",
            );
            return self.unit(span);
        };
        let Some(site) = self.closure_site(caller.callable_owner, syntax.span) else {
            self.unsupported(
                span,
                "generated iterator source has no actual lexical owner",
            );
            return self.unit(span);
        };
        let ExprKind::Lambda {
            parameters,
            return_type,
            body,
            ..
        } = &syntax.kind
        else {
            unreachable!()
        };
        self.closures.push(ClosureInfo {
            site: Some(site),
            creation_invocation: self.copy_invocation_stack.last().copied(),
            creation_closure: self.closure_invocation_stack.last().copied(),
            creation_default: self.default_use_stack.last().copied(),
            handler_context: self.active_handlers.clone(),
            parameters: parameters.clone(),
            body: (**body).clone(),
            lexical: environment.env.clone(),
            captures: capture_ids.clone(),
            writes: BTreeSet::new(),
            owner: environment.owner,
            node,
        });
        self.lambda_contracts.insert(
            closure,
            contracts::LambdaContract {
                return_type: return_type.clone(),
                annotations: vec![],
                span,
                typing_environment: self
                    .capture_typing_environment()
                    .with_contract_bindings(environment.env.clone()),
            },
        );
        self.iter_steps.insert(
            identity.clone(),
            StepFact {
                identity,
                closure,
                kind,
                state: state.clone(),
                item: item.clone(),
                span,
                cause,
            },
        );
        self.generated_sources
            .push(crate::sema::generated_sources::GeneratedSource {
                id: generated_id,
                origin_event,
                origin_context,
                adapter: kind,
                closure,
                site,
                syntax: std::sync::Arc::new(syntax.clone()),
                captures: capture_ids
                    .iter()
                    .enumerate()
                    .map(
                        |(slot, binding)| crate::sema::generated_sources::GeneratedCapture {
                            binding: *binding,
                            origin_slot: slot as u32,
                            path: vec![],
                        },
                    )
                    .collect(),
            });
        // The generated state parameter and result have complete schemas.
        // Source construction never invokes a retained transition callback.
        self.checked_closures.insert(closure);
        let mut step =
            Value::reference(Ty::Callable(vec![state], Box::new(result_ty)), node, cause);
        step.callables.push(Callable::Closure(closure));
        step.signature = Some(self.closures[closure].parameters.clone());
        let callable_schema = TypeExpr {
            text: String::new(),
            span,
            kind: TypeKind::Callable {
                parameters: parameters.clone(),
                result: return_type.clone().map(Box::new),
                annotations: vec![],
            },
        };
        step.source_type_witness = self.source_type_from_frozen_syntax(&callable_schema);
        step.permission = Permission::Read;
        step.publication = Publication::Immutable;
        step.construction = false;
        for (index, id) in capture_ids.iter().enumerate() {
            let captured = self.capture_value(*id);
            step.results.extend(&captured.results);
            step.must_results.extend(&captured.must_results);
            step.scoped.extend(&captured.scoped);
            if captured.publication != Publication::Immutable {
                step.publication = Publication::Live;
                step.observer_environment = true;
            }
            self.store_field(node, Slot::Capture(index as u32), captured);
        }
        let record = self.allocate_owned(span, 0, caller.owner);
        let mut source = Value::reference(
            Ty::Record([("step".into(), (false, step.ty.clone()))].into()),
            record,
            cause,
        );
        source.observer_environment = step.observer_environment;
        source.results = step.results.clone();
        source.must_results = step.must_results.clone();
        source.scoped = step.scoped.clone();
        source.source_type_witness = self.source_type_from_frozen_syntax(&TypeExpr {
            text: String::new(),
            span,
            kind: TypeKind::Record {
                fields: vec![TypeField {
                    name: "step".into(),
                    mutable: false,
                    ty: callable_schema,
                    span,
                }],
                row: None,
            },
        });
        self.store_field(record, Slot::Field("step".into()), step);
        for id in capture_ids {
            self.bindings[id].alive = false;
        }
        source
    }

    fn iter_transition(
        &mut self,
        fact: &StepFact,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        if args.len()
            != if matches!(fact.kind, AdapterKind::Indexed) {
                2
            } else {
                3
            }
        {
            self.unsupported(
                span,
                "iterator internal transition has an incomplete environment",
            );
            return self.unit(span);
        }
        self.require_type(&args[0].1, &fact.state, span);
        match fact.kind {
            AdapterKind::Indexed => {
                let items = &args[1].1;
                let index = match args[0].1.constant {
                    Some(Constant::Integer(index)) => Some(index),
                    _ => None,
                };
                if index.is_some_and(|index| index < 0) {
                    let mut never = self.unit(span);
                    never.ty = Ty::Never;
                    never.abnormal = true;
                    return never;
                }
                let length = self.known_array_length(items);
                let present = index
                    .zip(length)
                    .map(|(index, length)| (index as u128) < u128::from(length));
                let done =
                    self.iter_step_value(false, None, args[0].1.clone(), &fact.item, span, frame);
                if present == Some(false) {
                    return done;
                }
                let item = self.project(
                    items,
                    index
                        .and_then(|index| i64::try_from(index).ok())
                        .map(Slot::Index)
                        .unwrap_or(Slot::AnyIndex),
                    span,
                    frame,
                    true,
                );
                let successor = Value::scalar(
                    Ty::Int("int".into()),
                    index
                        .and_then(|index| index.checked_add(1))
                        .map(Constant::Integer),
                    item.cause,
                );
                let yielded =
                    self.iter_step_value(true, Some(item), successor, &fact.item, span, frame);
                if present == Some(true) {
                    yielded
                } else {
                    yielded.join(&done, self.choice(), fact.cause)
                }
            }
            AdapterKind::Map => {
                let response = self.iter_call_source(&args[1].1, args[0].1.clone(), span, frame);
                if response.ty == Ty::Never {
                    return response;
                }
                let done =
                    self.iter_step_value(false, None, args[0].1.clone(), &fact.item, span, frame);
                if response.variant_tag.as_deref() == Some("Iter::Step::Done") {
                    return done;
                }
                let before = self.snapshot_flow();
                let Some(payload) =
                    self.constructor_pattern_payload(&response, "Iter::Step::Yielded", span, frame)
                else {
                    return self.unit(span);
                };
                let item = self.project(&payload, Slot::Tuple(0), span, frame, true);
                let successor = self.project(&payload, Slot::Tuple(1), span, frame, true);
                let transformed = self.invoke(
                    &args[2].1,
                    vec![(ParameterMode::Read, item, span)],
                    span,
                    frame,
                );
                let output = if transformed.ty == Ty::Never {
                    transformed
                } else {
                    self.iter_step_value(
                        true,
                        Some(transformed),
                        successor,
                        &fact.item,
                        span,
                        frame,
                    )
                };
                self.conditional_flow(
                    &before,
                    &done,
                    &output,
                    response
                        .variant_tag
                        .as_ref()
                        .map(|tag| tag == "Iter::Step::Yielded"),
                    span,
                )
            }
            AdapterKind::Take => {
                let source_state = self.project(&args[0].1, Slot::Tuple(0), span, frame, true);
                let used = self.project(&args[0].1, Slot::Tuple(1), span, frame, true);
                self.require_type(&used, &Ty::Int("int".into()), span);
                let count = match args[2].1.constant {
                    Some(Constant::Integer(value)) => Some(value),
                    _ => None,
                };
                let consumed = match used.constant {
                    Some(Constant::Integer(value)) => Some(value),
                    _ => None,
                };
                if consumed.is_some_and(|value| value < 0)
                    || consumed
                        .zip(count)
                        .is_some_and(|(used, count)| used > count)
                {
                    let mut never = self.unit(span);
                    never.ty = Ty::Never;
                    never.abnormal = true;
                    return never;
                }
                let done =
                    self.iter_step_value(false, None, args[0].1.clone(), &fact.item, span, frame);
                if consumed
                    .zip(count)
                    .is_some_and(|(used, count)| used == count)
                {
                    return done;
                }
                let before = self.snapshot_flow();
                let response = self.iter_call_source(&args[1].1, source_state, span, frame);
                let output = if response.ty == Ty::Never {
                    response
                } else if response.variant_tag.as_deref() == Some("Iter::Step::Done") {
                    done.clone()
                } else {
                    let Some(payload) = self.constructor_pattern_payload(
                        &response,
                        "Iter::Step::Yielded",
                        span,
                        frame,
                    ) else {
                        return self.unit(span);
                    };
                    let item = self.project(&payload, Slot::Tuple(0), span, frame, true);
                    let successor = self.project(&payload, Slot::Tuple(1), span, frame, true);
                    let next_count = Value::scalar(
                        Ty::Int("int".into()),
                        consumed
                            .and_then(|value| value.checked_add(1))
                            .map(Constant::Integer),
                        used.cause,
                    );
                    let tuple = self.iter_tuple(vec![successor, next_count], span, frame.owner);
                    let yielded =
                        self.iter_step_value(true, Some(item), tuple, &fact.item, span, frame);
                    if response.variant_tag.is_some() {
                        yielded
                    } else {
                        yielded.join(&done, self.choice(), fact.cause)
                    }
                };
                self.conditional_flow(
                    &before,
                    &done,
                    &output,
                    consumed.zip(count).map(|(used, count)| used < count),
                    span,
                )
            }
            AdapterKind::Filter => self.iter_filter_transition(fact, args, span, frame),
        }
    }
    fn iter_join_output(
        &mut self,
        before: &super::flow::FlowSnapshot,
        outputs: &mut Option<(Value, super::flow::FlowSnapshot)>,
        mut value: Value,
        span: Span,
    ) {
        if let Some((previous, state)) = outputs.take() {
            value = self.branch_flow(before, &state, &previous, &value, span);
        }
        *outputs = Some((value, self.snapshot_flow()));
    }

    fn iter_filter_transition(
        &mut self,
        fact: &StepFact,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let before = self.snapshot_flow();
        let mut state = args[0].1.clone();
        let mut outputs = None;
        let mut summarize = false;
        for iteration in 0..33 {
            let summary = summarize || iteration == 32;
            let mut invocation = vec![(ParameterMode::Read, state.clone(), span)];
            let repeated = summary.then(|| self.begin_repeated_callback(&mut invocation, frame));
            state = invocation[0].1.clone();
            let response = self.iter_call_source(&args[1].1, state.clone(), span, frame);
            if response.ty == Ty::Never {
                if let Some(repeated) = repeated {
                    self.finish_repeated_callback(repeated, span);
                }
                if let Some((value, state)) = outputs {
                    self.restore_preview(&state);
                    return value;
                }
                return response;
            }
            let done = self.iter_step_value(false, None, state.clone(), &fact.item, span, frame);
            if response.variant_tag.as_deref() != Some("Iter::Step::Yielded") {
                let continuing = self.snapshot_flow();
                self.iter_join_output(&before, &mut outputs, done.clone(), span);
                if response.variant_tag.is_some() {
                    if let Some(repeated) = repeated {
                        self.finish_repeated_callback(repeated, span);
                    }
                    return outputs.unwrap().0;
                }
                self.restore_preview(&continuing);
            }
            let Some((item, successor)) = self.iter_yielded_parts(&response, span, frame) else {
                if let Some(repeated) = repeated {
                    self.finish_aborted_repeated_callback(repeated, span);
                }
                return self.unit(span);
            };
            if !item.results.is_empty() || !successor.results.is_empty() {
                self.unsupported(
                    span,
                    "filter requires inspection coverage for every rejected Result item",
                );
            }
            let predicate = self.invoke(
                &args[2].1,
                vec![(ParameterMode::Read, item.clone(), span)],
                span,
                frame,
            );
            self.require_type(&predicate, &Ty::Bool, span);
            if predicate.ty == Ty::Never {
                if let Some(repeated) = repeated {
                    self.finish_repeated_callback(repeated, span);
                }
                if let Some((value, state)) = outputs {
                    self.restore_preview(&state);
                    return value;
                }
                return predicate;
            }
            let accepted = match predicate.constant {
                Some(Constant::Bool(value)) => Some(value),
                _ => None,
            };
            if accepted != Some(false) {
                let yielded = self.iter_step_value(
                    true,
                    Some(item),
                    successor.clone(),
                    &fact.item,
                    span,
                    frame,
                );
                let continuing = self.snapshot_flow();
                self.iter_join_output(&before, &mut outputs, yielded, span);
                if accepted == Some(true) {
                    if let Some(repeated) = repeated {
                        self.finish_repeated_callback(repeated, span);
                    }
                    return outputs.unwrap().0;
                }
                self.restore_preview(&continuing);
            }
            if let Some(repeated) = repeated {
                if !self.iter_regular_state(&state, &successor) {
                    self.unsupported(
                        span,
                        "filter repetition requires a regular successor reference transfer",
                    );
                }
                self.finish_repeated_callback(repeated, span);
                // A rejected tail either ends at Done or does not return.
                self.iter_join_output(&before, &mut outputs, done, span);
                return outputs.unwrap().0;
            }
            state = successor;
            summarize = accepted.is_none() || response.variant_tag.is_none();
        }
        unreachable!()
    }
    fn iter_call_source(
        &mut self,
        source: &Value,
        state: Value,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let step = self.project(source, Slot::Field("step".into()), span, frame, true);
        if step.mutable_environment {
            self.error(
                "E0520",
                span,
                "iterator source invocation requires a read-only environment",
                [step.cause],
            );
        }
        self.invoke(&step, vec![(ParameterMode::Read, state, span)], span, frame)
    }
    fn iter_tuple(&mut self, items: Vec<Value>, span: Span, owner: ScopeId) -> Value {
        let node = self.allocate_owned(span, 0x1000_0000, owner);
        let cause = self.heap.nodes[node.0 as usize].cause;
        let mut tuple = Value::reference(
            Ty::Tuple(items.iter().map(|value| value.ty.clone()).collect()),
            node,
            cause,
        );
        for (index, value) in items.into_iter().enumerate() {
            tuple.results.extend(&value.results);
            tuple.must_results.extend(&value.must_results);
            tuple.scoped.extend(&value.scoped);
            tuple.callback_parameters.extend(&value.callback_parameters);
            tuple.mutable_environment |= value.mutable_environment;
            tuple.observer_environment |= value.observer_environment;
            self.store_field(node, Slot::Tuple(index as u32), value);
        }
        tuple
    }

    fn iter_pull(
        &mut self,
        cursor: &Value,
        source: &Value,
        span: Span,
        caller: &mut Frame,
    ) -> Value {
        if cursor.permission != Permission::Write {
            self.error(
                "E0520",
                span,
                "pull requires cursor write authority",
                [cursor.cause],
            );
        }
        let mut frame = self.frame(caller.env.clone(), true);
        self.scope_parents.insert(frame.owner, caller.owner);
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        self.loan_parents.insert(loan, cursor.participants.clone());
        let mut borrowed = cursor.clone();
        borrowed.participants = [Participant::Loan(loan)].into();
        borrowed.temporary = true;
        self.access(&borrowed, None, Mode::Write, span, &mut frame);
        let ended = self.project(
            &borrowed,
            Slot::Field("ended".into()),
            span,
            &mut frame,
            true,
        );
        self.require_type(&ended, &Ty::Bool, span);
        let state = self.project(
            &borrowed,
            Slot::Field("state".into()),
            span,
            &mut frame,
            true,
        );
        let step = self.project(source, Slot::Field("step".into()), span, &mut frame, true);
        if step.mutable_environment {
            self.error(
                "E0520",
                span,
                "explicit iteration retains only read-only callback handles",
                [step.cause],
            );
        }
        if step.signature.as_ref().is_some_and(|parameters| {
            parameters.len() != 1 || parameters[0].mode != ParameterMode::Read
        }) {
            self.error(
                "E0407",
                span,
                "source step must receive one read-only state",
                [step.cause],
            );
        }
        let Ty::Callable(inputs, declared_result) = self.call_inference_type(&step.ty) else {
            self.error(
                "E0301",
                span,
                "source step must be a callable",
                [step.cause],
            );
            return self.unit(span);
        };
        if inputs.len() != 1 || self.iter_step_parts(&declared_result).is_none() {
            self.error(
                "E0301",
                span,
                "source step has an incomplete transition signature",
                [step.cause],
            );
            return self.unit(span);
        }
        self.require_type(&state, &inputs[0], span);
        if ended.constant == Some(Constant::Bool(true)) {
            self.apply_handler_obligations(&frame.obligations, caller);
            return self.none_value(span);
        }
        let before = self.snapshot_flow();
        let response = self.invoke(
            &step,
            vec![(ParameterMode::Read, state, span)],
            span,
            &mut frame,
        );
        let output = if response.ty == Ty::Never {
            response
        } else {
            let Some((state_ty, item_ty)) = self.iter_step_parts(&response.ty) else {
                self.error(
                    "E0301",
                    span,
                    "source step must return Iter::Step<S,T>",
                    [response.cause],
                );
                return self.unit(span);
            };
            if !response.results.is_empty()
                || self.iter_type_has_results(&state_ty)
                || self.iter_type_has_results(&item_ty)
            {
                self.unsupported(span,"iterator Result families require exact transition membership and escape coverage");
            }
            let old_state = self.project(
                &borrowed,
                Slot::Field("state".into()),
                span,
                &mut frame,
                false,
            );
            self.require_type(&old_state, &state_ty, span);
            let payload = if response.variant_tag.as_deref() == Some("Iter::Step::Done") {
                None
            } else {
                self.constructor_pattern_payload(&response, "Iter::Step::Yielded", span, &mut frame)
            };
            let mut yielded = self.unit(span);
            let transition_choice = self.choice();
            if let Some(payload) = payload {
                let item = self.project(&payload, Slot::Tuple(0), span, &mut frame, true);
                let successor = self.project(&payload, Slot::Tuple(1), span, &mut frame, true);
                self.require_type(&successor, &state_ty, span);
                // Only Yielded installs a successor. The old state below is
                // retained on the Done branch, where no state write occurs;
                // it must not count as a newly published writable alias.
                // Check the actual written value before joining control flow.
                self.check_stored_authority(
                    &borrowed,
                    &successor,
                    Some(&old_state),
                    span,
                    &mut frame,
                );
                let installed = if response.variant_tag.is_some() {
                    successor.clone()
                } else {
                    successor.join(&old_state, transition_choice, response.cause)
                };
                for node in &borrowed.origins.nodes {
                    self.store_field(*node, Slot::Field("state".into()), installed.clone());
                }
                yielded = self.wrap_optional(item, Some(true));
            }
            let none = self.none_value(span);
            match response.variant_tag.as_deref() {
                Some("Iter::Step::Done") => {
                    for node in &borrowed.origins.nodes {
                        self.store_field(
                            *node,
                            Slot::Field("ended".into()),
                            Value::scalar(Ty::Bool, Some(Constant::Bool(true)), response.cause),
                        );
                    }
                    none
                }
                Some("Iter::Step::Yielded") => yielded,
                _ => {
                    for node in &borrowed.origins.nodes {
                        self.store_field(
                            *node,
                            Slot::Field("ended".into()),
                            Value::scalar(Ty::Bool, None, response.cause),
                        );
                    }
                    yielded.join(&none, transition_choice, response.cause)
                }
            }
        };
        let none = self.none_value(span);
        let output = self.conditional_flow(
            &before,
            &none,
            &output,
            match ended.constant {
                Some(Constant::Bool(ended)) => Some(!ended),
                _ => None,
            },
            span,
        );
        self.check_exclusivity(&frame.obligations.accesses, span);
        let loans = [(loan, cursor.participants.clone())].into();
        for access in &mut frame.obligations.accesses {
            access.participants =
                super::recursive_calls::normalize_participants(&access.participants, &loans);
        }
        self.apply_handler_obligations(&frame.obligations, caller);
        caller
            .obligations
            .accesses
            .extend(frame.obligations.accesses);
        self.transfer_results(&output, frame.owner, caller.owner);
        output
    }
}
