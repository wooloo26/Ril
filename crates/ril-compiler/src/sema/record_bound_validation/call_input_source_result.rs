//! Independently recover contextual Type leaves from this producing instance.
use super::*;

impl Replay<'_> {
    pub(super) fn open_carrier_source_result(
        &self,
        event: &crate::sema::copy_contract::CopyCallEvent,
        syntax: &Expr,
        callee: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check {
        let [crate::sema::model::Callable::Builtin(identity)] = callee.callables.as_slice() else {
            return Ok(());
        };
        let success = match identity.strip_prefix("Prelude::").unwrap_or(identity) {
            "Ok" => true,
            "Err" => false,
            _ => return Ok(()),
        };
        let root = event
            .result_expression
            .and_then(|index| self.facts.expressions.get(index))
            .ok_or_else(|| "Result source has no actual result root".to_owned())?;
        if root.value.ty == Ty::Never || root.value.source_type_witness.is_some() {
            return Ok(());
        }
        let Ty::Result(ok, error) = &root.value.ty else {
            return Err("Result source changed its actual primitive type".into());
        };
        if (if success { error } else { ok }).as_ref() == &Ty::Unknown {
            return Ok(());
        }
        require(
            self.original_carrier_source_schema(
                syntax,
                &root.value,
                context,
                sites,
                &mut 16384,
                SourceVisit {
                    depth: 0,
                    observation: event.result_expression,
                },
            )?
            .flatten()
            .is_some(),
            "contextual open Result has no independently reconstructed active source",
        )
    }

    pub(super) fn original_carrier_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<ArgumentKey>> {
        let Some(application) = AstApplication::from_ast(expression) else {
            return Ok(None);
        };
        let callee = application.callee;
        let arguments = &application.operands;
        let Some(success) = value.result_tag else {
            return Ok(None);
        };
        let identity = if success { "Ok" } else { "Err" };
        if arguments.len() != 1
            || arguments[0].label.is_some()
            || arguments[0].mode != ril_syntax::ast::ParameterMode::Read
        {
            return Ok(None);
        }
        let events: Vec<_> = self.facts.copy_call_events.iter().filter(|event| {
            event.matches_source(expression) && event.owner == context.owner && event.parent == context.invocation
                && event.result_expression.is_some_and(|index| {
                    self.facts.expressions.get(index).is_some_and(|fact| fact.source_id.is_some() && fact.source_id == expression.hir_id && fact.value == *value)
                        && self.observations.row(index, work).is_ok_and(|row| row.context == context)
                })
                && event.callee_expression.is_some_and(|index| {
                    self.facts.expressions.get(index).is_some_and(|fact| fact.source_id.is_some() && fact.source_id == callee.hir_id && fact.value.sources.is_empty()
                        && matches!(fact.value.callables.as_slice(), [crate::sema::model::Callable::Builtin(name)]
                            if name.strip_prefix("Prelude::").unwrap_or(name) == identity))
                        && self.observations.row(index, work).is_ok_and(|row| row.context == context)
                })
        }).collect();
        if events.is_empty() {
            return Ok(None);
        }
        let [event] = events.as_slice() else {
            return Err("open Result Source borrowed another carrier event".into());
        };
        super::super::super::checker::actual_prelude_name(self.facts, context, callee, identity)?;
        let preparations: Vec<_> = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id)
            .collect();
        let [preparation] = preparations.as_slice() else {
            return Err("open Result Source lacks its actual supplied operand".into());
        };
        require(
            preparation.target.is_none()
                && preparation.evaluation_complete
                && preparation.slots == [crate::sema::default_uses::ArgumentSource::Supplied]
                && preparation.supplied.len() == 1,
            "open Result Source changed its primitive invocation or operand slots",
        )?;
        let token = preparation
            .supplied
            .get(&0)
            .ok_or_else(|| "open Result Source lost slot zero".to_owned())?;
        let operand = self
            .facts
            .expressions
            .get(token.expression)
            .ok_or_else(|| "open Result Source operand is absent".to_owned())?;
        require(
            operand.source_id.is_some()
                && operand.source_id == arguments[0].expression.hir_id
                && self
                    .observations
                    .row(token.expression, work)
                    .is_ok_and(|row| {
                        row.context == context && row.argument_of == Some((event.id, 0))
                    }),
            "open Result Source operand borrowed another physical occurrence",
        )?;
        self.input_operand_interval(event, 0, token.expression, context, sites)?;
        let payload = if success {
            value.result_success.as_deref()
        } else {
            value.result_error.as_deref()
        }
        .ok_or_else(|| "open Result Source lost its active payload".to_owned())?;
        require(
            payload.cause == operand.value.cause
                && value.result_payload.as_deref() == Some(payload)
                && self
                    .facts
                    .explanations
                    .causes
                    .get(value.cause.0 as usize)
                    .is_some_and(|cause| cause.parents == [operand.value.cause]),
            "open Result Source active payload is not its actual constructor operand",
        )?;
        let active = self.original_source_key_inner(
            arguments[0].expression,
            &operand.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: depth + 1,
                observation: Some(token.expression),
            },
        )?;
        let receiver = self.producing_receiver_key(expression, value, context, sites)?;
        let ArgumentKey::Name { name, arguments } = receiver else {
            return Err("open Result Source has no actual Result receiver".into());
        };
        require(
            name == "Result" && arguments.len() == 2,
            "open Result Source changed its receiving family",
        )?;
        let inactive = arguments[usize::from(success)].clone();
        let key = ArgumentKey::Name {
            name: "Result".into(),
            arguments: if success {
                vec![active, inactive]
            } else {
                vec![inactive, active]
            },
        };
        require(
            source_reception::complete(&key, work).is_some(),
            "open Result Source exceeds its complete schema budget",
        )?;
        Ok(Some(key))
    }
    pub(super) fn input_type_sort(&self, identity: &str) -> Check<bool> {
        if self.type_binder(identity).is_ok() {
            return Ok(true);
        }
        let binder = self
            .facts
            .generic_binders
            .get(identity)
            .ok_or_else(|| "call input static sort has no genuine binder".to_owned())?;
        require(
            self.binder(binder.definition, binder.index)?.identity == identity,
            "call input static sort changed its original binder",
        )?;
        let parameter = &self.function(binder.definition)?.syntax.generics[binder.index as usize];
        if matches!(
            parameter.bound.as_ref().map(|bound| &bound.kind),
            Some(TypeKind::KeyOf(_))
        ) {
            return Ok(false);
        }
        if parameter
            .name
            .chars()
            .next()
            .is_some_and(char::is_lowercase)
            && let Some(bound) = &parameter.bound
        {
            let key = self.normalized_key(bound, &self.scope(binder.definition)?)?;
            if matches!(&key,ArgumentKey::Name {name,arguments} if arguments.is_empty()
                && matches!(name.as_str(),"bool"|"str"|"bytes"|"int"|"i8"|"i16"|"i32"|"i64"|"i128"|"isize"|"u8"|"u16"|"u32"|"u64"|"u128"|"usize"|"bigint"|"f32"|"f64"))
            {
                return Ok(false);
            }
        }
        Err("call input static position has no independently known sort".into())
    }

    pub(in crate::sema::record_bound_validation) fn parameter_has_type_source(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
    ) -> Check<bool> {
        if let TypeKind::Name { path, arguments } = &syntax.kind
            && arguments.is_empty()
            && path.len() == 1
            && let Some(identity) = scope.types.get(&path[0])
        {
            let binder = self
                .facts
                .generic_binders
                .get(identity)
                .ok_or("formal Source sort has no genuine binder")?;
            let function = self.function(binder.definition)?;
            let parameter = function
                .syntax
                .generics
                .get(binder.index as usize)
                .ok_or("formal Source binder index is outside its original declaration")?;
            require(
                self.binder(binder.definition, binder.index)?.identity == *identity,
                "formal Source sort changed its original binder",
            )?;
            if matches!(
                parameter.bound.as_ref().map(|bound| &bound.kind),
                Some(TypeKind::KeyOf(_))
            ) {
                require(
                    !self.input_type_sort(identity)?,
                    "a real Key coordinate cannot become a Type leaf",
                )?;
                return Ok(false);
            }
            require(
                self.input_type_sort(identity)?,
                "a static coordinate cannot become a formal Type Source",
            )?;
        }
        Ok(true)
    }

    pub(in crate::sema::record_bound_validation) fn input_parameter_source_key(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
    ) -> Check<Option<ArgumentKey>> {
        if !self.parameter_has_type_source(syntax, scope)? {
            return Ok(None);
        }
        self.input_callable_source_key(syntax, scope).map(Some)
    }

    pub(super) fn producing_result_contexts(
        &self,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check {
        for call in &self.facts.copy_invocations {
            let Some(returned) = &call.result else {
                continue;
            };
            if call.source_event.is_none() || returned.value.pending_inference.is_empty() {
                continue;
            }
            let context = self.input_caller_context(call)?;
            let event = call
                .source_event
                .and_then(|id| self.facts.copy_call_events.get(id.0 as usize))
                .ok_or_else(|| "producing result lost its actual source event".to_owned())?;
            let source: Vec<_> = sites
                .calls
                .iter()
                .filter(|site| {
                    Some(site.owner) == context.owner && event.matches_source(site.expression)
                })
                .collect();
            let [source] = source.as_slice() else {
                return Err("producing result has no unique actual Call AST".into());
            };
            let roots: Vec<_> = self
                .facts
                .invocation_expressions
                .iter()
                .filter_map(|observation| {
                    if observation.context != context {
                        return None;
                    }
                    let value = self.facts.expressions.get(observation.expression)?;
                    if value.source_id.is_none() || value.source_id != event.source_id {
                        return None;
                    }
                    self.producing_result_causes(value.value.cause)
                        .ok()
                        .filter(|causes| causes.contains(&returned.value.cause.0))
                        .map(|_| (observation.expression, &value.value))
                })
                .collect();
            let [(observation, actual)] = roots.as_slice() else {
                return Err("producing result lost its unique root Source observation".into());
            };
            self.validate_producing_result_transport(call, actual)?;
            let original_key =
                self.original_observed_source_key(source.expression, *observation, context, sites)?;
            if !self.producing_type_selections(call, actual)?.is_empty() {
                let expected =
                    self.producing_receiver_key(source.expression, actual, context, sites)?;
                require(
                    source_reception::compatible(&expected, &original_key, None, &mut 4096)
                        == Some(true),
                    "producing Type selection does not fit its actual Source receiver",
                )?;
            }
        }
        Ok(())
    }

    fn producing_receiver_key(
        &self,
        expression: &Expr,
        actual: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check<ArgumentKey> {
        let scope = match context.owner {
            Some(CallableOwner::Function(owner)) => self.scope(owner)?,
            Some(CallableOwner::Global) => BoundScope::default(),
            _ => return Err("producing context needs its actual lexical Source scope".into()),
        };
        let selected = context
            .invocation
            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
            .map(|call| self.input_selected_keys(call))
            .transpose()?
            .unwrap_or_default();
        let mut receivers = Vec::new();
        for site in &sites.bindings {
            if Some(site.owner) != context.owner {
                continue;
            }
            if !receiving_contains(&site.binding.value, expression, &mut 4096) {
                continue;
            }
            let Some(syntax) = &site.binding.ty else {
                continue;
            };
            let key = input_select_key(
                &self.input_callable_source_key(syntax, &scope)?,
                &selected,
                0,
            )?;
            if let Some(key) = receiving_path(
                self,
                context,
                &site.binding.value,
                expression,
                &key,
                &mut 4096,
            ) {
                receivers.push(key);
            }
        }
        for site in &sites.calls {
            if Some(site.owner) != context.owner {
                continue;
            }
            let application = AstApplication::from_ast(site.expression)
                .ok_or_else(|| "producing receiver has no original application".to_owned())?;
            let callee = application.callee;
            let arguments = &application.operands;
            if !arguments
                .iter()
                .any(|argument| receiving_contains(argument.expression, expression, &mut 4096))
            {
                continue;
            }
            for event in &self.facts.copy_call_events {
                if !event.matches_source(site.expression)
                    || event.owner != context.owner
                    || event.parent != context.invocation
                {
                    continue;
                }
                let Some(token) = event.callee_expression else {
                    continue;
                };
                let Some(fact) = self.facts.expressions.get(token) else {
                    continue;
                };
                if !self
                    .observations
                    .row(token, &mut 4096)
                    .is_ok_and(|row| row.context == context)
                {
                    continue;
                }
                let Some(preparation) = self
                    .facts
                    .call_arguments
                    .iter()
                    .find(|row| row.source_event == event.id)
                else {
                    continue;
                };
                let Ok(ArgumentKey::Callable { parameters, .. }) =
                    self.original_observed_source_key(callee, token, context, sites)
                else {
                    continue;
                };
                let mut occupied = BTreeSet::new();
                for argument in arguments {
                    let slot=match argument.label {
                        None=>(0..parameters.len()).find(|slot| !occupied.contains(slot)),
                        Some(label)=>fact.value.signature.as_ref().and_then(|parameters|parameters.iter().position(|parameter|
                            matches!(&parameter.pattern.kind,ril_syntax::ast::PatternKind::Name(name) if name.as_str()==label))),
                    };
                    let Some(slot) = slot else { continue };
                    if !occupied.insert(slot) {
                        continue;
                    }
                    if !receiving_contains(argument.expression, expression, &mut 4096) {
                        continue;
                    }
                    let Some(token) = preparation.supplied.get(&(slot as u32)) else {
                        continue;
                    };
                    let Some(value) = self.facts.expressions.get(token.expression) else {
                        continue;
                    };
                    if !std::ptr::eq(&value.value, actual) {
                        continue;
                    }
                    self.input_operand_interval(event, slot, token.expression, context, sites)?;
                    if let Some((_, key)) = parameters.get(slot)
                        && let Some(key) = receiving_path(
                            self,
                            context,
                            argument.expression,
                            expression,
                            key,
                            &mut 4096,
                        )
                    {
                        receivers.push(key);
                    }
                }
            }
        }
        if let Some(CallableOwner::Function(owner)) = context.owner {
            let declaration = self.function(owner)?;
            let functions: Vec<_> = sites
                .functions
                .iter()
                .filter(|site| {
                    site.owner == CallableOwner::Function(owner)
                        && *site.function == declaration.syntax
                })
                .collect();
            let [function] = functions.as_slice() else {
                return Err("producing result has no unique original function header".into());
            };
            let function = function.function;
            if let (Some(syntax), Some(body)) = (&function.return_type, &function.body)
                && let Some(Stmt {
                    kind:
                        StmtKind::Expr {
                            expression: tail, ..
                        },
                    ..
                }) = body.statements.last()
            {
                let key = input_select_key(
                    &self.input_callable_source_key(syntax, &scope)?,
                    &selected,
                    0,
                )?;
                if let Some(key) = receiving_path(self, context, tail, expression, &key, &mut 4096)
                {
                    receivers.push(key);
                }
            }
        }
        let [expected] = receivers.as_slice() else {
            return Err("producing context has no unique actual Source receiver".into());
        };
        Ok(expected.clone())
    }

    pub(in crate::sema::record_bound_validation) fn input_callable_source_key(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
    ) -> Check<ArgumentKey> {
        crate::static_eval::effects::bounded_argument_key(syntax, &self.key_scope(scope)?)
            .ok_or_else(|| "public callable Source exceeds its reconstruction budget".to_owned())?;
        self.input_callable_source_key_inner(syntax, scope, &mut 4096, 0)
    }

    fn input_callable_source_key_inner(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
        work: &mut usize,
        depth: usize,
    ) -> Check<ArgumentKey> {
        *work = work
            .checked_sub(1)
            .ok_or("public Source projection exceeds its work budget")?;
        require(
            depth < 64,
            "public Source projection exceeds its depth budget",
        )?;
        let mut child = |syntax: &TypeExpr| {
            self.input_callable_source_key_inner(syntax, scope, work, depth + 1)
        };
        match &syntax.kind {
            TypeKind::Record { fields, row } => {
                let mut fields = fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), field.mutable, child(&field.ty)?)))
                    .collect::<Check<Vec<_>>>()?;
                fields.sort_by(|left, right| left.0.cmp(&right.0));
                require(
                    fields.windows(2).all(|pair| pair[0].0 != pair[1].0),
                    "public Source record repeats a label",
                )?;
                return Ok(ArgumentKey::Record {
                    fields,
                    row: row
                        .as_ref()
                        .map(|row| child(row).map(Box::new))
                        .transpose()?,
                });
            }
            TypeKind::Tuple(items) => {
                return Ok(ArgumentKey::Tuple(
                    items.iter().map(&mut child).collect::<Check<_>>()?,
                ));
            }
            TypeKind::Map { key, value } => {
                return Ok(ArgumentKey::Map {
                    key: Box::new(child(key)?),
                    value: Box::new(child(value)?),
                });
            }
            TypeKind::Optional(inner) => {
                return Ok(ArgumentKey::Name {
                    name: "Option".into(),
                    arguments: vec![child(inner)?],
                });
            }
            TypeKind::Array { element, length } => {
                let mut shell = syntax.clone();
                let TypeKind::Array {
                    element: shell_element,
                    ..
                } = &mut shell.kind
                else {
                    unreachable!()
                };
                **shell_element = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Tuple(vec![]),
                };
                let key = self.normalized_key(&shell, scope)?;
                let ArgumentKey::Array {
                    length: normalized, ..
                } = key
                else {
                    return Err("public Source array has no declared dimension".into());
                };
                require(
                    length.is_some() == normalized.is_some(),
                    "public Source array changed its dimension kind",
                )?;
                return Ok(ArgumentKey::Array {
                    length: normalized,
                    element: Box::new(child(element)?),
                });
            }
            _ => {}
        }
        let TypeKind::Callable {
            parameters,
            result,
            annotations,
        } = &syntax.kind
        else {
            return self.normalized_key(syntax, scope).or_else(|original| {
                let raw = crate::static_eval::effects::bounded_argument_key(
                    syntax,
                    &self.key_scope(scope)?,
                )
                .ok_or_else(|| original.clone())?;
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or_else(|| original.clone())?;
                let mut limit = crate::sema::source_types::WorkLimit::new(*work);
                let expanded =
                    crate::sema::source_types::declarations::expanded_key(&raw, hir, &mut limit)
                        .map_err(|_| original.clone())?;
                *work = limit.remaining();
                require(expanded != raw, &original)?;
                Ok(expanded)
            });
        };
        require(
            parameters
                .iter()
                .all(|parameter| parameter.default.is_none()),
            "public callable Type coordinates cannot manufacture a default interface",
        )?;
        Ok(ArgumentKey::Callable {
            parameters: parameters
                .iter()
                .map(|parameter| {
                    Ok((
                        parameter.mode,
                        self.input_callable_source_key_inner(
                            parameter.ty.as_ref().ok_or_else(|| {
                                "public callable input has no written Source type".to_owned()
                            })?,
                            scope,
                            work,
                            depth + 1,
                        )?,
                    ))
                })
                .collect::<Check<_>>()?,
            result: Box::new(match result {
                Some(result) => {
                    self.input_callable_source_key_inner(result, scope, work, depth + 1)?
                }
                None => ArgumentKey::Tuple(vec![]),
            }),
            // These bytes are coordinates of the already anchored real header.
            // They are not a closed/static proof of state or effect authority.
            annotations: annotations
                .iter()
                .map(|annotation| annotation.text.replace(' ', ""))
                .collect(),
        })
    }

    pub(super) fn public_input_source_keys(
        &self,
        syntax: &Expr,
        callee: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        observation: Option<usize>,
    ) -> Check<Vec<Option<ArgumentKey>>> {
        let public = observation.map_or_else(
            || self.original_source_key(syntax, callee, context, sites),
            |index| self.original_observed_source_key(syntax, index, context, sites),
        );
        if let Ok(ArgumentKey::Callable { parameters, .. }) = public {
            return Ok(parameters.into_iter().map(|(_, key)| Some(key)).collect());
        }
        require(
            !callee.callables.is_empty(),
            "public input has no actual callable target",
        )?;
        let mut common = None;
        for callable in &callee.callables {
            let keys =
                match callable {
                    crate::sema::model::Callable::Closure(index) => {
                        let closure =
                            self.facts.closures.get(*index).ok_or_else(|| {
                                "public input closure target is absent".to_owned()
                            })?;
                        let site = self
                            .facts
                            .closure_sites
                            .iter()
                            .find(|site| Some(site.id) == closure.site)
                            .ok_or_else(|| {
                                "public input closure has no genuine lexical site".to_owned()
                            })?;
                        let headers: Vec<_> = sites
                            .lambdas
                            .iter()
                            .filter(|header| {
                                header.owner == site.owner
                                    && closure.hir_id.is_some()
                                    && header.expression.hir_id == closure.hir_id
                            })
                            .collect();
                        let [header] = headers.as_slice() else {
                            return Err("public input lambda header is not unique".into());
                        };
                        let ExprKind::Lambda { parameters, .. } = &header.expression.kind else {
                            unreachable!()
                        };
                        let scope = self.lambda_input_scope(site.owner)?;
                        let selected = match closure.creation_invocation {
                            Some(id) => self.input_selected_keys(
                                self.facts.copy_invocations.get(id.0 as usize).ok_or_else(
                                    || "public lambda creation instance is absent".to_owned(),
                                )?,
                            )?,
                            None => BTreeMap::new(),
                        };
                        parameters
                            .iter()
                            .map(|parameter| match &parameter.ty {
                                None => Ok(None),
                                Some(syntax) => {
                                    let key = self.input_callable_source_key(syntax, &scope)?;
                                    let key = input_select_key(&key, &selected, 0)?;
                                    Ok((source_reception::sensitive(&key, &mut 4096)
                                        != Some(false))
                                    .then_some(key))
                                }
                            })
                            .collect::<Check<Vec<_>>>()?
                    }
                    crate::sema::model::Callable::Symbolic(..)
                        if self.symbolic_source_has_no_inputs(callee) =>
                    {
                        Vec::new()
                    }
                    _ => return Err("public input target has no complete Source parameters".into()),
                };
            require(
                common.as_ref().is_none_or(|previous| previous == &keys),
                "public input alternatives disagree about their Source parameter coordinates",
            )?;
            common = Some(keys);
        }
        common.ok_or_else(|| "public input has no Source parameter proof".into())
    }

    fn symbolic_source_has_no_inputs(&self, callee: &Value) -> bool {
        let sources: BTreeSet<_> = callee
            .callback_parameters
            .union(&callee.sources)
            .copied()
            .collect();
        !sources.is_empty()
            && sources.iter().all(|id| {
                let Some(binding) = self.facts.bindings.get(*id) else {
                    return false;
                };
                if !binding.parameter {
                    return false;
                }
                let headers: Vec<_> = self
                    .facts
                    .functions
                    .iter()
                    .filter(|function| {
                        binding.context.owner == Some(CallableOwner::Function(function.definition))
                    })
                    .flat_map(|function| function.syntax.parameters.iter())
                    .filter(|parameter| {
                        parameter.pattern.hir_id.is_some()
                            && parameter.pattern.hir_id == binding.pattern
                    })
                    .collect();
                let [parameter] = headers.as_slice() else {
                    return false;
                };
                let Some(mut syntax) = parameter.ty.as_ref() else {
                    return false;
                };
                if let TypeKind::Optional(inner) = &syntax.kind {
                    syntax = inner;
                }
                matches!(&syntax.kind,TypeKind::Callable {parameters,..} if parameters.is_empty())
            })
    }

    pub(in crate::sema::record_bound_validation) fn lambda_input_scope(
        &self,
        mut owner: CallableOwner,
    ) -> Check<BoundScope> {
        let mut seen = BTreeSet::new();
        loop {
            require(
                seen.len() < 256 && seen.insert(owner),
                "public lambda lexical Source ancestry is cyclic or too deep",
            )?;
            match owner {
                CallableOwner::Function(definition) => return self.scope(definition),
                CallableOwner::Global => return Ok(BoundScope::default()),
                CallableOwner::Lambda(id) => {
                    let sites: Vec<_> = self
                        .facts
                        .closure_sites
                        .iter()
                        .filter(|site| site.id == id)
                        .collect();
                    let [site] = sites.as_slice() else {
                        return Err("public lambda ancestor is not unique".into());
                    };
                    owner = site.owner;
                }
            }
        }
    }

    fn carrier_payload_key(
        &self,
        root: &Expr,
        key: &ArgumentKey,
        context: InvocationContext,
    ) -> Option<ArgumentKey> {
        let application = AstApplication::from_ast(root)?;
        let callee = application.callee;
        let arguments = &application.operands;
        if arguments.len() != 1
            || arguments[0].label.is_some()
            || arguments[0].mode != ril_syntax::ast::ParameterMode::Read
        {
            return None;
        }
        let identity = match &callee.kind {
            ExprKind::Name(name) => name.as_str(),
            ExprKind::Path(path) if path.len() == 2 && path[0] == "Prelude" => path[1].as_str(),
            _ => return None,
        };
        let index = match (identity, key) {
            ("Some", ArgumentKey::Name { name, arguments })
                if name == "Option" && arguments.len() == 1 =>
            {
                0
            }
            ("Ok", ArgumentKey::Name { name, arguments })
                if name == "Result" && arguments.len() == 2 =>
            {
                0
            }
            ("Err", ArgumentKey::Name { name, arguments })
                if name == "Result" && arguments.len() == 2 =>
            {
                1
            }
            _ => return None,
        };
        super::super::super::checker::actual_prelude_name(self.facts, context, callee, identity)
            .ok()?;
        let matches=self.facts.copy_call_events.iter().filter(|event| {
            if event.owner!=context.owner||event.parent!=context.invocation||!event.matches_source(root) {return false;}
            let Some(token)=event.callee_expression else {return false};
            let Some(fact)=self.facts.expressions.get(token) else {return false};
            fact.source_id.is_some()&&fact.source_id==callee.hir_id&&fact.value.sources.is_empty()
                && matches!(fact.value.callables.as_slice(),[crate::sema::model::Callable::Builtin(name)]
                    if name.strip_prefix("Prelude::").unwrap_or(name)==identity)
                && self.observations.row(token, &mut 4096).is_ok_and(|row|row.context==context)
                && self.facts.call_arguments.iter().filter(|row|row.source_event==event.id
                    &&row.target.is_none()&&row.evaluation_complete&&row.slots==[crate::sema::default_uses::ArgumentSource::Supplied]
                    &&row.supplied.len()==1&&row.supplied.get(&0).is_some_and(|token|
                        self.observations.row(token.expression, &mut 4096).is_ok_and(|row|
                            row.context==context&&row.argument_of==Some((event.id,0)))
                        &&self.facts.expressions.get(token.expression).is_some_and(|fact| {
                            if fact.source_id.is_none()||fact.source_id!=arguments[0].expression.hir_id {return false;}
                            self.facts.invocation_expressions.iter().any(|row| {
                                if row.context!=context||row.expression<=token.expression {return false;}
                                let Some(result)=self.facts.expressions.get(row.expression) else {return false};
                                if result.source_id.is_none()||result.source_id!=root.hir_id {return false;}
                                let Some(cause)=self.facts.explanations.causes.get(result.value.cause.0 as usize) else {return false};
                                if !cause.parents.contains(&fact.value.cause) {return false;}
                                let tagged=match identity {"Some"=>result.value.option_tag==Some(true),
                                    "Ok"=>result.value.result_tag==Some(true),"Err"=>result.value.result_tag==Some(false),_=>false};
                                let Some(witness)=result.value.source_type_witness.as_ref().filter(|witness|witness.validate_closed()) else {return false};
                                let Some(actual)=crate::static_eval::effects::bounded_argument_key(&witness.syntax,&BTreeMap::new()) else {return false};
                                tagged&&source_reception::compatible(key,&actual,None,&mut 4096)==Some(true)
                            })
                        }))).count()==1
        }).count();
        if matches == 0 {
            return None;
        }
        let ArgumentKey::Name { arguments, .. } = key else {
            unreachable!()
        };
        Some(arguments[index].clone())
    }

    pub(super) fn producing_result_causes(&self, root: CauseId) -> Check<BTreeSet<u32>> {
        let mut seen = BTreeSet::new();
        let mut pending = vec![root];
        let mut work = 4096usize;
        while let Some(id) = pending.pop() {
            work = work
                .checked_sub(1)
                .ok_or_else(|| "producing result cause budget exhausted".to_owned())?;
            let cause = self
                .facts
                .explanations
                .causes
                .get(id.0 as usize)
                .ok_or_else(|| "producing result has an absent cause".to_owned())?;
            if seen.insert(id.0) {
                pending.extend(cause.parents.iter().copied());
            }
        }
        Ok(seen)
    }

    pub(super) fn producing_input_selected_keys(
        &self,
        call: &CopyInvocation,
        actual: &Value,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let mut keys = self.input_selected_keys(call)?;
        let selections = self.producing_type_selections(call, actual)?;
        for (binder, selected) in selections {
            let key = match selected {
                Ty::Generic(identity) => {
                    self.type_binder(&identity)?;
                    ArgumentKey::Binder {
                        identity,
                        sort: StaticBinderSort::Type,
                    }
                }
                Ty::Unit => ArgumentKey::Tuple(vec![]),
                Ty::Bool => ArgumentKey::Name {
                    name: "bool".into(),
                    arguments: vec![],
                },
                Ty::Str => ArgumentKey::Name {
                    name: "str".into(),
                    arguments: vec![],
                },
                Ty::Bytes => ArgumentKey::Name {
                    name: "bytes".into(),
                    arguments: vec![],
                },
                Ty::Int(name) | Ty::Float(name) => ArgumentKey::Name {
                    name,
                    arguments: vec![],
                },
                _ => {
                    return Err(
                        "producing result Type leaf lacks a complete Source selection".into(),
                    );
                }
            };
            let declaration = binder
                .rsplit_once(":invocation:")
                .ok_or_else(|| "producing result meta lacks its genuine activation".to_owned())?
                .0;
            if matches!(keys.get(declaration), Some(ArgumentKey::Binder {identity,..}) if identity == declaration)
            {
                keys.insert(declaration.to_owned(), key);
            }
        }
        Ok(keys)
    }

    fn producing_type_selections(
        &self,
        call: &CopyInvocation,
        actual: &Value,
    ) -> Check<BTreeMap<String, Ty>> {
        let returned = &call
            .result
            .as_ref()
            .ok_or_else(|| "producing result snapshot is absent".to_owned())?
            .value;
        let before = self.producing_result_causes(returned.cause)?;
        let after = self.producing_result_causes(actual.cause)?;
        require(
            after.contains(&returned.cause.0),
            "producing result borrowed another instance's cause",
        )?;
        let summaries: Vec<_> = self
            .facts
            .invocations
            .iter()
            .filter(|summary| {
                summary.context.is_some_and(|context| {
                    context.invocation == Some(call.id)
                        && context.owner == Some(CallableOwner::Function(call.target))
                })
            })
            .collect();
        let [summary] = summaries.as_slice() else {
            return Ok(BTreeMap::new());
        };
        let activation = summary
            .activation
            .ok_or_else(|| "producing result lacks its actual activation".to_owned())?;
        let mut selected = BTreeMap::new();
        for row in &self.facts.inference_resolutions {
            if !after.contains(&row.cause.0) || !after.contains(&row.origin.0) {
                continue;
            }
            let Some((binder, scope)) = row.binder.rsplit_once(":invocation:") else {
                continue;
            };
            if scope != activation.0.to_string() {
                continue;
            }
            let declared =
                self.facts.generic_binders.get(binder).ok_or_else(|| {
                    "producing result meta has no original declared Type".to_owned()
                })?;
            require(
                declared.definition == call.target,
                "producing result borrowed another declaration's meta",
            )?;
            self.type_binder(binder)?;
            require(
                self.facts
                    .inference_resolutions
                    .iter()
                    .filter(|initial| {
                        initial.binder == binder
                            && initial.selected == Ty::Generic(row.binder.clone())
                            && before.contains(&initial.cause.0)
                    })
                    .count()
                    == 1,
                "producing result lacks its original owned-meta substitution",
            )?;
            if let Some(previous) = selected.insert(row.binder.clone(), row.selected.clone()) {
                require(
                    previous == row.selected,
                    "producing result meta has inconsistent contexts",
                )?;
            }
        }
        Ok(selected)
    }

    pub(super) fn validate_producing_result_transport(
        &self,
        call: &CopyInvocation,
        actual: &Value,
    ) -> Check {
        let original = &call
            .result
            .as_ref()
            .ok_or_else(|| "producing result snapshot is absent".to_owned())?
            .value;
        let selected = self.producing_type_selections(call, actual)?;
        require(
            type_transport(&original.ty, &actual.ty, &selected, &mut 4096),
            "producing result changed an already selected type coordinate",
        )?;
        require(
            original.permission == actual.permission
                && original.publication == actual.publication
                && original.callables == actual.callables
                && original.participants == actual.participants,
            "producing result Type inference changed permission or callable identity",
        )?;
        let mut copy = original.clone();
        copy.cause = actual.cause;
        // The source key above comes from the actual return declaration. No
        // selected shell/dimension is taken from this contextual descriptor.
        copy.source_type_witness = actual.source_type_witness.clone();
        self.input_value_transport(&copy, actual, 0, 0)
    }
}

fn receiving_path(
    replay: &Replay<'_>,
    context: InvocationContext,
    root: &Expr,
    target: &Expr,
    key: &ArgumentKey,
    work: &mut usize,
) -> Option<ArgumentKey> {
    *work = work.checked_sub(1)?;
    if std::ptr::eq(root, target) {
        return Some(key.clone());
    }
    if let Some(application) = AstApplication::from_ast(root) {
        if application.operands.len() != 1 {
            return None;
        }
        let payload = replay.carrier_payload_key(root, key, context)?;
        return receiving_path(
            replay,
            context,
            application.operands[0].expression,
            target,
            &payload,
            work,
        );
    }
    match (&root.kind, key) {
        (ExprKind::Tuple(items), ArgumentKey::Tuple(keys)) if items.len() == keys.len() => items
            .iter()
            .zip(keys)
            .find_map(|(item, key)| receiving_path(replay, context, item, target, key, work)),
        (ExprKind::Array(items), ArgumentKey::Array { element, .. }) => items
            .iter()
            .find_map(|item| receiving_path(replay, context, item, target, element, work)),
        (
            ExprKind::Control {
                operation: ril_syntax::ast::ControlOperation::Return,
                value: Some(value),
            },
            _,
        ) => receiving_path(replay, context, value, target, key, work),
        _ => None,
    }
}

fn receiving_contains(root: &Expr, target: &Expr, work: &mut usize) -> bool {
    let Some(next) = work.checked_sub(1) else {
        return false;
    };
    *work = next;
    if std::ptr::eq(root, target) {
        return true;
    }
    if let Some(application) = AstApplication::from_ast(root) {
        return application
            .operands
            .iter()
            .any(|operand| receiving_contains(operand.expression, target, work));
    }
    match &root.kind {
        ExprKind::Tuple(items) | ExprKind::Array(items) => items
            .iter()
            .any(|item| receiving_contains(item, target, work)),
        ExprKind::Control {
            operation: ril_syntax::ast::ControlOperation::Return,
            value: Some(value),
        } => receiving_contains(value, target, work),
        _ => false,
    }
}

fn type_transport(
    original: &Ty,
    actual: &Ty,
    selected: &BTreeMap<String, Ty>,
    work: &mut usize,
) -> bool {
    let Some(next) = work.checked_sub(1) else {
        return false;
    };
    *work = next;
    if original == actual {
        return true;
    }
    if let Ty::Generic(identity) = original {
        return selected.get(identity) == Some(actual);
    }
    match (original, actual) {
        (Ty::Array(a), Ty::Array(b))
        | (Ty::Optional(a), Ty::Optional(b))
        | (Ty::Immutable(a), Ty::Immutable(b))
        | (Ty::Set(a), Ty::Set(b))
        | (Ty::Range(a), Ty::Range(b)) => type_transport(a, b, selected, work),
        (Ty::Result(a, b), Ty::Result(c, d)) | (Ty::Map(a, b), Ty::Map(c, d)) => {
            type_transport(a, c, selected, work) && type_transport(b, d, selected, work)
        }
        (Ty::Tuple(a), Ty::Tuple(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b)
                    .all(|(a, b)| type_transport(a, b, selected, work))
        }
        (Ty::Record(a), Ty::Record(b)) => {
            a.len() == b.len()
                && a.iter().all(|(label, (mode, a))| {
                    b.get(label).is_some_and(|(other, b)| {
                        mode == other && type_transport(a, b, selected, work)
                    })
                })
        }
        _ => false,
    }
}
