//! Rebuild lambda types from real lexical headers and completed body entries.
//! Neither a private cache nor Ty::Callable supplies a missing source schema.
use super::*;
use crate::sema::facts::ScopeId;
use crate::sema::model::Callable;

impl Replay<'_> {
    /// Preparation formals belong to the scope that evaluated the actual
    /// default root. A captured read keeps that declaration scope even though
    /// its current owner is a lambda or handler. An enclosing default does not
    /// turn an ordinary nested function activation into a preparation scope.
    pub(super) fn parameter_preparation(
        &self,
        binding: &crate::sema::model::BindingInfo,
        reading: InvocationContext,
        work: &mut usize,
    ) -> Check<Option<&crate::sema::default_uses::DefaultUse>> {
        let current = reading
            .default_use
            .and_then(|id| self.facts.default_uses.get(id.0 as usize))
            .filter(|receipt| {
                receipt
                    .result_expression
                    .and_then(|index| self.facts.evaluations.get(index))
                    .is_some_and(|root| root.scope == binding.owner)
            });
        let receipt = current.or_else(|| {
            self.frames
                .preparations(binding.owner)
                .iter()
                .copied()
                .find(|receipt| {
                    binding.context
                        == InvocationContext {
                            owner: receipt.owner,
                            ..receipt.caller
                        }
                })
        });
        let Some(receipt) = receipt else {
            return Ok(None);
        };
        let declaration = self.preparation_scope(receipt, binding.owner, work)?;
        require(
            binding.context == declaration,
            "formal Source preparation changed its declaration context",
        )?;
        Ok(Some(receipt))
    }

    pub(in crate::sema::record_bound_validation) fn preparation_scope(
        &self,
        receipt: &crate::sema::default_uses::DefaultUse,
        scope: ScopeId,
        work: &mut usize,
    ) -> Check<InvocationContext> {
        source_scan_work(work, 8)?;
        let id = receipt.id;
        let token = receipt
            .result_expression
            .ok_or_else(|| "formal Source preparation root is absent".to_owned())?;
        let root = self
            .facts
            .evaluations
            .get(token)
            .ok_or_else(|| "formal Source preparation root has no actual scope".to_owned())?;
        let declaration = InvocationContext {
            owner: receipt.owner,
            ..receipt.caller
        };
        let context = InvocationContext {
            default_use: Some(id),
            ..declaration
        };
        require(
            root.scope == scope
                && root.id.0 as usize == token
                && root.context == context
                && self
                    .observations
                    .row(token, work)
                    .is_ok_and(|row| row.expression == token && row.context == context)
                && !matches!(
                    receipt.status,
                    CopyInvocationStatus::Rejected | CopyInvocationStatus::Unsupported
                ),
            "formal Source preparation changed its declaration or root context",
        )?;
        let source = match receipt.owner {
            Some(CallableOwner::Function(owner)) => {
                require(
                    receipt.target == Some(owner),
                    "formal preparation changed its named header",
                )?;
                self.function(owner)?
                    .syntax
                    .parameters
                    .get(receipt.parameter as usize)
                    .and_then(|parameter| parameter.default.as_ref())
                    .and_then(|default| default.hir_id)
            }
            Some(CallableOwner::Lambda(site)) => {
                require(
                    receipt.target.is_none(),
                    "lambda preparation borrowed a named target",
                )?;
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or_else(|| "formal preparation has no original HIR".to_owned())?;
                self.facts
                    .closure_sites
                    .get(site.0 as usize)
                    .filter(|actual| actual.id == site)
                    .and_then(|site| hir.expression(site.source))
                    .and_then(|expression| match &expression.kind {
                        crate::hir::nodes::ExprKind::Lambda { parameters, .. } => {
                            parameters.get(receipt.parameter as usize)?.default
                        }
                        _ => None,
                    })
            }
            _ => None,
        };
        require(
            source.is_some()
                && root
                    .identity
                    .is_some_and(|identity| Some(identity.source) == source)
                && self
                    .facts
                    .expressions
                    .get(token)
                    .is_some_and(|fact| fact.source_id == source),
            "formal preparation root differs from its original default HIR",
        )?;
        Ok(declaration)
    }

    /// A read uses its binding's declaration activation. Captures must be
    /// grounded in the actual reading environment, never inferred from an
    /// equal name or the invocation which happens to be on top of the stack.
    pub(in crate::sema::record_bound_validation) fn parameter_declaration_context(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: Option<usize>,
        work: &mut usize,
    ) -> Check<InvocationContext> {
        let binding_id = *value
            .sources
            .first()
            .ok_or_else(|| "formal Source has no binding".to_owned())?;
        let binding = self
            .facts
            .bindings
            .get(binding_id)
            .ok_or_else(|| "formal Source binding is absent".to_owned())?;
        let pattern = binding
            .pattern
            .ok_or_else(|| "formal Source lost its HIR declaration".to_owned())?;
        require(
            self.facts.semantic_hir.as_deref().and_then(|hir| hir.pattern(pattern))
                .is_some_and(|pattern| matches!(&pattern.kind,crate::hir::nodes::PatternKind::Name(name) if name == &binding.name)),
            "formal Source declaration is not its actual HIR Name pattern",
        )?;
        let index = self.original_source_root(expression, value, context, observation, work)?;
        let read = self
            .facts
            .evaluations
            .get(index)
            .ok_or_else(|| "formal Source read has no actual scope".to_owned())?;
        let declaration = binding.context;
        let operation = self.frames.operation(binding.owner, work)?;
        if let Some(operation) = &operation {
            require(
                binding.context == operation.entry.context
                    && operation
                        .arm
                        .parameters
                        .iter()
                        .any(|parameter| parameter.pattern.hir_id == Some(pattern)),
                "operation formal Source borrowed another parameter receiver",
            )?;
        }
        if operation.is_none()
            && self
                .parameter_preparation(binding, context, work)?
                .is_none()
        {
            match declaration.owner {
                Some(CallableOwner::Function(owner)) => require(
                    self.facts
                        .invocations
                        .iter()
                        .filter(|summary| {
                            summary.activation == Some(binding.owner)
                                && summary.context == Some(declaration)
                        })
                        .count()
                        == 1
                        && declaration
                            .invocation
                            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                            .is_some_and(|call| {
                                Some(call.id) == declaration.invocation
                                    && call.target == owner
                                    && call.status == CopyInvocationStatus::Completed
                            }),
                    "formal Source declaration borrowed another named activation",
                )?,
                Some(CallableOwner::Lambda(site)) => require(
                    declaration
                        .closure_invocation
                        .and_then(|id| self.facts.closure_invocations.get(id.0 as usize))
                        .is_some_and(|call| {
                            Some(call.id) == declaration.closure_invocation
                                && call.activation == Some(binding.owner)
                                && Some(call.closure) == declaration.closure
                                && call.status == CopyInvocationStatus::Completed
                                && self
                                    .facts
                                    .closures
                                    .get(call.closure)
                                    .is_some_and(|closure| closure.site == Some(site))
                        }),
                    "formal Source declaration borrowed another lambda activation",
                )?,
                _ => return Err("formal Source declaration has no callable activation".into()),
            }
        }
        if read.scope == binding.owner && (context == declaration || context.default_use.is_some())
        {
            return Ok(declaration);
        }
        if let Some(handler) = self.storage_handler(context, read.scope, work)? {
            require(
                handler.lexical.get(&binding.name) == Some(&binding_id),
                "formal Source read is absent from its actual handler capture",
            )?;
            return Ok(declaration);
        }
        if matches!(context.owner, Some(CallableOwner::Lambda(_)))
            && let Some(id) = context.closure_invocation
        {
            let call = self
                .facts
                .closure_invocations
                .get(id.0 as usize)
                .filter(|call| call.id == id && call.activation == Some(read.scope))
                .ok_or_else(|| {
                    "captured formal Source has no actual reading lambda activation".to_owned()
                })?;
            let closure = self
                .facts
                .closures
                .get(call.closure)
                .ok_or_else(|| "captured formal Source reading lambda is absent".to_owned())?;
            require(
                closure.lexical.get(&binding.name) == Some(&binding_id)
                    && closure.captures.contains(&binding_id),
                "formal Source borrowed an uncaptured binding from another environment",
            )?;
            return Ok(declaration);
        }
        let environments = self.storage_named_environments(context)?;
        require(
            self.facts.invocations.iter().any(|summary| {
                summary.activation == Some(read.scope) && summary.context == Some(context)
            }) && environments.iter().all(|function| {
                function.lexical.get(&binding.name) == Some(&binding_id)
                    && function.captures.contains(&binding_id)
            }),
            "formal Source read is absent from its actual named capture",
        )?;
        Ok(declaration)
    }

    pub(super) fn operation_formal_source_key(
        &self,
        binding: &crate::sema::model::BindingInfo,
        work: &mut usize,
    ) -> Check<Option<ArgumentKey>> {
        let Some(frame) = self.frames.operation(binding.owner, work)? else {
            return Ok(None);
        };
        let slots: Vec<_> = frame
            .arm
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, parameter)| {
                parameter.pattern.hir_id.is_some() && parameter.pattern.hir_id == binding.pattern
            })
            .collect();
        let [(slot, _)] = slots.as_slice() else {
            return Err("operation formal Source has no unique original parameter".into());
        };
        let source = frame
            .operation
            .source
            .as_ref()
            .ok_or("operation parameter has no original declaration")?;
        require(
            binding.typing_environment.id() == source.environment.id()
                && self.facts.source_types.binding_environment(
                    *binding
                        .value
                        .sources
                        .first()
                        .ok_or("operation parameter lost its root")?,
                ) == Some(source.environment.id()),
            "operation formal Source borrowed another declaration environment",
        )?;
        let signature = self.frames.receiver_signature(&frame, work)?;
        let ArgumentKey::Callable { parameters, .. } = signature.declared else {
            return Err("operation parameter has no callable Source signature".into());
        };
        let key = &parameters
            .get(*slot)
            .ok_or("operation parameter is outside its Source signature")?
            .1;
        crate::sema::clone_work::key(work, key, 0)
            .ok_or("operation parameter Source clone exceeds its shared work bound")?;
        Ok(Some(key.clone()))
    }

    pub(super) fn lambda_formal_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<ArgumentKey> {
        self.lambda_formal_source_schema(expression, value, context, sites, work, visit)?
            .0
            .key()
            .map_err(|error| format!("legacy lambda formal Source export: {error}"))
    }

    pub(in crate::sema::record_bound_validation) fn lambda_formal_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<OriginalSource> {
        let ExprKind::Name(name) = &expression.kind else {
            return Err("lambda formal Source is not a real Name".into());
        };
        require(
            value.sources.len() == 1,
            "lambda formal Source has ambiguous binding roots",
        )?;
        let binding = self
            .facts
            .bindings
            .get(*value.sources.first().unwrap())
            .ok_or_else(|| "lambda formal Source binding is absent".to_owned())?;
        let reading = context;
        let context = binding.context;
        if let Some(default) = self.parameter_preparation(binding, reading, work)? {
            let Some(CallableOwner::Lambda(site)) = context.owner else {
                return Err("lambda preparation has no original callable site".into());
            };
            let site = self
                .facts
                .closure_sites
                .get(site.0 as usize)
                .filter(|actual| actual.id == site)
                .ok_or("lambda preparation lost its original site")?;
            source_scan_work(work, sites.lambdas.len())?;
            let mut headers = sites.lambdas.iter().filter(|header| {
                header.owner == site.owner && header.expression.hir_id == Some(site.source)
            });
            let header = headers
                .next()
                .ok_or("lambda preparation has no original header")?;
            require(
                headers.next().is_none(),
                "lambda preparation header is ambiguous",
            )?;
            let ExprKind::Lambda { parameters, .. } = &header.expression.kind else {
                return Err("lambda preparation header is not callable".into());
            };
            source_scan_work(work, parameters.len())?;
            let mut formals = parameters.iter().enumerate().filter(|(_, parameter)| {
                parameter.pattern.hir_id == binding.pattern && binding.pattern.is_some()
            });
            let (slot, parameter) = formals.next().ok_or("lambda preparation lost its formal")?;
            require(
                formals.next().is_none()
                    && slot < default.parameter as usize
                    && binding.parameter
                    && binding.name == *name,
                "lambda preparation borrowed a later or unrelated formal",
            )?;
            let annotation = parameter
                .ty
                .as_ref()
                .ok_or("lambda preparation needs its actual inferred argument Source")?;
            return self.source_type_header(
                annotation,
                &self.lambda_input_scope(site.owner, work)?,
                binding.typing_environment.clone(),
                work,
            );
        }
        let id = context
            .closure_invocation
            .ok_or_else(|| "lambda formal Source has no actual body entry".to_owned())?;
        let invocation = self
            .facts
            .closure_invocations
            .get(id.0 as usize)
            .filter(|invocation| invocation.id == id)
            .ok_or_else(|| "lambda formal Source entry is absent".to_owned())?;
        let closure = self
            .facts
            .closures
            .get(invocation.closure)
            .ok_or_else(|| "lambda formal Source object is absent".to_owned())?;
        require(
            invocation.activation == Some(binding.owner)
                && binding.parameter
                && binding.name == *name
                && context.closure == Some(invocation.closure)
                && closure.site.map(CallableOwner::Lambda) == context.owner
                && invocation.status == CopyInvocationStatus::Completed,
            "lambda formal Source borrowed another activation or lexical object",
        )?;
        let site = self
            .facts
            .closure_sites
            .iter()
            .find(|site| Some(site.id) == closure.site)
            .ok_or_else(|| "lambda formal Source lost its lexical site".to_owned())?;
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
            return Err("lambda formal Source header is not unique".into());
        };
        let ExprKind::Lambda { parameters, .. } = &header.expression.kind else {
            unreachable!()
        };
        let parameters:Vec<_>=parameters.iter().enumerate().filter(|(_,parameter)|binding.pattern.is_some() && parameter.pattern.hir_id==binding.pattern
            &&matches!(&parameter.pattern.kind,ril_syntax::ast::PatternKind::Name(actual) if actual==name)).collect();
        let [(slot, parameter)] = parameters.as_slice() else {
            return Err("lambda formal Source differs from its actual header".into());
        };
        let Some(annotation) = parameter.ty.as_ref() else {
            let observation =
                self.original_source_root(expression, value, reading, visit.observation, work)?;
            self.inferred_lambda_receipt(invocation, *slot, value, observation, work)?;
            return self
                .inferred_closure_parameter_schema(*value.sources.first().unwrap(), sites, work)?
                .flatten()
                .ok_or_else(|| {
                    "inferred lambda input has no complete admitted Source graph".into()
                });
        };
        self.source_type_header(
            annotation,
            &self.lambda_input_scope(site.owner, work)?,
            binding.typing_environment.clone(),
            work,
        )
    }

    pub(super) fn inferred_lambda_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check<Option<ArgumentKey>> {
        self.inferred_lambda_source_schema(expression, value, context, sites, &mut 4096)?
            .map(|(schema, _)| schema.key().map_err(|error| error.to_string()))
            .transpose()
    }

    pub(super) fn inferred_lambda_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let [Callable::Closure(index)] = value.callables.as_slice() else {
            return Ok(None);
        };
        let closure = self
            .facts
            .closures
            .get(*index)
            .ok_or_else(|| "inferred lambda Source object is absent".to_owned())?;
        let site = self
            .facts
            .closure_sites
            .iter()
            .find(|site| Some(site.id) == closure.site)
            .ok_or_else(|| "inferred lambda Source site is absent".to_owned())?;
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
            return Err("inferred lambda Source header is not unique".into());
        };
        match &expression.kind {
            ExprKind::Lambda { .. } => require(
                closure.hir_id.is_some()
                    && expression.hir_id == closure.hir_id
                    && context.owner == Some(site.owner)
                    && context.invocation == closure.creation_invocation
                    && context.closure_invocation == closure.creation_closure
                    && context.default_use == closure.creation_default,
                "inferred lambda literal belongs to another creation",
            )?,
            ExprKind::Name(name) => {
                if value.sources.len() != 1 {
                    return Ok(None);
                }
                let id = *value.sources.first().unwrap();
                let binding = self
                    .facts
                    .bindings
                    .get(id)
                    .ok_or_else(|| "inferred lambda Name binding is absent".to_owned())?;
                let declarations: Vec<_> = sites
                    .bindings
                    .iter()
                    .filter(|declaration| {
                        declaration.owner == site.owner
                            && declaration.binding.pattern.span == binding.span
                            && closure.hir_id.is_some()
                            && declaration.binding.value.hir_id == closure.hir_id
                            && matches!(declaration.binding.value.kind, ExprKind::Lambda { .. })
                    })
                    .collect();
                if declarations.len() != 1
                    || binding.parameter
                    || binding.name != *name
                    || binding.owner != closure.owner
                {
                    return Ok(None);
                }
                if context.owner != Some(site.owner) {
                    let caller = context
                        .closure
                        .and_then(|index| self.facts.closures.get(index))
                        .ok_or_else(|| {
                            "captured lambda Source has no actual capturing object".to_owned()
                        })?;
                    require(
                        caller.lexical.get(name) == Some(&id) && caller.captures.contains(&id),
                        "captured lambda Source borrowed an independent ambient binding",
                    )?;
                }
            }
            _ => return Ok(None),
        }
        let ExprKind::Lambda {
            parameters,
            annotations,
            body,
            ..
        } = &header.expression.kind
        else {
            unreachable!()
        };
        let scope = self.lambda_input_scope(site.owner, work)?;
        let parameter_headers = parameters;
        let written_parameters = parameter_headers
            .iter()
            .map(|parameter| {
                let Some(syntax) = parameter.ty.as_ref() else {
                    return Ok(None);
                };
                Ok(Some((
                    parameter.mode,
                    self.source_type_header(
                        syntax,
                        &scope,
                        closure.contract.typing_environment.clone(),
                        work,
                    )?,
                )))
            })
            .collect::<Check<Vec<_>>>()?;
        let mut keys = Vec::new();
        for invocation in self.facts.closure_invocations.iter().filter(|invocation| {
            invocation.closure == *index
                && invocation.probe
                && invocation.parent_named == closure.creation_invocation
                && invocation.parent_closure == closure.creation_closure
                && invocation.source_event.is_none()
                && invocation.status == CopyInvocationStatus::Completed
                && invocation.activation.is_some()
        }) {
            let mut parameters = Vec::new();
            for (slot, parameter) in parameter_headers.iter().enumerate() {
                if let Some(written) = &written_parameters[slot] {
                    parameters.push(written.clone());
                    continue;
                }
                *work = work
                    .checked_sub(self.facts.bindings.len())
                    .ok_or("inferred lambda parameter index work exhausted")?;
                let mut bindings = self
                    .facts
                    .bindings
                    .iter()
                    .enumerate()
                    .filter(|(_, binding)| {
                        binding.parameter
                            && Some(binding.owner) == invocation.activation
                            && binding.context.closure_invocation == Some(invocation.id)
                            && binding.pattern.is_some()
                            && binding.pattern == parameter.pattern.hir_id
                    });
                let (binding, _) = bindings
                    .next()
                    .ok_or("inferred lambda parameter receiver is absent")?;
                require(
                    bindings.next().is_none(),
                    "inferred lambda has duplicate parameter receivers",
                )?;
                let Some(source) = self
                    .inferred_closure_parameter_schema(binding, sites, work)?
                    .flatten()
                else {
                    return Ok(None);
                };
                parameters.push((parameter.mode, source));
            }
            for parameter in parameter_headers {
                let mut names = Vec::new();
                parameter_names(&parameter.pattern, &mut names, &mut 4096)?;
                for (span, name) in names {
                    require(
                        self.facts
                            .bindings
                            .iter()
                            .filter(|binding| {
                                binding.parameter
                                    && Some(binding.owner) == invocation.activation
                                    && binding.span == span
                                    && binding.name == name
                            })
                            .count()
                            == 1,
                        "inferred lambda formal bindings belong to another activation",
                    )?;
                }
            }
            let roots: Vec<_> = self
                .facts
                .invocation_expressions
                .iter()
                .filter_map(|row| {
                    if row.context.owner != Some(CallableOwner::Lambda(site.id))
                        || row.context.closure != Some(*index)
                        || row.context.closure_invocation != Some(invocation.id)
                        || row.context.invocation != invocation.parent_named
                        || row.context.default_use != closure.creation_default
                        || row.context.budget_validation != invocation.budget_validation
                    {
                        return None;
                    }
                    self.facts
                        .expressions
                        .get(row.expression)
                        .filter(|fact| fact.source_id.is_some() && fact.source_id == body.hir_id)
                        .map(|fact| (row.context, row.expression, &fact.value))
                })
                .collect();
            let [(body_context, observation, result)] = roots.as_slice() else {
                continue;
            };
            if result.ty == Ty::Never {
                continue;
            }
            let Some(result) = self.original_observed_source_schema_with_work(
                body,
                *observation,
                *body_context,
                sites,
                work,
            )?
            else {
                return Ok(None);
            };
            *work = work
                .checked_sub(annotations.len())
                .ok_or("lambda Source annotations exceed their work bound")?;
            for annotation in annotations {
                *work = work
                    .checked_sub(annotation.text.len().div_ceil(32))
                    .ok_or("lambda Source annotation text exceeds its work bound")?;
            }
            let row = self.source_callable_row_identity(
                crate::sema::source_types::CallableRowOrigin::Lambda(
                    closure.hir_id.ok_or("lambda row has no original HIR")?,
                ),
                annotations,
                &scope,
                &closure.contract.typing_environment,
                work,
            )?;
            let annotations: Vec<_> = annotations
                .iter()
                .map(|annotation| annotation.text.clone())
                .collect();
            *work = work
                .checked_sub(parameters.len() * 2 + 1)
                .ok_or("lambda Source parts exceed their work bound")?;
            let parameter_graphs = parameters
                .iter()
                .map(|(mode, (schema, _))| (*mode, schema.clone()))
                .collect::<Vec<_>>();
            let mut parts = parameters
                .iter()
                .map(|(_, source)| source.clone())
                .collect::<Vec<_>>();
            parts.push(result.clone());
            let mut environment = self.source_composite_environment(&parts, work)?;
            let key = super::graph_sources::schema_work(work, |budget| {
                SourceSchema::callable_original(
                    &parameter_graphs,
                    &result.0,
                    &annotations,
                    row.as_ref(),
                    None,
                    budget,
                )
            })?;
            let depends_on_parts = parts
                .iter()
                .map(|(schema, _)| {
                    super::graph_sources::schema_work(work, |budget| {
                        schema.requires_environment(budget)
                    })
                })
                .collect::<Check<Vec<_>>>()?
                .into_iter()
                .any(|required| required);
            if super::graph_sources::schema_work(work, |budget| {
                key.callable_contract_requires_environment(budget)
            })? {
                require(
                    !depends_on_parts
                        || environment.id() == closure.contract.typing_environment.id(),
                    "lambda Source annotations combine different lexical interpretations",
                )?;
                environment = closure.contract.typing_environment.clone();
            } else if !depends_on_parts {
                environment = closure.contract.typing_environment.clone();
            }
            keys.push((key, environment));
        }
        let Some(first) = keys.first() else {
            return Ok(None);
        };
        for key in &keys[1..] {
            require(
                super::graph_sources::schema_work(work, |budget| {
                    first.0.equivalent(&key.0, budget)
                })? && (!super::graph_sources::schema_work(work, |budget| {
                    first.0.requires_environment(budget)
                })? || first.1.id() == key.1.id()),
                "inferred lambda bodies disagree about their Source type",
            )?;
        }
        require(
            self.lambda_public_graph_view_agrees(value, &first.0, work)?,
            "inferred lambda Source would restore a changed public view",
        )?;
        Ok(Some(first.clone()))
    }

    fn lambda_public_graph_view_agrees(
        &self,
        value: &Value,
        schema: &SourceSchema,
        work: &mut usize,
    ) -> Check<bool> {
        let annotations =
            super::graph_sources::schema_work(work, |budget| schema.callable_annotations(budget))?
                .ok_or("lambda Source graph is not callable")?;
        if value.callable_bounds.iter().any(|bound| {
            bound
                .annotations
                .iter()
                .map(|annotation| annotation.text.replace(' ', ""))
                .collect::<Vec<_>>()
                != annotations
        }) {
            return Ok(false);
        }
        let (_, result) =
            super::graph_sources::schema_work(work, |budget| schema.callable_parts(budget))?
                .ok_or("lambda Source graph is not callable")?;
        for bound in value.callable_returns.iter().filter(|bound| !bound.raw) {
            let scope = BoundScope {
                types: bound.typing_environment.generic_context.clone(),
                rows: bound.typing_environment.bound_row_context.clone(),
            };
            let expected = self
                .source_type_header(
                    &bound.syntax,
                    &scope,
                    bound.typing_environment.clone(),
                    work,
                )?
                .0;
            if !super::graph_sources::schema_work(work, |budget| {
                expected.equivalent(&result, budget)
            })? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(in crate::sema::record_bound_validation) fn binding_source_selections(
        &self,
        binding: &crate::sema::model::BindingInfo,
        owner: CallableOwner,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let invocation = match owner {
            CallableOwner::Global => return Ok(BTreeMap::new()),
            CallableOwner::Function(definition) => {
                let summaries: Vec<_> = self
                    .facts
                    .invocations
                    .iter()
                    .filter(|summary| {
                        summary.activation == Some(binding.owner)
                            && summary
                                .context
                                .is_some_and(|context| context.owner == Some(owner))
                    })
                    .collect();
                let [summary] = summaries.as_slice() else {
                    return Err(
                        "local Source declaration has no unique actual named activation".into(),
                    );
                };
                let id = summary
                    .context
                    .and_then(|context| context.invocation)
                    .ok_or_else(|| "local Source declaration has no named instance".to_owned())?;
                require(
                    self.facts
                        .copy_invocations
                        .get(id.0 as usize)
                        .is_some_and(|call| call.id == id && call.target == definition),
                    "local Source declaration borrowed another function's activation",
                )?;
                Some(id)
            }
            CallableOwner::Lambda(site) => {
                let calls: Vec<_> = self
                    .facts
                    .closure_invocations
                    .iter()
                    .filter(|call| {
                        call.activation == Some(binding.owner)
                            && self
                                .facts
                                .closures
                                .get(call.closure)
                                .is_some_and(|closure| closure.site == Some(site))
                            && call.status == CopyInvocationStatus::Completed
                    })
                    .collect();
                let [call] = calls.as_slice() else {
                    return Err(
                        "local Source declaration has no unique actual lambda activation".into(),
                    );
                };
                self.facts.closures[call.closure].creation_invocation
            }
        };
        invocation
            .map(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .ok_or_else(|| "local Source declaration instance is absent".to_owned())
                    .and_then(|call| self.input_selected_keys(call))
            })
            .transpose()
            .map(|keys| keys.unwrap_or_default())
    }
}

fn parameter_names(
    pattern: &ril_syntax::ast::Pattern,
    out: &mut Vec<(Span, String)>,
    work: &mut usize,
) -> Check {
    *work = work
        .checked_sub(1)
        .ok_or_else(|| "lambda Source parameter walk exceeds its budget".to_owned())?;
    use ril_syntax::ast::PatternKind;
    match &pattern.kind {
        PatternKind::Name(name) => out.push((pattern.span, name.clone())),
        PatternKind::Mode { pattern, .. } => parameter_names(pattern, out, work)?,
        PatternKind::Tuple(items) => {
            for item in items {
                parameter_names(item, out, work)?;
            }
        }
        PatternKind::Record { fields, .. } => {
            for field in fields {
                parameter_names(&field.pattern, out, work)?;
            }
        }
        PatternKind::Wildcard => {}
        _ => return Err("lambda Source formal pattern has no complete binder proof".into()),
    }
    Ok(())
}
