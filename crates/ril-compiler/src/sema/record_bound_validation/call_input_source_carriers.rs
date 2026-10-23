//! Reconstruct carrier graphs from the physical active operand. Only the
//! branch which did not execute may come from an original receiving header.
use super::*;
use crate::sema::source_types::{SourceContainer, SourcePath};
use ril_syntax::ast::RecordMember;

struct CarrierInput {
    projection: SourcePath,
    event: crate::sema::copy_contract::CopyCallEventId,
    operand: usize,
}

#[derive(Clone, Copy)]
struct ReceivingOccurrence<'a> {
    syntax: &'a Expr,
    observation: usize,
    context: InvocationContext,
}

impl Replay<'_> {
    fn source_occurrence_encloses(
        &self,
        outer: usize,
        inner: usize,
        work: &mut usize,
    ) -> Check<bool> {
        let outer = self
            .facts
            .evaluations
            .get(outer)
            .and_then(|row| row.identity)
            .ok_or("receiving Source has no actual outer occurrence")?;
        let mut current = self
            .facts
            .evaluations
            .get(inner)
            .and_then(|row| row.identity)
            .ok_or("receiving Source has no actual inner occurrence")?
            .activation;
        loop {
            *work = work
                .checked_sub(1)
                .ok_or("receiving Source ancestry exceeds its work bound")?;
            if current == outer.activation {
                return Ok(true);
            }
            let activation = self
                .facts
                .activations
                .get(current.0 as usize)
                .filter(|activation| activation.id == current)
                .ok_or("receiving Source ancestry is outside its arena")?;
            let Some(parent) = activation.parent else {
                return Ok(false);
            };
            require(parent.0 < current.0, "receiving Source ancestry is cyclic")?;
            current = parent;
        }
    }

    fn source_carrier_input(
        &self,
        expression: &Expr,
        root: usize,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check<Option<CarrierInput>> {
        let Some(application) = AstApplication::from_ast(expression) else {
            return Ok(None);
        };
        if application.operands.len() != 1 {
            return Ok(None);
        }
        *work = work
            .checked_sub(self.facts.copy_call_events.len())
            .ok_or("carrier Source events exceed their work bound")?;
        let mut events = self
            .facts
            .copy_call_events
            .iter()
            .filter(|event| event.result_expression == Some(root));
        let Some(event) = events.next() else {
            return Ok(None);
        };
        require(
            events.next().is_none()
                && event.matches_source(expression)
                && event.owner == context.owner
                && event.parent == context.invocation,
            "carrier Source borrowed another actual call",
        )?;
        let callee_token = event
            .callee_expression
            .ok_or("carrier Source lost its actual callee")?;
        let callee = self
            .facts
            .expressions
            .get(callee_token)
            .ok_or("carrier callee is outside its arena")?;
        let [Callable::Builtin(name)] = callee.value.callables.as_slice() else {
            return Ok(None);
        };
        let identity = name.strip_prefix("Prelude::").unwrap_or(name);
        let projection = match identity {
            "Some" => SourcePath::OptionalPayload,
            "Ok" => SourcePath::ResultSuccess,
            "Err" => SourcePath::ResultError,
            _ => return Ok(None),
        };
        require(
            event.target.is_none()
                && callee.source_id.is_some()
                && callee.source_id == application.callee.hir_id
                && callee.value.sources.is_empty()
                && self.observations.row(callee_token, work)?.context == context
                && application.operands[0].label.is_none()
                && matches!(
                    application.operands[0].mode,
                    ril_syntax::ast::ParameterMode::Read
                        | ril_syntax::ast::ParameterMode::SharedMut
                ),
            "carrier Source changed its actual primitive or argument role",
        )?;
        self.actual_prelude_name(context, application.callee, identity, work)?;
        *work = work
            .checked_sub(self.facts.call_arguments.len())
            .ok_or("carrier Source preparation exceeds its work bound")?;
        let mut preparations = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id);
        let preparation = preparations
            .next()
            .ok_or("carrier Source has no actual operand preparation")?;
        require(
            preparations.next().is_none()
                && preparation.target.is_none()
                && preparation.evaluation_complete
                && preparation.slots == [ArgumentSource::Supplied]
                && preparation.supplied.len() == 1,
            "carrier Source changed its completed supplied input",
        )?;
        let token = preparation
            .supplied
            .get(&0)
            .ok_or("carrier Source lost its original operand token")?;
        let operand = self
            .facts
            .expressions
            .get(token.expression)
            .ok_or("carrier operand is outside its arena")?;
        let row = self.observations.row(token.expression, work)?;
        require(
            operand.source_id.is_some()
                && operand.source_id == application.operands[0].expression.hir_id
                && row.context == context
                && row.argument_of == Some((event.id, 0))
                && token.allocation_epoch <= self.facts.allocation_history.len(),
            "carrier Source operand borrowed another occurrence, context or epoch",
        )?;
        self.input_operand_interval(event, 0, token.expression, context, work)?;
        let result = &self.facts.expressions[root].value;
        let payload = match identity {
            "Some" => {
                require(
                    result.option_tag == Some(true),
                    "Some Source changed its actual carrier tag",
                )?;
                result.option_payload.as_deref()
            }
            "Ok" => {
                require(
                    result.result_tag == Some(true),
                    "Ok Source changed its actual carrier tag",
                )?;
                result.result_success.as_deref()
            }
            "Err" => {
                require(
                    result.result_tag == Some(false),
                    "Err Source changed its actual carrier tag",
                )?;
                result.result_error.as_deref()
            }
            _ => unreachable!(),
        }
        .ok_or("carrier Source lost its active payload")?;
        if application.operands[0].mode == ril_syntax::ast::ParameterMode::SharedMut {
            require(
                operand.value.permission == crate::sema::facts::Permission::Write
                    && !operand.value.temporary
                    && payload.marker,
                "retained carrier Source lacks its original writable retained input",
            )?;
        }
        require(
            payload.cause == operand.value.cause
                && self
                    .facts
                    .explanations
                    .causes
                    .get(result.cause.0 as usize)
                    .is_some_and(|cause| cause.parents == [operand.value.cause]),
            "carrier Source payload is not its actual constructor input",
        )?;
        if identity != "Some" {
            require(
                result.result_payload.as_deref() == Some(payload),
                "Result Source changed its active payload view",
            )?;
        }
        Ok(Some(CarrierInput {
            projection,
            event: event.id,
            operand: token.expression,
        }))
    }

    pub(super) fn original_carrier_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<Option<OriginalSource>>> {
        if AstApplication::from_ast(expression).is_none() {
            return Ok(None);
        }
        let root =
            self.original_source_root(expression, value, context, visit.observation, work)?;
        let Some(carrier) = self.source_carrier_input(expression, root, context, work)? else {
            return Ok(None);
        };
        let application = AstApplication::from_ast(expression).unwrap();
        let actual = &self.facts.expressions[carrier.operand];
        let Some(active) = self.original_source_schema_inner(
            application.operands[0].expression,
            &actual.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: visit.depth + 1,
                observation: Some(carrier.operand),
            },
        )?
        else {
            return Ok(Some(None));
        };
        if carrier.projection == SourcePath::OptionalPayload {
            let schema = super::graph_sources::schema_work(work, |budget| {
                SourceSchema::container(
                    SourceContainer::Option,
                    std::slice::from_ref(&active.0),
                    None,
                    budget,
                )
            })?;
            return Ok(Some(Some((schema, active.1))));
        }
        let Some((receiver, receiver_environment)) =
            self.producing_receiver_schema(expression, root, context, sites, work, visit.depth)?
        else {
            return Ok(Some(None));
        };
        let success = carrier.projection == SourcePath::ResultSuccess;
        let inactive_projection = if success {
            SourcePath::ResultError
        } else {
            SourcePath::ResultSuccess
        };
        let inactive = super::graph_sources::schema_work(work, |budget| {
            receiver.project_steps(&[inactive_projection], budget)
        })?;
        let parts = [active, (inactive, receiver_environment)];
        let environment = self.source_composite_environment(&parts, work)?;
        let arguments = if success {
            [parts[0].0.clone(), parts[1].0.clone()]
        } else {
            [parts[1].0.clone(), parts[0].0.clone()]
        };
        let schema = super::graph_sources::schema_work(work, |budget| {
            SourceSchema::container(SourceContainer::Result, &arguments, None, budget)
        })?;
        Ok(Some(Some((schema, environment))))
    }

    fn receiving_graph_path(
        &self,
        root: &Expr,
        target: ReceivingOccurrence<'_>,
        schema: &SourceSchema,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<SourceSchema>> {
        *work = work
            .checked_sub(1)
            .ok_or("receiving Source path exceeds its work bound")?;
        require(depth < 64, "receiving Source path exceeds its depth bound")?;
        if root.hir_id.is_some() && root.hir_id == target.syntax.hir_id {
            return Ok(Some(schema.clone()));
        }
        for child in receiving_value_children(root, work)? {
            if !source_contains(child, target.syntax, work, depth + 1)? {
                continue;
            }
            let source = root
                .hir_id
                .ok_or("receiving value position has no original HIR")?;
            let candidates = self.observations.range(
                source,
                target.context,
                target.observation..usize::MAX,
                work,
            )?;
            let mut enclosing = false;
            for &observation in candidates {
                *work = work
                    .checked_sub(1)
                    .ok_or("receiving value position work exhausted")?;
                if self.source_occurrence_encloses(observation, target.observation, work)? {
                    require(
                        !enclosing,
                        "receiving value position has multiple actual ancestors",
                    )?;
                    enclosing = true;
                }
            }
            if enclosing {
                return self.receiving_graph_path(child, target, schema, work, depth + 1);
            }
        }
        let mut children = Vec::new();
        match &root.kind {
            ExprKind::Tuple(items) => {
                *work = work
                    .checked_sub(items.len())
                    .ok_or("receiving tuple exceeds its work bound")?;
                for (index, item) in items.iter().enumerate() {
                    children.push((
                        item,
                        SourcePath::Tuple(
                            u32::try_from(index)
                                .map_err(|_| "receiving tuple coordinate overflow")?,
                        ),
                    ));
                }
            }
            ExprKind::Array(items) => {
                *work = work
                    .checked_sub(items.len())
                    .ok_or("receiving array exceeds its work bound")?;
                children.extend(items.iter().map(|item| (item, SourcePath::Element)));
            }
            ExprKind::Map(items) => {
                *work = work
                    .checked_sub(
                        items
                            .len()
                            .checked_mul(2)
                            .ok_or("receiving map size overflow")?,
                    )
                    .ok_or("receiving map exceeds its work bound")?;
                children.extend(items.iter().flat_map(|(key, value)| {
                    [(key, SourcePath::MapKey), (value, SourcePath::MapValue)]
                }));
            }
            ExprKind::Record { members, .. } => {
                *work = work
                    .checked_sub(members.len())
                    .ok_or("receiving record exceeds its work bound")?;
                for member in members {
                    if let RecordMember::Field(field) = member {
                        *work = work
                            .checked_sub(field.name.len().div_ceil(32))
                            .ok_or("receiving record labels exceed their work bound")?;
                        children.push((&field.value, SourcePath::Field(field.name.clone())));
                    }
                }
            }
            ExprKind::Control {
                operation: ril_syntax::ast::ControlOperation::Return,
                value: Some(value),
            } => {
                return self.receiving_graph_path(value, target, schema, work, depth + 1);
            }
            _ => {}
        }
        for (child, step) in children {
            if !source_contains(child, target.syntax, work, depth + 1)? {
                continue;
            }
            let projected = super::graph_sources::schema_work(work, |budget| {
                schema.project_steps(&[step], budget)
            })?;
            return self.receiving_graph_path(child, target, &projected, work, depth + 1);
        }
        if let Some(application) = AstApplication::from_ast(root)
            && application.operands.len() == 1
            && source_contains(
                application.operands[0].expression,
                target.syntax,
                work,
                depth + 1,
            )?
        {
            let source = root
                .hir_id
                .ok_or("receiving carrier has no original HIR identity")?;
            let candidates = self.observations.range(
                source,
                target.context,
                target.observation..usize::MAX,
                work,
            )?;
            let mut found = None;
            for &observation in candidates {
                if !self.source_occurrence_encloses(observation, target.observation, work)? {
                    continue;
                }
                let Some(carrier) =
                    self.source_carrier_input(root, observation, target.context, work)?
                else {
                    continue;
                };
                require(
                    found.is_none()
                        && self.source_occurrence_encloses(
                            carrier.operand,
                            target.observation,
                            work,
                        )?,
                    "receiving carrier borrowed another active operand",
                )?;
                self.input_operand_interval(
                    &self.facts.copy_call_events[carrier.event.0 as usize],
                    0,
                    carrier.operand,
                    target.context,
                    work,
                )?;
                found = Some(carrier.projection);
            }
            if let Some(step) = found {
                let projected = super::graph_sources::schema_work(work, |budget| {
                    schema.project_steps(&[step], budget)
                })?;
                return self.receiving_graph_path(
                    application.operands[0].expression,
                    target,
                    &projected,
                    work,
                    depth + 1,
                );
            }
        }
        Ok(None)
    }

    fn producing_receiver_schema(
        &self,
        expression: &Expr,
        observation: usize,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<OriginalSource>> {
        *work = work
            .checked_sub(1)
            .ok_or("receiving boundary ancestry work exhausted")?;
        require(
            depth < 64,
            "receiving boundary ancestry exceeds its depth bound",
        )?;
        let receiving = ReceivingOccurrence {
            syntax: expression,
            observation,
            context,
        };
        let scope = context
            .owner
            .map(|owner| self.lambda_input_scope(owner, work))
            .transpose()?
            .unwrap_or_default();
        let environment = self.source_graph_environment(context, Some(observation), work)?;
        let mut receivers = Vec::new();
        *work = work
            .checked_sub(sites.bindings.len() + sites.calls.len())
            .ok_or("receiving Source sites exceed their work bound")?;
        for site in &sites.bindings {
            if Some(site.owner) != context.owner
                || site.binding.is_meta
                || !source_contains(&site.binding.value, expression, work, 0)?
            {
                continue;
            }
            let Some(syntax) = &site.binding.ty else {
                continue;
            };
            let Some(source) = site.binding.value.hir_id else {
                return Err("receiving binding has no original HIR initializer".into());
            };
            let candidates =
                self.observations
                    .range(source, context, observation..usize::MAX, work)?;
            for &outer in candidates {
                if !self.source_occurrence_encloses(outer, observation, work)? {
                    continue;
                }
                let original_environment =
                    self.source_graph_environment(context, Some(outer), work)?;
                let (schema, original_environment) =
                    self.source_type_header(syntax, &scope, original_environment, work)?;
                if let Some(schema) =
                    self.receiving_graph_path(&site.binding.value, receiving, &schema, work, 0)?
                {
                    receivers.push((schema, original_environment));
                }
            }
        }
        for site in &sites.calls {
            if Some(site.owner) != context.owner {
                continue;
            }
            let Some(application) = AstApplication::from_ast(site.expression) else {
                return Err("receiving call has no original application".into());
            };
            if !application
                .operands
                .iter()
                .map(|operand| source_contains(operand.expression, expression, work, 0))
                .collect::<Check<Vec<_>>>()?
                .into_iter()
                .any(|contains| contains)
            {
                continue;
            }
            *work = work
                .checked_sub(self.facts.copy_call_events.len())
                .ok_or("receiving call events exceed their work bound")?;
            for event in &self.facts.copy_call_events {
                if !event.matches_source(site.expression)
                    || event.owner != context.owner
                    || event.parent != context.invocation
                {
                    continue;
                }
                let Some(outer) = event.result_expression else {
                    continue;
                };
                if !self.source_occurrence_encloses(outer, observation, work)? {
                    continue;
                }
                let token = event
                    .callee_expression
                    .ok_or("receiving call lost its actual callee")?;
                let callee_value = &self
                    .facts
                    .expressions
                    .get(token)
                    .ok_or("receiving callee is outside its arena")?
                    .value;
                let Some((callee, callee_environment)) = self
                    .original_observed_source_schema_with_work(
                        application.callee,
                        token,
                        context,
                        sites,
                        work,
                    )?
                else {
                    continue;
                };
                let Some((parameters, _)) = super::graph_sources::schema_work(work, |budget| {
                    callee.callable_parts(budget)
                })?
                else {
                    continue;
                };
                let labels =
                    crate::sema::builtin_sources::parameter_labels(callee_value, parameters.len());
                let mapping = crate::hir::application::bind_slots(
                    &labels,
                    application.operands.iter().map(|operand| operand.label),
                );
                let mut occupied = BTreeSet::new();
                for (operand, slot) in application.operands.iter().zip(mapping) {
                    let slot =
                        slot.map_err(|code| format!("receiving call slot is invalid: {code}"))?;
                    require(
                        occupied.insert(slot),
                        "receiving call repeats an actual slot",
                    )?;
                    if !source_contains(operand.expression, expression, work, 0)? {
                        continue;
                    }
                    let (_, parameter) = parameters
                        .get(slot)
                        .ok_or("receiving call parameter is absent")?;
                    *work = work
                        .checked_sub(self.facts.call_arguments.len())
                        .ok_or("receiving call preparation exceeds its work bound")?;
                    let preparations: Vec<_> = self
                        .facts
                        .call_arguments
                        .iter()
                        .filter(|row| row.source_event == event.id)
                        .collect();
                    let [preparation] = preparations.as_slice() else {
                        return Err("receiving call has no unique preparation".into());
                    };
                    let token = preparation
                        .supplied
                        .get(&(slot as u32))
                        .ok_or("receiving call operand is absent")?;
                    require(
                        preparation.target == event.target
                            && preparation.evaluation_complete
                            && self
                                .facts
                                .expressions
                                .get(token.expression)
                                .is_some_and(|fact| {
                                    fact.source_id.is_some()
                                        && fact.source_id == operand.expression.hir_id
                                })
                            && self.observations.row(token.expression, work)?.context == context
                            && self.source_occurrence_encloses(
                                token.expression,
                                observation,
                                work,
                            )?,
                        "receiving call borrowed another supplied occurrence",
                    )?;
                    self.input_operand_interval(event, slot, token.expression, context, work)?;
                    let selected_environment = if let Some(target) = event.target {
                        *work = work
                            .checked_sub(self.facts.copy_invocations.len())
                            .ok_or("receiving invocation lookup exceeds its work bound")?;
                        let calls: Vec<_> = self
                            .facts
                            .copy_invocations
                            .iter()
                            .filter(|call| {
                                call.source_event == Some(event.id) && call.target == target
                            })
                            .collect();
                        let [call] = calls.as_slice() else {
                            return Err(
                                "receiving call has no unique actual named activation".into()
                            );
                        };
                        self.source_graph_environment(
                            InvocationContext {
                                owner: Some(CallableOwner::Function(target)),
                                invocation: Some(call.id),
                                ..context
                            },
                            None,
                            work,
                        )?
                    } else {
                        environment.clone()
                    };
                    let selected = self.source_selected_schemas(&selected_environment, work)?;
                    let (parameter, parameter_environment) = self.source_substitute_schema(
                        parameter.clone(),
                        callee_environment.clone(),
                        &selected,
                        work,
                    )?;
                    if let Some(schema) = self.receiving_graph_path(
                        operand.expression,
                        receiving,
                        &parameter,
                        work,
                        0,
                    )? {
                        receivers.push((schema, parameter_environment));
                    }
                }
            }
        }
        if let Some(CallableOwner::Function(owner)) = context.owner {
            *work = work
                .checked_sub(sites.functions.len())
                .ok_or("return Source declaration lookup work exhausted")?;
            let mut declarations = sites
                .functions
                .iter()
                .filter(|site| site.owner == CallableOwner::Function(owner));
            let function = declarations
                .next()
                .ok_or("return Source has no original named declaration")?
                .function;
            require(
                declarations.next().is_none(),
                "return Source has multiple original named declarations",
            )?;
            if let (Some(syntax), Some(body)) = (&function.return_type, &function.body) {
                *work = work
                    .checked_sub(body.statements.len())
                    .ok_or("return Source statements exceed their work bound")?;
                for (index, statement) in body.statements.iter().enumerate() {
                    let StmtKind::Expr {
                        expression: root,
                        terminated,
                    } = &statement.kind
                    else {
                        continue;
                    };
                    if !matches!(
                        &root.kind,
                        ExprKind::Control {
                            operation: ril_syntax::ast::ControlOperation::Return,
                            ..
                        }
                    ) && (*terminated || index + 1 != body.statements.len())
                    {
                        continue;
                    }
                    if !source_contains(root, expression, work, 0)? {
                        continue;
                    }
                    let (schema, header_environment) =
                        self.source_type_header(syntax, &scope, environment.clone(), work)?;
                    if let Some(schema) =
                        self.receiving_graph_path(root, receiving, &schema, work, 0)?
                    {
                        receivers.push((schema, header_environment));
                    }
                }
            }
        }
        if let Some(CallableOwner::Lambda(site)) = context.owner
            && let Some((body, schema, header_environment)) =
                self.lambda_result_receiver(site, observation, context, sites, work, depth)?
            && source_contains(body, expression, work, 0)?
            && let Some(schema) = self.receiving_graph_path(body, receiving, &schema, work, 0)?
        {
            receivers.push((schema, header_environment));
        }
        let Some(first) = receivers.first() else {
            return Ok(None);
        };
        for next in &receivers[1..] {
            require(
                super::graph_sources::schema_work(work, |budget| {
                    first.0.equivalent(&next.0, budget)
                })?,
                "producing carrier has conflicting original Source receivers",
            )?;
        }
        let _ = self.source_composite_environment(&receivers, work)?;
        Ok(Some(first.clone()))
    }

    fn lambda_result_receiver<'a>(
        &self,
        site: ril_compiler_core::ids::ClosureSiteId,
        observation: usize,
        context: InvocationContext,
        sites: &'a super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<(&'a Expr, SourceSchema, FrozenEnvironment)>> {
        *work = work
            .checked_sub(8)
            .ok_or("lambda result boundary work exhausted")?;
        let call_id = context
            .closure_invocation
            .ok_or("lambda result has no actual invocation")?;
        let call = self
            .facts
            .closure_invocations
            .get(call_id.0 as usize)
            .filter(|call| call.id == call_id)
            .ok_or("lambda result invocation is absent")?;
        let entered = self
            .facts
            .evaluations
            .get(observation)
            .ok_or("lambda result observation is absent")?;
        require(
            call.activation == Some(entered.scope)
                && context.closure == Some(call.closure)
                && call.parent_named == context.invocation
                && call.budget_validation == context.budget_validation,
            "lambda result borrowed another actual body activation",
        )?;
        let closure = self
            .facts
            .closures
            .get(call.closure)
            .ok_or("lambda result object is absent")?;
        let static_site = self
            .facts
            .closure_sites
            .get(site.0 as usize)
            .filter(|source| source.id == site)
            .ok_or("lambda result site is absent")?;
        require(
            closure.site == Some(site) && closure.hir_id == Some(static_site.source),
            "lambda result changed its original creation source",
        )?;
        *work = work
            .checked_sub(1 + sites.expressions.len().checked_ilog2().unwrap_or(0) as usize)
            .ok_or("lambda result header lookup work exhausted")?;
        let original = sites
            .expressions
            .get(&static_site.source)
            .copied()
            .ok_or("lambda result has no original written header")?;
        let ExprKind::Lambda {
            body, return_type, ..
        } = &original.kind
        else {
            return Err("lambda result source is not an original lambda".into());
        };
        require(
            body.hir_id.is_some() && body.hir_id == closure.body.hir_id,
            "lambda result changed its original body",
        )?;
        if let Some(header) = return_type {
            let scope = self.lambda_input_scope(CallableOwner::Lambda(site), work)?;
            let (schema, environment) = self.source_type_header(
                header,
                &scope,
                closure.contract.typing_environment.clone(),
                work,
            )?;
            return Ok(Some((body, schema, environment)));
        }
        // A contextual return belongs to the original boundary receiving the
        // lambda value. Its body result does not supply its own expected type.
        *work = work
            .checked_sub(
                1 + self
                    .facts
                    .scopes
                    .records()
                    .len()
                    .checked_ilog2()
                    .unwrap_or(0) as usize,
            )
            .ok_or("lambda creation scope lookup work exhausted")?;
        let creation_scope = self
            .facts
            .scopes
            .get(&closure.owner)
            .ok_or("lambda result creation scope is absent")?;
        let mut creation = match &creation_scope.origin {
            crate::sema::scopes::ScopeOrigin::Named(id) => {
                let parent = self
                    .facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == *id)
                    .ok_or("lambda creation invocation is absent")?;
                InvocationContext {
                    owner: Some(CallableOwner::Function(parent.target)),
                    invocation: Some(*id),
                    ..parent.entry.caller_context
                }
            }
            crate::sema::scopes::ScopeOrigin::Closure(id) => {
                let parent = self
                    .facts
                    .closure_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == *id && call.activation == Some(closure.owner))
                    .ok_or("lambda creation closure invocation is absent")?;
                InvocationContext {
                    owner: self
                        .facts
                        .closures
                        .get(parent.closure)
                        .and_then(|closure| closure.site)
                        .map(CallableOwner::Lambda),
                    invocation: parent.parent_named,
                    closure: Some(parent.closure),
                    closure_invocation: Some(*id),
                    budget_validation: parent.budget_validation,
                    ..parent.entry.caller_context
                }
            }
            crate::sema::scopes::ScopeOrigin::Operation(entry) => entry.context,
            crate::sema::scopes::ScopeOrigin::Module => InvocationContext {
                owner: Some(CallableOwner::Global),
                invocation: None,
                closure: None,
                closure_invocation: None,
                default_use: None,
                budget_validation: false,
            },
            crate::sema::scopes::ScopeOrigin::Unresolved => {
                return Err("lambda creation boundary is unresolved".into());
            }
        };
        creation.default_use = closure.creation_default;
        require(
            creation.owner == Some(static_site.owner)
                && creation.invocation == closure.creation_invocation
                && creation.closure_invocation == closure.creation_closure,
            "lambda result borrowed another creation context",
        )?;
        let candidates =
            self.observations
                .range(static_site.source, creation, 0..usize::MAX, work)?;
        let mut actual_creation = None;
        for &token in candidates {
            *work = work
                .checked_sub(2)
                .ok_or("lambda creation occurrence work exhausted")?;
            let fact = self
                .facts
                .expressions
                .get(token)
                .ok_or("lambda creation observation is absent")?;
            let record = self
                .facts
                .evaluations
                .get(token)
                .ok_or("lambda creation evaluation is absent")?;
            if record.scope == closure.owner
                && matches!(fact.value.callables.as_slice(), [Callable::Closure(id)] if *id == call.closure)
            {
                require(
                    actual_creation.replace(token).is_none(),
                    "lambda result has multiple original creations",
                )?;
            }
        }
        let token = actual_creation.ok_or("lambda result has no actual creation occurrence")?;
        if call.probe {
            let parent = self.facts.evaluations[token]
                .identity
                .ok_or("lambda creation lost its activation")?
                .activation;
            require(
                call.entry.parent == Some(parent)
                    && call.parent_named == closure.creation_invocation
                    && call.parent_closure == closure.creation_closure
                    && self.source_occurrence_encloses(token, observation, work)?,
                "lambda result probe borrowed an unrelated creation boundary",
            )?;
        } else {
            require(
                token < observation,
                "lambda result precedes its original creation",
            )?;
        }
        let Some((schema, environment)) =
            self.producing_receiver_schema(original, token, creation, sites, work, depth + 1)?
        else {
            return Ok(None);
        };
        let Some((_, result)) =
            super::graph_sources::schema_work(work, |budget| schema.callable_parts(budget))?
        else {
            return Err("lambda receiving boundary has no original callable result".into());
        };
        Ok(Some((body, result, environment)))
    }
}

/// Only expression positions which contribute this value receive its expected
/// schema. Conditions, guards, initializers and nested callable bodies do not.
fn receiving_value_children<'a>(root: &'a Expr, work: &mut usize) -> Check<Vec<&'a Expr>> {
    match &root.kind {
        ExprKind::Block(block) => {
            *work = work
                .checked_sub(block.statements.len())
                .ok_or("receiving block work exhausted")?;
            Ok(block
                .statements
                .iter()
                .enumerate()
                .filter_map(|(index, statement)| {
                    let StmtKind::Expr {
                        expression,
                        terminated,
                    } = &statement.kind
                    else {
                        return None;
                    };
                    (matches!(
                        expression.kind,
                        ExprKind::Control {
                            operation: ril_syntax::ast::ControlOperation::Return,
                            ..
                        }
                    ) || (!*terminated && index + 1 == block.statements.len()))
                    .then_some(expression)
                })
                .collect())
        }
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } => {
            *work = work
                .checked_sub(2)
                .ok_or("receiving conditional work exhausted")?;
            Ok(std::iter::once(then_branch.as_ref())
                .chain(else_branch.as_deref())
                .collect())
        }
        ExprKind::Match { arms, .. } => {
            *work = work
                .checked_sub(arms.len())
                .ok_or("receiving match work exhausted")?;
            Ok(arms.iter().map(|arm| &arm.body).collect())
        }
        _ => Ok(Vec::new()),
    }
}

fn source_contains(root: &Expr, target: &Expr, work: &mut usize, depth: usize) -> Check<bool> {
    *work = work
        .checked_sub(1)
        .ok_or("receiving Source syntax exceeds its work bound")?;
    require(
        depth < 64,
        "receiving Source syntax exceeds its depth bound",
    )?;
    if root.hir_id.is_some() && root.hir_id == target.hir_id {
        return Ok(true);
    }
    let control = receiving_value_children(root, work)?;
    let children: Vec<&Expr> = if !control.is_empty() {
        control
    } else if let Some(application) = AstApplication::from_ast(root) {
        *work = work
            .checked_sub(application.operands.len())
            .ok_or("receiving Source arguments exceed their work bound")?;
        application
            .operands
            .iter()
            .map(|operand| operand.expression)
            .collect()
    } else {
        match &root.kind {
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                *work = work
                    .checked_sub(items.len())
                    .ok_or("receiving Source items exceed their work bound")?;
                items.iter().collect()
            }
            ExprKind::Map(items) => {
                *work = work
                    .checked_sub(
                        items
                            .len()
                            .checked_mul(2)
                            .ok_or("receiving Source map size overflow")?,
                    )
                    .ok_or("receiving Source map exceeds its work bound")?;
                items.iter().flat_map(|(key, value)| [key, value]).collect()
            }
            ExprKind::Record { members, .. } => {
                *work = work
                    .checked_sub(members.len())
                    .ok_or("receiving Source fields exceed their work bound")?;
                members
                    .iter()
                    .map(|member| match member {
                        RecordMember::Field(field) => &field.value,
                        RecordMember::Spread(source) => source,
                    })
                    .collect()
            }
            ExprKind::Control {
                operation: ril_syntax::ast::ControlOperation::Return,
                value: Some(value),
            } => vec![value],
            _ => vec![],
        }
    };
    for child in children {
        if source_contains(child, target, work, depth + 1)? {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckOptions, Session};

    fn fixture(case: &str, layout: &str) -> SemanticFacts {
        let verified = Session::with_options(
            ril_test::case_bytes(case).to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{case}/{layout}: {error:?}"));
        crate::lower::lower_core(&verified).unwrap();
        verified.facts().clone()
    }

    #[test]
    fn carrier_receivers_follow_conditional_named_and_contextual_lambda_results() {
        for layout in ["pointer32", "pointer64"] {
            for case in [
                "tests/stdlib/io.ril::io-all-alias-chunks",
                "tests/stdlib/io.ril::io-all-alias-handler",
                "tests/regressions/evaluation-identity.ril::retained-carrier-tag-sources",
                "tests/regressions/evaluation-identity.ril::retained-carrier-caller-source",
            ] {
                fixture(case, layout);
            }
        }
    }

    fn source(facts: &SemanticFacts, observation: usize) -> Check<OriginalSource> {
        let mut work = 4_000_000;
        let sources = OriginalOperandSources::new_with_work(facts, &mut work)?;
        sources
            .observed_with_work(
                facts.expressions[observation]
                    .source_id
                    .ok_or("carrier source is absent")?,
                observation,
                &mut work,
            )?
            .0
            .ok_or_else(|| "carrier lost its independent receiving graph".into())
    }

    #[test]
    fn carrier_receiver_cannot_borrow_another_creation_or_return_boundary() {
        for layout in ["pointer32", "pointer64"] {
            let facts = fixture(
                "tests/regressions/evaluation-identity.ril::retained-carrier-tag-sources",
                layout,
            );
            let (observation, invocation) = facts
                .copy_call_events
                .iter()
                .filter_map(|event| {
                    let token = event.result_expression?;
                    let context = facts.evaluations[token].context;
                    if !matches!(context.owner, Some(CallableOwner::Lambda(_)))
                        || facts.expressions[token].value.result_tag != Some(true)
                    {
                        return None;
                    }
                    let id = context.closure_invocation?;
                    let call = facts.closure_invocations.get(id.0 as usize)?;
                    call.probe.then_some((token, id))
                })
                .next()
                .expect("the actual contextual lambda probe must construct an Ok result");
            let call = &facts.closure_invocations[invocation.0 as usize];
            let closure = &facts.closures[call.closure];
            let creation = facts.expressions.iter().enumerate().find(|(token, fact)| {
                fact.source_id == closure.hir_id && facts.evaluations[*token].scope == closure.owner
                    && matches!(fact.value.callables.as_slice(), [Callable::Closure(id)] if *id == call.closure)
            }).map(|(token, _)| token).expect("the lambda must have a real physical creation");
            let parent = closure
                .creation_invocation
                .expect("the lambda is received through its creating function's return");
            let definition = facts.copy_invocations[parent.0 as usize].target;
            let function = facts
                .functions
                .iter()
                .position(|function| function.definition == definition)
                .unwrap();
            let original = source(&facts, observation).unwrap();
            let inactive = graph_sources::schema_work(&mut 4096, |work| {
                original.0.project_steps(&[SourcePath::ResultError], work)
            })
            .unwrap();
            assert_eq!(
                graph_sources::schema_work(&mut 4096, |work| inactive.runtime_type(work)).unwrap(),
                Ty::Str
            );
            for mutation in 0..8 {
                let mut changed = facts.clone();
                match mutation {
                    0 => changed.closures[call.closure].creation_invocation = None,
                    1 => changed.closures[call.closure].creation_closure = Some(invocation),
                    2 => {
                        changed.closures[call.closure].creation_default =
                            Some(crate::sema::default_uses::DefaultUseId(u32::MAX))
                    }
                    3 => {
                        changed.closure_invocations[invocation.0 as usize].activation =
                            Some(crate::sema::facts::ScopeId(0))
                    }
                    4 => {
                        changed.closure_invocations[invocation.0 as usize]
                            .entry
                            .parent = None
                    }
                    5 => changed.expressions[creation]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .callables
                        .clear(),
                    6 => changed.functions[function].syntax.return_type = None,
                    7 => changed.closures[call.closure].hir_id = closure.body.hir_id,
                    _ => unreachable!(),
                }
                assert!(
                    source(&changed, observation).is_err(),
                    "{layout}: carrier receiving mutation {mutation} was accepted"
                );
            }
            let mut work = 4_000_000;
            let sources = OriginalOperandSources::new_with_work(&facts, &mut work).unwrap();
            assert!(
                sources
                    .observed_with_work(
                        facts.expressions[observation].source_id.unwrap(),
                        observation,
                        &mut 0
                    )
                    .is_err()
            );
        }
    }
}
