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
        crate::sema::checker::actual_prelude_name(
            self.facts,
            context,
            application.callee,
            identity,
        )?;
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
            self.producing_receiver_schema(expression, root, context, sites, work)?
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
    ) -> Check<Option<OriginalSource>> {
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
            let function = self.function(owner)?;
            if let (Some(syntax), Some(body)) =
                (&function.syntax.return_type, &function.syntax.body)
            {
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
    let children: Vec<&Expr> = if let Some(application) = AstApplication::from_ast(root) {
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
