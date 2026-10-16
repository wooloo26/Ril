//! Original named input replay. Complete source coordinates are read before
//! reception; physical argument/default identities never come from a span scan.
use super::*;
#[path = "call_input_source_closures.rs"]
mod closure_sources;
#[path = "call_input_source_composites.rs"]
mod composites;
#[path = "constructor_input_source.rs"]
mod constructor_inputs;
#[path = "call_input_source_result.rs"]
mod producing_result;
#[path = "storage_input_source.rs"]
mod storage_inputs;
use crate::sema::{
    copy_contract::CopyInvocation,
    default_uses::{ArgumentSource, DefaultOrigin},
    effect_identity::{InvocationContext, StaticArgumentWitness},
    source_reception,
};

pub(super) fn original_operand_source_key(
    facts: &SemanticFacts,
    event_id: crate::sema::copy_contract::CopyCallEventId,
    slot: u32,
) -> Check<ArgumentKey> {
    let replay = Replay::new(facts)?;
    let sites = super::explicit_named::source_sites_base(facts)?;
    let event = facts
        .copy_call_events
        .get(event_id.0 as usize)
        .filter(|event| event.id == event_id)
        .ok_or_else(|| "source operand origin event is absent".to_owned())?;
    let origins: Vec<_> = sites
        .calls
        .iter()
        .filter(|site| Some(site.owner) == event.owner && site.expression.span == event.span)
        .collect();
    let [origin] = origins.as_slice() else {
        return Err("source operand origin has no unique actual Call".into());
    };
    let ExprKind::Call { callee, arguments } = &origin.expression.kind else {
        unreachable!()
    };
    let callee_token = event
        .callee_expression
        .ok_or_else(|| "source operand origin callee is absent".to_owned())?;
    let callee_fact = facts
        .expressions
        .get(callee_token)
        .ok_or_else(|| "source operand callee token is outside its arena".to_owned())?;
    let contexts: Vec<_> = facts
        .invocation_expressions
        .iter()
        .filter(|row| row.expression == callee_token)
        .collect();
    let [context] = contexts.as_slice() else {
        return Err("source operand callee context is not unique".into());
    };
    let context = context.context;
    require(
        callee_fact.span == callee.span
            && context.owner == event.owner
            && context.invocation == event.parent,
        "source operand callee is borrowed from another occurrence",
    )?;
    let preparations: Vec<_> = facts
        .call_arguments
        .iter()
        .filter(|row| row.source_event == event.id)
        .collect();
    let [preparation] = preparations.as_slice() else {
        return Err("source operand preparation is not unique".into());
    };
    require(
        preparation.target == event.target && preparation.evaluation_complete,
        "source operand preparation changed its actual target or completion",
    )?;
    let mut occupied = BTreeSet::new();
    let mut selected = None;
    for argument in arguments {
        let position=if let Some(label)=&argument.label {
            callee_fact.value.signature.as_ref().and_then(|parameters|parameters.iter().position(|parameter|
                matches!(&parameter.pattern.kind,ril_syntax::ast::PatternKind::Name(name) if name==label)))
        } else {(0..preparation.slots.len()).find(|slot|!occupied.contains(slot))}
            .ok_or_else(||"source operand label is outside its original public signature".to_owned())?;
        require(
            occupied.insert(position),
            "source operand position is written twice",
        )?;
        if position == slot as usize {
            selected = Some(&argument.value);
        }
    }
    require(
        preparation.supplied.len() == occupied.len(),
        "source operand preparation lost or added an actual input",
    )?;
    let syntax =
        selected.ok_or_else(|| "source operand selected slot is not supplied".to_owned())?;
    require(
        preparation.slots.get(slot as usize) == Some(&ArgumentSource::Supplied),
        "source operand selected slot is not its actual supplied input",
    )?;
    let token = preparation
        .supplied
        .get(&slot)
        .ok_or_else(|| "source operand root token is absent".to_owned())?;
    let value = facts
        .expressions
        .get(token.expression)
        .ok_or_else(|| "source operand root token is outside its arena".to_owned())?;
    require(
        token.allocation_epoch <= facts.allocation_history.len()
            && value.span == syntax.span
            && facts
                .invocation_expressions
                .iter()
                .filter(|row| {
                    row.expression == token.expression
                        && row.context == context
                        && row.argument_of == Some((event.id, slot))
                })
                .count()
                == 1,
        "source operand token borrowed another physical occurrence or context",
    )?;
    replay.input_operand_interval(event, slot as usize, token.expression, context, &sites)?;
    replay.original_source_key(syntax, &value.value, context, &sites)
}

pub(super) fn input_select_key(
    key: &ArgumentKey,
    selected: &BTreeMap<String, ArgumentKey>,
    depth: usize,
) -> Check<ArgumentKey> {
    fn text(value: &str, work: &mut usize) -> Check<String> {
        *work = work
            .checked_sub(value.len().div_ceil(32))
            .ok_or_else(|| "call input source text exceeds its substitution budget".to_owned())?;
        Ok(value.to_owned())
    }
    fn select(
        key: &ArgumentKey,
        selected: &BTreeMap<String, ArgumentKey>,
        work: &mut usize,
        depth: usize,
    ) -> Check<ArgumentKey> {
        require(
            depth < 64 && *work > 0,
            "call input substitution/composition exceeds its source budget",
        )?;
        *work -= 1;
        if let ArgumentKey::Binder { identity, .. } = key
            && let Some(replacement) = selected.get(identity)
            && replacement != key
        {
            return select(replacement, selected, work, depth + 1);
        }
        let mut child = |key: &ArgumentKey| select(key, selected, work, depth + 1);
        Ok(match key {
            ArgumentKey::Binder { identity, sort } => ArgumentKey::Binder {
                identity: text(identity, work)?,
                sort: *sort,
            },
            ArgumentKey::Closed(value) => ArgumentKey::Closed(text(value, work)?),
            ArgumentKey::Record { fields, row } => {
                let mut complete_fields = Vec::new();
                for (name, mode, key) in fields {
                    let name = text(name, work)?;
                    let key = select(key, selected, work, depth + 1)?;
                    complete_fields.push((name, *mode, key));
                }
                let mut fields = complete_fields;
                let mut row = row
                    .as_ref()
                    .map(|row| select(row, selected, work, depth + 1).map(Box::new))
                    .transpose()?;
                if let Some(tail) = row.take() {
                    match *tail {
                        ArgumentKey::Record {
                            fields: extra,
                            row: rest,
                        } => {
                            for field in extra {
                                require(
                                    !fields.iter().any(|old| old.0 == field.0),
                                    "input row remainder overlaps its genuine header fields",
                                )?;
                                fields.push(field);
                            }
                            row = rest;
                        }
                        other => row = Some(Box::new(other)),
                    }
                }
                fields.sort_by(|left, right| left.0.cmp(&right.0));
                ArgumentKey::Record { fields, row }
            }
            ArgumentKey::Array { length, element } => {
                let element = child(element)?;
                ArgumentKey::Array {
                    length: length
                        .as_ref()
                        .map(|length| text(length, work))
                        .transpose()?,
                    element: Box::new(element),
                }
            }
            ArgumentKey::Map { key, value } => ArgumentKey::Map {
                key: Box::new(child(key)?),
                value: Box::new(child(value)?),
            },
            ArgumentKey::Name { name, arguments } => {
                let arguments = arguments.iter().map(&mut child).collect::<Check<_>>()?;
                ArgumentKey::Name {
                    name: text(name, work)?,
                    arguments,
                }
            }
            ArgumentKey::Tuple(items) => {
                ArgumentKey::Tuple(items.iter().map(&mut child).collect::<Check<_>>()?)
            }
            ArgumentKey::Callable {
                parameters,
                result,
                annotations,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|(mode, key)| Ok((*mode, child(key)?)))
                    .collect::<Check<_>>()?;
                let result = Box::new(child(result)?);
                let annotations = annotations
                    .iter()
                    .map(|annotation| text(annotation, work))
                    .collect::<Check<_>>()?;
                ArgumentKey::Callable {
                    parameters,
                    result,
                    annotations,
                }
            }
        })
    }
    select(key, selected, &mut 4096, depth)
}

pub(super) fn has_sources(facts: &SemanticFacts) -> Check<bool> {
    let sites = super::explicit_named::source_sites(facts)?;
    if !sites.calls.is_empty() {
        return Ok(true);
    }
    // Inspect genuine source headers before any input table or selector can
    // erase the obligation. Alias expansion is deferred to Replay::normalize.
    let mut pending: Vec<_> = facts
        .functions
        .iter()
        .flat_map(|function| {
            function
                .syntax
                .parameters
                .iter()
                .filter_map(|parameter| parameter.ty.as_ref())
        })
        .collect();
    let mut work = LIMIT;
    let mut aliases = BTreeSet::new();
    while let Some(syntax) = pending.pop() {
        work = work
            .checked_sub(1)
            .ok_or_else(|| "call input source predicate exceeds its work bound".to_owned())?;
        match &syntax.kind {
            TypeKind::Callable { .. } | TypeKind::Array { .. } => return Ok(true),
            TypeKind::Optional(element) => pending.push(element),
            TypeKind::Tuple(items) => pending.extend(items),
            TypeKind::Map { key, value } => pending.extend([key.as_ref(), value.as_ref()]),
            TypeKind::Record { fields, row } => {
                pending.extend(fields.iter().map(|field| &field.ty));
                pending.extend(row.iter().map(Box::as_ref));
            }
            TypeKind::Name { path, arguments } => {
                pending.extend(arguments);
                let name = path.join("::");
                if aliases.insert(name.clone())
                    && let Some(declaration) = facts.external_type_declarations.get(&name)
                    && !declaration.nominal
                    && !declaration.opaque
                {
                    pending.extend(declaration.value.iter());
                }
            }
            TypeKind::Computation(_) => return Ok(true),
            _ => {}
        }
    }
    Ok(false)
}

impl Replay<'_> {
    fn input_row_equations(
        &self,
        raw: &ArgumentKey,
        actual: &ArgumentKey,
        selected: &BTreeMap<String, ArgumentKey>,
        owner: DefinitionId,
        work: &mut usize,
        depth: usize,
    ) -> Check {
        require(
            depth < 64 && *work > 0,
            "call input row equations exceed their source budget",
        )?;
        *work -= 1;
        match (raw, actual) {
            (
                ArgumentKey::Record { fields, row },
                ArgumentKey::Record {
                    fields: present,
                    row: actual_tail,
                },
            ) => {
                for (name, _, field) in fields {
                    if let Some((_, _, value)) = present.iter().find(|(label, _, _)| label == name)
                    {
                        self.input_row_equations(field, value, selected, owner, work, depth + 1)?;
                    }
                }
                if let Some(tail) = row
                    && let ArgumentKey::Binder { identity, .. } = &**tail
                {
                    let declarations: Vec<_> = self.facts.bound_rows.iter().filter(|row|
                        row.definition == owner && matches!(&row.identity, RowIdentity::Binder(actual) if actual == identity)).collect();
                    if let [declaration] = declarations.as_slice() {
                        let required: BTreeMap<_, _> = fields
                            .iter()
                            .map(|(name, mode, _)| {
                                let field = present
                                    .iter()
                                    .find(|(label, _, _)| label == name)
                                    .ok_or_else(|| {
                                        "call input row equation lost a genuine required field"
                                            .to_owned()
                                    })?;
                                require(
                                    *mode == field.1,
                                    "call input row equation changed a field mode",
                                )?;
                                Ok((name.clone(), (field.1, field.2.clone())))
                            })
                            .collect::<Check<_>>()?;
                        let tail = match actual_tail {
                            None => RowTail::Closed,
                            Some(tail) => {
                                let ArgumentKey::Binder { identity, .. } = &**tail else {
                                    return Err(
                                        "call input actual row has no canonical rigid tail".into(),
                                    );
                                };
                                let declarations: Vec<_> = self.facts.bound_rows.iter().filter(|row|
                                    matches!(&row.identity, RowIdentity::Binder(actual) if actual == identity)).collect();
                                let [declaration] = declarations.as_slice() else {
                                    return Err(
                                        "call input actual row has no unique genuine declaration"
                                            .into(),
                                    );
                                };
                                RowTail::Open(OpenTail {
                                    identity: declaration.identity.clone(),
                                    lacks: declaration.lacks.clone(),
                                })
                            }
                        };
                        let actual = Row {
                            fields: present
                                .iter()
                                .map(|(name, mode, key)| (name.clone(), (*mode, key.clone())))
                                .collect(),
                            tail,
                        };
                        let residual = OpenTail {
                            // Solver-only variable for this equation. Even a
                            // recursive activation's same declaration UID is
                            // rigid on the actual/caller side.
                            identity: RowIdentity::Fresh {
                                owner: format!("call-source:{}", owner.0),
                                ordinal: u64::from(declaration.id.0),
                            },
                            lacks: declaration.lacks.clone(),
                        };
                        let mut solver =
                            Solver::new("original call input", [residual.identity.clone()]);
                        if let RowTail::Open(tail) = &actual.tail {
                            solver
                                .declare_rigid(tail.identity.clone(), tail.lacks.clone())
                                .map_err(|_| {
                                    "call input actual tail changed its genuine rigid role"
                                        .to_owned()
                                })?;
                        }
                        let remainder = crate::sema::record_bound_shapes::entail(
                            &mut solver,
                            &required,
                            Some(&residual),
                            &actual,
                        )
                        .map_err(|_| {
                            "call input selected row does not solve its actual source equation"
                                .to_owned()
                        })?;
                        let fields: Vec<_> = remainder
                            .fields
                            .into_iter()
                            .map(|(name, (mode, key))| (name, mode, key))
                            .collect();
                        let tail = match remainder.tail {
                            RowTail::Closed => None,
                            RowTail::Open(tail) => {
                                let RowIdentity::Binder(identity) = tail.identity else {
                                    return Err(
                                        "call input row equation invented an unregistered tail"
                                            .into(),
                                    );
                                };
                                Some(Box::new(ArgumentKey::Binder {
                                    identity,
                                    sort: StaticBinderSort::Type,
                                }))
                            }
                        };
                        let remainder = match (fields, tail) {
                            (fields, Some(tail)) if fields.is_empty() => *tail,
                            (fields, tail) => ArgumentKey::Record { fields, row: tail },
                        };
                        let choice = selected
                            .get(identity)
                            .cloned()
                            .unwrap_or_else(|| (**row.as_ref().unwrap()).clone());
                        require(
                            choice == remainder,
                            "call input closed/open row selection differs from its independently solved actual remainder",
                        )?;
                    }
                }
            }
            (ArgumentKey::Tuple(left), ArgumentKey::Tuple(right)) => {
                for (left, right) in left.iter().zip(right) {
                    self.input_row_equations(left, right, selected, owner, work, depth + 1)?;
                }
            }
            (
                ArgumentKey::Array { element: left, .. },
                ArgumentKey::Array { element: right, .. },
            ) => self.input_row_equations(left, right, selected, owner, work, depth + 1)?,
            _ => {}
        }
        Ok(())
    }
    fn input_operand_interval(
        &self,
        event: &super::super::copy_contract::CopyCallEvent,
        slot: usize,
        token: usize,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check {
        require(
            self.facts
                .invocation_expressions
                .iter()
                .filter(|row| row.argument_of == Some((event.id, slot as u32)))
                .count()
                == 1,
            "call input event/slot has missing or duplicate root emissions",
        )?;
        let current: Vec<_> = sites
            .calls
            .iter()
            .filter(|site| Some(site.owner) == event.owner && site.expression.span == event.span)
            .collect();
        let [current] = current.as_slice() else {
            return Err("call input operand interval has no unique actual Source call".into());
        };
        let lower = event
            .callee_expression
            .ok_or_else(|| "call input interval lost its actual callee".to_owned())?;
        require(lower < token, "call input operand precedes its own callee")?;
        for next in &self.facts.copy_call_events {
            let Some(bound) = next.callee_expression.filter(|bound| *bound > lower) else {
                continue;
            };
            if next.owner != event.owner || next.parent != event.parent {
                continue;
            }
            if !self
                .facts
                .invocation_expressions
                .iter()
                .any(|row| row.expression == bound && row.context == context)
            {
                continue;
            }
            let later: Vec<_> = sites
                .calls
                .iter()
                .filter(|site| Some(site.owner) == next.owner && site.expression.span == next.span)
                .collect();
            let [later] = later.as_slice() else {
                return Err("call input interval has no unique following Source call".into());
            };
            let outer = current.expression.span;
            let inner = later.expression.span;
            // A genuine descendant call may run while this operand is being
            // evaluated. Another occurrence of the same AST is a boundary,
            // as is any following sibling; source span equality is not identity.
            let descendant = !std::ptr::eq(current.expression, later.expression)
                && outer.file == inner.file
                && outer.start <= inner.start
                && inner.end <= outer.end;
            if !descendant {
                require(
                    token < bound,
                    "call input operand borrowed a later sibling or repeated occurrence",
                )?;
            }
        }
        Ok(())
    }
    fn input_static_arguments<'a>(
        &'a self,
        call: &CopyInvocation,
    ) -> Check<&'a [StaticArgumentWitness]> {
        let matching: Vec<_> = self
            .facts
            .effect_invocations
            .iter()
            .filter(|row| row.invocation == Some(call.id))
            .collect();
        let [row] = matching.as_slice() else {
            return Err("call input has no unique actual static environment".into());
        };
        let function = self.function(call.target)?;
        require(
            row.function == call.target
                && row.site == call.span
                && row.arguments.len() == function.syntax.generics.len(),
            "call input static environment has missing owned positions",
        )?;
        for (index, actual) in row.arguments.iter().enumerate() {
            let binder = self.binder(call.target, index as u32)?;
            require(
                actual.definition == call.target
                    && actual.index as usize == index
                    && actual.binder == binder.identity,
                "call input static environment changed a genuine owned binder",
            )?;
        }
        Ok(&row.arguments)
    }

    pub(super) fn input_selected_keys(
        &self,
        call: &CopyInvocation,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let mut selected = BTreeMap::new();
        for argument in self.input_static_arguments(call)? {
            if !self.input_type_sort(&argument.binder)? {
                continue;
            }
            if let Some(key) = &argument.key {
                selected.insert(argument.binder.clone(), key.clone());
            } else if let Some(bound) = self.facts.record_bounds.iter().find(|bound| {
                bound.definition == call.target
                    && bound.binder == argument.binder
                    && bound.generic_index == argument.index
            }) {
                let caller = self.input_caller_context(call)?;
                let context = InvocationContext {
                    owner: Some(CallableOwner::Function(call.target)),
                    invocation: Some(call.id),
                    ..caller
                };
                let identities: Vec<_> = self
                    .facts
                    .scoped_source_identities
                    .iter()
                    .enumerate()
                    .filter(|(ordinal, source)| {
                        source.id.0 as usize == *ordinal
                            && source.required == bound.id
                            && source.binder == argument.binder
                            && source.context == context
                            && !source.occurrences.is_empty()
                    })
                    .collect();
                if let [(_, source)] = identities.as_slice() {
                    require(
                        source_reception::complete(&source.key, &mut 4096).is_some(),
                        "call input scoped actual Type identity is incomplete",
                    )?;
                    selected.insert(argument.binder.clone(), source.key.clone());
                }
            }
        }
        let observed = self
            .facts
            .effect_invocations
            .iter()
            .find(|row| row.invocation == Some(call.id))
            .expect("unique static observation");
        for argument in &observed.captured_arguments {
            if !self.input_type_sort(&argument.binder)? {
                continue;
            }
            if let Some(key) = &argument.key {
                selected.insert(argument.binder.clone(), key.clone());
            }
        }
        for check in &self.facts.generic_bound_checks {
            if check.context.invocation == Some(call.id) {
                require(
                    check.context.owner == Some(CallableOwner::Function(call.target)),
                    "call input structural selection borrowed another owner",
                )?;
                for (binder, key) in &check.substitutions {
                    if let Some(previous) = selected.insert(binder.clone(), key.clone()) {
                        require(
                            previous == *key,
                            "call input structural and static source selections disagree",
                        )?;
                    }
                }
            }
        }
        Ok(selected)
    }

    fn input_caller_context(&self, call: &CopyInvocation) -> Check<InvocationContext> {
        let rows: Vec<_> = self
            .facts
            .invocation_calls
            .iter()
            .filter(|row| row.invocation == call.id)
            .collect();
        let [row] = rows.as_slice() else {
            return Err("call input lacks a unique original caller context".into());
        };
        require(
            row.caller_owner == call.caller_owner,
            "call input caller owner differs from the actual instance",
        )?;
        Ok(InvocationContext {
            owner: row.caller_owner,
            invocation: call.parent,
            closure: row.caller_closure,
            closure_invocation: row.caller_closure_invocation,
            default_use: row.default_use,
            budget_validation: false,
        })
    }

    pub(super) fn original_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check<ArgumentKey> {
        self.original_source_key_inner(expression, value, context, sites, &mut 4096, 0)
    }

    fn original_source_key_inner(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<ArgumentKey> {
        require(
            depth < 64 && *work > 0,
            "original Source reconstruction exceeds its bound",
        )?;
        *work -= 1;
        let key = match self.raw_original_source_key(expression, value, context, sites, work, depth)
        {
            Ok(key) => key,
            Err(message) => self
                .symbolic_input_source_key(expression, value, context)
                .map_err(|detail| format!("{message}; {detail}"))?,
        };
        if self.source_optional_projection(expression, value, context)
            && let ArgumentKey::Name { name, arguments } = &key
            && name == "Option"
            && arguments.len() == 1
        {
            return Ok(arguments[0].clone());
        }
        Ok(key)
    }

    fn symbolic_input_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
    ) -> Check<ArgumentKey> {
        let Ty::Generic(identity) = &value.ty else {
            return Err("call input has no symbolic Type leaf".into());
        };
        self.type_binder(identity)?;
        require(
            self.facts
                .invocation_expressions
                .iter()
                .filter(|row| {
                    row.context == context
                        && self
                            .facts
                            .expressions
                            .get(row.expression)
                            .is_some_and(|fact| {
                                fact.span == expression.span
                                    && fact.value.cause == value.cause
                                    && fact.value.ty == value.ty
                            })
                })
                .count()
                == 1,
            "call input symbolic Source lost its exact actual expression observation",
        )?;
        if let Ok(key) = self.formal_input_path_key(expression, value.cause, context, &mut 4096, 0)
        {
            let call = context
                .invocation
                .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                .ok_or_else(|| "call input formal Source has no actual named entry".to_owned())?;
            let key = input_select_key(&key, &self.input_selected_keys(call)?, 0)?;
            require(
                matches!(&key, ArgumentKey::Binder {identity:actual,sort:StaticBinderSort::Type} if actual == identity),
                "call input formal Source selected another Type UID",
            )?;
            return Ok(key);
        }
        let ExprKind::Index { base, .. } = &expression.kind else {
            return Err("call input symbolic leaf has no proven Source operation".into());
        };
        let cause = self
            .facts
            .explanations
            .causes
            .get(value.cause.0 as usize)
            .ok_or_else(|| "call input symbolic index lost its actual cause".to_owned())?;
        let projections: Vec<_> = self
            .facts
            .generic_bound_projections
            .iter()
            .filter(|projection| {
                projection.context == context
                    && projection.span == base.span
                    && cause.parents.contains(&projection.output.value.cause)
            })
            .collect();
        let [projection] = projections.as_slice() else {
            return Err(
                "call input symbolic index has no unique actual bound member Source".into(),
            );
        };
        let bound = self
            .facts
            .record_bounds
            .get(projection.required.0 as usize)
            .filter(|bound| bound.id == projection.required)
            .ok_or_else(|| {
                "call input symbolic index lost its real bound declaration".to_owned()
            })?;
        let Slot::Field(label) = &projection.slot else {
            return Err("call input symbolic index borrowed a nonmember projection".into());
        };
        let field = bound
            .fields
            .iter()
            .find(|field| &field.label == label)
            .ok_or_else(|| {
                "call input symbolic index is absent from its actual bound".to_owned()
            })?;
        let raw = self.normalized_key(&field.syntax, &bound.scope)?;
        require(
            raw == field.key,
            "call input symbolic index changed its original declared field coordinates",
        )?;
        let call = context
            .invocation
            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
            .filter(|call| Some(CallableOwner::Function(call.target)) == context.owner)
            .ok_or_else(|| "call input symbolic index has no actual named scope".to_owned())?;
        let key = input_select_key(&raw, &self.input_selected_keys(call)?, 0)?;
        let ArgumentKey::Array { element, .. } = key else {
            return Err("call input symbolic index's actual source is not an array".into());
        };
        require(
            matches!(&*element, ArgumentKey::Binder { identity:actual, sort:StaticBinderSort::Type } if actual == identity),
            "call input symbolic index borrowed a different genuine Type identity",
        )?;
        Ok(*element)
    }

    fn formal_input_path_key(
        &self,
        expression: &Expr,
        cause: CauseId,
        context: InvocationContext,
        work: &mut usize,
        depth: usize,
    ) -> Check<ArgumentKey> {
        require(
            depth < 64 && *work > 0,
            "call input formal Source path exceeds its bound",
        )?;
        *work -= 1;
        let matching: Vec<_> = self
            .facts
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                if row.context != context {
                    return None;
                }
                self.facts
                    .expressions
                    .get(row.expression)
                    .filter(|fact| fact.span == expression.span && fact.value.cause == cause)
            })
            .collect();
        let [fact] = matching.as_slice() else {
            return Err("call input formal Source path lost its exact observation".into());
        };
        if let ExprKind::Name(name) = &expression.kind {
            let binding = fact
                .value
                .sources
                .first()
                .and_then(|id| self.facts.bindings.get(*id))
                .filter(|binding| binding.parameter && binding.name == *name)
                .ok_or_else(|| {
                    "call input formal Source root is not its genuine parameter".to_owned()
                })?;
            let Some(CallableOwner::Function(owner)) = context.owner else {
                return Err("call input formal Source has no named owner".into());
            };
            let function = self.function(owner)?;
            let parameter = function.syntax.parameters.iter().find(|parameter| parameter.pattern.span == binding.span
                && matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(actual) if actual == name))
                .ok_or_else(|| "call input formal Source differs from its real header index".to_owned())?;
            let call = context
                .invocation
                .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                .filter(|call| call.target == owner)
                .ok_or_else(|| "call input formal Source root lacks its whole entry".to_owned())?;
            self.read_parameter_reception(
                &fact.value,
                expression,
                context,
                binding.owner,
                call.entry_allocation_epoch,
            )?;
            return self.normalized_key(
                parameter
                    .ty
                    .as_ref()
                    .ok_or_else(|| "call input formal Source has no written type".to_owned())?,
                &self.scope(owner)?,
            );
        }
        require(
            self.facts.explanations.kinds.get(cause.0 as usize)
                == Some(&super::super::facts::CauseKind::Projection),
            "call input formal Source path lacks a genuine projection cause",
        )?;
        let parent = *self
            .facts
            .explanations
            .causes
            .get(cause.0 as usize)
            .and_then(|cause| cause.parents.first())
            .ok_or_else(|| "call input formal Source path lost its actual parent".to_owned())?;
        let (base, step) = match &expression.kind {
            ExprKind::Index { base, .. } => (base.as_ref(), None),
            ExprKind::Field { base, field, .. } => {
                (base.as_ref(), Some(Slot::Field(field.clone())))
            }
            ExprKind::ComputedField { base, key } => {
                let ExprKind::Literal(Literal::Integer(text)) = &key.kind else {
                    return Err("call input formal tuple path lacks a literal coordinate".into());
                };
                let coordinate = text.parse::<u32>().map_err(|_| {
                    "call input formal tuple coordinate is not canonical".to_owned()
                })?;
                require(
                    self.facts
                        .invocation_expressions
                        .iter()
                        .filter(|row| {
                            row.context == context
                                && self
                                    .facts
                                    .expressions
                                    .get(row.expression)
                                    .is_some_and(|fact| {
                                        fact.span == key.span
                                            && fact.value.constant
                                                == Some(super::super::model::Constant::Integer(
                                                    i128::from(coordinate),
                                                ))
                                    })
                        })
                        .count()
                        == 1,
                    "call input formal tuple coordinate lost its actual observation",
                )?;
                (base.as_ref(), Some(Slot::Tuple(coordinate)))
            }
            _ => return Err("call input formal Source path has an unsupported operation".into()),
        };
        let key = self.formal_input_path_key(base, parent, context, work, depth + 1)?;
        match (key, step) {
            (ArgumentKey::Array { element, .. }, None) => Ok(*element),
            (ArgumentKey::Tuple(items), Some(Slot::Tuple(index))) => items
                .get(index as usize)
                .cloned()
                .ok_or_else(|| "call input formal tuple path is outside its header".to_owned()),
            (ArgumentKey::Record { fields, .. }, Some(Slot::Field(label))) => fields
                .into_iter()
                .find(|field| field.0 == label)
                .map(|field| field.2)
                .ok_or_else(|| "call input formal field is absent from its header".to_owned()),
            (ArgumentKey::Binder { identity, .. }, Some(Slot::Field(label))) => {
                let bound = self
                    .facts
                    .record_bounds
                    .iter()
                    .find(|bound| bound.binder == identity)
                    .ok_or_else(|| {
                        "call input formal field has no real structural constraint".to_owned()
                    })?;
                let field = bound
                    .fields
                    .iter()
                    .find(|field| field.label == label)
                    .ok_or_else(|| {
                        "call input formal field is absent from its real bound".to_owned()
                    })?;
                let key = self.normalized_key(&field.syntax, &bound.scope)?;
                require(
                    key == field.key,
                    "call input formal field changed its actual declared type",
                )?;
                Ok(key)
            }
            _ => Err("call input formal Source shape does not support this actual path".into()),
        }
    }

    fn source_optional_projection(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
    ) -> bool {
        self.facts.invocation_witnesses.iter().filter(|row| {
            row.context == context && row.span == expression.span
                && matches!(&row.kind, super::super::effect_identity::InvocationWitnessKind::ImplicitUnwrap(proof)
                    if proof.cause == value.cause && proof.depth == 1 && proof.tags == ["Some"])
        }).count() == 1
            && self.facts.explanations.kinds.get(value.cause.0 as usize)
                == Some(&super::super::facts::CauseKind::Restriction)
    }

    fn raw_original_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<ArgumentKey> {
        if let Some(key) = self.storage_binding_source_key(expression, value, context, sites) {
            return key;
        }
        if value.source_type_witness.is_none()
            && let Some(key) =
                self.original_carrier_source_key(expression, value, context, sites, work, depth)?
        {
            return Ok(key);
        }
        if let ExprKind::Name(name) = &expression.kind
            && self.facts.constant_pool.references.contains_key(name)
        {
            let original = self
                .facts
                .constant_pool
                .source_views
                .get(name)
                .ok_or_else(|| {
                    "constant reference has no sealed original Source view".to_owned()
                })?;
            require(
                original.validate_closed() && value.source_type_witness.as_ref() == Some(original),
                "constant reference changed its original per-reference Source view",
            )?;
            return self.normalized_key(&original.syntax, &BoundScope::default());
        }
        if let Some(key) = super::super::checker::original_canonical_builtin_source_key(
            self.facts, value, expression, context,
        ) {
            return Ok(key);
        }
        if let ExprKind::Name(name) = &expression.kind
            && value.sources.len() == 1
        {
            let binding = value
                .sources
                .iter()
                .next()
                .and_then(|id| self.facts.bindings.get(*id))
                .ok_or_else(|| "call input source Name has no actual binding".to_owned())?;
            require(
                binding.name == *name,
                "call input source borrowed another Name binding",
            )?;
            if binding.parameter {
                if matches!(context.owner, Some(CallableOwner::Lambda(_))) {
                    return self.lambda_formal_source_key(expression, value, context, sites);
                }
                let Some(CallableOwner::Function(owner)) = context.owner else {
                    return Err("call input parameter has no genuine named header".into());
                };
                let function = self.function(owner)?;
                let (parameter_index, parameter) = function.syntax.parameters.iter().enumerate().find(|(_,parameter)|
                    parameter.pattern.span == binding.span && matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(actual) if actual == name))
                    .ok_or_else(|| "call input parameter Name differs from its actual header".to_owned())?;
                let scope = self.scope(owner)?;
                let key = self.normalized_key(
                    parameter.ty.as_ref().ok_or_else(|| {
                        "call input header has no complete type source".to_owned()
                    })?,
                    &scope,
                )?;
                if let Some(id) = context.default_use {
                    let default = self
                        .facts
                        .default_uses
                        .get(id.0 as usize)
                        .filter(|default| default.id == id)
                        .ok_or_else(|| {
                            "call input earlier formal lost its actual default identity".to_owned()
                        })?;
                    require(
                        default.owner == context.owner
                            && default.target == Some(owner)
                            && parameter_index < default.parameter as usize
                            && default.evaluation_complete
                            && default.status == CopyInvocationStatus::Completed,
                        "call input default borrowed a later or unrelated formal header",
                    )?;
                    let [entered] = default.entered.as_slice() else {
                        return Err(
                            "call input default has no unique receiving named instance".into()
                        );
                    };
                    let instance = self
                        .facts
                        .copy_invocations
                        .get(entered.0 as usize)
                        .filter(|call| call.id == *entered && call.target == owner)
                        .ok_or_else(|| {
                            "call input default entry differs from its actual owner".to_owned()
                        })?;
                    require(
                        instance.caller_activation.is_some_and(|parent| {
                            self.facts.scope_parents.get(&binding.owner) == Some(&parent)
                        }),
                        "call input earlier formal belongs to another default activation",
                    )?;
                    let selected = self.input_selected_keys(instance)?;
                    for argument in default.arguments.iter().chain(&default.captured_arguments) {
                        require(
                            argument
                                .key
                                .as_ref()
                                .is_some_and(|key| selected.get(&argument.binder) == Some(key)),
                            "call input default and body selected different source identities",
                        )?;
                    }
                    return input_select_key(&key, &selected, 0);
                }
                let instance = context
                    .invocation
                    .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                    .filter(|call| call.target == owner)
                    .ok_or_else(|| {
                        "call input formal has no original header instance".to_owned()
                    })?;
                // This independently checks the real root/participants/epoch,
                // rather than consulting the binding's final mutable Value.
                if parameter.mode == ril_syntax::ast::ParameterMode::Read {
                    self.read_parameter_reception(
                        value,
                        expression,
                        context,
                        binding.owner,
                        instance.entry_allocation_epoch,
                    )?;
                    let original = &instance.arguments[parameter_index].1.value;
                    let original = if self.source_optional_projection(expression, value, context) {
                        original.option_payload.as_deref().ok_or_else(|| {
                            "call input optional projection lacks its original Some payload"
                                .to_owned()
                        })?
                    } else {
                        original
                    };
                    require(
                        value.callables == original.callables,
                        "call input readonly formal changed its original callable targets",
                    )?;
                } else {
                    let matching: Vec<_> = self
                        .facts
                        .invocation_loan_starts
                        .iter()
                        .filter(|loan| {
                            loan.owner == context.owner
                                && loan.named == Some(instance.id)
                                && loan.parameter as usize == parameter_index
                                && loan.activation == binding.owner
                                && loan.bindings.contains(value.sources.first().unwrap())
                        })
                        .collect();
                    let [loan] = matching.as_slice() else {
                        return Err(
                            "call input mutable formal lost its exact original loan entry".into(),
                        );
                    };
                    let entry = instance.arguments.get(parameter_index).ok_or_else(|| {
                        "call input mutable formal lost its whole entry".to_owned()
                    })?;
                    require(
                        loan.retained
                            == (parameter.mode == ril_syntax::ast::ParameterMode::SharedMut)
                            && loan.origins == entry.1.value.origins
                            && loan.allocation_epoch == instance.entry_allocation_epoch
                            && value.origins == loan.origins
                            && value.participants
                                == BTreeSet::from([super::super::facts::Participant::Loan(
                                    loan.loan,
                                )])
                            && binding.forwarded == entry.1.value.sources,
                        "call input mutable formal changed its source or actual loan participant",
                    )?;
                }
                return input_select_key(&key, &self.input_selected_keys(instance)?, 0);
            }
            let declared: Vec<_> = sites
                .bindings
                .iter()
                .filter(|site| site.binding.pattern.span == binding.span)
                .collect();
            if let [declaration] = declared.as_slice()
                && let Some(syntax) = &declaration.binding.ty
            {
                let scope = self.lambda_input_scope(declaration.owner)?;
                let key = self.normalized_key(syntax, &scope)?;
                let selected = self.binding_source_selections(binding, declaration.owner)?;
                return input_select_key(&key, &selected, 0);
            }
            if let [crate::sema::model::Callable::Named(index)] = value.callables.as_slice() {
                let function = self
                    .facts
                    .functions
                    .get(*index)
                    .ok_or_else(|| "call input function source target is missing".to_owned())?;
                require(
                    binding.span == function.syntax.span && binding.name == function.syntax.name,
                    "call input callable source is an unproved alias",
                )?;
                let mut parameters = function.syntax.parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                let syntax = TypeExpr {
                    text: String::new(),
                    span: expression.span,
                    kind: TypeKind::Callable {
                        parameters,
                        result: function.syntax.return_type.clone().map(Box::new),
                        annotations: function.syntax.annotations.clone(),
                    },
                };
                return self.input_callable_source_key(&syntax, &self.scope(function.definition)?);
            }
        }
        if let Some(key) = self.inferred_lambda_source_key(expression, value, context, sites)? {
            return Ok(key);
        }
        if let ExprKind::Call {
            callee: callee_syntax,
            ..
        } = &expression.kind
        {
            let calls: Vec<_> = self
                .facts
                .copy_call_events
                .iter()
                .filter(|call| {
                    call.span == expression.span
                        && call.owner == context.owner
                        && call.parent == context.invocation
                })
                .collect();
            if let [source] = calls.as_slice()
                && let Some(target) = source.target
            {
                let function = self.function(target)?;
                if let Some(result) = &function.syntax.return_type {
                    let instances: Vec<_> = self
                        .facts
                        .copy_invocations
                        .iter()
                        .filter(|call| call.source_event == Some(source.id))
                        .filter(|call| {
                            call.result.as_ref().is_some_and(|result| {
                                self.producing_result_causes(value.cause)
                                    .is_ok_and(|causes| causes.contains(&result.value.cause.0))
                            })
                        })
                        .collect();
                    if let [instance] = instances.as_slice() {
                        let key = self.normalized_key(result, &self.scope(target)?)?;
                        let selected = self.producing_input_selected_keys(instance, value)?;
                        let declared = input_select_key(&key, &selected, 0)?;
                        let callee = source
                            .callee_expression
                            .and_then(|index| self.facts.expressions.get(index))
                            .ok_or_else(|| {
                                "call input returned Source lost its exact callee".to_owned()
                            })?;
                        require(
                            callee.span == callee_syntax.span
                                && self
                                    .facts
                                    .invocation_expressions
                                    .iter()
                                    .filter(|row| {
                                        Some(row.expression) == source.callee_expression
                                            && row.context == context
                                    })
                                    .count()
                                    == 1,
                            "call input returned Source borrowed another callee context",
                        )?;
                        let mut base = callee_syntax.as_ref();
                        while let ExprKind::Generic { base: inner, .. } = &base.kind {
                            base = inner;
                        }
                        let public =
                            self.original_source_key(base, &callee.value, context, sites)?;
                        let ArgumentKey::Callable { result: public, .. } = public else {
                            return Err("call input returned Source has no public Fn result".into());
                        };
                        let public = input_select_key(&public, &selected, 0)?;
                        self.validate_producing_result_transport(instance, value)?;
                        if let Ty::Generic(identity) = &value.ty {
                            self.type_binder(identity)?;
                            require(
                                matches!(&public, ArgumentKey::Binder { identity:actual,sort:StaticBinderSort::Type } if actual == identity)
                                    && declared == public,
                                "call input returned Source differs from its genuine selected Type UID",
                            )?;
                        }
                        return Ok(public);
                    }
                }
            }
        }
        if value.source_type_witness.is_none()
            && let Some(key) =
                self.original_composite_source_key(expression, value, context, sites, work, depth)?
        {
            return Ok(key);
        }
        let witness = value
            .source_type_witness
            .as_ref()
            .ok_or_else(|| "call input has no complete original source view".to_owned())?;
        require(
            witness.validate_closed()
                && crate::sema::source_type_validation::resolved_names(
                    witness,
                    &self.facts.external_type_declarations,
                ),
            "call input complete witness has inconsistent or unresolved source names",
        )?;
        self.normalized_key(&witness.syntax, &BoundScope::default())
    }

    pub(super) fn input_value_transport(
        &self,
        original: &Value,
        actual: &Value,
        from: usize,
        to: usize,
    ) -> Check {
        require(
            from <= to && to <= self.facts.allocation_history.len(),
            "call input source epoch is outside its actual interval",
        )?;
        let mut origins = original.origins.clone();
        for &(recent, older) in &self.facts.allocation_history[from..to] {
            if origins.nodes.remove(&recent) {
                origins.nodes.insert(older);
            }
            for alternatives in origins.choices.values_mut() {
                for alternative in alternatives {
                    if alternative.remove(&recent) {
                        alternative.insert(older);
                    }
                }
            }
        }
        require(
            origins == actual.origins
                && original.sources == actual.sources
                && original.results == actual.results
                && original.outer_results == actual.outer_results
                && original.cause == actual.cause
                && original.source_type_witness == actual.source_type_witness,
            "call input entry differs from its original physical expression or source schema",
        )
    }

    pub(super) fn call_input_sources(&self) -> Result<(), Failure> {
        let fallback = self
            .facts
            .functions
            .first()
            .map(|function| function.syntax.span)
            .unwrap_or(Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            });
        let sites = super::explicit_named::source_sites(self.facts)
            .map_err(|message| (fallback, None, message))?;
        self.producing_result_contexts(&sites)
            .map_err(|message| (fallback, None, message))?;
        // The frozen Program, rather than an arena's current contents, supplies
        // the coverage obligation. A deleted event/instance cannot make a real
        // invocation disappear from this replay.
        for site in &sites.calls {
            require(
                self.facts.copy_call_events.iter().any(|event| {
                    event.owner == Some(site.owner) && event.span == site.expression.span
                }),
                "call input Source lost every actual event for a genuine Call",
            )
            .map_err(|message| (site.expression.span, None, message))?;
        }
        for event in &self.facts.copy_call_events {
            let run = || -> Check {
                let matching: Vec<_> = sites
                    .calls
                    .iter()
                    .filter(|site| {
                        event.owner == Some(site.owner) && event.span == site.expression.span
                    })
                    .collect();
                let [site] = matching.as_slice() else {
                    return Err(
                        "call input event has no unique genuine Call in its real owner".into(),
                    );
                };
                let ExprKind::Call { callee: syntax, .. } = &site.expression.kind else {
                    unreachable!()
                };
                let token = event
                    .callee_expression
                    .ok_or_else(|| "call input event lost its actual callee token".to_owned())?;
                let callee = self.facts.expressions.get(token).ok_or_else(|| {
                    "call input callee token is outside the expression arena".to_owned()
                })?;
                let rows: Vec<_> = self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|row| row.expression == token)
                    .collect();
                let [row] = rows.as_slice() else {
                    return Err("call input callee lacks its unique emission context".into());
                };
                require(
                    callee.span == syntax.span
                        && row.context.owner == event.owner
                        && row.context.invocation == event.parent,
                    "call input callee token belongs to another Source occurrence or caller",
                )?;
                let targets: BTreeSet<_> = callee
                    .value
                    .callables
                    .iter()
                    .filter_map(|callable| {
                        if let crate::sema::model::Callable::Named(index) = callable {
                            self.facts
                                .functions
                                .get(*index)
                                .map(|function| function.definition)
                        } else {
                            None
                        }
                    })
                    .collect();
                let expected_target = if callee.value.callables.len() == 1 && targets.len() == 1 {
                    targets.first().copied()
                } else {
                    None
                };
                require(
                    event.target == expected_target,
                    "call input event changed its actual named callee identity",
                )?;
                require(
                    self.facts
                        .copy_invocations
                        .iter()
                        .filter(|call| call.source_event == Some(event.id))
                        .all(|call| targets.contains(&call.target)),
                    "call input instance targets a function absent from its genuine callee",
                )?;
                if let Some(target) = expected_target
                    && let ExprKind::Name(name) = &syntax.kind
                    && callee.value.sources.len() == 1
                {
                    let binding = callee
                        .value
                        .sources
                        .first()
                        .and_then(|id| self.facts.bindings.get(*id))
                        .ok_or_else(|| {
                            "call input named callee lost its actual source binding".to_owned()
                        })?;
                    require(
                        binding.name == *name,
                        "call input named callee borrowed another Source Name",
                    )?;
                    if self
                        .facts
                        .functions
                        .iter()
                        .any(|function| function.syntax.span == binding.span)
                    {
                        let function = self.function(target)?;
                        require(
                            !binding.parameter
                                && binding.span == function.syntax.span
                                && binding.name == function.syntax.name,
                            "call input named callee changed its genuine declaration identity",
                        )?;
                    }
                }
                for target in targets {
                    require(
                        self.facts.copy_invocations.iter().any(|call| {
                            call.source_event == Some(event.id) && call.target == target
                        }) || self.call_input_terminal_operand(
                            event,
                            site.expression,
                            row.context,
                        )?,
                        "call input Source lost an actual named body instance",
                    )?;
                }
                self.constructor_input_sources(
                    event,
                    site.expression,
                    &callee.value,
                    row.context,
                    &sites,
                )?;
                self.storage_input_sources(
                    event,
                    site.expression,
                    &callee.value,
                    row.context,
                    &sites,
                )?;
                self.open_carrier_source_result(
                    event,
                    site.expression,
                    &callee.value,
                    row.context,
                    &sites,
                )?;
                if expected_target.is_none()
                    && callee.value.callables.iter().any(|callable| {
                        !matches!(
                            callable,
                            crate::sema::model::Callable::Builtin(_)
                                | crate::sema::model::Callable::Constructor(_)
                        )
                    })
                {
                    self.public_input_sources(
                        event,
                        site.expression,
                        &callee.value,
                        row.context,
                        &sites,
                    )?;
                }
                Ok(())
            };
            run().map_err(|message| (event.span, None, message))?;
        }
        for call in &self.facts.copy_invocations {
            let run = || -> Check {
                let function = self.function(call.target)?;
                if function.syntax.parameters.is_empty() {
                    return Ok(());
                }
                // Genuine header entries do not claim an actual input receipt.
                if call.span == function.syntax.span
                    && call.parent.is_none()
                    && call.source_event.is_none()
                    && call.caller_owner.is_none()
                    && call.caller_activation.is_none()
                {
                    return Ok(());
                }
                if function.syntax.generics.is_empty() {
                    let scope = self.scope(call.target)?;
                    let needs = function
                        .syntax
                        .parameters
                        .iter()
                        .filter_map(|parameter| parameter.ty.as_ref())
                        .map(|syntax| {
                            self.normalized_key(syntax, &scope).map(|key| {
                                source_reception::sensitive(&key, &mut 4096) != Some(false)
                            })
                        })
                        .collect::<Check<Vec<_>>>()?;
                    if needs.iter().all(|needed| !needed) {
                        return Ok(());
                    }
                }
                let scope = self.scope(call.target)?;
                let selected = self.input_selected_keys(call)?;
                let expected: Vec<_> = function
                    .syntax
                    .parameters
                    .iter()
                    .map(|parameter| {
                        parameter.ty.as_ref().map_or(Ok(None), |syntax| {
                            self.input_parameter_source_key(syntax, &scope)?
                                .map(|key| input_select_key(&key, &selected, 0))
                                .transpose()
                        })
                    })
                    .collect::<Check<_>>()?;
                let needs = expected
                    .iter()
                    .flatten()
                    .map(|key| {
                        source_reception::sensitive(key, &mut 4096)
                            .ok_or_else(|| "call input formal source is incomplete".to_owned())
                    })
                    .collect::<Check<Vec<_>>>()?
                    .into_iter()
                    .any(|needed| needed);
                if !needs {
                    return Ok(());
                }
                let event = call
                    .source_event
                    .and_then(|id| {
                        self.facts
                            .copy_call_events
                            .get(id.0 as usize)
                            .filter(|event| event.id == id)
                    })
                    .ok_or_else(|| "call input has no actual application identity".to_owned())?;
                let context = self.input_caller_context(call)?;
                require(
                    event.owner == context.owner
                        && event.parent == context.invocation
                        && event.span == call.span,
                    "call input source event belongs to another actual caller",
                )?;
                let source_sites: Vec<_> = sites
                    .calls
                    .iter()
                    .filter(|site| {
                        Some(site.owner) == event.owner && site.expression.span == event.span
                    })
                    .collect();
                let [site] = source_sites.as_slice() else {
                    return Err("call input has no unique real Call AST in its owner".into());
                };
                let ExprKind::Call { arguments, .. } = &site.expression.kind else {
                    unreachable!()
                };
                let preparations: Vec<_> = self
                    .facts
                    .call_arguments
                    .iter()
                    .filter(|row| row.source_event == event.id)
                    .collect();
                let [preparation] = preparations.as_slice() else {
                    return Err("call input has no unique actual argument preparation".into());
                };
                require(
                    preparation.target == event.target
                        && preparation.evaluation_complete
                        && preparation.slots.len() == function.syntax.parameters.len()
                        && call.arguments.len() == function.syntax.parameters.len(),
                    "call input preparation changed its target, completion or full arity",
                )?;
                let callee = event
                    .callee_expression
                    .and_then(|index| self.facts.expressions.get(index))
                    .ok_or_else(|| "call input has no physical callee expression".to_owned())?;
                let parameters = callee
                    .value
                    .signature
                    .as_ref()
                    .unwrap_or(&function.syntax.parameters);
                let mut written = BTreeMap::new();
                for argument in arguments {
                    let index = if let Some(label) = &argument.label {
                        parameters.iter().position(|parameter| matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(name) if name == label))
                    } else { (0..parameters.len()).find(|index| !written.contains_key(index)) }
                        .ok_or_else(|| "call input label/position is outside its actual public signature".to_owned())?;
                    require(
                        written.insert(index, &argument.value).is_none(),
                        "call input parameter is supplied twice",
                    )?;
                }
                require(
                    preparation.supplied.len() == written.len(),
                    "call input supplied tokens have missing or excess actual slots",
                )?;
                for (index, expected) in expected.iter().enumerate() {
                    let Some(expected) = expected else {
                        continue;
                    };
                    if source_reception::sensitive(expected, &mut 4096) == Some(false) {
                        continue;
                    }
                    let entry = call.arguments.get(index).ok_or_else(|| {
                        "call input entry lacks its original whole argument".to_owned()
                    })?;
                    let (syntax, original, epoch, source_context) = match preparation
                        .slots
                        .get(index)
                    {
                        Some(ArgumentSource::Supplied) => {
                            let syntax = written.get(&index).ok_or_else(|| {
                                "call input supplied slot has no real written argument".to_owned()
                            })?;
                            let token =
                                preparation.supplied.get(&(index as u32)).ok_or_else(|| {
                                    "call input supplied slot lost its actual expression token"
                                        .to_owned()
                                })?;
                            let expression = self
                                .facts
                                .expressions
                                .get(token.expression)
                                .ok_or_else(|| {
                                    "call input supplied expression token is missing".to_owned()
                                })?;
                            require(
                                expression.span == syntax.span
                                    && event
                                        .callee_expression
                                        .is_some_and(|callee| callee < token.expression)
                                    && self
                                        .facts
                                        .invocation_expressions
                                        .iter()
                                        .filter(|row| {
                                            row.expression == token.expression
                                                && row.context == context
                                                && row.argument_of == Some((event.id, index as u32))
                                        })
                                        .count()
                                        == 1,
                                "call input supplied token belongs to another Source occurrence or caller",
                            )?;
                            self.input_operand_interval(
                                event,
                                index,
                                token.expression,
                                context,
                                &sites,
                            )?;
                            (*syntax, &expression.value, token.allocation_epoch, context)
                        }
                        Some(ArgumentSource::Default(id)) => {
                            require(
                                !preparation.supplied.contains_key(&(index as u32)),
                                "call input default slot borrowed a supplied token",
                            )?;
                            let default = self
                                .facts
                                .default_uses
                                .get(id.0 as usize)
                                .filter(|default| default.id == *id)
                                .ok_or_else(|| {
                                    "call input default identity is missing".to_owned()
                                })?;
                            require(
                                default.origin == DefaultOrigin::Call(event.id)
                                    && default.target == Some(call.target)
                                    && default.parameter as usize == index
                                    && default.caller == context
                                    && default.entered.contains(&call.id)
                                    && default.evaluation_complete
                                    && default.status == CopyInvocationStatus::Completed,
                                "call input default borrowed another event, target, parameter or completed body",
                            )?;
                            let syntax = function.syntax.parameters[index]
                                .default
                                .as_ref()
                                .ok_or_else(|| {
                                    "call input default has no genuine declared expression"
                                        .to_owned()
                                })?;
                            require(
                                default.span == syntax.span,
                                "call input default source differs from its real parameter",
                            )?;
                            let snapshot = default.result.as_ref().ok_or_else(|| {
                                "call input default has no original result snapshot".to_owned()
                            })?;
                            (
                                syntax,
                                &snapshot.value,
                                default.result_allocation_epoch.ok_or_else(|| {
                                    "call input default has no actual completion epoch".to_owned()
                                })?,
                                InvocationContext {
                                    owner: default.owner,
                                    default_use: Some(*id),
                                    ..default.caller
                                },
                            )
                        }
                        _ => {
                            return Err(
                                "call input full-source slot is missing its physical input source"
                                    .into(),
                            );
                        }
                    };
                    self.input_value_transport(
                        original,
                        &entry.1.value,
                        epoch,
                        call.entry_allocation_epoch,
                    )?;
                    let actual =
                        self.original_source_key(syntax, original, source_context, &sites)?;
                    let raw = self.normalized_key(
                        function.syntax.parameters[index].ty.as_ref().unwrap(),
                        &scope,
                    )?;
                    self.input_row_equations(&raw, &actual, &selected, call.target, &mut 4096, 0)?;
                    let fresh =
                        source_reception::construction(syntax, &mut 4096).ok_or_else(|| {
                            "call input construction Source exceeds its work bound".to_owned()
                        })?;
                    require(
                        source_reception::compatible(expected, &actual, Some(&fresh), &mut 4096)
                            == Some(true),
                        "call input original whole source does not prove its receiving coordinates",
                    )?;
                }
                Ok(())
            };
            run().map_err(|message| (call.span, None, message))?;
        }
        Ok(())
    }

    fn public_input_sources(
        &self,
        event: &super::super::copy_contract::CopyCallEvent,
        syntax: &Expr,
        callee: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check {
        let ExprKind::Call {
            callee: callee_syntax,
            arguments,
        } = &syntax.kind
        else {
            unreachable!()
        };
        let parameters = self.public_input_source_keys(callee_syntax, callee, context, sites)?;
        if parameters.iter().all(|key| {
            key.as_ref()
                .is_none_or(|key| source_reception::sensitive(key, &mut 4096) == Some(false))
        }) {
            return Ok(());
        }
        let rows: Vec<_> = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id)
            .collect();
        let [preparation] = rows.as_slice() else {
            return Err("public callable input lost its actual preparation".into());
        };
        require(
            preparation.target == event.target
                && preparation.evaluation_complete
                && preparation.slots.len() == parameters.len(),
            "public callable preparation changed its target, arity or completion",
        )?;
        let mut written = BTreeMap::new();
        for argument in arguments {
            let slot = if let Some(label) = &argument.label {
                callee.signature.as_ref().and_then(|parameters| parameters.iter().position(|parameter|
                    matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(name) if name == label)))
            } else { (0..parameters.len()).find(|slot| !written.contains_key(slot)) }
                .ok_or_else(|| "public callable Source label is outside its actual signature".to_owned())?;
            require(
                written.insert(slot, &argument.value).is_none(),
                "public callable Source supplies one slot twice",
            )?;
        }
        require(
            preparation.supplied.len() == written.len(),
            "public callable Source lost or added a supplied operand",
        )?;
        for (slot, expected) in parameters.iter().enumerate() {
            let Some(expected) = expected else { continue };
            if source_reception::sensitive(expected, &mut 4096) == Some(false) {
                continue;
            }
            let (actual_syntax, value, actual_context) = match preparation.slots.get(slot) {
                Some(ArgumentSource::Supplied) => {
                    let actual_syntax = written.get(&slot).ok_or_else(|| {
                        "public callable input lacks its written operand".to_owned()
                    })?;
                    let token = preparation.supplied.get(&(slot as u32)).ok_or_else(|| {
                        "public callable input lost its actual expression token".to_owned()
                    })?;
                    let value = self
                        .facts
                        .expressions
                        .get(token.expression)
                        .ok_or_else(|| {
                            "public callable input token is outside its arena".to_owned()
                        })?;
                    require(
                        value.span == actual_syntax.span
                            && token.allocation_epoch <= self.facts.allocation_history.len()
                            && event
                                .callee_expression
                                .is_some_and(|callee| callee < token.expression)
                            && self
                                .facts
                                .invocation_expressions
                                .iter()
                                .filter(|row| {
                                    row.expression == token.expression
                                        && row.context == context
                                        && row.argument_of == Some((event.id, slot as u32))
                                })
                                .count()
                                == 1,
                        "public callable input token borrowed another actual event or slot",
                    )?;
                    self.input_operand_interval(event, slot, token.expression, context, sites)?;
                    (*actual_syntax, &value.value, context)
                }
                Some(ArgumentSource::Default(id)) => {
                    let default = self
                        .facts
                        .default_uses
                        .get(id.0 as usize)
                        .filter(|default| default.id == *id)
                        .ok_or_else(|| {
                            "public callable input lost its actual default".to_owned()
                        })?;
                    require(
                        default.origin == DefaultOrigin::Call(event.id)
                            && default.target == event.target
                            && default.parameter as usize == slot
                            && default.caller == context
                            && default.evaluation_complete
                            && default.status == CopyInvocationStatus::Completed
                            && default
                                .result_allocation_epoch
                                .is_some_and(|epoch| epoch <= self.facts.allocation_history.len())
                            && !preparation.supplied.contains_key(&(slot as u32)),
                        "public callable input default belongs to another occurrence or incomplete evaluation",
                    )?;
                    let actual_syntax = callee
                        .signature
                        .as_ref()
                        .and_then(|parameters| parameters.get(slot))
                        .and_then(|parameter| parameter.default.as_ref())
                        .ok_or_else(|| {
                            "public callable default lacks its original signature Source".to_owned()
                        })?;
                    require(
                        actual_syntax.span == default.span,
                        "public callable default changed its actual declaration",
                    )?;
                    let value = default
                        .result
                        .as_ref()
                        .ok_or_else(|| "public callable default lost its result".to_owned())?;
                    (
                        actual_syntax,
                        &value.value,
                        InvocationContext {
                            owner: default.owner,
                            default_use: Some(*id),
                            ..default.caller
                        },
                    )
                }
                _ => return Err("public callable input lacks a full-source operand".into()),
            };
            let actual = self.original_source_key(actual_syntax, value, actual_context, sites)?;
            let fresh =
                source_reception::construction(actual_syntax, &mut 4096).ok_or_else(|| {
                    "public callable construction Source exceeds its bound".to_owned()
                })?;
            require(
                source_reception::compatible(expected, &actual, Some(&fresh), &mut 4096)
                    == Some(true),
                "public callable original input does not prove its receiving Source coordinates",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binder(index: usize) -> ArgumentKey {
        ArgumentKey::Binder {
            identity: format!("budget:{index}"),
            sort: StaticBinderSort::Type,
        }
    }

    #[test]
    fn bounded_input_substitution_stops_before_exponential_expansion() {
        let mut selected = BTreeMap::new();
        for index in 0..24 {
            selected.insert(
                format!("budget:{index}"),
                ArgumentKey::Tuple(vec![binder(index + 1), binder(index + 1)]),
            );
        }
        selected.insert(
            "budget:24".into(),
            ArgumentKey::Name {
                name: "int".into(),
                arguments: vec![],
            },
        );
        let error = input_select_key(&binder(0), &selected, 0).unwrap_err();
        assert!(error.contains("budget"), "{error}");
    }

    #[test]
    fn input_row_composition_preserves_open_uid_and_field_modes() {
        let key = ArgumentKey::Record {
            fields: vec![("head".into(), false, binder(0))],
            row: Some(Box::new(binder(1))),
        };
        let selected = BTreeMap::from([(
            "budget:1".into(),
            ArgumentKey::Record {
                fields: vec![("tail".into(), true, binder(2))],
                row: Some(Box::new(binder(3))),
            },
        )]);
        let result = input_select_key(&key, &selected, 0).unwrap();
        assert_eq!(
            result,
            ArgumentKey::Record {
                fields: vec![
                    ("head".into(), false, binder(0)),
                    ("tail".into(), true, binder(2))
                ],
                row: Some(Box::new(binder(3))),
            }
        );
    }
}
