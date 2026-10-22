use super::*;

pub(super) struct SourceExpression {
    pub(super) value: Value,
    pub(super) observation: Option<usize>,
    pub(super) source_valid: bool,
}

#[derive(Clone, Copy)]
pub(super) struct SourceContext<'a> {
    pub(super) ordinary: Option<&'a Ty>,
    pub(super) source: Option<&'a super::super::source_reception::Target>,
}

impl Checker {
    pub(super) fn expression(&mut self, expr: &Expr, frame: &mut Frame) -> Value {
        self.expression_expected(expr, frame, None)
    }
    pub(super) fn expression_expected(
        &mut self,
        expr: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
    ) -> Value {
        self.expression_expected_observed(expr, frame, expected).0
    }
    pub(super) fn expression_observed(
        &mut self,
        expr: &Expr,
        frame: &mut Frame,
    ) -> (Value, Option<usize>) {
        self.expression_expected_observed(expr, frame, None)
    }
    pub(super) fn expression_expected_observed(
        &mut self,
        expr: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
    ) -> (Value, Option<usize>) {
        let observed = self.expression_expected_source(expr, frame, expected, None);
        (observed.value, observed.observation)
    }

    pub(super) fn expression_expected_source(
        &mut self,
        expr: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
        source: Option<&super::super::source_reception::Target>,
    ) -> SourceExpression {
        self.cancellation_checkpoint(expr.span, frame);
        if self.analysis_depth >= 64 || self.analysis_visits >= 1_000_000 {
            self.unsupported(expr.span,"semantic traversal resource budget exhausted; no permission certificate was issued");
            return SourceExpression {
                value: Value::scalar(
                    Ty::Unknown,
                    None,
                    self.cause(
                        CauseKind::MissingProof,
                        expr.span,
                        "bounded source traversal stopped",
                        [],
                    ),
                ),
                observation: None,
                source_valid: false,
            };
        }
        let context = self.invocation_context(frame.callable_owner);
        let kind = if matches!(
            expr.kind,
            ExprKind::Control {
                operation: ControlOperation::Resume,
                ..
            }
        ) {
            crate::sema::application_effect::ActivationKind::ControlTransfer
        } else {
            crate::sema::application_effect::ActivationKind::Expression
        };
        let activation = if kind == crate::sema::application_effect::ActivationKind::Expression {
            self.application_effect
                .enter(expr.hir_id, frame.owner, context)
        } else {
            self.application_effect
                .enter_kind(expr.hir_id, frame.owner, context, kind)
        };
        let Some(activation) = activation else {
            self.unsupported(
                expr.span,
                "evaluation activation budget exhausted before entering syntax",
            );
            return SourceExpression {
                value: Value::scalar(Ty::Unknown, None, CauseId(0)),
                observation: None,
                source_valid: false,
            };
        };
        self.analysis_depth += 1;
        self.expression_owners.push(frame.callable_owner);
        self.analysis_visits += 1;
        self.window_expression_uses
            .push(self.window_expression_uses(expr, frame));
        let expected = expected.map(|ty| self.expanded_at(ty, expr.span.file));
        let mut source_handled = None;
        let mut source_call_event = None;
        let mut value = expected
            .as_ref()
            .and_then(|ty| self.numeric_expected_literal(expr, ty, frame))
            .or_else(|| self.numeric_pending_literal(expr, frame))
            .unwrap_or_else(|| {
                self.expression_inner(
                    expr,
                    frame,
                    expected.as_ref(),
                    source,
                    &mut source_handled,
                    &mut source_call_event,
                )
            });
        self.window_expression_uses.pop();
        self.analysis_depth -= 1;
        value = self.narrow_expression(expr, value, frame);
        self.prepare_producing_result_context(expr, &mut value, expected.as_ref(), source, frame);
        if self.expanded_at(&value.ty, expr.span.file) != Ty::Bool {
            value.condition_inspections = Default::default();
        }
        if let Some(source) = expr.hir_id {
            self.read_epochs
                .insert((source, frame.owner), self.write_events.len());
        }
        if value.unsuffixed_numeric
            && matches!(value.ty, Ty::Int(_) | Ty::Float(_))
            && let Some(ty) =
                self.contextual_types
                    .get(&(expr.span.file.0, expr.span.start, expr.span.end))
        {
            value.ty = ty.clone();
        }
        self.infer_expression_source_type(&mut value, expr);
        self.channel_boolean_evaluation(&mut value, expr.span, frame);
        let argument_of = self.source_argument_of(expr, frame);
        let evaluation_context = self.invocation_context(frame.callable_owner);
        self.record_copy_references(&value, expr.span, frame);
        let Some(observation) = self.application_effect.observe_in(
            activation,
            || super::super::ExpressionFact {
                allocation_epoch: self.recency_moves.len(),
                source_id: expr.hir_id,
                span: expr.span,
                value: value.clone(),
            },
            evaluation_context,
            frame.owner,
            argument_of,
        ) else {
            self.application_effect.leave(activation);
            self.expression_owners.pop();
            return SourceExpression {
                value,
                observation: None,
                source_valid: false,
            };
        };
        self.record_builtin_source_observation(expr, &value, observation, frame);
        if let Some(event) = source_call_event {
            let context = self.invocation_context(frame.callable_owner);
            let call = &mut self.copy_call_events[event.0 as usize];
            if call.id == event
                && call.owner == context.owner
                && call.parent == context.invocation
                && call.source_id.is_some()
                && call.source_id == expr.hir_id
                && call.result_expression.is_none()
            {
                call.result_expression = Some(observation);
            } else {
                self.unsupported(
                    expr.span,
                    "call result lost its original event and root emission",
                );
            }
        }
        if let Some(target) = source
            && let Some(syntax) = target.syntax.as_deref()
        {
            self.with_typing_environment(&target.environment, |checker| {
                checker.check_signature_modes(&value, syntax);
            });
        }
        let source_valid = source_handled.unwrap_or_else(|| {
            source.is_none_or(|target| {
                self.require_source_reception(target, expr, &value, Some(observation), frame)
            })
        });
        if !source_valid {
            // The frame accumulates failed receptions for its final answer.
            // It is not a premise of this occurrence's independent reception:
            // an earlier failure cannot erase a later declaration's own Source.
            frame.return_source_valid = false;
            if let Some(target) = source
                && let Some(syntax) = target.syntax.as_deref()
            {
                self.with_typing_environment(&target.environment, |checker| {
                    checker.check_receiving_callable_bounds(&value, syntax);
                });
            }
        }
        self.cancellation_checkpoint(expr.span, frame);
        self.expression_owners.pop();
        self.application_effect.leave(activation);
        SourceExpression {
            value,
            observation: Some(observation),
            source_valid,
        }
    }
    fn expression_inner(
        &mut self,
        expr: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
        source: Option<&super::super::source_reception::Target>,
        source_handled: &mut Option<bool>,
        source_call_event: &mut Option<super::super::copy_contract::CopyCallEventId>,
    ) -> Value {
        if let ExprKind::Name(name) = &expr.kind
            && let Some(reference) = self.constant_references.get(name)
        {
            let mut value = self.constant_values[reference.node.0 as usize]
                .value
                .clone();
            value.source_type_witness = self.constant_source_views.get(name).cloned();
            return value;
        }
        if let Some(operation) = self.explicit_effect_operation(expr) {
            if operation.is_empty() {
                // Resolution already emitted a diagnostic or missing-proof
                // obligation. Do not invent a unit callee and a second E0338.
                let mut unresolved = self.unit(expr.span);
                unresolved.ty = Ty::Never;
                return unresolved;
            }
            return self.name(&operation, expr.span, frame);
        }
        match &expr.kind {
            ExprKind::Literal(literal) => self.literal(literal, expr.span, frame),
            ExprKind::Interpolated(parts) => {
                for (index, part) in parts.iter().enumerate() {
                    if let StringPart::Interpolation {
                        expression,
                        format,
                        span,
                    } = part
                    {
                        let value = self.expression(expression, frame);
                        if value.ty == Ty::Never {
                            for part in &parts[index + 1..] {
                                if let StringPart::Interpolation {
                                    expression,
                                    format,
                                    span,
                                } = part
                                {
                                    let value = self.preview_expression(expression, frame);
                                    if value.ty != Ty::Never {
                                        self.format_type(
                                            &value,
                                            format.as_deref().unwrap_or(""),
                                            *span,
                                        );
                                    }
                                }
                            }
                            return value;
                        }
                        self.format_type(&value, format.as_deref().unwrap_or(""), *span);
                    }
                }
                let cause = self.cause(CauseKind::Source, expr.span, "interpolated string", []);
                let mut value = Value::scalar(Ty::Str, None, cause);
                if parts.iter().all(|part| matches!(part, StringPart::Text(_))) {
                    value.static_coordinate = Some(StaticCoordinate::Label(
                        parts
                            .iter()
                            .filter_map(|part| {
                                if let StringPart::Text(text) = part {
                                    Some(text.as_str())
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    ));
                }
                value
            }
            ExprKind::Name(name) => self.name(name, expr.span, frame),
            ExprKind::Path(path) => self.name(&path.join("::"), expr.span, frame),
            ExprKind::Generic { base, arguments } => {
                let mut value = self.expression(base, frame);
                if !self.prepare_explicit_named(expr, &value, frame)
                    && !self.constructor_generic(&mut value, arguments, expr.span)
                {
                    self.standard_generic(&mut value, arguments, expr.span);
                }
                value
            }
            ExprKind::Block(block) => {
                let result = self.block_expected_source(block, frame, expected, source);
                *source_handled = Some(result.source_valid);
                result.value
            }
            ExprKind::Match {
                value,
                arms,
                type_match,
            } => {
                if expected.is_none() && source.is_none() {
                    return self.check_match(value, arms, *type_match, expr.span, frame);
                }
                let result = self.check_match_expected_source(
                    value,
                    arms,
                    *type_match,
                    expr.span,
                    frame,
                    SourceContext {
                        ordinary: expected,
                        source,
                    },
                );
                *source_handled = Some(result.source_valid);
                result.value
            }
            ExprKind::Is { value, pattern } => {
                self.validate_variant_predicate(value, pattern, frame);
                self.suppress_refinement += 1;
                let result = self.check_is(value, pattern, expr.span, frame);
                self.suppress_refinement -= 1;
                result
            }
            ExprKind::Range {
                start,
                end,
                inclusive,
            } => {
                let a = start.as_ref().map(|v| self.expression(v, frame));
                if let Some(value) = a.as_ref().filter(|value| value.ty == Ty::Never) {
                    if let Some(end) = end {
                        let endpoint = self.preview_expression(end, frame);
                        if !matches!(endpoint.ty, Ty::Int(_) | Ty::Never) {
                            self.error(
                                "E0327",
                                end.span,
                                "range endpoints require integer values",
                                [endpoint.cause],
                            );
                        }
                    }
                    return value.clone();
                }
                let b = end.as_ref().map(|v| self.expression(v, frame));
                if let Some(value) = b.as_ref().filter(|value| value.ty == Ty::Never) {
                    return value.clone();
                }
                let element_type = a
                    .iter()
                    .chain(b.iter())
                    .find(|value| !value.unsuffixed_numeric && matches!(value.ty, Ty::Int(_)))
                    .map(|value| value.ty.clone())
                    .unwrap_or(Ty::Int("int".into()));
                for value in a.iter().chain(b.iter()) {
                    if matches!(value.ty, Ty::Int(_)) {
                        self.require_type(value, &element_type, expr.span);
                    } else {
                        self.error(
                            "E0327",
                            expr.span,
                            "range endpoints require integer values",
                            [value.cause],
                        );
                    }
                }
                let node = self.allocate_owned(expr.span, 0, frame.owner);
                self.concurrent_range_bound(node, a.as_ref(), b.as_ref(), *inclusive);
                let cause = self.heap.nodes[node.0 as usize].cause;
                let element = Value::scalar(element_type.clone(), None, cause);
                self.store_field(node, Slot::AnyIndex, element);
                let mut value = Value::reference(Ty::Range(Box::new(element_type)), node, cause);
                value.permission = Permission::Read;
                value.publication = Publication::Immutable;
                value.construction = false;
                value
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let tuple = matches!(expr.kind, ExprKind::Tuple(_));
                // Fresh members receive their contexts before the container
                // freezes its element/member type. Stored children still pass
                // through the ordinary source relation independently.
                let mut source_valid = true;
                let mut receiving = None;
                if let Some(target) = source {
                    use crate::sema::source_types::{SourceLength, SourceTypesError, WorkLimit};
                    let shape = (|| {
                        let Some(schema) = &target.schema else {
                            return Ok(None);
                        };
                        let mut work = WorkLimit::new(16384);
                        if tuple {
                            schema
                                .tuple_parts(&mut work)
                                .map(|parts| parts.map(|parts| parts.len() == items.len()))
                        } else {
                            let count = u64::try_from(items.len())
                                .map_err(|_| SourceTypesError::BudgetExceeded)?;
                            schema.array_parts(&mut work).map(|parts| {
                                parts.map(|(length, _)| {
                                    matches!(length, SourceLength::Dynamic)
                                        || length == SourceLength::Fixed(count)
                                })
                            })
                        }
                    })();
                    let shape_fits = match shape {
                        Ok(Some(fits)) => {
                            receiving = Some(target);
                            Some(fits)
                        }
                        Ok(None) => None,
                        Err(error) => {
                            self.unsupported(
                                expr.span,
                                format!("literal context Source graph is incomplete: {error}"),
                            );
                            source_valid = false;
                            None
                        }
                    };
                    if shape_fits == Some(false) {
                        let annotation = self.cause(
                            CauseKind::MissingProof,
                            target.span,
                            "receiving literal schema was frozen here",
                            [],
                        );
                        self.error(
                            "E0301",
                            expr.span,
                            "literal shape does not fit the receiving source schema",
                            [annotation],
                        );
                        source_valid = false;
                    }
                }
                let mut values = Vec::new();
                for (index, item) in items.iter().enumerate() {
                    let child_type = match expected {
                        Some(Ty::Tuple(types)) if matches!(expr.kind, ExprKind::Tuple(_)) => {
                            types.get(index)
                        }
                        Some(Ty::Array(element)) if matches!(expr.kind, ExprKind::Array(_)) => {
                            Some(&**element)
                        }
                        _ => None,
                    };
                    let child_source = receiving.map(|target| {
                        if tuple {
                            super::source_receiving::tuple_target(target, index, item.span)
                        } else {
                            super::source_receiving::array_element_target(target, item.span)
                        }
                    });
                    let checked = self.expression_expected_source(
                        item,
                        frame,
                        child_type,
                        child_source.as_ref(),
                    );
                    source_valid &= checked.source_valid;
                    let value = checked.value;
                    if value.ty == Ty::Never {
                        for remaining in &items[index + 1..] {
                            self.preview_expression(remaining, frame);
                        }
                        return value;
                    }
                    values.push(EvaluatedValue::new(value, self.recency_moves.len()));
                }
                if receiving.is_some() {
                    *source_handled = Some(source_valid);
                }
                let current: Vec<_> = values
                    .iter_mut()
                    .map(|value| value.current(&self.recency_moves))
                    .collect();
                let element = current
                    .iter()
                    .find(|v| !v.unsuffixed_numeric)
                    .or_else(|| current.first())
                    .map(|v| v.ty.clone())
                    .unwrap_or(Ty::Unknown);
                if !tuple && current.iter().any(|value| !value.unsuffixed_numeric) {
                    for value in &mut values {
                        self.require_type(&value.current(&self.recency_moves), &element, expr.span);
                    }
                } else if !tuple {
                    for value in &mut values {
                        let value = value.current(&self.recency_moves);
                        if !matches!(
                            (&value.ty, &element),
                            (Ty::Int(_), Ty::Int(_)) | (Ty::Float(_), Ty::Float(_))
                        ) {
                            self.require_type(&value, &element, expr.span);
                        }
                    }
                }
                let array_length = values.len() as u64;
                let ty = if tuple {
                    Ty::Tuple(current.iter().map(|v| v.ty.clone()).collect())
                } else {
                    Ty::Array(Box::new(element))
                };
                let node = self.allocate_owned(expr.span, 0, frame.owner);
                let cause = self.heap.nodes[node.0 as usize].cause;
                let mut value = Value::reference(ty, node, cause);
                if !tuple {
                    self.array_lengths.insert(node, Some(array_length));
                }
                for (i, child) in values.into_iter().enumerate() {
                    let child = child.into_current(&self.recency_moves);
                    value.numeric.include(&child.numeric);
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    value.callback_parameters.extend(&child.callback_parameters);
                    value.scoped.extend(&child.scoped);
                    if child.permission == Permission::Write
                        && !child.construction
                        && self.has_writer(&child)
                        && !child.marker
                    {
                        value.internal_aliases = true;
                    }
                    value.mutable_environment |= child.mutable_environment;
                    value.observer_environment |= child.observer_environment;
                    self.store_field(
                        node,
                        if tuple {
                            Slot::Tuple(i as u32)
                        } else {
                            Slot::Index(i as i64)
                        },
                        child,
                    );
                }
                value
            }
            ExprKind::Map(entries) => {
                let (expected_key, expected_value) = match expected {
                    Some(Ty::Map(key, value)) => (Some(&**key), Some(&**value)),
                    _ => (None, None),
                };
                let mut evaluated = Vec::new();
                for (index, (key, value)) in entries.iter().enumerate() {
                    let key = self.expression_expected(key, frame, expected_key);
                    if key.ty == Ty::Never {
                        self.preview_expression(value, frame);
                        for (later_key, later_value) in &entries[index + 1..] {
                            self.preview_expression(later_key, frame);
                            self.preview_expression(later_value, frame);
                        }
                        return key;
                    }
                    let key = EvaluatedValue::new(key, self.recency_moves.len());
                    let value = self.expression_expected(value, frame, expected_value);
                    if value.ty == Ty::Never {
                        for (later_key, later_value) in &entries[index + 1..] {
                            self.preview_expression(later_key, frame);
                            self.preview_expression(later_value, frame);
                        }
                        return value;
                    }
                    evaluated.push((key, EvaluatedValue::new(value, self.recency_moves.len())));
                }
                let mut entries = evaluated;
                let current: Vec<_> = entries
                    .iter_mut()
                    .map(|(key, value)| {
                        (
                            key.current(&self.recency_moves),
                            value.current(&self.recency_moves),
                        )
                    })
                    .collect();
                let key_ty = current
                    .iter()
                    .map(|(key, _)| key)
                    .find(|value| !value.unsuffixed_numeric)
                    .or_else(|| current.first().map(|(key, _)| key))
                    .map(|value| value.ty.clone())
                    .unwrap_or(Ty::Unknown);
                let value_ty = current
                    .iter()
                    .map(|(_, value)| value)
                    .find(|value| !value.unsuffixed_numeric)
                    .or_else(|| current.first().map(|(_, value)| value))
                    .map(|value| value.ty.clone())
                    .unwrap_or(Ty::Unknown);
                if !entries.is_empty() {
                    self.require_key_type(&key_ty, expr.span);
                }
                let keys_selected = current.iter().any(|(key, _)| !key.unsuffixed_numeric);
                let values_selected = current.iter().any(|(_, value)| !value.unsuffixed_numeric);
                for (key, value) in &mut entries {
                    if keys_selected {
                        self.require_type(&key.current(&self.recency_moves), &key_ty, expr.span);
                    }
                    if values_selected {
                        self.require_type(
                            &value.current(&self.recency_moves),
                            &value_ty,
                            expr.span,
                        );
                    }
                }
                let node = self.allocate_owned(expr.span, 0, frame.owner);
                let cause = self.heap.nodes[node.0 as usize].cause;
                let mut result = Value::reference(
                    Ty::Map(Box::new(key_ty.clone()), Box::new(value_ty.clone())),
                    node,
                    cause,
                );
                result.requires_inference = entries.is_empty();
                let mut keys: Option<Value> = None;
                for (index, (key, value)) in entries.into_iter().enumerate() {
                    let key = key.into_current(&self.recency_moves);
                    let value = value.into_current(&self.recency_moves);
                    result.numeric.include(&key.numeric);
                    result.numeric.include(&value.numeric);
                    keys = Some(if let Some(previous) = keys {
                        previous.join(&key, self.choice(), cause)
                    } else {
                        key
                    });
                    result.results.extend(&value.results);
                    result.must_results.extend(&value.must_results);
                    result
                        .callback_parameters
                        .extend(&value.callback_parameters);
                    result.scoped.extend(&value.scoped);
                    result.internal_aliases |= value.permission == Permission::Write
                        && !value.construction
                        && self.has_writer(&value)
                        && !value.marker;
                    result.mutable_environment |= value.mutable_environment;
                    result.observer_environment |= value.observer_environment;
                    self.store_field(node, Slot::Index(index as i64), value);
                }
                if let Some(keys) = keys {
                    self.store_field(node, Slot::Field("key".into()), keys);
                }
                result
            }
            ExprKind::Record { ty, members, .. } => {
                self.set_contract_environment(&frame.env);
                let declared_source = ty
                    .as_ref()
                    .map(|syntax| self.freeze_source_receiving_target(syntax));
                let declared = ty.as_ref().map(|t| self.ty(t));
                let receiving = declared_source.as_ref().or(source);
                let explicit_construction = members
                    .iter()
                    .all(|member| matches!(member, RecordMember::Field(_)));
                let structural_labels = receiving
                    .and_then(|target| target.schema.as_ref())
                    .and_then(|schema| {
                        schema
                            .closed_record_labels(&mut crate::sema::source_types::WorkLimit::new(
                                16384,
                            ))
                            .ok()
                    });
                let structural_target = receiving.filter(|_| structural_labels.is_some());
                let mut source_valid = true;
                if let Some(target) = declared_source.as_ref() {
                    use super::super::source_reception::SchemaSensitivity;
                    if target.sensitivity == SchemaSensitivity::Unknown
                        || (target.sensitivity == SchemaSensitivity::Required
                            && !explicit_construction)
                    {
                        self.unsupported(expr.span,
                            "typed record receiving requires its complete original member schemas and observations");
                        source_valid = false;
                    }
                }
                let expected_fields = declared
                    .as_ref()
                    .or(expected)
                    .and_then(|ty| self.value_row(ty))
                    .map(|row| row.fields);
                let mut shape = BTreeMap::new();
                let mut values = BTreeMap::new();
                let mut overrides = BTreeMap::new();
                let mut row_spreads = Vec::new();
                let mut row_tails = Vec::new();
                let explicit: BTreeSet<_> = members
                    .iter()
                    .filter_map(|member| {
                        if let RecordMember::Field(field) = member {
                            Some(field.name.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                let mut spread_names = BTreeSet::new();
                for (index, member) in members.iter().enumerate() {
                    match member {
                        RecordMember::Field(field) => {
                            let child_type = expected_fields
                                .as_ref()
                                .and_then(|fields| fields.get(&field.name))
                                .map(|(_, ty)| ty);
                            let child_source = structural_target
                                .filter(|_| {
                                    structural_labels
                                        .as_ref()
                                        .is_some_and(|labels| labels.contains(&field.name))
                                })
                                .map(|target| {
                                    super::source_receiving::member_target(
                                        target,
                                        &field.name,
                                        field.value.span,
                                    )
                                });
                            let checked = self.expression_expected_source(
                                &field.value,
                                frame,
                                child_type,
                                child_source.as_ref(),
                            );
                            source_valid &= checked.source_valid;
                            let child = checked.value;
                            if child.ty == Ty::Never {
                                self.preview_record_members(&members[index + 1..], frame);
                                return child;
                            }
                            shape.insert(field.name.clone(), (false, child.ty.clone()));
                            overrides.insert(
                                field.name.clone(),
                                EvaluatedValue::new(child, self.recency_moves.len()),
                            );
                        }
                        RecordMember::Spread(expression) => {
                            let spread = self.expression(expression, frame);
                            if spread.ty == Ty::Never {
                                self.preview_record_members(&members[index + 1..], frame);
                                return spread;
                            }
                            let mut spread = EvaluatedValue::new(spread, self.recency_moves.len());
                            let current_spread = spread.current(&self.recency_moves);
                            if let Some(row) = self.value_row(&current_spread.ty) {
                                for (name, shape_field) in &row.fields {
                                    shape.entry(name.clone()).or_insert(shape_field.clone());
                                }
                                if let crate::sema::model::rows::RowTail::Open(tail) = &row.tail
                                    && let Some(witness) = self.carried_row_tail(
                                        &spread.current(&self.recency_moves),
                                        tail,
                                        expression.span,
                                    )
                                {
                                    row_tails.push((
                                        tail.identity.clone(),
                                        EvaluatedValue::new(witness, self.recency_moves.len()),
                                    ));
                                }
                                row_spreads.push(row);
                            } else {
                                self.error(
                                    "E0301",
                                    expression.span,
                                    "record spread requires a record value",
                                    [current_spread.cause],
                                );
                            }
                            let labels: Vec<_> = self
                                .value_row(&current_spread.ty)
                                .map(|row| row.fields.into_keys().collect())
                                .unwrap_or_default();
                            for name in labels {
                                if !spread_names.insert(name.clone()) && !explicit.contains(&name) {
                                    self.error(
                                        "E0211",
                                        expression.span,
                                        format!("conflicting spreads both supply {name}"),
                                        [current_spread.cause],
                                    );
                                }
                                // Projection joins all source alternatives and applies
                                // the complete access-path authority exactly once.
                                let mut child = self.project(
                                    &spread.current(&self.recency_moves),
                                    Slot::Field(name.clone()),
                                    expression.span,
                                    frame,
                                    true,
                                );
                                child.readonly_spread = child.permission == Permission::Read
                                    && !child.origins.nodes.is_empty();
                                values.insert(
                                    name,
                                    EvaluatedValue::new(child, self.recency_moves.len()),
                                );
                            }
                        }
                    }
                }
                values.extend(overrides);
                let actual = if row_spreads.iter().any(|row| !row.is_closed()) {
                    use crate::sema::model::rows::Row;
                    let explicit_shape = shape
                        .iter()
                        .filter(|(label, _)| explicit.contains(*label))
                        .map(|(label, field)| (label.clone(), field.clone()))
                        .collect();
                    let mut combined = Row::closed(BTreeMap::new());
                    for row in row_spreads {
                        match self.row_solver().union(&combined, &row, &explicit_shape).ok().and_then(|plan| plan.exact()) {
                            Some(row) => combined = row,
                            None => self.unsupported(expr.span, "record spread requires proved disjoint tails and exact override membership"),
                        }
                    }
                    Self::row_type(combined)
                } else {
                    Ty::Record(shape)
                };
                if let Some(expected) = &declared {
                    let expected_shape = self.expanded_at(expected, expr.span.file);
                    if let Ty::Record(expected_fields) = expected_shape {
                        for (name, (_, ty)) in &expected_fields {
                            if let Some(child) = values.get_mut(name) {
                                self.require_type(
                                    &child.current(&self.recency_moves),
                                    ty,
                                    expr.span,
                                );
                                if source_valid {
                                    child.current_mut(&self.recency_moves).ty = ty.clone();
                                }
                            } else {
                                self.error(
                                    "E0307",
                                    expr.span,
                                    format!("missing record field {name}"),
                                    [],
                                );
                            }
                        }
                        for name in values.keys() {
                            if !expected_fields.contains_key(name) {
                                self.error(
                                    "E0302",
                                    expr.span,
                                    format!("unexpected record field {name}"),
                                    [],
                                );
                            }
                        }
                    } else if self.foreign_opaque_type(expected) || self.resource_type(expected) {
                        self.error("E0907",expr.span,"opaque resource authority cannot be created by structural record construction",[]);
                    } else if matches!(expected, Ty::Generic(_) | Ty::Projection { .. }) {
                        self.unsupported(expr.span,"generic record construction requires a concrete complete structural shape");
                    } else {
                        self.error(
                            "E0301",
                            expr.span,
                            "typed record construction requires a structural record type",
                            [],
                        );
                    }
                }
                let node = self.allocate_owned(expr.span, 0, frame.owner);
                let receiving_fields_complete = structural_labels
                    .as_ref()
                    .is_some_and(|labels| labels.iter().all(|name| values.contains_key(name)));
                if ty.is_none()
                    && source.is_some()
                    && explicit_construction
                    && receiving_fields_complete
                {
                    *source_handled = Some(source_valid);
                }
                if !source_valid {
                    frame.return_source_valid = false;
                }
                let mut value = Value::reference(
                    if source_valid {
                        declared.unwrap_or(actual)
                    } else {
                        actual
                    },
                    node,
                    self.heap.nodes[node.0 as usize].cause,
                );
                for (name, child) in values {
                    let child = child.into_current(&self.recency_moves);
                    value.numeric.include(&child.numeric);
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    value.callback_parameters.extend(&child.callback_parameters);
                    value.scoped.extend(&child.scoped);
                    if child.permission == Permission::Write
                        && !child.construction
                        && self.has_writer(&child)
                        && !child.marker
                    {
                        value.internal_aliases = true;
                    }
                    value.mutable_environment |= child.mutable_environment;
                    value.observer_environment |= child.observer_environment;
                    self.store_field(node, Slot::Field(name), child);
                }
                for (identity, child) in row_tails {
                    let child = child.into_current(&self.recency_moves);
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    value.callback_parameters.extend(&child.callback_parameters);
                    value.scoped.extend(&child.scoped);
                    value.mutable_environment |= child.mutable_environment;
                    value.observer_environment |= child.observer_environment;
                    value.internal_aliases |= child.permission == Permission::Write
                        && !child.construction
                        && self.has_writer(&child)
                        && !child.marker;
                    self.store_field(node, Slot::RowTail(identity), child);
                }
                if let Some(syntax) = ty.as_ref().filter(|_| source_valid) {
                    let mut held = EvaluatedValue::new(value, self.recency_moves.len());
                    self.set_contract_environment(&frame.env);
                    self.ascribe_signature(held.current_mut(&self.recency_moves), syntax);
                    value = held.into_current(&self.recency_moves);
                }
                value
            }
            ExprKind::Field { base, field, safe } => {
                if *safe {
                    self.suppress_refinement += 1;
                }
                let mut base = self.expression(base, frame);
                if *safe {
                    self.suppress_refinement -= 1;
                }
                if base.ty == Ty::Never {
                    return base;
                }
                let tag = base.option_tag;
                let before = (*safe).then(|| self.snapshot_flow());
                if *safe {
                    if let Ty::Optional(inner) = self.expanded(&base.ty, &mut BTreeSet::new()) {
                        base = self.optional_payload(&base, *inner);
                    } else {
                        self.error(
                            "E0715",
                            expr.span,
                            "safe field access requires an optional receiver",
                            [base.cause],
                        );
                    }
                }
                if matches!(
                    self.expanded(&base.ty, &mut BTreeSet::new()),
                    Ty::Map(..) | Ty::Array(_) | Ty::Set(_) | Ty::Range(_)
                ) {
                    self.error(
                        "E0337",
                        expr.span,
                        "collection values expose no named or tuple members",
                        [base.cause],
                    );
                    return Value::scalar(Ty::Unknown, None, base.cause);
                }
                let slot = field
                    .parse()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone()));
                if !*safe
                    && let Some(value) = self.concurrent_receiver(&base, field, expr.span, frame)
                {
                    return value;
                }
                let value = self.project(&base, slot, expr.span, frame, true);
                if let Some(before) = before {
                    let present = if matches!(
                        self.expanded(&value.ty, &mut BTreeSet::new()),
                        Ty::Optional(_)
                    ) {
                        value
                    } else {
                        self.wrap_optional(value, Some(true))
                    };
                    let absent = self.none_value(expr.span);
                    self.conditional_flow(&before, &absent, &present, tag, expr.span)
                } else {
                    value
                }
            }
            ExprKind::Index { base, index, safe } => {
                if let ExprKind::Range {
                    start,
                    end,
                    inclusive,
                } = &index.kind
                {
                    if *safe {
                        self.unsupported(
                            expr.span,
                            "optional slicing requires a conditional bounds and ownership proof",
                        );
                    }
                    return self.slice_window(
                        base,
                        start.as_deref(),
                        end.as_deref(),
                        *inclusive,
                        expr.span,
                        frame,
                    );
                }
                if *safe {
                    self.suppress_refinement += 1;
                }
                let mut base = self.expression(base, frame);
                if *safe {
                    self.suppress_refinement -= 1;
                }
                if base.ty == Ty::Never {
                    return base;
                }
                let mut optional_receiver = false;
                let tag = base.option_tag;
                let before = (*safe).then(|| self.snapshot_flow());
                if *safe && let Ty::Optional(inner) = self.expanded(&base.ty, &mut BTreeSet::new())
                {
                    optional_receiver = true;
                    base = self.optional_payload(&base, *inner);
                }
                let base_recency = self.recency_moves.len();
                let index = self.expression(index, frame);
                self.transport_value_since(&mut base, base_recency);
                if index.ty == Ty::Never {
                    if optional_receiver {
                        let absent = self.none_value(expr.span);
                        return self.conditional_flow(
                            &before.unwrap(),
                            &absent,
                            &index,
                            tag,
                            expr.span,
                        );
                    }
                    return index;
                }
                if self.foreign_opaque_type(&base.ty) {
                    self.error(
                        "E0907",
                        expr.span,
                        "opaque foreign storage cannot be indexed",
                        [base.cause],
                    );
                    return Value::scalar(Ty::Unknown, None, base.cause);
                }
                match self.collection_type(&base) {
                    Ty::Array(_) | Ty::Bytes | Ty::Str => {
                        self.require_type(&index, &Ty::Int("int".into()), expr.span)
                    }
                    Ty::Map(key, _) => self.require_type(&index, &key, expr.span),
                    Ty::Record(_) => self.error(
                        "E0324",
                        expr.span,
                        "record bracket indexing is prohibited",
                        [base.cause],
                    ),
                    _ => self.error(
                        "E0352",
                        expr.span,
                        "receiver does not provide element lookup",
                        [base.cause],
                    ),
                }
                let slot = if matches!(self.expanded(&base.ty, &mut BTreeSet::new()), Ty::Map(..)) {
                    Slot::AnyIndex
                } else if let Some(Constant::Integer(i)) = index.constant {
                    Slot::Index(i as i64)
                } else {
                    Slot::AnyIndex
                };
                let value = match self.expanded(&base.ty, &mut BTreeSet::new()) {
                    Ty::Bytes => Value::scalar(Ty::Int("u8".into()), None, base.cause),
                    Ty::Str => Value::scalar(Ty::Int("u32".into()), None, base.cause),
                    _ => self.project(&base, slot, expr.span, frame, true),
                };
                let optional =
                    *safe || matches!(self.expanded(&base.ty, &mut BTreeSet::new()), Ty::Map(..));
                let value = if optional {
                    if *safe
                        && matches!(
                            self.expanded(&value.ty, &mut BTreeSet::new()),
                            Ty::Optional(_)
                        )
                    {
                        let mut value = value;
                        value.option_tag = None;
                        value.must_results.clear();
                        value.must_outer_results.clear();
                        value
                    } else {
                        self.wrap_optional(value, None)
                    }
                } else {
                    value
                };
                if optional_receiver {
                    let absent = self.none_value(expr.span);
                    self.conditional_flow(&before.unwrap(), &absent, &value, tag, expr.span)
                } else {
                    value
                }
            }
            ExprKind::ComputedField { base, key } => {
                self.computed_projection(base, key, expr.span, frame)
            }
            ExprKind::Unary { operator, operand } => {
                let previous_negative = self.literal_negative;
                self.literal_negative = operator == "-"
                    && matches!(operand.kind, ExprKind::Literal(Literal::Integer(_)));
                if operator == "?" {
                    self.suppress_refinement += 1;
                }
                let operand_expected = (operator == "-").then_some(expected).flatten();
                let mut value = self.expression_expected(operand, frame, operand_expected);
                if operator == "?" {
                    self.suppress_refinement -= 1;
                }
                self.literal_negative = previous_negative;
                if value.ty == Ty::Never {
                    return value;
                }
                value.ty = self.representation_at(&value.ty, expr.span.file);
                if operator == "-"
                    && let Some(pending) = self.numeric_pending_unary(&value, operator, expr.span)
                {
                    return pending;
                }
                match operator.as_str() {
                    "^mut" => {
                        if value.permission != Permission::Write {
                            self.error(
                                "E0520",
                                expr.span,
                                "sharing marker cannot grant write authority",
                                [value.cause],
                            );
                        }
                        self.access(&value, None, Mode::Retain, expr.span, frame);
                        value.marker = true;
                        value.cause = self.cause(
                            CauseKind::Retention,
                            expr.span,
                            "checked local writable-sharing marker",
                            [value.cause],
                        );
                    }
                    "!" => {
                        self.require_boolean(&value, expr.span);
                        value.constant = match value.constant {
                            Some(Constant::Bool(b)) => Some(Constant::Bool(!b)),
                            _ => None,
                        };
                        value.condition_inspections.negate();
                        value.cause = self.cause(
                            CauseKind::Projection,
                            expr.span,
                            "boolean negation reverses the actual condition outcomes",
                            [value.cause],
                        );
                        self.record_condition_evaluation(
                            &mut value,
                            super::super::result_conditions::ConditionKind::Negation,
                            expr.span,
                            frame,
                        );
                    }
                    "-" | "~" => {
                        if operator == "~" && !matches!(value.ty, Ty::Int(_)) {
                            self.error(
                                "E0327",
                                expr.span,
                                "bitwise complement requires an integer",
                                [value.cause],
                            );
                        }
                        if !matches!(value.ty, Ty::Int(_) | Ty::Float(_)) {
                            self.error(
                                "E0301",
                                expr.span,
                                "numeric unary operator requires a number",
                                [value.cause],
                            );
                        }
                        value.constant = if operator == "-" {
                            match value.constant {
                                Some(Constant::Integer(i)) => {
                                    i.checked_neg().map(Constant::Integer)
                                }
                                _ => None,
                            }
                        } else {
                            None
                        };
                    }
                    "?" => return self.propagate_value(value, expr.span, frame),
                    _ => self.unsupported(expr.span, format!("unary operator {operator}")),
                }
                value.static_coordinate = if operator == "-" && value.static_coordinate.is_some() {
                    if let Some(Constant::Integer(number)) = value.constant {
                        Some(StaticCoordinate::Index(number))
                    } else {
                        None
                    }
                } else {
                    None
                };
                value
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "!>" || operator == "|>" {
                    if let ExprKind::Derive { base: None, recipe } = &right.kind {
                        let (value, observation) = self.expression_observed(left, frame);
                        if value.ty == Ty::Never {
                            self.preview_expression(recipe, frame);
                            return value;
                        }
                        return self.derive_value(value, observation, recipe, expr.span, frame);
                    }
                    return self.application_expression(expr, expected, frame, source_call_event);
                }
                let tag_test = matches!(operator.as_str(), "==" | "!=")
                    && (narrowing::is_none(left, frame) || narrowing::is_none(right, frame));
                if tag_test {
                    self.suppress_refinement += 1;
                }
                let numeric_operands = matches!(
                    operator.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "%"
                        | "/?"
                        | "%?"
                        | "+%"
                        | "-%"
                        | "*%"
                        | "&"
                        | "|"
                        | "^"
                        | "=="
                        | "!="
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                );
                let operand_hint = numeric_operands
                    .then(|| {
                        expected
                            .filter(|ty| super::numeric::numeric_type(ty).is_some())
                            .cloned()
                            .or_else(|| self.rigid_numeric_argument(left, frame))
                            .or_else(|| self.rigid_numeric_argument(right, frame))
                    })
                    .flatten();
                let operand_expected = operand_hint.as_ref();
                let defer_left = numeric_operands
                    && operand_expected.is_none()
                    && super::numeric_pending::candidate(left)
                    && (self.numeric.deferred_depth > 0
                        || matches!(
                            right.kind,
                            ExprKind::Call { .. }
                                | ExprKind::Field { .. }
                                | ExprKind::Index { .. }
                                | ExprKind::ComputedField { .. }
                        ));
                self.numeric.deferred_depth += usize::from(defer_left);
                let mut a = self.expression_expected(left, frame, operand_expected);
                self.numeric.deferred_depth -= usize::from(defer_left);
                let left_recency = self.recency_moves.len();
                if tag_test {
                    self.suppress_refinement -= 1;
                }
                if a.ty == Ty::Never {
                    return a;
                }
                a.ty = self.representation_at(&a.ty, expr.span.file);
                if operator == "??" {
                    let mut a = a;
                    if matches!(self.expanded(&a.ty, &mut BTreeSet::new()), Ty::Result(..)) {
                        self.inspect_result(&a);
                    }
                    let mut before = self.snapshot_flow();
                    if matches!(self.expanded(&a.ty, &mut BTreeSet::new()), Ty::Result(..)) {
                        let guard = self.channel_result_outcome(&a, true);
                        if !before.channel_project(&guard) && self.channel_has_messages() {
                            self.unsupported(
                                expr.span,
                                "Result fallback success requires a bounded channel outcome proof",
                            );
                        }
                        self.channel_assume_result(&a, false, expr.span, frame);
                    }
                    if matches!(a.ty, Ty::Optional(_)) {
                        self.discharge_absent_results(&a, expr.span);
                    }
                    self.fallback_boundaries
                        .push((frame.owner, self.loop_depth));
                    let fallback = self.expression(right, frame);
                    self.fallback_boundaries.pop();
                    self.transport_value_since(&mut a, left_recency);
                    let fallback_recency = self.recency_moves.len();
                    if let Ty::Result(ok, _) = self.expanded(&a.ty, &mut BTreeSet::new()) {
                        if fallback.callables.is_empty() {
                            self.error(
                                "E0711",
                                right.span,
                                "Result fallback requires an error-consuming callable",
                                [fallback.cause],
                            );
                            return self.unit(expr.span);
                        }
                        let error = self.result_payload(&a, false, expr.span, frame);
                        let recovered = self.invoke(
                            &fallback,
                            vec![(ParameterMode::Read, error, expr.span)],
                            expr.span,
                            frame,
                        );
                        self.transport_value_since(&mut a, fallback_recency);
                        let mut success = self.result_payload(&a, true, expr.span, frame);
                        if *ok != Ty::Unknown {
                            self.require_type(&recovered, &ok, expr.span);
                            success.ty = *ok;
                        }
                        return self.conditional_flow(
                            &before,
                            &success,
                            &recovered,
                            a.result_tag.map(|success| !success),
                            expr.span,
                        );
                    }
                    if let Ty::Optional(inner) = a.ty.clone() {
                        let execute = a.option_tag.map(|some| !some);
                        a = self.optional_payload(&a, *inner);
                        if fallback.ty == Ty::Never {
                            return self
                                .conditional_flow(&before, &a, &fallback, execute, expr.span);
                        }
                        self.require_type(&fallback, &a.ty, right.span);
                        return self.conditional_flow(&before, &a, &fallback, execute, expr.span);
                    }
                    self.error(
                        "E0714",
                        expr.span,
                        "fallback requires an optional value",
                        [a.cause],
                    );
                    return a;
                }
                if (operator == "&&" && a.constant == Some(Constant::Bool(false)))
                    || (operator == "||" && a.constant == Some(Constant::Bool(true)))
                {
                    let skipped = self.preview_expression(right, frame);
                    self.require_boolean(&skipped, right.span);
                    return a;
                }
                let conditional = matches!(operator.as_str(), "&&" | "||") && a.constant.is_none();
                let before = conditional.then(|| self.snapshot_flow());
                if matches!(operator.as_str(), "&&" | "||") {
                    self.inspect_condition_value(&a, operator == "&&", left.span);
                    self.refine_condition(left, operator == "&&", a.cause, frame);
                }
                if tag_test {
                    self.suppress_refinement += 1;
                }
                let right_hint = operand_hint.clone().or_else(|| {
                    (numeric_operands
                        && !a.unsuffixed_numeric
                        && super::numeric::numeric_type(&a.ty).is_some())
                    .then(|| a.ty.clone())
                });
                let right_expected = right_hint.as_ref();
                let defer_right = numeric_operands
                    && right_expected.is_none()
                    && super::numeric_pending::candidate(right)
                    && (self.numeric.deferred_depth > 0
                        || matches!(
                            left.kind,
                            ExprKind::Call { .. }
                                | ExprKind::Field { .. }
                                | ExprKind::Index { .. }
                                | ExprKind::ComputedField { .. }
                        ));
                self.numeric.deferred_depth += usize::from(defer_right);
                let mut b = self.expression_expected(right, frame, right_expected);
                self.numeric.deferred_depth -= usize::from(defer_right);
                self.transport_value_since(&mut a, left_recency);
                b.ty = self.representation_at(&b.ty, expr.span.file);
                if tag_test {
                    self.suppress_refinement -= 1;
                }
                if b.ty == Ty::Never && before.is_none() {
                    if let Ty::NumericHole(id) = a.ty {
                        let expected = self
                            .numeric_preference(id)
                            .unwrap_or_else(|| Ty::Int("int".into()));
                        self.commit_numeric_value(&mut a, &expected);
                    }
                    return b;
                }
                if self.numeric.deferred_depth == 0 {
                    self.resolve_numeric_operands(&mut a, &mut b, expr.span);
                }
                if let Some(pending) = self.numeric_pending_binary(&a, &b, operator, expr.span) {
                    return pending;
                }
                if matches!(operator.as_str(), "==" | "!=") && !tag_test {
                    self.deep_read(&a, left.span, frame);
                    self.deep_read(&b, right.span, frame);
                }
                if operator == "in" {
                    if matches!(self.expanded(&b.ty, &mut BTreeSet::new()), Ty::Array(_)) {
                        self.deep_read(&a, left.span, frame);
                        self.deep_read(&b, right.span, frame);
                    } else {
                        self.access(&b, None, Mode::Read, right.span, frame);
                    }
                }
                if matches!(operator.as_str(), "==" | "!=")
                    && !tag_test
                    && (self.contains_callable(&a)
                        || self.contains_callable(&b)
                        || self.contains_resource(&a)
                        || self.contains_resource(&b))
                {
                    self.error(
                        "E0327",
                        expr.span,
                        "structural equality cannot contain callable values at any reachable depth",
                        [a.cause, b.cause],
                    );
                }
                if matches!(operator.as_str(), "==" | "!=" | "in")
                    && !tag_test
                    && (self.equality_has_generic(&a.ty) || self.equality_has_generic(&b.ty))
                {
                    self.unsupported(expr.span,"structural equality eligibility requires a proved constraint for every generic constituent");
                }
                let shift = matches!(operator.as_str(), "<<" | ">>");
                let provisional = a.unsuffixed_numeric && b.unsuffixed_numeric;
                if !shift
                    && a.unsuffixed_numeric
                    && !b.unsuffixed_numeric
                    && matches!(b.ty, Ty::Int(_) | Ty::Float(_))
                {
                    if !self.legacy_numeric_context(&a, &b.ty, left.span) {
                        return Value::scalar(Ty::Unknown, None, a.cause);
                    }
                    a.ty = b.ty.clone();
                }
                if !shift
                    && b.unsuffixed_numeric
                    && !a.unsuffixed_numeric
                    && matches!(a.ty, Ty::Int(_) | Ty::Float(_))
                {
                    if !self.legacy_numeric_context(&b, &a.ty, right.span) {
                        return Value::scalar(Ty::Unknown, None, b.cause);
                    }
                    b.ty = a.ty.clone();
                }
                let numeric = matches!(a.ty, Ty::Int(_) | Ty::Float(_));
                let arithmetic = matches!(
                    operator.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "%"
                        | "/?"
                        | "%?"
                        | "+%"
                        | "-%"
                        | "*%"
                        | "&"
                        | "|"
                        | "^"
                        | "<<"
                        | ">>"
                );
                if arithmetic && matches!(a.ty, Ty::Optional(_)) {
                    self.error(
                        self.optional_error_code(&a),
                        left.span,
                        "optional operand requires a valid Some refinement",
                        [a.cause],
                    );
                }
                if arithmetic && matches!(b.ty, Ty::Optional(_)) {
                    self.error(
                        self.optional_error_code(&b),
                        right.span,
                        "optional operand requires a valid Some refinement",
                        [b.cause],
                    );
                }
                let bitwise = matches!(operator.as_str(), "&" | "|" | "^" | "<<" | ">>");
                let ordering = matches!(operator.as_str(), "<" | ">" | "<=" | ">=");
                if (bitwise && (!matches!(a.ty, Ty::Int(_)) || !matches!(b.ty, Ty::Int(_))))
                    || (ordering
                        && (!matches!(a.ty, Ty::Int(_) | Ty::Float(_) | Ty::Str | Ty::Bytes)
                            || !matches!(b.ty, Ty::Int(_) | Ty::Float(_) | Ty::Str | Ty::Bytes)))
                {
                    self.error(
                        "E0327",
                        expr.span,
                        "operator operands are outside its admitted value family",
                        [a.cause, b.cause],
                    );
                }
                let wrapping = matches!(operator.as_str(), "+%" | "-%" | "*%");
                if (arithmetic && !numeric)
                    || (wrapping
                        && (!matches!(a.ty, Ty::Int(_))
                            || matches!(&a.ty,Ty::Int(name)if name=="bigint")))
                    || (matches!(operator.as_str(), "==" | "!=")
                        && !tag_test
                        && (!a.callables.is_empty() || !b.callables.is_empty()))
                {
                    self.error(
                        "E0327",
                        expr.span,
                        "operator is not defined for these operand types",
                        [a.cause, b.cause],
                    );
                }
                let ty = if matches!(
                    operator.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "in" | "&&" | "||"
                ) {
                    Ty::Bool
                } else {
                    a.ty.clone()
                };
                if matches!(operator.as_str(), "&&" | "||") {
                    self.require_boolean(&a, left.span);
                    self.require_boolean(&b, right.span);
                } else if operator == "in" {
                    let element = match self.collection_type(&b) {
                        Ty::Array(element) | Ty::Set(element) | Ty::Range(element) => {
                            Some(*element)
                        }
                        Ty::Map(key, _) => Some(*key),
                        _ => None,
                    };
                    if let Some(element) = element {
                        self.require_type(&a, &element, left.span);
                        if self.contains_callable(&a) {
                            self.error(
                                "E0327",
                                expr.span,
                                "membership equality cannot compare callable values",
                                [a.cause],
                            );
                        }
                    } else {
                        self.error(
                            "E0327",
                            right.span,
                            "membership requires an array, map, set or integer range",
                            [b.cause],
                        );
                    }
                } else if matches!(operator.as_str(), "==" | "!=")
                    && matches!((&a.ty,&b.ty),(Ty::Named(left),Ty::Named(right))if left!=right)
                    && self
                        .constructors
                        .values()
                        .any(|constructor| constructor.owner == a.ty)
                    && self
                        .constructors
                        .values()
                        .any(|constructor| constructor.owner == b.ty)
                {
                    self.error(
                        "E0305",
                        expr.span,
                        "distinct nominal or sum owners have distinct value identities",
                        [a.cause, b.cause],
                    );
                } else if shift {
                    // The count has its own integer type, independent of the
                    // shifted value's width and signedness.
                } else if !provisional {
                    self.require_type(&b, &a.ty, right.span);
                } else if provisional
                    && !matches!(
                        (&a.ty, &b.ty),
                        (Ty::Int(_), Ty::Int(_)) | (Ty::Float(_), Ty::Float(_))
                    )
                {
                    self.error(
                        "E0301",
                        right.span,
                        "numeric operand families differ",
                        [a.cause, b.cause],
                    );
                }
                let cause = self.cause(
                    CauseKind::Source,
                    expr.span,
                    format!("operator {operator}"),
                    [a.cause, b.cause],
                );
                if shift {
                    self.type_alternatives.insert(cause.0, vec![a.clone()]);
                }
                let constant = match (&a.constant, &b.constant, operator.as_str()) {
                    (Some(Constant::Integer(a)), Some(Constant::Integer(b)), "+") => {
                        a.checked_add(*b).map(Constant::Integer)
                    }
                    (Some(Constant::Integer(a)), Some(Constant::Integer(b)), "-") => {
                        a.checked_sub(*b).map(Constant::Integer)
                    }
                    (Some(Constant::Integer(a)), Some(Constant::Integer(b)), "*") => {
                        a.checked_mul(*b).map(Constant::Integer)
                    }
                    (Some(a), Some(b), "==") => Some(Constant::Bool(a == b)),
                    (Some(a), Some(b), "!=") => Some(Constant::Bool(a != b)),
                    _ => None,
                };
                let mut value = Value::scalar(ty, constant, cause);
                if arithmetic {
                    value.constant = self.numeric_arithmetic_constant(&value.ty, value.constant);
                }
                value.numeric.include(&a.numeric);
                value.numeric.include(&b.numeric);
                if matches!(operator.as_str(), "/?" | "%?") {
                    // Checked arithmetic carries the successful numeric payload;
                    // the tag stays unknown until execution.
                    value.unsuffixed_numeric = a.unsuffixed_numeric && b.unsuffixed_numeric;
                    let payload = value.clone();
                    value.ty = Ty::Optional(Box::new(value.ty));
                    value.unsuffixed_numeric = false;
                    value.construction = true;
                    value.option_payload = Some(Box::new(payload));
                } else {
                    value.unsuffixed_numeric = if shift {
                        a.unsuffixed_numeric
                    } else {
                        a.unsuffixed_numeric && b.unsuffixed_numeric && numeric
                    };
                }
                value.abnormal = b.abnormal;
                if let Some(before) = &before {
                    value = self.conditional_flow(before, &a, &value, None, expr.span);
                }
                if matches!(operator.as_str(), "&&" | "||") {
                    value.condition_inspections = if b.ty == Ty::Never {
                        a.condition_inspections.clone()
                    } else {
                        a.condition_inspections.sequence(
                            match a.constant {
                                Some(Constant::Bool(v)) => Some(v),
                                _ => None,
                            },
                            &b.condition_inspections,
                            match b.constant {
                                Some(Constant::Bool(v)) => Some(v),
                                _ => None,
                            },
                            operator == "&&",
                        )
                    };
                    self.record_condition_evaluation(
                        &mut value,
                        if operator == "&&" {
                            super::super::result_conditions::ConditionKind::Conjunction
                        } else {
                            super::super::result_conditions::ConditionKind::Disjunction
                        },
                        expr.span,
                        frame,
                    );
                }
                value
            }
            ExprKind::Call { .. } => {
                self.application_expression(expr, expected, frame, source_call_event)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition_syntax = &**condition;
                let condition = self.expression(condition, frame);
                if condition.ty == Ty::Never {
                    let mut valid = self
                        .preview_expression_source(then_branch, frame, expected, source)
                        .source_valid;
                    if let Some(other) = else_branch {
                        valid &= self
                            .preview_expression_source(other, frame, expected, source)
                            .source_valid;
                    }
                    *source_handled = Some(valid);
                    return condition;
                }
                self.require_boolean(&condition, expr.span);
                if let Some(Constant::Bool(chosen)) = condition.constant {
                    let refinements = self.refinements.clone();
                    self.refine_condition(condition_syntax, !chosen, condition.cause, frame);
                    let dead = if chosen {
                        else_branch
                            .as_ref()
                            .map(|branch| {
                                self.preview_expression_source(branch, frame, expected, source)
                            })
                            .unwrap_or_else(|| SourceExpression {
                                value: self.unit(expr.span),
                                observation: None,
                                source_valid: true,
                            })
                    } else {
                        self.preview_expression_source(then_branch, frame, expected, source)
                    };
                    let mut source_valid = dead.source_valid;
                    let mut dead = dead.value;
                    let dead_recency = self.recency_moves.len();
                    self.refinements = refinements;
                    self.inspect_condition_value(&condition, chosen, condition_syntax.span);
                    self.refine_condition(condition_syntax, chosen, condition.cause, frame);
                    let selected = if chosen {
                        self.expression_expected_source(then_branch, frame, expected, source)
                    } else {
                        else_branch
                            .as_ref()
                            .map(|branch| {
                                self.expression_expected_source(branch, frame, expected, source)
                            })
                            .unwrap_or_else(|| SourceExpression {
                                value: self.unit(expr.span),
                                observation: None,
                                source_valid: true,
                            })
                    };
                    source_valid &= selected.source_valid;
                    let mut selected = selected.value;
                    self.transport_value_since(&mut dead, dead_recency);
                    self.require_branch_types(&mut selected, &mut dead, expr.span);
                    if selected.ty != Ty::Never && dead.ty != Ty::Never {
                        selected.ty = join_type_holes(&selected.ty, &dead.ty);
                    }
                    let cause=self.cause(CauseKind::BranchJoin,expr.span,"constant condition selects runtime state while both source branches retain type constraints",[selected.cause,dead.cause]);
                    self.type_alternatives
                        .insert(cause.0, vec![selected.clone(), dead]);
                    selected.cause = cause;
                    *source_handled = Some(source_valid);
                    return selected;
                }
                let before_duties = self.result_duties.clone();
                let before = self.snapshot_flow();
                let return_count = frame.returned.len();
                let before_cursor = self.recency_moves.len();
                let before_accesses = frame.obligations.accesses.len();
                self.inspect_condition_value(&condition, true, condition_syntax.span);
                self.refine_condition(condition_syntax, true, condition.cause, frame);
                let left = self.expression_expected_source(then_branch, frame, expected, source);
                let mut source_valid = left.source_valid;
                let mut left = left.value;
                self.transport_frame_prefix(frame, before_cursor, before_accesses, return_count);
                let left_state = self.snapshot_flow();
                let left_cursor = self.recency_moves.len();
                let left_accesses = frame.obligations.accesses.len();
                let left_returns = frame.returned.len();
                self.restore_definition_state(&before);
                self.inspect_condition_value(&condition, false, condition_syntax.span);
                self.refine_condition(condition_syntax, false, condition.cause, frame);
                let right = else_branch
                    .as_ref()
                    .map(|branch| self.expression_expected_source(branch, frame, expected, source))
                    .unwrap_or_else(|| SourceExpression {
                        value: self.unit(expr.span),
                        observation: None,
                        source_valid: true,
                    });
                source_valid &= right.source_valid;
                let mut right = right.value;
                self.transport_frame_prefix(frame, left_cursor, left_accesses, left_returns);
                // Type reception can inspect aggregate members. It needs the
                // current graph too; branch_flow still receives the original
                // epoch and performs its own checked snapshot transport.
                let mut current_left = self.transport_flow_value(&left, &left_state, expr.span);
                self.require_branch_types(&mut current_left, &mut right, expr.span);
                left.ty = current_left.ty;
                let joined = self.branch_flow(&before, &left_state, &left, &right, expr.span);
                if frame.returned.len() != return_count
                    && before_duties
                        .iter()
                        .any(|duty| duty.owner == frame.owner && !duty.covered && !duty.abnormal)
                    && frame.returned[return_count..]
                        .iter()
                        .any(|value| !self.result_return_covered(frame.owner, value))
                {
                    self.unsupported(expr.span,"conditional callable exits require path-sensitive Result obligation summaries");
                }
                *source_handled = Some(source_valid);
                joined
            }
            ExprKind::Control { operation, value } => {
                let escapes_fallback = self.fallback_boundaries.iter().any(|(owner, depth)| {
                    *owner == frame.owner
                        && (matches!(operation, ControlOperation::Return)
                            || (matches!(
                                operation,
                                ControlOperation::Last | ControlOperation::Next
                            ) && self.loop_depth <= *depth))
                });
                if escapes_fallback {
                    self.error(
                        "E0710",
                        expr.span,
                        "control transfer escapes a fallback expression",
                        [],
                    );
                }
                let return_expected = match operation {
                    ControlOperation::Return => frame.expected_return.clone(),
                    ControlOperation::Resume => self
                        .resume_contexts
                        .last()
                        .map(|context| context.result.clone()),
                    _ => None,
                };
                let return_source = match operation {
                    ControlOperation::Return => frame.expected_return_source.clone(),
                    ControlOperation::Resume => self
                        .resume_contexts
                        .last()
                        .and_then(|context| context.source.clone()),
                    _ => None,
                };
                let value = value
                    .as_ref()
                    .map(|v| {
                        let mut supplied = self.expression_expected_source(
                            v,
                            frame,
                            return_expected.as_ref(),
                            return_source.as_ref(),
                        );
                        if *operation == ControlOperation::Resume
                            && let Some(target) = &return_source
                        {
                            let valid = self.require_source_reception(
                                target,
                                v,
                                &supplied.value,
                                supplied.observation,
                                frame,
                            );
                            if valid && let Some(syntax) = target.syntax.as_ref() {
                                self.with_typing_environment(&target.environment, |checker| {
                                    checker.ascribe_signature(&mut supplied.value, syntax)
                                });
                            }
                        }
                        supplied.value
                    })
                    .unwrap_or_else(|| self.unit(expr.span));
                match operation {
                    ControlOperation::Return => {
                        *source_handled = Some(frame.return_source_valid);
                        self.record_result_control_exit(frame.owner, &value, expr.span, true);
                        self.return_results(&value);
                        self.record_foreign_return(&value, frame);
                        frame.returned.push(value.clone());
                        let mut never = value.clone();
                        never.ty = Ty::Never;
                        never.unsuffixed_numeric = false;
                        never.literal_number = false;
                        never
                    }
                    ControlOperation::Resume => {
                        // Resumption needs an independent per-activation exit
                        // proof before a surrounding Result loop can close it.
                        self.result_exit_checks.insert(
                            (
                                frame.owner.0,
                                expr.span.file.0,
                                expr.span.start,
                                expr.span.end,
                            ),
                            false,
                        );
                        self.resume_operation(value, expr.span, frame)
                    }
                    ControlOperation::Last | ControlOperation::Next => {
                        self.record_result_control_exit(frame.owner, &value, expr.span, false);
                        if self.loop_depth == 0 {
                            self.error(
                                "E0707",
                                expr.span,
                                "loop control requires an enclosing loop in this callable",
                                [value.cause],
                            );
                        }
                        if *operation == ControlOperation::Last {
                            if self.loop_unit.last() == Some(&true) {
                                self.require_type(&value, &Ty::Unit, expr.span);
                            }
                            if let Some((_, values)) = self
                                .loop_breaks
                                .iter_mut()
                                .rev()
                                .find(|(owner, _)| *owner == frame.owner)
                            {
                                values.push(value.clone());
                            }
                        } else {
                            self.require_type(&value, &Ty::Unit, expr.span);
                            if let Some((_, backedge)) = self
                                .loop_continuations
                                .iter_mut()
                                .rev()
                                .find(|(owner, _)| *owner == frame.owner)
                            {
                                *backedge = true;
                            }
                        }
                        let mut never = value;
                        never.ty = Ty::Never;
                        never.unsuffixed_numeric = false;
                        never.literal_number = false;
                        never
                    }
                }
            }
            ExprKind::While { condition, body } => {
                let condition = self.expression(condition, frame);
                if condition.ty == Ty::Never {
                    self.loop_depth += 1;
                    self.loop_breaks.push((frame.owner, Vec::new()));
                    self.loop_continuations.push((frame.owner, false));
                    self.loop_unit.push(true);
                    self.preview_block_source(body, frame, None, None);
                    self.loop_unit.pop();
                    self.loop_breaks.pop();
                    self.loop_continuations.pop();
                    self.loop_depth -= 1;
                    return condition;
                }
                self.require_boolean(&condition, expr.span);
                if condition.constant != Some(Constant::Bool(false)) {
                    for value in self.loop_body(body, frame, expr.span, true, false) {
                        self.require_type(&value, &Ty::Unit, expr.span);
                    }
                } else {
                    self.loop_depth += 1;
                    self.loop_breaks.push((frame.owner, Vec::new()));
                    self.loop_continuations.push((frame.owner, false));
                    self.loop_unit.push(true);
                    let _ = self.preview_block_source(body, frame, None, None);
                    self.loop_breaks.pop();
                    self.loop_continuations.pop();
                    self.loop_unit.pop();
                    self.loop_depth -= 1;
                }
                self.unit(expr.span)
            }
            ExprKind::Loop(body) => {
                let mut values = self
                    .loop_body(body, frame, expr.span, false, false)
                    .into_iter();
                if let Some(mut first) = values.next() {
                    for value in values {
                        self.require_type(&value, &first.ty, expr.span);
                        let cause = self.cause(
                            CauseKind::BranchJoin,
                            expr.span,
                            "loop result includes every reachable last value",
                            [first.cause, value.cause],
                        );
                        first = first.join(&value, self.choice(), cause);
                    }
                    first
                } else {
                    let mut value = self.unit(expr.span);
                    value.ty = Ty::Never;
                    value
                }
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                let iterable = self.expression(iterable, frame);
                if !matches!(
                    self.expanded(&iterable.ty, &mut BTreeSet::new()),
                    Ty::Array(_) | Ty::Map(..) | Ty::Set(_) | Ty::Range(_)
                ) {
                    self.error(
                        "E0355",
                        expr.span,
                        "value is not an admitted built-in iteration source",
                        [iterable.cause],
                    );
                    return self.unit(expr.span);
                }
                let child = if let Ty::Map(key, value) = self.collection_type(&iterable) {
                    let key_value =
                        self.project(&iterable, Slot::Field("key".into()), expr.span, frame, true);
                    let value_value =
                        self.project(&iterable, Slot::AnyIndex, expr.span, frame, true);
                    let node = self.allocate_owned(expr.span, 0x4000_0000, frame.owner);
                    let cause = self.heap.nodes[node.0 as usize].cause;
                    let mut pair = Value::reference(Ty::Tuple(vec![*key, *value]), node, cause);
                    pair.permission = Permission::Read;
                    pair.construction = false;
                    pair.results = value_value.results.clone();
                    pair.must_results = value_value.must_results.clone();
                    pair.participants = iterable.participants.clone();
                    pair.sources = iterable.sources.clone();
                    self.store_field(node, Slot::Tuple(0), key_value);
                    self.store_field(node, Slot::Tuple(1), value_value);
                    pair
                } else {
                    self.project(&iterable, Slot::AnyIndex, expr.span, frame, true)
                };
                let old = frame.env.clone();
                self.bind_iteration_pattern(child, pattern, expr.span, frame);
                let empty = matches!(
                    self.expanded(&iterable.ty, &mut BTreeSet::new()),
                    Ty::Array(_)
                ) && self.known_array_length(&iterable) == Some(0);
                let may_be_empty = !self.concurrent_iteration_definitely_nonempty(&iterable);
                let before = may_be_empty.then(|| self.snapshot_flow());
                let previous_frame = empty.then(|| frame.clone());
                let at_most_once = self.concurrent_iteration_at_most_once(&iterable);
                self.active_iterations.push(iterable.origins);
                for value in self.loop_body(body, frame, expr.span, true, at_most_once) {
                    self.require_type(&value, &Ty::Unit, expr.span);
                }
                self.active_iterations.pop();
                if let Some(before) = before {
                    if empty {
                        self.restore_preview(&before);
                        *frame = previous_frame.unwrap();
                    } else {
                        let unit = self.unit(expr.span);
                        let _ = self.conditional_flow(&before, &unit, &unit, None, expr.span);
                    }
                }
                frame.env = old;
                self.unit(expr.span)
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                body,
            } => {
                let contextual =
                    source
                        .and_then(|target| target.syntax.as_deref())
                        .and_then(|syntax| match &syntax.kind {
                            TypeKind::Callable {
                                parameters: expected,
                                result,
                                ..
                            } if expected.len() == parameters.len()
                                && expected
                                    .iter()
                                    .zip(parameters)
                                    .all(|(expected, actual)| expected.mode == actual.mode) =>
                            {
                                Some((expected, result))
                            }
                            _ => None,
                        });
                let mut elaborated = parameters.clone();
                let mut result_type = return_type.clone();
                if let Some((expected_parameters, expected_result)) = contextual {
                    for (actual, expected) in elaborated.iter_mut().zip(expected_parameters) {
                        if actual.ty.is_none() {
                            actual.ty = expected.ty.clone();
                        }
                    }
                    if result_type.is_none() {
                        result_type = expected_result.as_deref().cloned();
                    }
                }
                // This elaborates missing syntax, then runs the existing
                // latent invocation/body checks with those real parameters.
                // No expected descriptor is installed on an unchecked body.
                self.lambda(
                    &elaborated,
                    result_type.as_ref(),
                    annotations,
                    body,
                    expr,
                    frame,
                )
            }
            _ => {
                self.unsupported(
                    expr.span,
                    format!("expression {:?}", std::mem::discriminant(&expr.kind)),
                );
                let cause = self.cause(
                    CauseKind::MissingProof,
                    expr.span,
                    "expression analysis is not implemented",
                    [],
                );
                Value::scalar(Ty::Unknown, None, cause)
            }
        }
    }
    fn require_boolean(&mut self, value: &Value, span: Span) {
        if !matches!(
            self.expanded(&value.ty, &mut BTreeSet::new()),
            Ty::Bool | Ty::Never
        ) {
            self.error(
                "E0350",
                span,
                "condition or logical operand must be bool",
                [value.cause],
            );
        }
    }
    pub(super) fn contains_callable(&self, value: &Value) -> bool {
        if !self.graph_callables(value).is_empty() {
            return true;
        }
        if !value.callables.is_empty() {
            return true;
        }
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        self.fields.iter().any(|((node, _), child)| {
            reachable.contains(node)
                && (!child.callables.is_empty()
                    || matches!(
                        self.expanded(&child.ty, &mut BTreeSet::new()),
                        Ty::Callable(..)
                    ))
        })
    }
    pub(super) fn equality_has_generic(&self, ty: &Ty) -> bool {
        fn visit(checker: &Checker, ty: &Ty, seen: &mut BTreeSet<String>) -> bool {
            if !seen.insert(format!("{ty:?}")) {
                return false;
            }
            match checker.expanded(ty, &mut BTreeSet::new()) {
                Ty::Generic(_)
                | Ty::StaticKey(_)
                | Ty::Projection { .. }
                | Ty::OpenRecord { .. } => true,
                Ty::Optional(inner)
                | Ty::Immutable(inner)
                | Ty::Array(inner)
                | Ty::Set(inner)
                | Ty::Range(inner) => visit(checker, &inner, seen),
                Ty::Map(a, b) | Ty::Result(a, b) => {
                    visit(checker, &a, seen) || visit(checker, &b, seen)
                }
                Ty::Applied { arguments, .. } => arguments.iter().any(|argument| match argument {
                    TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                        visit(checker, ty, seen)
                    }
                    TypeArgument::Symbolic(_) => true,
                    TypeArgument::Static(_) => false,
                }),
                Ty::Tuple(items) => items.iter().any(|ty| visit(checker, ty, seen)),
                Ty::Record(fields) => fields.values().any(|(_, ty)| visit(checker, ty, seen)),
                _ => false,
            }
        }
        visit(self, ty, &mut BTreeSet::new())
    }
    fn preview_record_members(&mut self, members: &[RecordMember], frame: &mut Frame) {
        for member in members {
            match member {
                RecordMember::Field(field) => {
                    self.preview_expression(&field.value, frame);
                }
                RecordMember::Spread(value) => {
                    self.preview_expression(value, frame);
                }
            }
        }
    }
    pub(super) fn optional_payload(&mut self, source: &Value, inner: Ty) -> Value {
        let mut value = source
            .option_payload
            .as_ref()
            .map(|payload| *payload.clone())
            .unwrap_or_else(|| {
                let mut value = source.clone();
                value.source_type_witness = None;
                value.option_payload = None;
                value.option_tag = None;
                value.option_identity = None;
                value
            });
        value.ty = inner;
        self.project_optional_source_type(source, &mut value);
        value.permission = value.permission.meet(source.permission);
        value.construction &= source.construction;
        value.publication = if value.publication == Publication::Immutable
            || source.publication == Publication::Immutable
        {
            Publication::Immutable
        } else {
            source.publication
        };
        value.marker = source.marker || (source.construction && value.marker);
        value.retention_result =
            source.retention_result || (source.construction && value.retention_result);
        value.through_return |= source.through_return;
        value.participants = source.participants.clone();
        value.sources = source.sources.clone();
        value.scoped.extend(&source.scoped);
        value.temporary |= source.temporary;
        if value.ty.scalar() {
            if !source.sources.is_empty() || source.through_return {
                value.unsuffixed_numeric = false;
                value.literal_number = false;
            }
            value.origins = Origins::default();
            value.participants.clear();
            value.temporary = false;
            value.scoped.clear();
        }
        value
    }
    pub(super) fn wrap_optional(&self, payload: Value, tag: Option<bool>) -> Value {
        let mut value = payload.clone();
        value.option_identity = None;
        value.source_type_witness = None;
        value.ty = Ty::Optional(Box::new(payload.ty.clone()));
        value.condition_inspections = Default::default();
        value.option_payload = Some(Box::new(payload));
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value.callables.clear();
        value.signature = None;
        value.callable_bounds.clear();
        value.callable_returns.clear();
        value.result_payload = None;
        value.result_success = None;
        value.result_error = None;
        value.result_tag = None;
        value.variant_tag = None;
        value.variant_payload = None;
        value.variant_witnesses.clear();
        value.option_tag = tag;
        value.constant = None;
        value.outer_results.clear();
        value.must_outer_results.clear();
        if tag != Some(true) {
            value.must_results.clear();
        }
        value
    }
    pub(super) fn none_value(&mut self, span: Span) -> Value {
        let mut value = self.unit(span);
        value.ty = Ty::Optional(Box::new(Ty::Unknown));
        value.option_tag = Some(false);
        value.constant = None;
        value
    }
    pub(super) fn literal(&mut self, literal: &Literal, span: Span, _frame: &mut Frame) -> Value {
        let cause = self.cause(CauseKind::Source, span, "literal", []);
        match literal {
            Literal::Unit => Value::scalar(Ty::Unit, Some(Constant::Unit), cause),
            Literal::Bool(b) => Value::scalar(Ty::Bool, Some(Constant::Bool(*b)), cause),
            Literal::Integer(raw) => {
                let raw = raw.replace('_', "");
                let suffix = [
                    "bigint", "int", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
                ]
                .into_iter()
                .find(|suffix| raw.ends_with(suffix));
                let number = &raw[..raw.len() - suffix.map(str::len).unwrap_or(0)];
                let parsed = if let Some(n) = number
                    .strip_prefix("0x")
                    .or_else(|| number.strip_prefix("0X"))
                {
                    i128::from_str_radix(n, 16).ok()
                } else if let Some(n) = number
                    .strip_prefix("0b")
                    .or_else(|| number.strip_prefix("0B"))
                {
                    i128::from_str_radix(n, 2).ok()
                } else if let Some(n) = number
                    .strip_prefix("0o")
                    .or_else(|| number.strip_prefix("0O"))
                {
                    i128::from_str_radix(n, 8).ok()
                } else {
                    number.parse().ok()
                };
                let name = suffix.unwrap_or("int");
                if parsed.is_none() && name != "bigint" {
                    // Syntax validation already checked digits and suffixes.
                    // Exceeding the parser's i128 magnitude also exceeds every
                    // admitted fixed-width type, so this is a range error.
                    self.error(
                        "E0326",
                        span,
                        "integer literal exceeds its selected type's range",
                        [cause],
                    );
                }
                if let Some(number) = parsed {
                    self.integer_range(
                        if self.literal_negative {
                            -number
                        } else {
                            number
                        },
                        name,
                        span,
                        cause,
                    );
                }
                let mut value =
                    Value::scalar(Ty::Int(name.into()), parsed.map(Constant::Integer), cause);
                value.unsuffixed_numeric = suffix.is_none();
                value.literal_number = true;
                if suffix.is_none_or(|suffix| suffix == "int") {
                    value.static_coordinate = parsed.map(StaticCoordinate::Index);
                }
                value
            }
            Literal::Float(raw) => {
                match crate::static_eval::committed_float::decode(raw) {
                    Ok(Some(committed)) => {
                        let mut value =
                            Value::scalar(Ty::Float(format!("f{}", committed.width)), None, cause);
                        value.literal_number = true;
                        return value;
                    }
                    Err(()) => {
                        self.unsupported(span, "invalid committed floating-point literal witness");
                        return Value::scalar(Ty::Unknown, None, cause);
                    }
                    Ok(None) => {}
                }
                let suffix = ["f32", "f64"]
                    .into_iter()
                    .find(|suffix| raw.ends_with(suffix));
                let mut value =
                    Value::scalar(Ty::Float(suffix.unwrap_or("f64").into()), None, cause);
                value.unsuffixed_numeric = suffix.is_none();
                value.literal_number = true;
                value
            }
            Literal::String(raw) => {
                let mut value = Value::scalar(Ty::Str, None, cause);
                value.static_coordinate = crate::lower::decode_text(&raw[1..raw.len() - 1])
                    .ok()
                    .map(StaticCoordinate::Label);
                value
            }
            Literal::RawString(raw) => {
                let mut value = Value::scalar(Ty::Str, None, cause);
                value.static_coordinate =
                    Some(StaticCoordinate::Label(raw[1..raw.len() - 1].into()));
                value
            }
            Literal::Bytes(_) => Value::scalar(Ty::Bytes, None, cause),
        }
    }
    fn name(&mut self, name: &str, span: Span, frame: &mut Frame) -> Value {
        if let Some(&id) = frame.env.get(name) {
            self.use_binding(id, Mode::Read, frame);
            let mut value = self.bindings[id].value.clone();
            let declaration=value.callables.iter().any(|callable|matches!(callable,Callable::Named(function) if self.bindings[id].span==self.functions[*function].syntax.span));
            value = self.named_environment_value(value, declaration);
            if self.bindings[id].cell.is_some_and(|cell| {
                self.uncertain_slots
                    .contains(&(cell, Slot::Field("value".into())))
            }) {
                self.unsupported(span,"a reference-bearing variable slot may have been replaced by an unknown callable");
            }
            self.check_operation_loan(&value, span);
            if let Some(cell) = self.bindings[id].cell {
                frame.obligations.accesses.push(AccessFact {
                    observed_recency: self.recency_moves.len(),
                    recency: self.recency_moves.len(),
                    origin_owners: self.access_owners(&Origins::one(cell)),
                    origins: Origins::one(cell),
                    slot: Some(Slot::Field("value".into())),
                    mode: Mode::Read,
                    participants: value.participants.clone(),
                    cause: value.cause,
                    span,
                });
            }
            value.sources = [id].into();
            value.unsuffixed_numeric = false;
            value.static_coordinate = None;
            return value;
        }
        if let Some(identity) = self
            .type_source
            .environment
            .generic_context
            .get(name)
            .cloned()
            && self.generic_key_bounds.contains_key(&identity)
        {
            let cause = self.cause(CauseKind::Source, span, "static coordinate binder", []);
            let mut value = Value::scalar(Ty::StaticKey(identity.clone()), None, cause);
            value.static_coordinate = self
                .type_source
                .environment
                .static_key_arguments
                .get(&identity)
                .cloned();
            return value;
        }
        if let Some(value) = self.iter_private_name(name, span) {
            return value;
        }
        let builtin_name = name.strip_prefix("Prelude::").unwrap_or(name);
        if let Some(value) = self.constructor_name(name, span, frame) {
            return value;
        }
        if let Some(value) = self.standard_intrinsic_constant(name, span, frame) {
            return value;
        }
        if let Some(ty) = standard::constant_ty(name) {
            let cause = self.cause(
                CauseKind::Source,
                span,
                "standard-library nominal variant constant",
                [],
            );
            return Value::scalar(ty, None, cause);
        }
        if builtin_name == "None" {
            let cause = self.cause(CauseKind::Source, span, "None constructor", []);
            let mut value = Value::scalar(
                Ty::Optional(Box::new(Ty::Unknown)),
                Some(Constant::Unit),
                cause,
            );
            value.option_tag = Some(false);
            value.constant = None;
            return value;
        }
        let builtin = matches!(
            builtin_name,
            "assert"
                | "panic"
                | "len"
                | "clone"
                | "clone_immut"
                | "inner"
                | "Some"
                | "None"
                | "Ok"
                | "Err"
        ) || standard::is_builtin(name)
            || iter::builtin(name)
            || matches!(
                name,
                "File::with_file"
                    | "Process::with_child"
                    | "Io::read_all"
                    | "Io::write_all"
                    | "Div::budget"
            )
            || matches!(
                name,
                "Array::push" | "Array::insert" | "Array::truncate" | "Map::set"
            );
        if let Some(operation) = self.effect_alias_operation(name, span) {
            return if operation.is_empty() {
                self.unit(span)
            } else {
                self.name(&operation, span, frame)
            };
        }
        if builtin || self.operations.contains_key(name) {
            let cause = self.cause(
                CauseKind::Source,
                span,
                format!("builtin or effect operation {name}"),
                [],
            );
            let standard_signature = standard::builtin_callable_signature(name, span);
            let ty = self
                .operations
                .get(name)
                .map(|operation| {
                    Ty::Callable(
                        operation
                            .parameters
                            .iter()
                            .map(|(_, ty)| ty.clone())
                            .collect(),
                        Box::new(operation.result.clone()),
                    )
                })
                .or_else(|| standard_signature.as_ref().map(|(ty, _)| ty.clone()))
                .or_else(|| standard::builtin_callable_type(name))
                .unwrap_or(Ty::Unknown);
            let mut value = Value::scalar(ty, None, cause);
            if let Some(operation) = self.operations.get(name) {
                value.signature = self
                    .effects
                    .get(&operation.effect)
                    .and_then(|effect| {
                        effect
                            .operations
                            .iter()
                            .find(|syntax| syntax.span == operation.span)
                    })
                    .map(|syntax| syntax.parameters.clone());
                if value.signature.is_none() && operation.parameters.is_empty() {
                    value.signature = Some(Vec::new());
                }
            }
            if value.signature.is_none() {
                value.signature = standard_signature.map(|(_, parameters)| parameters);
            }
            if name == "Div::budget" {
                value.ty = Ty::Callable(
                    vec![
                        Ty::Int("int".into()),
                        Ty::Callable(Vec::new(), Box::new(Ty::Unknown)),
                    ],
                    Box::new(Ty::Unknown),
                );
                value.signature = Some(
                    ["limit", "action"]
                        .into_iter()
                        .map(|name| Parameter {
                            pattern: Pattern {
                                hir_id: None,
                                kind: PatternKind::Name(name.into()),
                                span,
                            },
                            mode: ParameterMode::Read,
                            ty: (name == "limit").then(|| TypeExpr {
                                hir_id: None,
                                text: "int".into(),
                                kind: TypeKind::Name {
                                    path: vec!["int".into()],
                                    arguments: Vec::new(),
                                },
                                span,
                            }),
                            default: None,
                            span,
                        })
                        .collect(),
                );
            }
            value.callables.push(Callable::Builtin(builtin_name.into()));
            if builtin && !self.operations.contains_key(name) {
                self.mark_canonical_builtin_source(name, &mut value, span, frame);
            }
            return value;
        }
        if crate::modules::known_standard_identity(name) {
            self.unsupported(
                span,
                format!("standard export {name} has no implemented semantic contract"),
            );
            let cause = self.cause(
                CauseKind::MissingProof,
                span,
                "resolved standard identity requires an implemented contract",
                [],
            );
            let mut value = Value::scalar(Ty::Unknown, None, cause);
            value.callables.push(Callable::Builtin(name.into()));
            return value;
        }
        self.error("E0204", span, format!("unknown name {name}"), []);
        Value::scalar(
            Ty::Unknown,
            None,
            self.cause(CauseKind::Source, span, "unresolved name", []),
        )
    }
    fn application_expression(
        &mut self,
        syntax: &Expr,
        expected: Option<&Ty>,
        frame: &mut Frame,
        source_call_event: &mut Option<super::super::copy_contract::CopyCallEventId>,
    ) -> Value {
        let Some(application) = crate::hir::application::AstApplication::from_ast(syntax) else {
            self.unsupported(syntax.span, "application has no bounded source structure");
            return self.unit(syntax.span);
        };
        let (value, event) = self.evaluate_application(&application, expected, frame);
        *source_call_event = Some(event);
        value
    }
    fn loop_body(
        &mut self,
        body: &Block,
        frame: &mut Frame,
        span: Span,
        unit: bool,
        at_most_once: bool,
    ) -> Vec<Value> {
        self.loop_depth += 1;
        self.loop_allocation_owners.push(frame.owner);
        self.loop_breaks.push((frame.owner, Vec::new()));
        self.loop_continuations.push((frame.owner, false));
        self.loop_unit.push(unit);
        self.loop_fixedpoint(body, frame, span, at_most_once);
        let values = self.loop_breaks.pop().unwrap().1;
        self.loop_continuations.pop();
        self.loop_unit.pop();
        self.loop_depth -= 1;
        self.loop_allocation_owners.pop();
        values
    }
    fn loop_fixedpoint(&mut self, body: &Block, frame: &mut Frame, span: Span, at_most_once: bool) {
        let outside_bindings: BTreeMap<_, _> = self
            .bindings
            .iter()
            .enumerate()
            .filter(|(_, b)| b.alive)
            .map(|(id, b)| (id, b.value.origins.nodes.clone()))
            .collect();
        let mut outside = self.heap.reachable(
            outside_bindings
                .values()
                .flat_map(|nodes| nodes.iter().copied()),
        );
        let limit = (self.functions.len() + self.closures.len() + 2)
            * (outside_bindings.len() + self.fields.len() + 2)
            + 2;
        for _ in 0..limit {
            let before_concurrency = self.concurrency.clone();
            let recency = self.recency_moves.len();
            let old_accesses = frame.obligations.accesses.len();
            let old_returns = frame.returned.len();
            let mut before_fields = self.fields.clone();
            let mut before_bindings: BTreeMap<_, _> = outside_bindings
                .keys()
                .map(|id| (*id, self.bindings[*id].value.clone()))
                .collect();
            let head_fields = before_fields.clone();
            let head_bindings = before_bindings.clone();
            let pending: Vec<_> = self
                .deferred_arm_cleanups
                .iter()
                .map(|arm| (arm.boundary, arm.frame.owner))
                .collect();
            let result_scope = self.begin_loop_results(frame.owner);
            let channel_start = self.channel_message_sequence;
            let mut iteration = self.block(body, frame);
            self.transport_frame_prefix(frame, recency, old_accesses, old_returns);
            if self
                .deferred_arm_cleanups
                .iter()
                .map(|arm| (arm.boundary, arm.frame.owner))
                .collect::<Vec<_>>()
                != pending
            {
                self.unsupported(
                    span,
                    "repeated resumed-arm cleanup requires an activation multiplicity fixed point",
                );
            }
            self.finish_loop_results(result_scope, &mut iteration, frame, span, body);
            let single_iteration = at_most_once
                || (iteration.ty == Ty::Never
                    && self
                        .loop_continuations
                        .last()
                        .is_some_and(|(_, next)| !next));
            if single_iteration {
                return;
            }
            self.channel_repeated_events(channel_start, self.channel_message_sequence, span);
            let choice = self.choice();
            let cause = self.cause(CauseKind::BranchJoin, span,
                "ordinary loop may-graph retains zero iterations and transported allocation histories", []);
            let moves = self.recency_moves[recency..].to_vec();
            loop_graph::transport_values(&mut before_bindings, &moves);
            loop_graph::transport_fields(&mut before_fields, &moves, choice, cause);
            loop_graph::transport_nodes(&mut outside, &moves);
            outside.extend(loop_graph::reachable(
                &before_fields,
                before_bindings
                    .values()
                    .flat_map(|value| value.origins.nodes.iter().copied()),
            ));
            outside.extend(self.heap.reachable(outside_bindings.keys().flat_map(|id| {
                self.bindings[*id]
                    .value
                    .origins
                    .nodes
                    .iter()
                    .copied()
                    .chain(self.bindings[*id].cell)
            })));
            let ordinary: BTreeSet<_> = self
                .fields
                .iter()
                .filter_map(|(key, value)| {
                    (outside.contains(&key.0)
                        && self.ordinary_loop_value(value, &self.fields)
                        && before_fields
                            .get(key)
                            .is_none_or(|before| self.ordinary_loop_value(before, &before_fields)))
                    .then_some(key.clone())
                })
                .collect();
            if self.fields.iter().any(|(key, value)| {
                outside.contains(&key.0)
                    && !ordinary.contains(key)
                    && before_fields
                        .get(key)
                        .map_or(!value.origins.nodes.is_empty(), |old| {
                            old.origins != value.origins
                        })
            }) || before_bindings.iter().any(|(id, before)| {
                self.bindings[*id].value.origins != before.origins
                    && !(self.ordinary_loop_value(before, &before_fields)
                        && self.ordinary_loop_value(&self.bindings[*id].value, &self.fields))
            }) {
                self.unsupported(span, "loop nonordinary reference-shape fixed point requires separate resource, Result or callable transfer");
                return;
            }
            let mut changed =
                self.concurrent_iteration_changes_authority(&before_concurrency, &outside);
            for (id, before) in before_bindings {
                let merged =
                    self.join_ordinary_loop_value(&before, &self.bindings[id].value, choice, cause);
                changed |= !head_bindings[&id].same_abstract_value(&merged);
                self.bindings[id].value = merged;
            }
            for (key, before) in before_fields {
                if outside.contains(&key.0)
                    && let Some(after) = self.fields.get(&key).cloned()
                {
                    let merged = if ordinary.contains(&key) {
                        self.join_ordinary_loop_value(&before, &after, choice, cause)
                    } else {
                        before.join(&after, choice, cause)
                    };
                    self.store_field(key.0, key.1, merged);
                }
            }
            changed |= self.fields.iter().any(|(key, value)| {
                outside.contains(&key.0)
                    && head_fields
                        .get(key)
                        .is_none_or(|before| !before.same_abstract_value(value))
            });
            self.refresh_heap_fields();
            self.refresh_writable_roots();
            if !changed {
                return;
            }
        }
        self.unsupported(
            span,
            "loop abstract values did not reach the finite fixed point",
        );
    }
    fn lambda(
        &mut self,
        parameters: &[Parameter],
        return_type: Option<&TypeExpr>,
        annotations: &[Annotation],
        body: &Expr,
        syntax: &Expr,
        frame: &mut Frame,
    ) -> Value {
        let span = syntax.span;
        for annotation in annotations {
            if annotation.kind == AnnotationKind::Effect {
                self.effect_row(annotation);
            }
        }
        let mut names = BTreeSet::new();
        collect_names(body, &mut names);
        for parameter in parameters {
            if let PatternKind::Name(name) = &parameter.pattern.kind {
                names.remove(name);
            }
        }
        let captures: BTreeSet<_> = names
            .iter()
            .filter_map(|name| frame.env.get(name).copied())
            .filter(|binding| !self.static_value_bindings.contains(binding))
            .filter(|binding|!self.bindings[*binding].value.callables.iter().any(|callable|matches!(callable,Callable::Named(id)if self.functions[*id].owner.is_none()&&self.bindings[*binding].span==self.functions[*id].syntax.span)))
            .collect();
        let mutable = mutated_names(body);
        let mutable_environment = captures
            .iter()
            .any(|id| mutable.contains(&self.bindings[*id].name));
        let observer = captures.iter().any(|id| {
            self.bindings[*id].value.publication == Publication::Live
                || self.bindings[*id].mode.is_reassignable()
        });
        let node = self.allocate_owned(span, 0, frame.owner);
        let id = self.closures.len();
        if self
            .source_argument_of(syntax, frame)
            .is_some_and(|argument| self.immediate_scope_arguments.contains(&argument))
        {
            self.immediate_scope_closures.insert(id);
        }
        let contract = std::sync::Arc::new(LambdaContract {
            source: syntax
                .hir_id
                .map(ril_compiler_core::ids::CallableContractSource::Expression),
            return_type: return_type.cloned(),
            annotations: annotations.to_vec(),
            span,
            typing_environment: self.capture_typing_environment_with_bindings(&frame.env),
        });
        let site = self.closure_site(frame.callable_owner, syntax.hir_id, span);
        self.closures.push(ClosureInfo {
            contract,
            hir_id: syntax.hir_id,
            site,
            creation_invocation: self.copy_invocation_stack.last().copied(),
            creation_closure: self.closure_invocation_stack.last().copied(),
            creation_default: self.default_use_stack.last().copied(),
            handler_context: self.active_handlers.clone(),
            parameters: parameters.to_vec(),
            body: body.clone(),
            lexical: frame.env.clone(),
            captures: captures.clone(),
            writes: captures
                .iter()
                .copied()
                .filter(|binding| mutable.contains(&self.bindings[*binding].name))
                .collect(),
            owner: frame.owner,
            node,
        });
        for (i, &binding) in captures.iter().enumerate() {
            let capture = self.capture_value(binding);
            self.store_field(node, Slot::Capture(i as u32), capture);
        }
        let mut value = Value::reference(
            Ty::Callable(
                parameters
                    .iter()
                    .map(|p| p.ty.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unknown))
                    .collect(),
                Box::new(Ty::Unknown),
            ),
            node,
            self.heap.nodes[node.0 as usize].cause,
        );
        value.callables.push(Callable::Closure(id));
        for binding in &captures {
            value.scoped.extend(&self.bindings[*binding].value.scoped);
        }
        value.signature = Some(parameters.to_vec());
        if !annotations.is_empty() {
            value.callable_bounds.push(CallableBound {
                annotations: annotations.to_vec(),
                source: syntax
                    .hir_id
                    .map(ril_compiler_core::ids::CallableContractSource::Expression),
                typing_environment: self.closures[id].contract.typing_environment.clone(),
                span,
            });
        }
        value.mutable_environment = mutable_environment;
        value.observer_environment = observer && !mutable_environment;
        if !mutable_environment && !observer {
            value.publication = Publication::Immutable;
            value.permission = Permission::Read;
        }
        // Verify latent operations now, but preserve the current invocation's
        // heap and rows. Creating a callable does not execute its body.
        if parameters.iter().all(|p| p.ty.is_some()) {
            let budget = std::mem::take(&mut self.budget_coverage);
            let original_fields = self.fields.clone();
            let preview = self.snapshot_flow();
            let original_values: Vec<_> = self.bindings.iter().map(|b| b.value.clone()).collect();
            let mut latent = self.frame(frame.env.clone(), true);
            let args: Vec<_> = parameters
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let ty = p.ty.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unknown);
                    let mut value = self.formal_value(ty, i as u32, p.span, &mut BTreeSet::new());
                    if let Some(syntax) = &p.ty {
                        self.set_contract_environment(&frame.env);
                        self.ascribe_signature(&mut value, syntax);
                        // This is the genuine declaration probe's formal,
                        // rather than an observed actual argument. Its type
                        // supplies its shape obligation to the latent body.
                        self.promise_array_shape(&value, syntax, &mut latent);
                    }
                    (p.mode, value, p.span)
                })
                .collect();
            self.widen_callable_environment(&Callable::Closure(id));
            let returned = self.invoke_closure_probe(id, args, span, &mut latent);
            let dependent: BTreeSet<_> = latent
                .obligations
                .named
                .keys()
                .copied()
                .filter(|binding| {
                    self.bindings[*binding].owner != ScopeId(0)
                        && !self.scope_is_within(self.bindings[*binding].owner, latent.owner)
                })
                .collect();
            self.closures[id].captures.extend(&dependent);
            self.closures[id].writes.extend(
                latent
                    .obligations
                    .named
                    .iter()
                    .filter_map(|(binding, mode)| (*mode != Mode::Read).then_some(*binding)),
            );
            let inferred_write = latent.obligations.named.iter().any(|(binding, mode)| {
                *mode != Mode::Read && self.closures[id].captures.contains(binding)
            });
            if inferred_write {
                value.mutable_environment = true;
                value.observer_environment = false;
                value.permission = Permission::Write;
                value.publication = Publication::Live;
            }
            let captures = self.closures[id].captures.clone();
            for (index, binding) in captures.iter().enumerate() {
                let capture = self.capture_value(*binding);
                self.store_field(node, Slot::Capture(index as u32), capture);
            }
            value.ty = Ty::Callable(
                parameters
                    .iter()
                    .map(|p| p.ty.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unknown))
                    .collect(),
                Box::new(returned.ty),
            );
            for (key, old) in original_fields {
                self.fields.insert(key, old);
            }
            for (binding, old) in self.bindings.iter_mut().zip(original_values) {
                binding.value = old;
            }
            self.restore_preview(&preview);
            self.budget_coverage = budget;
            for binding in self.closures[id].writes.clone() {
                if self.bindings[binding].mode.is_reassignable() {
                    self.bindings[binding].slot_used = true;
                } else {
                    self.mark_write(binding);
                }
            }
            for binding in &self.closures[id].captures {
                value.scoped.extend(&self.bindings[*binding].value.scoped);
            }
        }
        self.finalize_closure_environment(id, &mut value);
        self.validate_empty_callable_rows(&value.ty, annotations, span);
        if let Some(result) = return_type {
            let syntax = TypeExpr {
                hir_id: None,
                text: String::new(),
                span,
                kind: TypeKind::Callable {
                    parameters: parameters.to_vec(),
                    result: Some(Box::new(result.clone())),
                    annotations: annotations.to_vec(),
                },
            };
            value.source_type_witness = self.source_type_from_syntax(&syntax);
        }
        value
    }
    pub(super) fn capture_value(&self, binding: BindingId) -> Value {
        let binding = &self.bindings[binding];
        if let Some(cell) = binding.cell {
            let mut capture = Value::reference(binding.value.ty.clone(), cell, binding.value.cause);
            capture.publication = Publication::Live;
            capture.construction = false;
            capture.sources = binding.value.sources.clone();
            capture.participants = binding.value.participants.clone();
            capture.scoped = binding.value.scoped.clone();
            capture
        } else {
            binding.value.clone()
        }
    }
    fn format_type(&mut self, value: &Value, format: &str, span: Span) {
        use ril_text_format::{FormatSpec, Kind};
        let spec = match FormatSpec::parse(format, self.layout.pointer_bits) {
            Ok(spec) => spec,
            Err(error) => {
                self.error("E0112", span, error.to_string(), [value.cause]);
                return;
            }
        };
        let kind = match self.expanded(&value.ty, &mut BTreeSet::new()) {
            Ty::Str => Some(Kind::String),
            Ty::Bool => Some(Kind::Bool),
            Ty::Int(_) => Some(Kind::Integer),
            Ty::Float(name) if name == "f32" || name == "f64" => Some(Kind::Float),
            Ty::Unknown => {
                self.unsupported(
                    span,
                    "interpolation requires a resolved format-capable type",
                );
                return;
            }
            _ => None,
        };
        if kind.is_none_or(|kind| spec.validate(kind).is_err()) {
            self.error(
                "E0329",
                span,
                "value type does not admit this format or precision",
                [value.cause],
            );
        }
    }
}
pub(super) fn binding_count(pattern: &Pattern) -> usize {
    match &pattern.kind {
        PatternKind::Name(_) => 1,
        PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
            items.iter().map(binding_count).sum()
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            fields
                .iter()
                .map(|f| binding_count(&f.pattern))
                .sum::<usize>()
                + usize::from(rest_binding.as_ref().is_some_and(|name| name != "_"))
        }
        PatternKind::Constructor { arguments, .. } => arguments.iter().map(binding_count).sum(),
        PatternKind::Mode { pattern, .. } => binding_count(pattern),
        _ => 0,
    }
}

pub(super) fn collect_names(expr: &Expr, names: &mut BTreeSet<String>) {
    match &expr.kind {
        ExprKind::Name(name) => {
            names.insert(name.clone());
        }
        ExprKind::Path(path) => {
            names.insert(path.join("::"));
        }
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation { expression, .. } = part {
                    collect_names(expression, names);
                }
            }
        }
        ExprKind::Field { base, .. }
        | ExprKind::Unary { operand: base, .. }
        | ExprKind::Generic { base, .. } => collect_names(base, names),
        ExprKind::Binary { left, right, .. } => {
            collect_names(left, names);
            collect_names(right, names);
        }
        ExprKind::Call { callee, arguments } => {
            collect_names(callee, names);
            for arg in arguments {
                collect_names(&arg.value, names);
            }
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                collect_names(item, names);
            }
        }
        ExprKind::Map(entries) => {
            for (key, value) in entries {
                collect_names(key, names);
                collect_names(value, names);
            }
        }
        ExprKind::Record { members, .. } => {
            for member in members {
                match member {
                    RecordMember::Field(field) => collect_names(&field.value, names),
                    RecordMember::Spread(value) => collect_names(value, names),
                }
            }
        }
        ExprKind::Block(block) | ExprKind::Loop(block) => collect_block_names(block, names),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_names(condition, names);
            collect_names(then_branch, names);
            if let Some(branch) = else_branch {
                collect_names(branch, names);
            }
        }
        ExprKind::Index { base, index, .. } => {
            collect_names(base, names);
            collect_names(index, names);
        }
        ExprKind::ComputedField { base, key } => {
            collect_names(base, names);
            collect_names(key, names);
        }
        ExprKind::While { condition, body } => {
            collect_names(condition, names);
            collect_block_names(body, names);
        }
        ExprKind::For {
            iterable,
            pattern,
            body,
        } => {
            collect_names(iterable, names);
            let mut inner = BTreeSet::new();
            collect_block_names(body, &mut inner);
            remove_pattern_names(pattern, &mut inner);
            names.extend(inner);
        }
        ExprKind::Lambda {
            parameters, body, ..
        } => {
            let mut inner = BTreeSet::new();
            collect_names(body, &mut inner);
            for parameter in parameters {
                remove_pattern_names(&parameter.pattern, &mut inner);
            }
            names.extend(inner);
        }
        ExprKind::Match { value, arms, .. } => {
            collect_names(value, names);
            for arm in arms {
                let mut inner = BTreeSet::new();
                collect_names(&arm.body, &mut inner);
                if let Some(guard) = &arm.guard {
                    collect_names(guard, &mut inner);
                }
                remove_pattern_names(&arm.pattern, &mut inner);
                names.extend(inner);
                collect_pattern_values(&arm.pattern, names);
            }
        }
        ExprKind::Is { value, pattern } => {
            collect_names(value, names);
            collect_pattern_values(pattern, names);
        }
        ExprKind::Derive { base, recipe } => {
            if let Some(base) = base {
                collect_names(base, names);
            }
            collect_names(recipe, names);
        }
        ExprKind::Range { start, end, .. } => {
            for value in start.iter().chain(end) {
                collect_names(value, names);
            }
        }
        ExprKind::Control {
            value: Some(value), ..
        } => collect_names(value, names),
        _ => {}
    }
}
pub(super) fn collect_block_names(block: &Block, names: &mut BTreeSet<String>) {
    let mut inner = BTreeSet::new();
    for statement in block.statements.iter().chain(&block.where_items) {
        match &statement.kind {
            StmtKind::Binding(binding) => {
                collect_names(&binding.value, &mut inner);
                if let Some(fallback) = &binding.fallback {
                    collect_names(fallback, &mut inner);
                }
            }
            StmtKind::Assignment { target, value, .. } => {
                collect_names(target, &mut inner);
                collect_names(value, &mut inner);
            }
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                collect_names(expression, &mut inner)
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    let mut body = BTreeSet::new();
                    collect_names(&arm.body, &mut body);
                    for parameter in &arm.parameters {
                        remove_pattern_names(&parameter.pattern, &mut body);
                    }
                    inner.extend(body);
                }
            }
            StmtKind::Function(function) => {
                if let Some(body) = &function.body {
                    let mut body_names = BTreeSet::new();
                    collect_block_names(body, &mut body_names);
                    for parameter in &function.parameters {
                        remove_pattern_names(&parameter.pattern, &mut body_names);
                    }
                    inner.extend(body_names);
                }
            }
            _ => {}
        }
    }
    for statement in block.statements.iter().chain(&block.where_items) {
        match &statement.kind {
            StmtKind::Binding(binding) => remove_pattern_names(&binding.pattern, &mut inner),
            StmtKind::Function(function) => {
                inner.remove(&function.name);
            }
            _ => {}
        }
    }
    names.extend(inner);
}
fn remove_pattern_names(pattern: &Pattern, names: &mut BTreeSet<String>) {
    match &pattern.kind {
        PatternKind::Name(name) => {
            names.remove(name);
        }
        PatternKind::Tuple(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                remove_pattern_names(item, names);
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                remove_pattern_names(&field.pattern, names);
            }
            if let Some(name) = rest_binding {
                names.remove(name);
            }
        }
        PatternKind::Mode { pattern, .. } => remove_pattern_names(pattern, names),
        _ => {}
    }
}
fn collect_pattern_values(pattern: &Pattern, names: &mut BTreeSet<String>) {
    match &pattern.kind {
        PatternKind::Value(expression) => collect_names(expression, names),
        PatternKind::Tuple(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                collect_pattern_values(item, names);
            }
        }
        PatternKind::Record { fields, .. } => {
            for field in fields {
                collect_pattern_values(&field.pattern, names);
            }
        }
        PatternKind::Mode { pattern, .. } => collect_pattern_values(pattern, names),
        _ => {}
    }
}
pub(super) fn mutated_names(expr: &Expr) -> BTreeSet<String> {
    mutation_names(MutationSource::Expression(expr))
}

pub(super) fn mutated_block_names(block: &Block) -> BTreeSet<String> {
    mutation_names(MutationSource::Block(block))
}

enum MutationSource<'a> {
    Expression(&'a Expr),
    Block(&'a Block),
}

fn mutation_names(source: MutationSource<'_>) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    fn root(expr: &Expr) -> Option<&str> {
        match &expr.kind {
            ExprKind::Name(name) => Some(name),
            ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => root(base),
            _ => None,
        }
    }
    fn visit(expr: &Expr, result: &mut BTreeSet<String>) {
        match &expr.kind {
            ExprKind::Block(block) => visit_block(block, result),
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "!>"
                    && let Some(name) = root(left)
                {
                    result.insert(name.into());
                }
                visit(left, result);
                visit(right, result);
            }
            ExprKind::Call { arguments, .. } => {
                for arg in arguments {
                    if arg.mode != ParameterMode::Read
                        && let Some(name) = root(&arg.value)
                    {
                        result.insert(name.into());
                    }
                }
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, result);
                if let Some(branch) = else_branch {
                    visit(branch, result);
                }
            }
            _ => {}
        }
    }
    fn visit_block(block: &Block, result: &mut BTreeSet<String>) {
        for statement in &block.statements {
            match &statement.kind {
                StmtKind::Assignment { target, .. } => {
                    if let Some(name) = root(target) {
                        result.insert(name.into());
                    }
                }
                StmtKind::Expr { expression, .. } => visit(expression, result),
                _ => {}
            }
        }
    }
    match source {
        MutationSource::Expression(expression) => visit(expression, &mut result),
        MutationSource::Block(block) => visit_block(block, &mut result),
    }
    result
}

#[cfg(test)]
mod observation_tests {
    use super::*;

    fn integer(start: u32, value: &str) -> Expr {
        Expr {
            hir_id: None,
            kind: ExprKind::Literal(Literal::Integer(value.into())),
            span: Span {
                file: FileId(0),
                start,
                end: start + 1,
            },
        }
    }

    #[test]
    fn observed_parent_returns_its_real_emission_after_nested_operands() {
        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(BTreeMap::new(), false);
        let expression = Expr {
            hir_id: None,
            span: Span {
                file: FileId(0),
                start: 0,
                end: 7,
            },
            kind: ExprKind::Tuple(vec![integer(2, "7"), integer(4, "8")]),
        };
        let (value, observation) = checker.expression_observed(&expression, &mut frame);
        let observation = observation.unwrap();
        assert_eq!(checker.application_effect.expressions.len(), 3);
        assert_eq!(observation, 2);
        assert_eq!(
            checker.application_effect.expressions[observation].span,
            expression.span
        );
        assert_eq!(
            checker.application_effect.expressions[observation]
                .value
                .cause,
            value.cause
        );
        assert_eq!(
            checker
                .application_effect
                .contexts
                .last()
                .unwrap()
                .expression,
            observation
        );
    }

    #[test]
    fn exhausted_source_traversal_cannot_invent_an_operand_observation() {
        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(BTreeMap::new(), false);
        checker.analysis_depth = 64;
        let (_, observation) = checker.expression_observed(&integer(2, "7"), &mut frame);
        assert_eq!(observation, None);
        assert!(checker.application_effect.expressions.is_empty());
        assert!(checker.application_effect.contexts.is_empty());
        assert!(!checker.unsupported.is_empty());
    }

    #[test]
    fn pattern_expected_expression_cannot_replace_the_receipts_operand_token() {
        use crate::sema::channel_messages::ChannelAction;

        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(BTreeMap::new(), false);
        let binding_span = integer(0, "7").span;
        let cause = checker.cause(CauseKind::Source, binding_span, "test Result payload", []);
        let payload = Value::scalar(Ty::Int("int".into()), Some(Constant::Integer(7)), cause);
        let result = checker.make_result(true, payload, binding_span, frame.owner);
        checker.bind_name(
            "result",
            BindingMode::Let,
            result,
            binding_span,
            &mut frame,
            false,
        );
        let subject_span = Span {
            file: FileId(0),
            start: 2,
            end: 8,
        };
        let expected = integer(15, "7");
        let expression = Expr {
            hir_id: None,
            span: Span {
                file: FileId(0),
                start: 2,
                end: 18,
            },
            kind: ExprKind::Is {
                value: Box::new(Expr {
                    hir_id: None,
                    kind: ExprKind::Name("result".into()),
                    span: subject_span,
                }),
                pattern: Pattern {
                    hir_id: None,
                    span: Span {
                        file: FileId(0),
                        start: 12,
                        end: 18,
                    },
                    kind: PatternKind::Constructor {
                        path: vec!["Ok".into()],
                        arguments: vec![Pattern {
                            hir_id: None,
                            span: expected.span,
                            kind: PatternKind::Value(Box::new(expected)),
                        }],
                        parenthesized: true,
                    },
                },
            },
        };
        let (_, whole) = checker.expression_observed(&expression, &mut frame);
        assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
        assert!(checker.unsupported.is_empty(), "{:?}", checker.unsupported);
        assert_eq!(checker.application_effect.expressions.len(), 3);
        assert_eq!(whole, Some(2));
        assert_eq!(
            checker.application_effect.expressions[1].span,
            integer(15, "7").span
        );
        let receipts: Vec<_> = checker
            .channel_message_facts
            .iter()
            .filter_map(|fact| {
                if let ChannelAction::ConditionEvaluated {
                    subject_expression,
                    subject,
                    ..
                } = &fact.action
                {
                    Some((*subject_expression, subject))
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(receipts.len(), 1);
        assert_eq!(receipts[0].0, 0);
        assert_eq!(
            checker.application_effect.expressions[receipts[0].0].span,
            subject_span
        );
        assert_eq!(
            checker.application_effect.expressions[0].value,
            receipts[0].1.value
        );
        // This exercises real recorder ordering, not independent Source
        // authorization. A refutable payload is outside that theorem.
    }
}
