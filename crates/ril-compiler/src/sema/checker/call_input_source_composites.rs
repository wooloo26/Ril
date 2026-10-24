//! Fresh products and copies carry the actual operand graphs without export.
use super::*;
use ril_syntax::ast::RecordMember;

impl Checker {
    pub(super) fn original_copy_source_schema(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<Option<Option<(SourceSchema, FrozenEnvironment)>>, SourceTypesError> {
        let context = self.invocation_context(frame.callable_owner);
        if let ExprKind::Binary {
            operator,
            left,
            right,
        } = &syntax.kind
            && matches!(operator.as_str(), "|>" | "!>")
            && matches!(right.kind, ExprKind::Derive { base: None, .. })
        {
            let roots = self
                .application_effect
                .occurrences(syntax.hir_id.ok_or(SourceTypesError::MissingNode)?, context);
            work.charge(roots.len())?;
            let roots: Vec<_> = roots
                .iter()
                .copied()
                .filter(|index| self.application_effect.expressions[*index].value == *value)
                .collect();
            let [root] = roots.as_slice() else {
                return Err(SourceTypesError::Unresolved);
            };
            let anchor = self
                .application_effect
                .evaluations
                .get(*root)
                .and_then(|row| row.identity)
                .ok_or(SourceTypesError::MissingNode)?
                .activation;
            let operands = self
                .application_effect
                .occurrences(left.hir_id.ok_or(SourceTypesError::MissingNode)?, context);
            work.charge(operands.len())?;
            let operands: Vec<_> = operands
                .iter()
                .copied()
                .filter(|index| {
                    self.application_effect.evaluations[*index]
                        .identity
                        .and_then(|id| {
                            self.application_effect
                                .activations
                                .get(id.activation.0 as usize)
                        })
                        .is_some_and(|activation| activation.parent == Some(anchor))
                })
                .collect();
            let [operand] = operands.as_slice() else {
                return Err(SourceTypesError::Unresolved);
            };
            work.charge(1)?;
            let input = self.application_effect.expressions[*operand]
                .value
                .packet()
                .clone();
            let source = self.raw_original_source_schema(
                input.value(),
                left,
                frame,
                work,
                depth + 1,
                Some(*operand),
            )?;
            return source
                .map(|(schema, env)| {
                    Ok((
                        schema.copy_view(crate::sema::copy_contract::CopyMode::Immutable, work)?,
                        env,
                    ))
                })
                .transpose()
                .map(Some);
        }
        let Some(application) = crate::hir::application::AstApplication::from_ast(syntax) else {
            return Ok(None);
        };
        work.charge(self.copy_call_events.len() + self.call_arguments.len())?;
        let mut matching = self.copy_call_events.iter().filter(|event| {
            event.matches_source(syntax)
                && event.owner == context.owner
                && event.parent == context.invocation
                && event.result_expression.is_some_and(|index| {
                    self.application_effect
                        .expressions
                        .get(index)
                        .is_some_and(|fact| fact.value == *value)
                        && self
                            .application_effect
                            .contexts
                            .get(index)
                            .is_some_and(|row| row.context == context)
                })
        });
        let Some(event) = matching.next() else {
            return Ok(None);
        };
        let Some(mode) = event.copy_operation else {
            return Ok(None);
        };
        if matching.next().is_some() || application.operands.len() != 1 {
            return Err(SourceTypesError::Unresolved);
        }
        let event_id = event.id;
        let mut arguments = self
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event_id);
        let argument = arguments.next().ok_or(SourceTypesError::MissingNode)?;
        if arguments.next().is_some() || !argument.slots_bound || !argument.evaluation_complete {
            return Err(SourceTypesError::Unresolved);
        }
        let operand = argument
            .supplied
            .get(&0)
            .ok_or(SourceTypesError::MissingNode)?
            .expression;
        work.charge(1)?;
        let input = self
            .application_effect
            .expressions
            .get(operand)
            .ok_or(SourceTypesError::MissingNode)?
            .value
            .packet()
            .clone();
        let source = self.raw_original_source_schema(
            input.value(),
            application.operands[0].expression,
            frame,
            work,
            depth + 1,
            Some(operand),
        )?;
        source
            .map(|(schema, env)| Ok((schema.copy_view(mode, work)?, env)))
            .transpose()
            .map(Some)
    }

    pub(super) fn original_composite_source_schema(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
        depth: usize,
    ) -> InputSource {
        let optional_exit = matches!(&syntax.kind,ExprKind::Binary{operator,..} if operator=="??");
        let children: Vec<(Option<&str>, &Expr)> = match &syntax.kind {
            ExprKind::Unary { operator, operand } if operator == "^mut" => vec![(None, operand)],
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => vec![(None, left), (None, right)],
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                work.charge(items.len())?;
                if items.is_empty() && matches!(syntax.kind, ExprKind::Array(_)) {
                    return Ok(None);
                }
                items.iter().map(|item| (None, item)).collect()
            }
            ExprKind::Map(entries) => {
                work.charge(
                    entries
                        .len()
                        .checked_mul(2)
                        .ok_or(SourceTypesError::BudgetExceeded)?,
                )?;
                if entries.is_empty() {
                    return Ok(None);
                }
                entries
                    .iter()
                    .flat_map(|(key, value)| [(None, key), (None, value)])
                    .collect()
            }
            ExprKind::Record {
                ty: None, members, ..
            } => {
                let mut children = Vec::new();
                work.charge(members.len())?;
                for member in members {
                    let RecordMember::Field(field) = member else {
                        return Ok(None);
                    };
                    children.push((Some(field.name.as_str()), &field.value));
                }
                children
            }
            _ => return Ok(None),
        };
        let context = self.invocation_context(frame.callable_owner);
        let parent = self.source_projection_occurrence(
            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
            value,
            context,
            work,
        )?;
        let mut previous = None;
        let mut schemas = Vec::new();
        let mut environment: Option<FrozenEnvironment> = None;
        for (position, (label, child)) in children.into_iter().enumerate() {
            work.charge(1 + label.map_or(0, |label| label.len().div_ceil(32)))?;
            let index = self
                .source_projection_receipts()
                .child_observation(
                    parent,
                    child.hir_id.ok_or(SourceTypesError::MissingNode)?,
                    work,
                )?
                .0 as usize;
            if previous.is_some_and(|previous| previous >= index) {
                return Err(SourceTypesError::Unresolved);
            }
            previous = Some(index);
            let fact = &self.application_effect.expressions[index];
            if optional_exit {
                if position == 0 && !matches!(fact.value.ty, Ty::Optional(_)) {
                    return Err(SourceTypesError::Unresolved);
                }
                if position == 1 {
                    if fact.value.ty == Ty::Never {
                        continue;
                    }
                    return Ok(None);
                }
            }
            work.charge(1)?;
            let child_value = fact.value.packet().clone();
            let Some((schema, child_environment)) = self.raw_original_source_schema(
                child_value.value(),
                child,
                frame,
                work,
                depth + 1,
                Some(index),
            )?
            else {
                return Ok(None);
            };
            if child_environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            if schema.requires_environment(work)? {
                if let Some(previous) = &environment
                    && !schema.same_interpretation_in(previous, &child_environment, work)?
                {
                    return Err(SourceTypesError::Unresolved);
                }
                environment = Some(child_environment);
            }
            schemas.push((label, schema));
        }
        let schema = if optional_exit {
            schemas
                .pop()
                .ok_or(SourceTypesError::MissingNode)?
                .1
                .project_steps(
                    &[crate::sema::source_types::SourcePath::OptionalPayload],
                    work,
                )?
        } else if matches!(syntax.kind, ExprKind::Unary { .. }) {
            schemas.pop().ok_or(SourceTypesError::MissingNode)?.1
        } else if matches!(syntax.kind, ExprKind::Array(_)) {
            let first = &schemas.first().ok_or(SourceTypesError::MissingNode)?.1;
            for (_, schema) in schemas.iter().skip(1) {
                if !first.equivalent(schema, work)? {
                    return Err(SourceTypesError::Unresolved);
                }
            }
            // Inference gives this fresh literal a dynamic shell. Only the
            // separately retained Construction may supply its receiving count.
            SourceSchema::array(
                crate::sema::source_types::SourceLength::Dynamic,
                first,
                None,
                work,
            )?
        } else if matches!(syntax.kind, ExprKind::Map(_)) {
            let key = &schemas.first().ok_or(SourceTypesError::MissingNode)?.1;
            let value = &schemas.get(1).ok_or(SourceTypesError::MissingNode)?.1;
            for pair in schemas.as_chunks::<2>().0.iter().skip(1) {
                if !key.equivalent(&pair[0].1, work)? || !value.equivalent(&pair[1].1, work)? {
                    return Err(SourceTypesError::Unresolved);
                }
            }
            SourceSchema::map(key, value, None, work)?
        } else if matches!(syntax.kind, ExprKind::Tuple(_)) {
            SourceSchema::tuple(
                &schemas
                    .into_iter()
                    .map(|(_, schema)| schema)
                    .collect::<Vec<_>>(),
                None,
                work,
            )?
        } else {
            let mut fields = BTreeMap::new();
            for (label, schema) in schemas {
                if fields
                    .insert(
                        label.ok_or(SourceTypesError::Unresolved)?.to_owned(),
                        schema,
                    )
                    .is_some()
                {
                    return Err(SourceTypesError::DuplicateField);
                }
            }
            SourceSchema::record(
                &fields
                    .into_iter()
                    .map(|(label, schema)| (label, false, schema))
                    .collect::<Vec<_>>(),
                None,
                None,
                work,
            )?
        };
        let environment = environment.unwrap_or_else(|| self.capture_typing_environment());
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(Some((schema, environment)))
    }
}
