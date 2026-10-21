//! Fresh products retain the original schemas of their actual operands.
//! Open callable rows cannot be recovered from the erased product Ty.
use super::*;
use ril_syntax::ast::RecordMember;

impl Checker {
    pub(super) fn original_copy_source_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut usize,
        depth: usize,
    ) -> Option<Option<ArgumentKey>> {
        if let ExprKind::Binary {
            operator,
            left,
            right,
        } = &syntax.kind
            && matches!(operator.as_str(), "|>" | "!>")
            && matches!(right.kind, ExprKind::Derive { base: None, .. })
        {
            let mut publication = || -> Option<ArgumentKey> {
                let context = self.invocation_context(frame.callable_owner);
                let roots = self.application_effect.occurrences(syntax.hir_id?, context);
                *work = work.checked_sub(roots.len())?;
                let mut roots = roots
                    .iter()
                    .copied()
                    .filter(|index| self.application_effect.expressions[*index].value == *value);
                let root = roots.next()?;
                if roots.next().is_some() {
                    return None;
                }
                let anchor = self
                    .application_effect
                    .evaluations
                    .get(root)?
                    .identity?
                    .activation;
                let operands = self.application_effect.occurrences(left.hir_id?, context);
                *work = work.checked_sub(operands.len())?;
                let mut operands = operands.iter().copied().filter(|index| {
                    self.application_effect.evaluations[*index]
                        .identity
                        .and_then(|id| {
                            self.application_effect
                                .activations
                                .get(id.activation.0 as usize)
                        })
                        .is_some_and(|activation| activation.parent == Some(anchor))
                });
                let operand = operands.next()?;
                if operands.next().is_some() {
                    return None;
                }
                let input = self.application_effect.expressions[operand].value.clone();
                let key = self.raw_original_source_receiving_key_inner(
                    &input,
                    left,
                    frame,
                    work,
                    depth + 1,
                )?;
                source_reception::copy_view(
                    key,
                    crate::sema::copy_contract::CopyMode::Immutable,
                    work,
                )
            };
            return Some(publication());
        }
        let application = crate::hir::application::AstApplication::from_ast(syntax)?;
        let context = self.invocation_context(frame.callable_owner);
        let Some(remaining) =
            work.checked_sub(self.copy_call_events.len() + self.call_arguments.len())
        else {
            *work = 0;
            return Some(None);
        };
        *work = remaining;
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
        let event = matching.next()?;
        let mode = event.copy_operation?;
        let mut derive = || -> Option<_> {
            if matching.next().is_some() || application.operands.len() != 1 {
                return None;
            }
            let event_id = event.id;
            let arguments = self
                .call_arguments
                .iter()
                .find(|row| row.source_event == event_id)?;
            let operand = arguments.supplied.get(&0)?.expression;
            let input = &self.application_effect.expressions.get(operand)?.value;
            Some((mode, input.clone()))
        };
        let Some((mode, input)) = derive() else {
            return Some(None);
        };
        Some(
            self.raw_original_source_receiving_key_inner(
                &input,
                application.operands[0].expression,
                frame,
                work,
                depth + 1,
            )
            .and_then(|key| source_reception::copy_view(key, mode, work)),
        )
    }

    pub(super) fn original_composite_source_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut usize,
        depth: usize,
    ) -> Option<ArgumentKey> {
        let optional_exit =
            matches!(&syntax.kind, ExprKind::Binary { operator, .. } if operator == "??");
        let children: Vec<(Option<&str>, &Expr)> = match &syntax.kind {
            ExprKind::Unary { operator, operand } if operator == "^mut" => vec![(None, operand)],
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => vec![(None, left), (None, right)],
            ExprKind::Tuple(items) => items.iter().map(|item| (None, item)).collect(),
            ExprKind::Record {
                ty: None, members, ..
            } => members
                .iter()
                .map(|member| match member {
                    RecordMember::Field(field) => Some((Some(field.name.as_str()), &field.value)),
                    RecordMember::Spread(_) => None,
                })
                .collect::<Option<_>>()?,
            _ => return None,
        };
        let context = self.invocation_context(frame.callable_owner);
        let occurrences = self.application_effect.occurrences(syntax.hir_id?, context);
        *work = work.checked_sub(occurrences.len())?;
        let mut roots = occurrences
            .iter()
            .copied()
            .filter(|index| self.application_effect.expressions[*index].value == *value);
        let root = roots.next()?;
        if roots.next().is_some() {
            return None;
        }
        // The preceding execution of this same AST root is an exclusive lower
        // boundary. A later loop iteration cannot pay an earlier one's source.
        let position = occurrences.partition_point(|index| *index < root);
        let mut lower = position
            .checked_sub(1)
            .map_or(0, |index| occurrences[index] + 1);
        let mut keys = Vec::new();
        for (position, (label, child)) in children.into_iter().enumerate() {
            *work = work.checked_sub(1 + label.map_or(0, |label| label.len().div_ceil(32)))?;
            let candidates = self.application_effect.occurrences(child.hir_id?, context);
            let begin = candidates.partition_point(|index| *index < lower);
            let end = candidates.partition_point(|index| *index < root);
            *work = work.checked_sub(end - begin)?;
            let [index] = &candidates[begin..end] else {
                return None;
            };
            let fact = &self.application_effect.expressions[*index];
            if optional_exit {
                if position == 0 && !matches!(fact.value.ty, Ty::Optional(_)) {
                    return None;
                }
                if position == 1 {
                    if fact.value.ty == Ty::Never {
                        continue;
                    }
                    return None;
                }
            }
            let child_value = fact.value.clone();
            lower = *index + 1;
            let key = self.raw_original_source_receiving_key_inner(
                &child_value,
                child,
                frame,
                work,
                depth + 1,
            )?;
            source_reception::complete(&key, work)?;
            keys.push((label, key));
        }
        if optional_exit {
            let key = keys.pop()?.1;
            let mut limit = crate::sema::source_types::WorkLimit::new(*work);
            let key = crate::sema::source_types::declarations::project_steps(
                &key,
                &[crate::sema::source_types::SourcePath::OptionalPayload],
                &self.semantic_hir,
                &mut limit,
            );
            *work = limit.remaining();
            key.ok()
        } else if matches!(syntax.kind, ExprKind::Unary { .. }) {
            keys.pop().map(|(_, key)| key)
        } else if matches!(syntax.kind, ExprKind::Tuple(_)) {
            Some(ArgumentKey::Tuple(
                keys.into_iter().map(|(_, key)| key).collect(),
            ))
        } else {
            let mut fields = BTreeMap::new();
            for (name, key) in keys {
                if fields.insert(name?.to_owned(), key).is_some() {
                    return None;
                }
            }
            Some(ArgumentKey::Record {
                fields: fields
                    .into_iter()
                    .map(|(name, key)| (name, false, key))
                    .collect(),
                row: None,
            })
        }
    }
}
