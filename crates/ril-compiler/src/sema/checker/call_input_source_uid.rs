//! Source-derived symbolic Type leaves. The semantic Ty is an equality check
//! after the real formal, projection or returning declaration chose the key.
use super::*;
use crate::sema::effect_identity::StaticBinderSort;

impl Checker {
    pub(super) fn original_symbolic_source_key(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let Ty::Generic(identity) = &value.ty else {
            return None;
        };
        let binder = self.generic_binders.get(identity)?;
        let function = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)?;
        let parameter = function.syntax.generics.get(binder.index as usize)?;
        if !crate::sema::record_bounds::certifies_type_sort(
            identity,
            binder,
            parameter,
            &self.record_bounds,
        ) {
            return None;
        }
        let context = self.invocation_context(frame.callable_owner);
        if self
            .invocation_expressions
            .iter()
            .filter(|row| {
                row.context == context
                    && self
                        .expression_facts
                        .get(row.expression)
                        .is_some_and(|fact| {
                            fact.source_id.is_some()
                                && fact.source_id == syntax.hir_id
                                && fact.value.cause == value.cause
                                && fact.value.ty == value.ty
                        })
            })
            .count()
            != 1
        {
            return None;
        }
        let key = match &syntax.kind {
            ExprKind::Name(_) if value.sources.len() == 1 => {
                self.formal_source_type_key(value, syntax, frame)?
            }
            ExprKind::Index { .. } | ExprKind::Field { .. } | ExprKind::ComputedField { .. } => {
                if let Some(key) =
                    self.formal_source_path_key(syntax, value.cause, frame, &mut 4096, 0)
                {
                    let key = self.selected_bound_key(&key)?;
                    return matches!(&key, ArgumentKey::Binder { identity:actual, sort:StaticBinderSort::Type } if actual == identity).then_some(key);
                }
                let ExprKind::Index { base, .. } = &syntax.kind else {
                    return None;
                };
                let parents = &self
                    .explanations
                    .causes
                    .get(value.cause.0 as usize)?
                    .parents;
                let projections: Vec<_> = self
                    .generic_bound_projections
                    .iter()
                    .filter(|projection| {
                        projection.context == context
                            && projection.span == base.span
                            && parents.contains(&projection.output.value.cause)
                    })
                    .collect();
                let [projection] = projections.as_slice() else {
                    return None;
                };
                let bound = self.record_bounds.get(projection.required.0 as usize)?;
                let Slot::Field(label) = &projection.slot else {
                    return None;
                };
                let field = bound.fields.iter().find(|field| &field.label == label)?;
                let key = self.selected_bound_key(&field.key)?;
                let ArgumentKey::Array { element, .. } = key else {
                    return None;
                };
                *element
            }
            ExprKind::Call { .. } => self.original_called_result_source(value, syntax, frame)?,

            _ => return None,
        };
        matches!(&key, ArgumentKey::Binder { identity: actual, sort: StaticBinderSort::Type } if actual == identity).then_some(key)
    }

    fn formal_source_path_key(
        &self,
        syntax: &Expr,
        cause: CauseId,
        frame: &Frame,
        work: &mut usize,
        depth: usize,
    ) -> Option<ArgumentKey> {
        *work = work.checked_sub(1)?;
        if depth >= 64 {
            return None;
        }
        let context = self.invocation_context(frame.callable_owner);
        let observations: Vec<_> = self
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                if row.context != context {
                    return None;
                }
                self.expression_facts.get(row.expression).filter(|fact| {
                    fact.source_id.is_some()
                        && fact.source_id == syntax.hir_id
                        && fact.value.cause == cause
                })
            })
            .collect();
        let [observation] = observations.as_slice() else {
            return None;
        };
        if let ExprKind::Name(name) = &syntax.kind {
            let id = *frame.env.get(name)?;
            let binding = self.bindings.get(id)?;
            if !binding.parameter
                || binding.owner != frame.owner
                || observation.value.sources != BTreeSet::from([id])
            {
                return None;
            }
            return self.raw_formal_source_type_key(&observation.value, syntax, frame);
        }
        if self.explanations.kinds.get(cause.0 as usize) != Some(&CauseKind::Projection) {
            return None;
        }
        let parent = *self
            .explanations
            .causes
            .get(cause.0 as usize)?
            .parents
            .first()?;
        let (base, step) = match &syntax.kind {
            ExprKind::Index { base, .. } => (base.as_ref(), None),
            ExprKind::Field { base, field, .. } => (
                base.as_ref(),
                Some(
                    field
                        .parse()
                        .map(Slot::Tuple)
                        .unwrap_or_else(|_| Slot::Field(field.clone())),
                ),
            ),
            ExprKind::ComputedField { base, key } => {
                let ExprKind::Literal(Literal::Integer(text)) = &key.kind else {
                    return None;
                };
                let coordinate = text.parse::<u32>().ok()?;
                let matching: Vec<_> = self
                    .invocation_expressions
                    .iter()
                    .filter_map(|row| {
                        if row.context != context {
                            return None;
                        }
                        self.expression_facts.get(row.expression).filter(|fact| {
                            fact.source_id.is_some()
                                && fact.source_id == key.hir_id
                                && fact.value.constant
                                    == Some(Constant::Integer(i128::from(coordinate)))
                        })
                    })
                    .collect();
                if matching.len() != 1 {
                    return None;
                }
                (base.as_ref(), Some(Slot::Tuple(coordinate)))
            }
            _ => return None,
        };
        let key = self.formal_source_path_key(base, parent, frame, work, depth + 1)?;
        match (key, step) {
            (ArgumentKey::Array { element, .. }, None) => Some(*element),
            (ArgumentKey::Tuple(items), Some(Slot::Tuple(index))) => {
                items.get(index as usize).cloned()
            }
            (ArgumentKey::Record { fields, .. }, Some(Slot::Field(label))) => fields
                .into_iter()
                .find(|field| field.0 == label)
                .map(|field| field.2),
            (ArgumentKey::Binder { identity, .. }, Some(Slot::Field(label))) => self
                .record_bounds
                .iter()
                .find(|bound| bound.binder == identity)?
                .fields
                .iter()
                .find(|field| field.label == label)
                .map(|field| field.key.clone()),
            _ => None,
        }
    }
}
