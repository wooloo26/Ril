//! Fresh products retain the original schemas of their actual operands.
//! Open callable rows cannot be recovered from the erased product Ty.
use super::*;
use ril_syntax::ast::RecordMember;

impl Checker {
    pub(super) fn original_composite_source_key(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut usize,
        depth: usize,
    ) -> Option<ArgumentKey> {
        let children: Vec<(Option<&str>, &Expr)> = match &syntax.kind {
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
        let roots: Vec<_> = self
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                let fact = self.expression_facts.get(row.expression)?;
                (row.context == context
                    && fact.source_id.is_some()
                    && fact.source_id == syntax.hir_id
                    && fact.value == *value)
                    .then_some(row.expression)
            })
            .collect();
        let [root] = roots.as_slice() else {
            return None;
        };
        // The preceding execution of this same AST root is an exclusive lower
        // boundary. A later loop iteration cannot pay an earlier one's source.
        let mut lower = self
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                (row.expression < *root
                    && row.context == context
                    && self
                        .expression_facts
                        .get(row.expression)
                        .is_some_and(|fact| {
                            fact.source_id.is_some() && fact.source_id == syntax.hir_id
                        }))
                .then_some(row.expression + 1)
            })
            .max()
            .unwrap_or(0);
        let mut keys = Vec::new();
        for (label, child) in children {
            *work = work.checked_sub(1 + label.map_or(0, |label| label.len().div_ceil(32)))?;
            let candidates: Vec<_> = self
                .invocation_expressions
                .iter()
                .filter_map(|row| {
                    (row.expression >= lower && row.expression < *root && row.context == context)
                        .then(|| {
                            self.expression_facts
                                .get(row.expression)
                                .map(|fact| (row.expression, fact))
                        })
                        .flatten()
                        .filter(|(_, fact)| {
                            fact.source_id.is_some() && fact.source_id == child.hir_id
                        })
                })
                .collect();
            let [(index, fact)] = candidates.as_slice() else {
                return None;
            };
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
        if matches!(syntax.kind, ExprKind::Tuple(_)) {
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
