//! Replay each original product operand in the same physical root occurrence.
use super::*;
use ril_syntax::ast::RecordMember;

impl Replay<'_> {
    pub(super) fn original_composite_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<ArgumentKey>> {
        let children: Vec<(Option<&str>, &Expr)> = match &expression.kind {
            ExprKind::Tuple(items) => items.iter().map(|item| (None, item)).collect(),
            ExprKind::Record {
                ty: None, members, ..
            } => members
                .iter()
                .map(|member| match member {
                    RecordMember::Field(field) => Ok((Some(field.name.as_str()), &field.value)),
                    RecordMember::Spread(_) => {
                        Err("open product Source requires its actual spread transport".to_owned())
                    }
                })
                .collect::<Check<_>>()?,
            _ => return Ok(None),
        };
        let roots: Vec<_> = self
            .facts
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                let fact = self.facts.expressions.get(row.expression)?;
                (row.context == context
                    && fact.source_id.is_some()
                    && fact.source_id == expression.hir_id
                    && fact.value == *value)
                    .then_some(row.expression)
            })
            .collect();
        let [root] = roots.as_slice() else {
            return Err("product Source has no unique actual root observation".into());
        };
        let mut lower = self
            .facts
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                (row.expression < *root
                    && row.context == context
                    && self
                        .facts
                        .expressions
                        .get(row.expression)
                        .is_some_and(|fact| {
                            fact.source_id.is_some() && fact.source_id == expression.hir_id
                        }))
                .then_some(row.expression + 1)
            })
            .max()
            .unwrap_or(0);
        let mut keys = Vec::new();
        for (label, child) in children {
            *work = work
                .checked_sub(1 + label.map_or(0, |label| label.len().div_ceil(32)))
                .ok_or_else(|| "product Source exceeds its reconstruction budget".to_owned())?;
            let candidates: Vec<_> = self
                .facts
                .invocation_expressions
                .iter()
                .filter_map(|row| {
                    (row.expression >= lower && row.expression < *root && row.context == context)
                        .then(|| {
                            self.facts
                                .expressions
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
                return Err("product Source operand borrowed another physical occurrence".into());
            };
            lower = *index + 1;
            let key = self.original_source_key_inner(
                child,
                &fact.value,
                context,
                sites,
                work,
                depth + 1,
            )?;
            require(
                source_reception::complete(&key, work).is_some(),
                "product operand Source is incomplete",
            )?;
            keys.push((label, key));
        }
        if matches!(expression.kind, ExprKind::Tuple(_)) {
            Ok(Some(ArgumentKey::Tuple(
                keys.into_iter().map(|(_, key)| key).collect(),
            )))
        } else {
            let mut fields = BTreeMap::new();
            for (name, key) in keys {
                require(
                    fields.insert(name.unwrap().to_owned(), key).is_none(),
                    "product Source repeats a field",
                )?;
            }
            Ok(Some(ArgumentKey::Record {
                fields: fields
                    .into_iter()
                    .map(|(name, key)| (name, false, key))
                    .collect(),
                row: None,
            }))
        }
    }
}
