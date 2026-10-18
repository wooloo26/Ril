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
        visit: SourceVisit,
    ) -> Check<Option<ArgumentKey>> {
        let SourceVisit { depth, observation } = visit;
        if let ExprKind::Block(block) = &expression.kind {
            let Some(Stmt {
                kind:
                    StmtKind::Expr {
                        expression: tail,
                        terminated: false,
                    },
                ..
            }) = block.statements.last()
            else {
                return Ok(None);
            };
            // A block may replace its ordinary tail with an effect answer or
            // cleanup outcome. Only the actual unchanged tail Source can be
            // forwarded; a same-span node or current callable tag is not it.
            let root = self.original_source_root(expression, value, context, observation, work)?;
            let source = expression.hir_id.unwrap();
            let lower = self
                .observations
                .previous(source, context, root, work)?
                .map_or(0, |index| index + 1);
            let tail_source = tail
                .hir_id
                .ok_or_else(|| "block Source tail has no genuine HIR identity".to_owned())?;
            let tails = self
                .observations
                .range(tail_source, context, lower..root, work)?;
            let [index] = tails else {
                return Err("block Source tail borrowed another physical occurrence".into());
            };
            let actual = &self.facts.expressions[*index];
            require(
                actual.value.ty != Ty::Never
                    && actual.value.cause == value.cause
                    && actual.value.ty == value.ty
                    && actual.value.source_type_witness == value.source_type_witness
                    && actual.value.callables == value.callables
                    && actual.value.callable_bounds == value.callable_bounds
                    && actual.value.callable_returns == value.callable_returns
                    && actual.value.signature == value.signature,
                "block Source differs from its actual tail's complete public view",
            )?;
            return self
                .original_source_key_inner(
                    tail,
                    &actual.value,
                    context,
                    sites,
                    work,
                    SourceVisit {
                        depth: depth + 1,
                        observation: Some(*index),
                    },
                )
                .map(Some);
        }
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
        let root = self.original_source_root(expression, value, context, observation, work)?;
        let mut lower = self
            .observations
            .previous(expression.hir_id.unwrap(), context, root, work)?
            .map_or(0, |index| index + 1);
        let mut keys = Vec::new();
        for (label, child) in children {
            *work = work
                .checked_sub(1 + label.map_or(0, |label| label.len().div_ceil(32)))
                .ok_or_else(|| "product Source exceeds its reconstruction budget".to_owned())?;
            let source = child
                .hir_id
                .ok_or_else(|| "product operand has no genuine HIR identity".to_owned())?;
            let candidates = self
                .observations
                .range(source, context, lower..root, work)?;
            let [index] = candidates else {
                return Err("product Source operand borrowed another physical occurrence".into());
            };
            let fact = &self.facts.expressions[*index];
            lower = *index + 1;
            let key = self.original_source_key_inner(
                child,
                &fact.value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: depth + 1,
                    observation: Some(*index),
                },
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
