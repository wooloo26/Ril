//! Source construction helpers for generated iterator bodies.
use super::*;
use crate::sema::source_types::{SourceSchema, WorkLimit};
#[path = "../generated_source_syntax.rs"]
mod syntax;
pub(super) use syntax::iterator_lambda as iterator_syntax;

fn scalar_schema(name: &str) -> Result<SourceSchema, String> {
    SourceSchema::import(
        &crate::sema::effect_identity::ArgumentKey::Name {
            name: name.into(),
            arguments: vec![],
        },
        None,
        &mut WorkLimit::new(64),
    )
    .map_err(|error| format!("generated scalar Source: {error}"))
}

pub(super) fn scalar_body(
    body: &Expr,
    name: &str,
    input: &SourceSchema,
    work: &mut WorkLimit,
    depth: usize,
) -> Result<Option<SourceSchema>, String> {
    work.charge(1)
        .map_err(|error| format!("generated scalar body: {error}"))?;
    if depth >= 64 {
        return Err("generated scalar body exceeds its depth bound".into());
    }
    Ok(match &body.kind {
        ExprKind::Name(actual) if actual == name => Some(input.clone()),
        ExprKind::Literal(Literal::Integer(_)) => Some(scalar_schema("int")?),
        ExprKind::Literal(Literal::Bool(_)) => Some(scalar_schema("bool")?),
        ExprKind::Literal(Literal::String(_) | Literal::RawString(_)) => {
            Some(scalar_schema("str")?)
        }
        ExprKind::Binary {
            left,
            operator,
            right,
        } if matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") => {
            let Some(left) = scalar_body(left, name, input, work, depth + 1)? else {
                return Ok(None);
            };
            let Some(right) = scalar_body(right, name, input, work, depth + 1)? else {
                return Ok(None);
            };
            let integer = scalar_schema("int")?;
            let fits = left
                .equivalent(&integer, work)
                .and_then(|fits| Ok(fits && right.equivalent(&left, work)?))
                .map_err(|error| format!("generated scalar operation Source: {error}"))?;
            fits.then_some(left)
        }
        ExprKind::Block(block) if block.where_items.is_empty() && block.statements.len() == 1 => {
            let StmtKind::Expr {
                expression,
                terminated: false,
            } = &block.statements[0].kind
            else {
                return Ok(None);
            };
            scalar_body(expression, name, input, work, depth + 1)?
        }
        _ => None,
    })
}
