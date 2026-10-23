//! Syntactic normal/control exits, independent of actual static execution and
//! event quotas. Continuing paths require their own finite-iteration evidence.
use super::*;

const NORMAL: u8 = 1;
const NEXT: u8 = 2;
const LAST: u8 = 4;
const RETURN: u8 = 8;
const ABNORMAL: u8 = 16;

fn sequence(before: u8, after: impl FnOnce() -> u8) -> u8 {
    (before & !NORMAL) | if before & NORMAL != 0 { after() } else { 0 }
}
pub(super) fn continues_statement(statement: &Stmt) -> bool {
    statement_flow(statement) & NORMAL != 0
}
pub(super) fn repeats(body: &Block) -> bool {
    block_flow(body) & (NORMAL | NEXT) != 0
}
pub(super) fn boolean(value: &Expr) -> Option<bool> {
    match &value.kind {
        ExprKind::Literal(Literal::Bool(value)) => Some(*value),
        ExprKind::Unary { operator, operand } if operator == "!" => {
            boolean(operand).map(|value| !value)
        }
        _ => None,
    }
}
fn block_flow(body: &Block) -> u8 {
    body.statements.iter().fold(NORMAL, |flow, statement| {
        sequence(flow, || statement_flow(statement))
    })
}
fn statement_flow(statement: &Stmt) -> u8 {
    match &statement.kind {
        StmtKind::Binding(binding) => {
            sequence(binding.ty.as_ref().map_or(NORMAL, type_flow), || {
                expr_flow(&binding.value)
            })
        }
        StmtKind::Expr { expression, .. } => expr_flow(expression),
        _ => NORMAL,
    }
}
fn operands<'a>(values: impl Iterator<Item = &'a Expr>) -> u8 {
    values.fold(NORMAL, |flow, value| sequence(flow, || expr_flow(value)))
}
fn expr_flow(value: &Expr) -> u8 {
    match &value.kind {
        ExprKind::Control { operation, value } => sequence(
            value.as_deref().map_or(NORMAL, expr_flow),
            || match operation {
                ControlOperation::Next => NEXT,
                ControlOperation::Last => LAST,
                ControlOperation::Return => RETURN,
                _ => NORMAL,
            },
        ),
        ExprKind::Block(body) => block_flow(body),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => sequence(expr_flow(condition), || match boolean(condition) {
            Some(true) => expr_flow(then_branch),
            Some(false) => else_branch.as_deref().map_or(NORMAL, expr_flow),
            None => expr_flow(then_branch) | else_branch.as_deref().map_or(NORMAL, expr_flow),
        }),
        ExprKind::IfLet {
            pattern,
            value,
            then_branch,
            else_branch,
        } => sequence(expr_flow(value), || {
            sequence(pattern_flow(pattern), || {
                expr_flow(then_branch) | else_branch.as_deref().map_or(NORMAL, expr_flow)
            })
        }),
        ExprKind::Match { value, arms, .. } => sequence(expr_flow(value), || {
            if arms.is_empty() {
                return ABNORMAL;
            }
            arms.iter().fold(0, |flow, arm| {
                flow | sequence(arm.guard.as_ref().map_or(NORMAL, expr_flow), || {
                    expr_flow(&arm.body)
                })
            })
        }),
        ExprKind::Loop(body) => {
            let body = block_flow(body);
            (body & (RETURN | ABNORMAL)) | if body & LAST != 0 { NORMAL } else { 0 }
        }
        ExprKind::While { condition, body } => sequence(expr_flow(condition), || {
            if boolean(condition) == Some(false) {
                return NORMAL;
            }
            let body = block_flow(body);
            (body & (RETURN | ABNORMAL))
                | if body & LAST != 0 || boolean(condition).is_none() {
                    NORMAL
                } else {
                    0
                }
        }),
        ExprKind::WhileLet {
            pattern,
            value,
            body,
        } => sequence(expr_flow(value), || {
            sequence(pattern_flow(pattern), || {
                NORMAL | (block_flow(body) & (RETURN | ABNORMAL))
            })
        }),
        ExprKind::For { iterable, body, .. } => sequence(expr_flow(iterable), || {
            NORMAL | (block_flow(body) & (RETURN | ABNORMAL))
        }),
        ExprKind::Call { callee, arguments } => sequence(
            operands(
                std::iter::once(callee.as_ref())
                    .chain(arguments.iter().map(|argument| &argument.value)),
            ),
            || {
                if expression_name(callee)
                    .is_some_and(|name| name.strip_prefix("Prelude::").unwrap_or(&name) == "assert")
                    && arguments
                        .first()
                        .is_some_and(|argument| boolean(&argument.value) == Some(false))
                {
                    ABNORMAL
                } else {
                    NORMAL
                }
            },
        ),
        ExprKind::Tuple(values) | ExprKind::Array(values) => operands(values.iter()),
        ExprKind::Map(values) => operands(values.iter().flat_map(|(key, value)| [key, value])),
        ExprKind::Record { ty, members, .. } => {
            sequence(ty.as_ref().map_or(NORMAL, type_flow), || {
                operands(members.iter().map(|member| match member {
                    RecordMember::Field(field) => &field.value,
                    RecordMember::Spread(value) => value,
                }))
            })
        }
        ExprKind::Interpolated(parts) => operands(parts.iter().filter_map(|part| match part {
            StringPart::Interpolation { expression, .. } => Some(expression.as_ref()),
            _ => None,
        })),
        ExprKind::Generic { base, arguments } => sequence(expr_flow(base), || {
            arguments.iter().fold(NORMAL, |flow, argument| {
                sequence(flow, || type_flow(argument))
            })
        }),
        ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => type_flow(ty),
        ExprKind::Is { value, pattern } => sequence(expr_flow(value), || pattern_flow(pattern)),
        ExprKind::Lambda {
            parameters,
            return_type,
            ..
        } => parameters
            .iter()
            .filter_map(|parameter| parameter.ty.as_ref())
            .chain(return_type)
            .fold(NORMAL, |flow, ty| sequence(flow, || type_flow(ty))),
        ExprKind::Binary {
            operator,
            left,
            right,
        } if matches!(operator.as_str(), "&&" | "||" | "??") => sequence(expr_flow(left), || {
            let skipped = match (operator.as_str(), boolean(left)) {
                ("&&", Some(false)) | ("||", Some(true)) => Some(true),
                ("&&", Some(true)) | ("||", Some(false)) => Some(false),
                _ => None,
            };
            match skipped {
                Some(true) => NORMAL,
                Some(false) => expr_flow(right),
                None => NORMAL | expr_flow(right),
            }
        }),
        ExprKind::Binary { left, right, .. }
        | ExprKind::Index {
            base: left,
            index: right,
            ..
        }
        | ExprKind::ComputedField {
            base: left,
            key: right,
        } => operands([left.as_ref(), right.as_ref()].into_iter()),
        ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
            expr_flow(operand)
        }
        ExprKind::Range { start, end, .. } => operands(start.iter().chain(end).map(Box::as_ref)),
        _ => NORMAL,
    }
}

fn type_flow(ty: &TypeExpr) -> u8 {
    match &ty.kind {
        TypeKind::Computation(value) => expr_flow(value),
        TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => arguments
            .iter()
            .fold(NORMAL, |flow, ty| sequence(flow, || type_flow(ty))),
        TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::KeyOf(inner)
        | TypeKind::Projection { base: inner, .. } => type_flow(inner),
        TypeKind::Array { length, element } => {
            type_flow(element) | length.as_deref().map_or(NORMAL, expr_flow)
        }
        TypeKind::Map { key, value } => type_flow(key) | type_flow(value),
        TypeKind::Record { fields, row } => fields
            .iter()
            .map(|field| &field.ty)
            .chain(row.as_deref())
            .fold(NORMAL, |flow, ty| flow | type_flow(ty)),
        TypeKind::ComputedProjection { base, key } => type_flow(base) | expr_flow(key),
        TypeKind::Mapped { keys, value, .. } => expr_flow(keys) | type_flow(value),
        _ => NORMAL,
    }
}
fn pattern_flow(pattern: &Pattern) -> u8 {
    match &pattern.kind {
        PatternKind::Value(value) => expr_flow(value),
        PatternKind::Tuple(values)
        | PatternKind::Array(values)
        | PatternKind::Alternative(values)
        | PatternKind::Constructor {
            arguments: values, ..
        } => values
            .iter()
            .fold(NORMAL, |flow, pattern| flow | pattern_flow(pattern)),
        PatternKind::Record { fields, .. } => fields
            .iter()
            .fold(NORMAL, |flow, field| flow | pattern_flow(&field.pattern)),
        PatternKind::Type { ty, .. } => type_flow(ty),
        PatternKind::Mode { pattern, .. } => pattern_flow(pattern),
        _ => NORMAL,
    }
}

impl Visitor<'_> {
    pub(super) fn finite_source(&self, source: &Expr, seen: &mut BTreeSet<String>) -> bool {
        match &source.kind {
            ExprKind::Array(_) | ExprKind::Map(_) => true,
            ExprKind::Range { end: Some(_), .. } => true,
            ExprKind::Name(name) => {
                if !seen.insert(name.clone()) { return false; }
                match self.aliases.get(name) {
                    Some(Some(source)) => self.finite_source(source, seen),
                    Some(None) => false,
                    None => self.finite_sources.contains(name),
                }
            }
            ExprKind::Block(body) => body.statements.last().is_some_and(|statement|
                matches!(&statement.kind, StmtKind::Expr { expression, terminated: false } if self.finite_source(expression,seen))),
            ExprKind::Call { callee, .. } => expression_name(callee).and_then(|name| self.evaluator.functions.get(&name))
                .and_then(|function| function.return_type.as_ref()).is_some_and(collection_type),
            _ => false,
        }
    }
}
pub(super) fn collection_type(ty: &TypeExpr) -> bool {
    matches!(ty.kind, TypeKind::Array { .. } | TypeKind::Map { .. })
}
