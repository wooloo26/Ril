//! Borrowed, iterative traversal of all source syntax. This is not evaluation order.
use super::*;

#[derive(Debug, Clone, Copy)]
pub enum Node<'a> {
    Statement(&'a Stmt),
    Function(&'a Function),
    TypeDeclaration(&'a TypeDeclaration),
    Block(&'a Block),
    Expression(&'a Expr),
    Type(&'a TypeExpr),
    Pattern(&'a Pattern),
    ValueTest(&'a ValueTest),
    Parameter(&'a Parameter),
    GenericParameter(&'a GenericParameter),
    Annotation(&'a Annotation),
}

impl Node<'_> {
    pub fn span(self) -> Span {
        match self {
            Self::Statement(node) => node.span,
            Self::Function(node) => node.span,
            Self::TypeDeclaration(node) => node.span,
            Self::Block(node) => node.span,
            Self::Expression(node) => node.span,
            Self::Type(node) => node.span,
            Self::Pattern(node) => node.span,
            Self::ValueTest(node) => node.span,
            Self::Parameter(node) => node.span,
            Self::GenericParameter(node) => node.span,
            Self::Annotation(node) => node.span,
        }
    }
}

pub struct Walk<'a> {
    pending: Vec<Node<'a>>,
    children: Vec<Node<'a>>,
}

pub fn walk(program: &Program) -> Walk<'_> {
    Walk {
        pending: program
            .statements
            .iter()
            .rev()
            .map(Node::Statement)
            .collect(),
        children: vec![],
    }
}

impl<'a> Iterator for Walk<'a> {
    type Item = Node<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.pending.pop()?;
        node.children(&mut self.children);
        self.pending.extend(self.children.drain(..).rev());
        Some(node)
    }
}

impl<'a> Node<'a> {
    fn children(self, out: &mut Vec<Self>) {
        match self {
            Self::Statement(statement) => match &statement.kind {
                StmtKind::Function(function) => out.push(Self::Function(function)),
                StmtKind::Type(ty) => out.push(Self::TypeDeclaration(ty)),
                StmtKind::Binding(binding) => {
                    out.push(Self::Pattern(&binding.pattern));
                    if let Some(ty) = &binding.ty {
                        out.push(Self::Type(ty));
                    }
                    if let Some(value) = &binding.initializer {
                        out.push(Self::Expression(value));
                    }
                    if let Some(value) = &binding.fallback {
                        out.push(Self::Expression(value));
                    }
                }
                StmtKind::Effect(effect) => {
                    out.extend(effect.generics.iter().map(Self::GenericParameter));
                    out.extend(effect.operations.iter().map(Self::Function));
                    out.extend(effect.members.iter().map(Self::Type));
                }
                StmtKind::Sub(sub) => out.extend(sub.items.iter().map(Self::Statement)),
                StmtKind::Use(_) => {}
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        out.push(Self::Expression(&arm.operation));
                        out.extend(arm.parameters.iter().map(Self::Parameter));
                        out.push(Self::Expression(&arm.body));
                    }
                }
                StmtKind::HandlerApplication(expression) | StmtKind::Expr { expression, .. } => {
                    out.push(Self::Expression(expression))
                }
            },
            Self::Function(function) => {
                out.extend(function.generics.iter().map(Self::GenericParameter));
                out.extend(function.parameters.iter().map(Self::Parameter));
                out.extend(function.annotations.iter().map(Self::Annotation));
                if let Some(ty) = &function.return_type {
                    out.push(Self::Type(ty));
                }
                out.extend(function.signature_where.iter().map(Self::Statement));
                if let Some(body) = &function.body {
                    out.push(Self::Block(body));
                }
            }
            Self::TypeDeclaration(ty) => {
                out.extend(ty.generics.iter().map(Self::GenericParameter));
                out.extend(ty.signature_where.iter().map(Self::Statement));
                if let Some(value) = &ty.value {
                    out.push(Self::Type(value));
                }
                for variant in &ty.variants {
                    out.extend(variant.generics.iter().map(Self::GenericParameter));
                    if let Some(ty) = &variant.payload {
                        out.push(Self::Type(ty));
                    }
                    if let Some(ty) = &variant.result {
                        out.push(Self::Type(ty));
                    }
                    out.extend(variant.annotations.iter().map(Self::Annotation));
                }
            }
            Self::Block(block) => {
                out.extend(block.statements.iter().map(Self::Statement));
                out.extend(block.where_items.iter().map(Self::Statement));
            }
            Self::Parameter(parameter) => {
                out.push(Self::Pattern(&parameter.pattern));
                if let Some(ty) = &parameter.ty {
                    out.push(Self::Type(ty));
                }
                if let Some(default) = &parameter.default {
                    out.push(Self::Expression(default));
                }
            }
            Self::GenericParameter(parameter) => {
                if let Some(bound) = &parameter.bound {
                    out.push(Self::Type(bound));
                }
                out.extend(parameter.guards.iter().map(Self::Type));
                if let Some(default) = &parameter.default {
                    out.push(Self::Type(default));
                }
            }
            Self::Annotation(annotation) => match &annotation.kind {
                AnnotationKind::Effects(EffectRow::Closed(types)) => {
                    out.extend(types.iter().map(Self::Type))
                }
                AnnotationKind::Effects(EffectRow::Open) | AnnotationKind::State(_) => {}
            },
            Self::Expression(expression) => match &expression.kind {
                ExprKind::Generic { base, arguments } => {
                    out.push(Self::Expression(base));
                    out.extend(arguments.iter().map(Self::Type));
                }
                ExprKind::Interpolated(parts) => {
                    for part in parts {
                        if let StringPart::Interpolation { expression, .. } = part {
                            out.push(Self::Expression(expression));
                        }
                    }
                }
                ExprKind::Tuple(values) | ExprKind::Array(values) => {
                    out.extend(values.iter().map(Self::Expression))
                }
                ExprKind::Map(entries) => {
                    for (key, value) in entries {
                        out.push(Self::Expression(key));
                        out.push(Self::Expression(value));
                    }
                }
                ExprKind::Record { ty, members } => {
                    if let Some(ty) = ty {
                        out.push(Self::Type(ty));
                    }
                    for member in members {
                        out.push(Self::Expression(match member {
                            RecordMember::Field(field) => &field.value,
                            RecordMember::Spread(value) => value,
                        }));
                    }
                }
                ExprKind::TupleMember { value, .. }
                | ExprKind::Unary { operand: value, .. }
                | ExprKind::Observe { operand: value, .. }
                | ExprKind::Field { base: value, .. }
                | ExprKind::EffectOperation { effect: value, .. } => {
                    out.push(Self::Expression(value))
                }
                ExprKind::Binary { left, right, .. }
                | ExprKind::Assignment {
                    target: left,
                    value: right,
                    ..
                }
                | ExprKind::ComputedField {
                    base: left,
                    key: right,
                }
                | ExprKind::Index {
                    base: left,
                    index: right,
                    ..
                } => {
                    out.push(Self::Expression(left));
                    out.push(Self::Expression(right));
                }
                ExprKind::Call { callee, arguments } => {
                    out.push(Self::Expression(callee));
                    out.extend(
                        arguments
                            .iter()
                            .map(|argument| Self::Expression(&argument.value)),
                    );
                }
                ExprKind::Block(block) | ExprKind::Loop(block) => out.push(Self::Block(block)),
                ExprKind::Lambda {
                    parameters,
                    return_type,
                    annotations,
                    body,
                } => {
                    out.extend(parameters.iter().map(Self::Parameter));
                    out.extend(annotations.iter().map(Self::Annotation));
                    if let Some(ty) = return_type {
                        out.push(Self::Type(ty));
                    }
                    out.push(Self::Expression(body));
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    out.push(Self::Expression(condition));
                    out.push(Self::Expression(then_branch));
                    if let Some(branch) = else_branch {
                        out.push(Self::Expression(branch));
                    }
                }
                ExprKind::IfLet {
                    pattern,
                    value,
                    then_branch,
                    else_branch,
                } => {
                    out.push(Self::Pattern(pattern));
                    out.push(Self::Expression(value));
                    out.push(Self::Expression(then_branch));
                    if let Some(branch) = else_branch {
                        out.push(Self::Expression(branch));
                    }
                }
                ExprKind::Match { value, arms } => {
                    out.push(Self::Expression(value));
                    for arm in arms {
                        out.push(Self::Pattern(&arm.pattern));
                        if let Some(guard) = &arm.guard {
                            out.push(Self::Expression(guard));
                        }
                        out.push(Self::Expression(&arm.body));
                    }
                }
                ExprKind::Is { value, test } => {
                    out.push(Self::Expression(value));
                    out.push(Self::ValueTest(test));
                }
                ExprKind::While { condition, body } => {
                    out.push(Self::Expression(condition));
                    out.push(Self::Block(body));
                }
                ExprKind::WhileLet {
                    pattern,
                    value,
                    body,
                }
                | ExprKind::For {
                    pattern,
                    iterable: value,
                    body,
                } => {
                    out.push(Self::Pattern(pattern));
                    out.push(Self::Expression(value));
                    out.push(Self::Block(body));
                }
                ExprKind::Control { value, .. } => {
                    if let Some(value) = value {
                        out.push(Self::Expression(value));
                    }
                }
                ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) | ExprKind::ModeOf(ty) => {
                    out.push(Self::Type(ty))
                }
                ExprKind::Range { start, end, .. } => {
                    if let Some(start) = start {
                        out.push(Self::Expression(start));
                    }
                    if let Some(end) = end {
                        out.push(Self::Expression(end));
                    }
                }
                ExprKind::Literal(_)
                | ExprKind::Name(_)
                | ExprKind::Path(_)
                | ExprKind::Accessor(_)
                | ExprKind::Error => {}
            },
            Self::Type(ty) => match &ty.kind {
                TypeKind::Name { arguments, .. }
                | TypeKind::Tuple(arguments)
                | TypeKind::Alternatives(arguments) => out.extend(arguments.iter().map(Self::Type)),
                TypeKind::Optional(ty)
                | TypeKind::Rest(ty)
                | TypeKind::Member { ty, .. }
                | TypeKind::PatternMode { ty, .. }
                | TypeKind::KeyOf(ty)
                | TypeKind::Projection { base: ty, .. }
                | TypeKind::Array { element: ty, .. } => out.push(Self::Type(ty)),
                TypeKind::ArrayPattern { length, element } => {
                    if let Some(length) = length {
                        out.push(Self::Expression(length));
                    }
                    out.push(Self::Type(element));
                }
                TypeKind::Map { key, value, .. }
                | TypeKind::KindArrow {
                    parameter: key,
                    result: value,
                } => {
                    out.push(Self::Type(key));
                    out.push(Self::Type(value));
                }
                TypeKind::VariantPayload(fields) => {
                    out.extend(fields.iter().map(|field| Self::Type(&field.ty)))
                }
                TypeKind::Record { fields, row } => {
                    out.extend(fields.iter().map(|field| Self::Type(&field.ty)));
                    if let Some(row) = row {
                        out.push(Self::Type(row));
                    }
                }
                TypeKind::Callable {
                    parameters,
                    result,
                    annotations,
                    ..
                } => {
                    out.extend(parameters.iter().map(Self::Parameter));
                    out.extend(annotations.iter().map(Self::Annotation));
                    if let Some(result) = result {
                        out.push(Self::Type(result));
                    }
                }
                TypeKind::TypeFunction { parameters, body } => {
                    out.extend(parameters.iter().map(Self::GenericParameter));
                    out.push(Self::Expression(body));
                }
                TypeKind::ComputedProjection { base, key } => {
                    out.push(Self::Type(base));
                    out.push(Self::Expression(key));
                }
                TypeKind::Computation(value) => out.push(Self::Expression(value)),
                TypeKind::Mapped {
                    mode, keys, value, ..
                } => {
                    if let Some(ModeExpression::Static(mode)) = mode {
                        out.push(Self::Expression(mode));
                    }
                    out.push(Self::Expression(keys));
                    out.push(Self::Type(value));
                }
                TypeKind::OpenRow
                | TypeKind::PatternRest(_)
                | TypeKind::TypeBinder(_)
                | TypeKind::ModeLiteral(_)
                | TypeKind::QualifiedMemberMode
                | TypeKind::Error => {}
            },
            Self::Pattern(pattern) => match &pattern.kind {
                PatternKind::Tuple(patterns)
                | PatternKind::Array(patterns)
                | PatternKind::Alternative(patterns)
                | PatternKind::Constructor {
                    arguments: patterns,
                    ..
                } => out.extend(patterns.iter().map(Self::Pattern)),
                PatternKind::Record { ty, fields, .. } => {
                    if let Some(ty) = ty {
                        out.push(Self::Type(ty));
                    }
                    out.extend(fields.iter().map(|field| Self::Pattern(&field.pattern)));
                }
                PatternKind::Mode { pattern, .. } => out.push(Self::Pattern(pattern)),
                PatternKind::Type(ty) => out.push(Self::Type(ty)),
                PatternKind::Name(_)
                | PatternKind::Wildcard
                | PatternKind::Literal(_)
                | PatternKind::Range { .. }
                | PatternKind::Rest(_)
                | PatternKind::Error => {}
            },
            Self::ValueTest(test) => match &test.kind {
                ValueTestKind::Value(value) => out.push(Self::Expression(value)),
                ValueTestKind::Range { start, end, .. } => {
                    out.push(Self::Expression(start));
                    out.push(Self::Expression(end));
                }
                ValueTestKind::Constructor { arguments, .. } => {
                    if let Some(arguments) = arguments {
                        out.extend(arguments.iter().map(Self::ValueTest));
                    }
                }
                ValueTestKind::Tuple(tests) | ValueTestKind::Alternative(tests) => {
                    out.extend(tests.iter().map(Self::ValueTest))
                }
                ValueTestKind::Record { ty, fields } => {
                    if let Some(ty) = ty {
                        out.push(Self::Type(ty));
                    }
                    out.extend(fields.iter().map(|field| Self::ValueTest(&field.test)));
                }
                ValueTestKind::Wildcard | ValueTestKind::Error => {}
            },
        }
    }
}
