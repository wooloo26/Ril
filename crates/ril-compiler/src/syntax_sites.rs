//! Until every owned AST node has an identity, a diagnostic span may not select
//! two different lexical handler/closure sites, or a contextual numeric literal
//! and another value expression. Actual invocations are separate.
use ril_compiler_core::source::Span;
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn ambiguous(program: &Program) -> Vec<crate::sema::UnsupportedFeature> {
    let mut visitor = Visitor {
        sites: BTreeSet::new(),
        numeric_sites: BTreeMap::new(),
        type_depth: 0,
        issues: vec![],
    };
    visitor.statements(&program.statements);
    visitor.issues
}
struct Visitor {
    sites: BTreeSet<(u8, u32, u32, u32)>,
    // Numeric contexts currently use a program-wide span key, unlike lexical
    // handler/closure keys. Keep this table across callable boundaries.
    numeric_sites: BTreeMap<(u32, u32, u32), (bool, bool)>,
    type_depth: usize,
    issues: Vec<crate::sema::UnsupportedFeature>,
}
impl Visitor {
    fn numeric_site(&mut self, span: Span, contextual: bool) {
        let key = (span.file.0, span.start, span.end);
        if let Some((was_contextual, reported)) = self.numeric_sites.get_mut(&key) {
            if (*was_contextual || contextual) && !*reported {
                self.issues.push(crate::sema::UnsupportedFeature {
                    span,
                    description: "distinct value expressions share a contextual numeric literal's diagnostic span; a unique syntax identity is required".into(),
                });
                *reported = true;
            }
            *was_contextual |= contextual;
        } else {
            self.numeric_sites.insert(key, (contextual, false));
        }
    }
    fn site(&mut self, kind: u8, span: Span) {
        if !self.sites.insert((kind, span.file.0, span.start, span.end)) {
            self.issues.push(crate::sema::UnsupportedFeature{span,description:format!("distinct lexical {} occurrences share one diagnostic span; a unique syntax identity is required",if kind==0{"handler"}else{"closure"})});
        }
    }
    fn callable(
        &mut self,
        generics: &[GenericParameter],
        parameters: &[Parameter],
        result: Option<&TypeExpr>,
        body: Option<&Block>,
        signature: &[Stmt],
    ) {
        let saved = std::mem::take(&mut self.sites);
        self.generics(generics);
        self.parameters(parameters);
        if let Some(result) = result {
            self.ty(result);
        }
        self.statements(signature);
        if let Some(body) = body {
            self.block(body);
        }
        self.sites = saved;
    }
    fn parameters(&mut self, parameters: &[Parameter]) {
        for parameter in parameters {
            self.pattern(&parameter.pattern);
            if let Some(ty) = &parameter.ty {
                self.ty(ty);
            }
            if let Some(default) = &parameter.default {
                self.expr(default);
            }
        }
    }
    fn generics(&mut self, parameters: &[GenericParameter]) {
        for parameter in parameters {
            for ty in parameter.bound.iter().chain(&parameter.default) {
                self.ty(ty);
            }
        }
    }
    fn statements(&mut self, statements: &[Stmt]) {
        for statement in statements {
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.pattern(&binding.pattern);
                    if let Some(ty) = &binding.ty {
                        self.ty(ty);
                    }
                    self.expr(&binding.value);
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback);
                    }
                }
                StmtKind::Function(function) => {
                    self.callable(
                        &function.generics,
                        &function.parameters,
                        function.return_type.as_ref(),
                        function.body.as_ref(),
                        &function.signature_where,
                    );
                }
                StmtKind::Type(declaration) => {
                    self.generics(&declaration.generics);
                    if let Some(ty) = &declaration.value {
                        self.ty(ty);
                    }
                    for variant in &declaration.variants {
                        self.generics(&variant.generics);
                        for ty in variant.payload.iter().chain(&variant.result) {
                            self.ty(ty);
                        }
                    }
                }
                StmtKind::Effect(effect) => {
                    self.generics(&effect.generics);
                    for member in &effect.members {
                        self.ty(member);
                    }
                    for operation in &effect.operations {
                        self.callable(
                            &operation.generics,
                            &operation.parameters,
                            operation.return_type.as_ref(),
                            operation.body.as_ref(),
                            &operation.signature_where,
                        );
                    }
                }
                StmtKind::Handler(arms) => {
                    self.site(0, statement.span);
                    for arm in arms {
                        self.expr(&arm.operation);
                        self.parameters(&arm.parameters);
                        self.expr(&arm.body);
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression)
                }
                StmtKind::Use(_) => {}
            }
        }
    }
    fn block(&mut self, block: &Block) {
        self.statements(&block.statements);
        self.statements(&block.where_items);
    }
    fn expr(&mut self, expression: &Expr) {
        self.numeric_site(expression.span, self.type_depth == 0 && matches!(&expression.kind, ExprKind::Literal(literal) if contextual_number(literal)));
        match &expression.kind {
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                ..
            } => {
                self.site(1, expression.span);
                let saved = std::mem::take(&mut self.sites);
                self.parameters(parameters);
                if let Some(ty) = return_type {
                    self.ty(ty);
                }
                self.expr(body);
                self.sites = saved;
            }
            ExprKind::Generic { base, arguments } => {
                self.expr(base);
                for ty in arguments {
                    self.ty(ty);
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Map(entries) => {
                for (key, value) in entries {
                    self.expr(key);
                    self.expr(value);
                }
            }
            ExprKind::Record { ty, members, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                for member in members {
                    match member {
                        RecordMember::Field(field) => self.expr(&field.value),
                        RecordMember::Spread(value) => self.expr(value),
                    }
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
                self.expr(operand)
            }
            ExprKind::Binary { left, right, .. }
            | ExprKind::ComputedField {
                base: left,
                key: right,
            }
            | ExprKind::Index {
                base: left,
                index: right,
                ..
            } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee);
                for argument in arguments {
                    self.expr(&argument.value);
                }
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                self.expr(then_branch);
                if let Some(branch) = else_branch {
                    self.expr(branch);
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.expr(value);
                for arm in arms {
                    self.pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&arm.body);
                }
            }
            ExprKind::Is { value, pattern } => {
                self.expr(value);
                self.pattern(pattern);
            }
            ExprKind::While { condition, body } => {
                self.expr(condition);
                self.block(body);
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expr(iterable);
                self.pattern(pattern);
                self.block(body);
            }
            ExprKind::Control { value, .. } => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => self.ty(ty),
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.expr(base);
                }
                self.expr(recipe);
            }
            ExprKind::Range { start, end, .. } => {
                for endpoint in start.iter().chain(end) {
                    self.expr(endpoint);
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression);
                    }
                }
            }
            ExprKind::Literal(_)
            | ExprKind::Name(_)
            | ExprKind::Path(_)
            | ExprKind::Accessor(_)
            | ExprKind::Ambient
            | ExprKind::Error => {}
        }
    }
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Literal(literal) => self.numeric_site(
                pattern.span,
                self.type_depth == 0 && contextual_number(literal),
            ),
            PatternKind::Value(value) => self.expr(value),
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    self.pattern(item);
                }
            }
            PatternKind::Record { ty, fields, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                for field in fields {
                    self.pattern(&field.pattern);
                }
            }
            PatternKind::Mode { pattern, .. } => self.pattern(pattern),
            PatternKind::Type { ty, .. } => self.ty(ty),
            PatternKind::Name(_) | PatternKind::Wildcard | PatternKind::Error => {}
        }
    }
    fn ty(&mut self, ty: &TypeExpr) {
        // Static type expressions can be copied when elaborating a written
        // construction context. Their literals are not runtime numeric holes.
        self.type_depth += 1;
        match &ty.kind {
            TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                for ty in arguments {
                    self.ty(ty);
                }
            }
            TypeKind::Optional(inner)
            | TypeKind::Rest(inner)
            | TypeKind::KeyOf(inner)
            | TypeKind::Projection { base: inner, .. } => self.ty(inner),
            TypeKind::Array { element, length } => {
                self.ty(element);
                if let Some(length) = length {
                    self.expr(length);
                }
            }
            TypeKind::Map { key, value }
            | TypeKind::KindArrow {
                parameter: key,
                result: value,
            } => {
                self.ty(key);
                self.ty(value);
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.ty(&field.ty);
                }
                if let Some(row) = row {
                    self.ty(row);
                }
            }
            TypeKind::Callable {
                parameters, result, ..
            } => {
                self.parameters(parameters);
                if let Some(result) = result {
                    self.ty(result);
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                self.generics(parameters);
                self.expr(body);
            }
            TypeKind::ComputedProjection { base, key } => {
                self.ty(base);
                self.expr(key);
            }
            TypeKind::Computation(value) => self.expr(value),
            TypeKind::Mapped { keys, value, .. } => {
                self.expr(keys);
                self.ty(value);
            }
            TypeKind::Error => {}
        }
        self.type_depth -= 1;
    }
}

fn contextual_number(literal: &Literal) -> bool {
    match literal {
        Literal::Integer(text) => ![
            "bigint", "int", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
        ]
        .iter()
        .any(|suffix| text.ends_with(suffix)),
        Literal::Float(text) => !text.ends_with("f32") && !text.ends_with("f64"),
        _ => false,
    }
}
