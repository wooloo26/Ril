//! Source roles are checked before module resolution can introduce internal names.
use crate::{ast::*, lexer::diagnostic};
use ril_compiler_core::{diagnostic::Diagnostic, source::Span};
use std::collections::BTreeSet;

pub(crate) fn validate(program: &Program) -> Vec<Diagnostic> {
    let mut nullary = BTreeSet::from(["None".to_owned()]);
    for statement in &program.statements {
        if let StmtKind::Type(declaration) = &statement.kind {
            if declaration.nominal && declaration.value.is_none() {
                nullary.insert(declaration.name.clone());
            }
            for variant in &declaration.variants {
                if variant.payload.is_none() {
                    nullary.insert(variant.name.clone());
                }
            }
        }
    }
    let mut validator = Validator {
        diagnostics: vec![],
        nullary,
    };
    validator.statements(&program.statements, true, false);
    validator.diagnostics
}
struct Validator {
    diagnostics: Vec<Diagnostic>,
    nullary: BTreeSet<String>,
}
impl Validator {
    fn spelling(&mut self, name: &str, span: Span) {
        if !crate::lexer::valid_identifier(name) {
            self.error("E0102", span, "malformed identifier spelling");
        }
    }
    fn annotations(&mut self, annotations: &[Annotation]) {
        for annotation in annotations {
            for diagnostic in
                crate::lexer::lex(&annotation.text, annotation.span.file, 0).diagnostics
            {
                self.error(&diagnostic.code, annotation.span, &diagnostic.message);
            }
        }
    }
    fn error(&mut self, code: &str, span: Span, message: &str) {
        self.diagnostics.push(diagnostic(
            span.file,
            span.start as usize,
            span.end as usize,
            code,
            message,
        ));
    }
    fn snake(&mut self, name: &str, span: Span) {
        self.spelling(name, span);
        if name == "_" {
            return;
        }
        let name = name.strip_prefix('_').unwrap_or(name);
        if !name.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
            || !name
                .bytes()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'_')
        {
            self.error("E0101", span, "this declaration requires snake_case");
        }
    }
    fn pascal(&mut self, name: &str, span: Span) {
        self.spelling(name, span);
        if !name.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
            || !name.bytes().all(|c| c.is_ascii_alphanumeric())
        {
            self.error("E0101", span, "this declaration requires PascalCase");
        } else if name
            .as_bytes()
            .windows(2)
            .any(|pair| pair[0].is_ascii_uppercase() && pair[1].is_ascii_uppercase())
        {
            self.error("E0102", span, "PascalCase acronyms must be title-cased");
        }
    }
    fn constant(&mut self, name: &str, span: Span) {
        self.spelling(name, span);
        if name != "_"
            && (!name.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
                || !name
                    .bytes()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_'))
        {
            self.error(
                "E0101",
                span,
                "immutable module and meta bindings require SCREAMING_SNAKE_CASE",
            );
        }
    }
    fn statements(&mut self, statements: &[Stmt], top: bool, where_scope: bool) {
        let mut declared = BTreeSet::new();
        for statement in statements {
            // A pattern introduces one lexical declaration per spelling.
            // Repeated binders within one pattern branch are checked by the
            // pattern verifier as E0347; alternatives may share names.
            let names: BTreeSet<_> = declaration_names(statement).into_iter().collect();
            for name in names {
                if !declared.insert(name) {
                    self.error(
                        "E0203",
                        statement.span,
                        "duplicate declaration in one lexical scope",
                    );
                }
            }
            if where_scope
                && !matches!(
                    statement.kind,
                    StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
                )
            {
                self.error(
                    "E0702",
                    statement.span,
                    "where clauses contain only hoisted functions, types and effects",
                );
            }
            if !top
                && !where_scope
                && matches!(
                    statement.kind,
                    StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
                )
            {
                self.error(
                    "E0703",
                    statement.span,
                    "declarations inside an executable block belong in its where clause",
                );
            }
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.binding_pattern(
                        &binding.pattern,
                        (top && binding.mode == BindingMode::Let) || binding.is_meta,
                        false,
                    );
                    if let Some(ty) = &binding.ty {
                        self.ty(ty);
                    }
                    self.expr(&binding.value);
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback);
                    }
                }
                StmtKind::Function(function) => self.function(function),
                StmtKind::Type(declaration) => {
                    self.pascal(&declaration.name, declaration.span);
                    for generic in &declaration.generics {
                        self.generic(generic);
                    }
                    if let Some(value) = &declaration.value {
                        self.ty(value);
                    }
                    for variant in &declaration.variants {
                        self.annotations(&variant.annotations);
                        self.pascal(&variant.name, variant.span);
                        for generic in &variant.generics {
                            self.generic(generic);
                        }
                        if let Some(payload) = &variant.payload {
                            self.ty(payload);
                        }
                        if let Some(result) = &variant.result {
                            self.ty(result);
                        }
                    }
                }
                StmtKind::Effect(declaration) => {
                    self.pascal(&declaration.name, declaration.span);
                    for generic in &declaration.generics {
                        self.generic(generic);
                    }
                    for operation in &declaration.operations {
                        self.function(operation);
                    }
                    for member in &declaration.members {
                        self.ty(member);
                    }
                }
                StmtKind::Use(import) => {
                    for component in &import.path {
                        self.snake(component, import.span);
                    }
                    if let Some(alias) = &import.alias {
                        self.pascal(alias, import.span);
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression)
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        self.expr(&arm.operation);
                        for parameter in &arm.parameters {
                            self.parameter(parameter);
                        }
                        self.expr(&arm.body);
                    }
                }
            }
            // An application supplies the remaining computation as an ordinary
            // nullary callable. Its declarations belong to that callable's
            // execution scope, and can shadow the containing block's bindings.
            if !top && !where_scope && matches!(statement.kind, StmtKind::HandlerApplication(_)) {
                declared.clear();
            }
        }
    }
    fn function(&mut self, function: &Function) {
        self.snake(&function.name, function.span);
        self.annotations(&function.annotations);
        for generic in &function.generics {
            self.generic(generic);
        }
        for parameter in &function.parameters {
            self.parameter(parameter);
        }
        if let Some(result) = &function.return_type {
            self.ty(result);
        }
        for item in &function.signature_where {
            if !matches!(item.kind, StmtKind::Type(_)) {
                self.error(
                    "E0704",
                    item.span,
                    "signature where admits only type aliases",
                );
            }
        }
        self.statements(&function.signature_where, true, true);
        if let Some(body) = &function.body {
            self.block(body);
        }
    }
    fn parameter(&mut self, parameter: &Parameter) {
        self.binding_pattern(&parameter.pattern, false, false);
        if let Some(ty) = &parameter.ty {
            self.ty(ty);
        }
        if let Some(default) = &parameter.default {
            self.expr(default);
        }
    }
    fn generic(&mut self, generic: &GenericParameter) {
        if generic.name.chars().next().is_some_and(char::is_uppercase) {
            self.pascal(&generic.name, generic.span);
        } else {
            self.snake(&generic.name, generic.span);
        }
        if let Some(bound) = &generic.bound {
            self.ty(bound);
        }
        if let Some(default) = &generic.default {
            self.ty(default);
        }
    }
    fn block(&mut self, block: &Block) {
        self.statements(&block.statements, false, false);
        self.statements(&block.where_items, false, true);
    }
    fn binding_pattern(&mut self, pattern: &Pattern, constant: bool, nested: bool) {
        if matches!(&pattern.kind,PatternKind::Literal(Literal::Integer(text)|Literal::Float(text))if text.contains('\0'))
        {
            self.error(
                "E0111",
                pattern.span,
                "private numeric witnesses are not source syntax",
            );
        }
        match &pattern.kind {
            PatternKind::Name(name) => {
                if self.nullary.contains(name) {
                    self.error(
                        "E0309",
                        pattern.span,
                        "a nullary constructor pattern binds no variables",
                    );
                } else if constant {
                    self.constant(name, pattern.span);
                } else if nested && name.chars().next().is_some_and(char::is_uppercase) {
                    self.error(
                        "E0103",
                        pattern.span,
                        "pattern bindings cannot use uppercase identifiers",
                    );
                } else {
                    self.snake(name, pattern.span);
                }
            }
            PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
                for item in items {
                    self.binding_pattern(item, constant, true);
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    self.binding_pattern(&field.pattern, constant, true);
                }
            }
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                if arguments.is_empty() && path.len() == 1 && path[0].contains('_') {
                    self.error(
                        "E0103",
                        pattern.span,
                        "pattern binding casing collides with a constructor",
                    );
                }
                for argument in arguments {
                    self.binding_pattern(argument, constant, true);
                }
            }
            PatternKind::Mode { pattern, .. } => self.binding_pattern(pattern, constant, nested),
            PatternKind::Type { ty, .. } => self.ty(ty),
            PatternKind::Value(value) => self.expr(value),
            _ => {}
        }
    }
    fn ty(&mut self, ty: &TypeExpr) {
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                for part in path {
                    self.spelling(part.strip_prefix("let ").unwrap_or(part), ty.span);
                }
                if path.iter().any(|part| part.contains('\0')) {
                    self.error(
                        "E0101",
                        ty.span,
                        "source type paths cannot name compiler-internal identities",
                    );
                }
                for argument in arguments {
                    self.ty(argument);
                }
            }
            TypeKind::Optional(inner) | TypeKind::KeyOf(inner) | TypeKind::Rest(inner) => {
                self.ty(inner)
            }
            TypeKind::Array { length, element } => {
                if let Some(length) = length {
                    self.expr(length);
                }
                self.ty(element);
            }
            TypeKind::Map { key, value } => {
                self.ty(key);
                self.ty(value);
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.ty(item);
                }
            }
            TypeKind::Record { fields, row } => {
                let mut names = BTreeSet::new();
                for field in fields {
                    self.snake(&field.name, field.span);
                    if !names.insert(&field.name) {
                        self.error("E0210", field.span, "duplicate record field");
                    }
                    self.ty(&field.ty);
                }
                if let Some(row) = row {
                    self.ty(row);
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                self.annotations(annotations);
                for parameter in parameters {
                    self.parameter(parameter);
                }
                if let Some(result) = result {
                    self.ty(result);
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                for generic in parameters {
                    self.generic(generic);
                }
                self.expr(body);
            }
            TypeKind::Projection { base, .. } => self.ty(base),
            TypeKind::ComputedProjection { base, key } => {
                self.ty(base);
                self.expr(key);
            }
            TypeKind::Computation(value) => self.expr(value),
            TypeKind::Mapped { keys, value, .. } => {
                self.expr(keys);
                self.ty(value);
            }
            TypeKind::KindArrow { parameter, result } => {
                self.ty(parameter);
                self.ty(result);
            }
            TypeKind::Error => {}
        }
    }
    fn expr(&mut self, expr: &Expr) {
        if matches!(&expr.kind,ExprKind::Literal(Literal::Integer(text)|Literal::Float(text))if text.contains('\0'))
        {
            self.error(
                "E0111",
                expr.span,
                "private numeric witnesses are not source syntax",
            );
        }
        match &expr.kind {
            ExprKind::Name(name) if name.contains('\0') => self.error(
                "E0101",
                expr.span,
                "source names cannot contain compiler-reserved characters",
            ),
            ExprKind::Path(path) if path.iter().any(|part| part.contains('\0')) => self.error(
                "E0101",
                expr.span,
                "source paths cannot contain compiler-reserved characters",
            ),
            ExprKind::Name(name) if name == "_" => self.error(
                "E0322",
                expr.span,
                "wildcard cannot be evaluated as a value",
            ),
            ExprKind::Name(name) => self.spelling(name, expr.span),
            ExprKind::Path(path) => {
                for part in path {
                    self.spelling(part, expr.span);
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression);
                    }
                }
            }
            ExprKind::Generic { base, arguments } => {
                self.expr(base);
                for argument in arguments {
                    self.ty(argument);
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Map(pairs) => {
                for (key, value) in pairs {
                    self.expr(key);
                    self.expr(value);
                }
            }
            ExprKind::Record {
                ty,
                fields,
                members,
                ..
            } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                let mut names = BTreeSet::new();
                for field in fields {
                    if !names.insert(&field.name) {
                        self.error("E0210", field.span, "duplicate explicit record field");
                    }
                }
                for member in members {
                    match member {
                        RecordMember::Field(field) => self.expr(&field.value),
                        RecordMember::Spread(value) => self.expr(value),
                    }
                }
            }
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee);
                for argument in arguments {
                    self.expr(&argument.value);
                }
            }
            ExprKind::Field { base, .. } => self.expr(base),
            ExprKind::ComputedField { base, key } => {
                self.expr(base);
                self.expr(key);
            }
            ExprKind::Index { base, index, .. } => {
                self.expr(base);
                self.expr(index);
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                annotations,
            } => {
                self.annotations(annotations);
                for parameter in parameters {
                    self.parameter(parameter);
                }
                if let Some(result) = return_type {
                    self.ty(result);
                }
                self.expr(body);
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
                    self.binding_pattern(&arm.pattern, false, true);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&arm.body);
                }
            }
            ExprKind::Is { value, pattern } => {
                self.expr(value);
                self.binding_pattern(pattern, false, false);
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
                self.binding_pattern(pattern, false, true);
                self.block(body);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(value),
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => self.ty(ty),
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.expr(base);
                }
                self.expr(recipe);
            }
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    self.expr(start);
                }
                if let Some(end) = end {
                    self.expr(end);
                }
            }
            _ => {}
        }
    }
}
fn declaration_names(statement: &Stmt) -> Vec<String> {
    match &statement.kind {
        StmtKind::Function(f) => vec![f.name.clone()],
        StmtKind::Type(t) => vec![t.name.clone()],
        StmtKind::Effect(e) => vec![e.name.clone()],
        StmtKind::Binding(b) => {
            let mut result = vec![];
            names(&b.pattern, &mut result);
            result
        }
        _ => vec![],
    }
}
fn names(pattern: &Pattern, result: &mut Vec<String>) {
    match &pattern.kind {
        PatternKind::Name(name) if name != "_" => result.push(name.clone()),
        PatternKind::Tuple(items) | PatternKind::Alternative(items) => {
            for item in items {
                names(item, result);
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                names(&field.pattern, result);
            }
            if let Some(name) = rest_binding {
                result.push(name.clone());
            }
        }
        PatternKind::Constructor { arguments, .. } => {
            for argument in arguments {
                names(argument, result);
            }
        }
        PatternKind::Mode { pattern, .. } => names(pattern, result),
        _ => {}
    }
}
