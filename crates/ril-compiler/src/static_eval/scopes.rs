//! Give source declarations lexical identities before building static registries.
//! Variables and generic binders keep their names and shadow enclosing declarations.
use super::*;
type Scope = BTreeMap<String, String>;
pub(super) fn normalize(program: &mut Program) {
    let mut resolver = Resolver {
        next: 0,
        instance: None,
    };
    let mut scope = Scope::new();
    resolver.declarations(&program.statements, &mut scope, true);
    resolver.statements(&mut program.statements, &scope);
}
pub(super) fn specialize_expression(expression: &mut Expr, instance: &str) {
    Resolver {
        next: 0,
        instance: Some(instance),
    }
    .expr(expression, &Scope::new());
}
struct Resolver<'a> {
    next: u64,
    instance: Option<&'a str>,
}
impl Resolver<'_> {
    fn declarations(&mut self, statements: &[Stmt], scope: &mut Scope, root: bool) {
        for statement in statements {
            let (name, type_name, compile_only) = match &statement.kind {
                StmtKind::Function(function) => (&function.name, false, function.is_meta),
                StmtKind::Type(declaration) => (
                    &declaration.name,
                    true,
                    matches!(
                        declaration.value.as_ref().map(|value| &value.kind),
                        Some(TypeKind::TypeFunction { .. })
                    ),
                ),
                StmtKind::Effect(declaration) => (&declaration.name, true, true),
                _ => continue,
            };
            let identity = if root && !compile_only {
                name.clone()
            } else {
                let number = self.next;
                self.next += 1;
                let instance = self.instance.unwrap_or("");
                if type_name {
                    format!("Ril__StaticScope{instance}{number}{name}")
                } else {
                    format!("ril__static_scope_{instance}{number}_{name}")
                }
            };
            scope.insert(name.clone(), identity);
        }
    }
    fn variable(&self, pattern: &Pattern, scope: &mut Scope) {
        match &pattern.kind {
            PatternKind::Name(name) | PatternKind::Rest(Some(name)) => {
                scope.insert(name.clone(), name.clone());
            }
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    self.variable(item, scope);
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    self.variable(&field.pattern, scope);
                }
                if let Some(name) = rest_binding {
                    scope.insert(name.clone(), name.clone());
                }
            }
            PatternKind::Mode { pattern, .. } => self.variable(pattern, scope),
            PatternKind::Type { ty, .. } => self.type_binders(ty, scope),
            _ => {}
        }
    }
    fn type_binders(&self, ty: &TypeExpr, scope: &mut Scope) {
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                if let Some(name) = path.first().and_then(|name| name.strip_prefix("let ")) {
                    scope.insert(name.into(), name.into());
                }
                for argument in arguments {
                    self.type_binders(argument, scope);
                }
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.type_binders(item, scope);
                }
            }
            TypeKind::Optional(inner)
            | TypeKind::Rest(inner)
            | TypeKind::Array { element: inner, .. } => self.type_binders(inner, scope),
            TypeKind::Map { key, value } => {
                self.type_binders(key, scope);
                self.type_binders(value, scope);
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.type_binders(&field.ty, scope);
                }
                if let Some(row) = row {
                    self.type_binders(row, scope);
                }
            }
            _ => {}
        }
    }
    fn generics(&mut self, parameters: &mut [GenericParameter], scope: &mut Scope) {
        for parameter in parameters {
            if let Some(bound) = &mut parameter.bound {
                self.ty(bound, scope);
            }
            if let Some(default) = &mut parameter.default {
                self.ty(default, scope);
            }
            scope.insert(parameter.name.clone(), parameter.name.clone());
        }
    }
    fn path(&self, path: &mut [String], scope: &Scope) {
        if let Some(name) = path.first_mut()
            && let Some(identity) = scope.get(name)
        {
            *name = identity.clone();
        }
    }
    fn statements(&mut self, statements: &mut [Stmt], parent: &Scope) {
        let mut scope = parent.clone();
        for statement in statements {
            match &mut statement.kind {
                StmtKind::Function(function) => {
                    if let Some(identity) = scope.get(&function.name) {
                        function.name = identity.clone();
                    }
                    let mut child = scope.clone();
                    self.generics(&mut function.generics, &mut child);
                    self.declarations(&function.signature_where, &mut child, false);
                    self.parameters(&mut function.parameters, &mut child);
                    if let Some(result) = &mut function.return_type {
                        self.ty(result, &child);
                    }
                    self.annotations(&mut function.annotations, &child);
                    self.statements(&mut function.signature_where, &child);
                    if let Some(body) = &mut function.body {
                        self.block(body, &child);
                    }
                }
                StmtKind::Type(declaration) => {
                    if let Some(identity) = scope.get(&declaration.name) {
                        declaration.name = identity.clone();
                    }
                    let mut child = scope.clone();
                    self.generics(&mut declaration.generics, &mut child);
                    if let Some(value) = &mut declaration.value {
                        self.ty(value, &child);
                    }
                    for variant in &mut declaration.variants {
                        let mut variant_scope = child.clone();
                        self.generics(&mut variant.generics, &mut variant_scope);
                        if let Some(ty) = &mut variant.payload {
                            self.ty(ty, &variant_scope);
                        }
                        if let Some(ty) = &mut variant.result {
                            self.ty(ty, &variant_scope);
                        }
                        self.annotations(&mut variant.annotations, &variant_scope);
                    }
                }
                StmtKind::Effect(declaration) => {
                    if let Some(identity) = scope.get(&declaration.name) {
                        declaration.name = identity.clone();
                    }
                    let mut child = scope.clone();
                    self.generics(&mut declaration.generics, &mut child);
                    for member in &mut declaration.members {
                        self.ty(member, &child);
                    }
                    for operation in &mut declaration.operations {
                        self.parameters(&mut operation.parameters, &mut child.clone());
                        if let Some(ty) = &mut operation.return_type {
                            self.ty(ty, &child);
                        }
                    }
                }
                StmtKind::Binding(binding) => {
                    self.pattern(&mut binding.pattern, &scope);
                    if let Some(ty) = &mut binding.ty {
                        self.ty(ty, &scope);
                    }
                    self.expr(&mut binding.value, &scope);
                    if let Some(fallback) = &mut binding.fallback {
                        self.expr(fallback, &scope);
                    }
                    self.variable(&binding.pattern, &mut scope);
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression, &scope)
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.expr(target, &scope);
                    self.expr(value, &scope);
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        self.expr(&mut arm.operation, &scope);
                        let mut child = scope.clone();
                        self.parameters(&mut arm.parameters, &mut child);
                        self.expr(&mut arm.body, &child);
                    }
                }
                StmtKind::Use(_) => {}
            }
        }
    }
    fn block(&mut self, block: &mut Block, parent: &Scope) {
        let mut scope = parent.clone();
        self.declarations(&block.where_items, &mut scope, false);
        self.declarations(&block.statements, &mut scope, false);
        for statement in &block.statements {
            if let StmtKind::Binding(binding) = &statement.kind {
                self.variable(&binding.pattern, &mut scope);
            }
        }
        self.statements(&mut block.where_items, &scope);
        self.statements(&mut block.statements, &scope);
    }
    fn parameters(&mut self, parameters: &mut [Parameter], scope: &mut Scope) {
        for parameter in parameters {
            self.pattern(&mut parameter.pattern, scope);
            if let Some(ty) = &mut parameter.ty {
                self.ty(ty, scope);
            }
            if let Some(default) = &mut parameter.default {
                self.expr(default, scope);
            }
            self.variable(&parameter.pattern, scope);
        }
    }
    fn annotations(&self, annotations: &mut [Annotation], scope: &Scope) {
        for annotation in annotations {
            let mut rewritten = String::new();
            let mut offset = 0;
            while offset < annotation.text.len() {
                let first = annotation.text.as_bytes()[offset];
                if first.is_ascii_alphabetic() || first == b'_' {
                    let start = offset;
                    offset += 1;
                    while offset < annotation.text.len()
                        && (annotation.text.as_bytes()[offset].is_ascii_alphanumeric()
                            || annotation.text.as_bytes()[offset] == b'_')
                    {
                        offset += 1;
                    }
                    let name = &annotation.text[start..offset];
                    if start == 0 || !matches!(annotation.text.as_bytes()[start - 1], b':' | b'.') {
                        rewritten.push_str(scope.get(name).map_or(name, String::as_str));
                    } else {
                        rewritten.push_str(name);
                    }
                } else {
                    let c = annotation.text[offset..].chars().next().unwrap();
                    rewritten.push(c);
                    offset += c.len_utf8();
                }
            }
            annotation.text = rewritten;
        }
    }
    fn ty(&mut self, ty: &mut TypeExpr, scope: &Scope) {
        match &mut ty.kind {
            TypeKind::Name { path, arguments } => {
                self.path(path, scope);
                for argument in arguments {
                    self.ty(argument, scope);
                }
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.ty(item, scope);
                }
            }
            TypeKind::Optional(inner)
            | TypeKind::Rest(inner)
            | TypeKind::KeyOf(inner)
            | TypeKind::Projection { base: inner, .. } => self.ty(inner, scope),
            TypeKind::Array { length, element } => {
                if let Some(length) = length {
                    self.expr(length, scope);
                }
                self.ty(element, scope);
            }
            TypeKind::Map { key, value }
            | TypeKind::KindArrow {
                parameter: key,
                result: value,
            } => {
                self.ty(key, scope);
                self.ty(value, scope);
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.ty(&mut field.ty, scope);
                }
                if let Some(row) = row {
                    self.ty(row, scope);
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                let mut child = scope.clone();
                self.parameters(parameters, &mut child);
                if let Some(result) = result {
                    self.ty(result, &child);
                }
                self.annotations(annotations, &child);
            }
            TypeKind::TypeFunction { parameters, body } => {
                let mut child = scope.clone();
                self.generics(parameters, &mut child);
                self.expr(body, &child);
            }
            TypeKind::ComputedProjection { base, key } => {
                self.ty(base, scope);
                self.expr(key, scope);
            }
            TypeKind::Mapped {
                binder,
                keys,
                value,
                ..
            } => {
                self.expr(keys, scope);
                let mut child = scope.clone();
                child.insert(binder.clone(), binder.clone());
                self.ty(value, &child);
            }
            TypeKind::Computation(value) => self.expr(value, scope),
            TypeKind::Error => {}
        }
    }
    fn pattern(&mut self, pattern: &mut Pattern, scope: &Scope) {
        match &mut pattern.kind {
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                self.path(path, scope);
                for pattern in arguments {
                    self.pattern(pattern, scope);
                }
            }
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items) => {
                for item in items {
                    self.pattern(item, scope);
                }
            }
            PatternKind::Record { ty, fields, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty, scope);
                }
                for field in fields {
                    self.pattern(&mut field.pattern, scope);
                }
            }
            PatternKind::Type { ty, .. } => self.ty(ty, scope),
            PatternKind::Mode { pattern, .. } => self.pattern(pattern, scope),
            PatternKind::Value(value) => self.expr(value, scope),
            _ => {}
        }
    }
    fn expr(&mut self, expression: &mut Expr, scope: &Scope) {
        match &mut expression.kind {
            ExprKind::Name(name) => {
                if let Some(identity) = scope.get(name) {
                    *name = identity.clone();
                }
            }
            ExprKind::Path(path) => self.path(path, scope),
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block, scope),
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                annotations,
            } => {
                let mut child = scope.clone();
                self.parameters(parameters, &mut child);
                if let Some(ty) = return_type {
                    self.ty(ty, &child);
                }
                self.annotations(annotations, &child);
                self.expr(body, &child);
            }
            ExprKind::Generic { base, arguments } => {
                self.expr(base, scope);
                for argument in arguments {
                    self.ty(argument, scope);
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(item, scope);
                }
            }
            ExprKind::Map(entries) => {
                for (key, value) in entries {
                    self.expr(key, scope);
                    self.expr(value, scope);
                }
            }
            ExprKind::Record { ty, members } => {
                if let Some(ty) = ty {
                    self.ty(ty, scope);
                }
                for member in members.iter_mut() {
                    match member {
                        RecordMember::Field(field) => self.expr(&mut field.value, scope),
                        RecordMember::Spread(value) => self.expr(value, scope),
                    }
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression, scope);
                    }
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
                self.expr(operand, scope)
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
                self.expr(left, scope);
                self.expr(right, scope);
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee, scope);
                for argument in arguments {
                    self.expr(&mut argument.value, scope);
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, scope);
                self.expr(then_branch, scope);
                if let Some(branch) = else_branch {
                    self.expr(branch, scope);
                }
            }
            ExprKind::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                self.expr(value, scope);
                self.pattern(pattern, scope);
                let mut child = scope.clone();
                self.variable(pattern, &mut child);
                self.expr(then_branch, &child);
                if let Some(branch) = else_branch {
                    self.expr(branch, scope);
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.expr(value, scope);
                for arm in arms {
                    self.pattern(&mut arm.pattern, scope);
                    let mut child = scope.clone();
                    self.variable(&arm.pattern, &mut child);
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard, &child);
                    }
                    self.expr(&mut arm.body, &child);
                }
            }
            ExprKind::Is { value, pattern } => {
                self.expr(value, scope);
                self.pattern(pattern, scope);
            }
            ExprKind::While { condition, body } => {
                self.expr(condition, scope);
                self.block(body, scope);
            }
            ExprKind::WhileLet {
                pattern,
                value,
                body,
            } => {
                self.expr(value, scope);
                self.pattern(pattern, scope);
                let mut child = scope.clone();
                self.variable(pattern, &mut child);
                self.block(body, &child);
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expr(iterable, scope);
                self.pattern(pattern, scope);
                let mut child = scope.clone();
                self.variable(pattern, &mut child);
                self.block(body, &child);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(value, scope),
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => self.ty(ty, scope),
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.expr(base, scope);
                }
                self.expr(recipe, scope);
            }
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    self.expr(start, scope);
                }
                if let Some(end) = end {
                    self.expr(end, scope);
                }
            }
            _ => {}
        }
    }
}
