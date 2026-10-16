//! Static declarations are verified even when hoisted in an ordinary callable's
//! lexical scope and never invoked. Collection must precede erasing runtime AST.
use super::*;
pub(super) struct Collected {
    pub functions: Vec<Function>,
    pub types: Vec<TypeDeclaration>,
    pub all_functions: BTreeMap<String, Function>,
    pub all_types: BTreeMap<String, TypeDeclaration>,
    pub all_effects: BTreeMap<String, EffectDeclaration>,
}
pub(super) fn collect(program: &Program) -> Collected {
    let mut visitor = Collector {
        functions: vec![],
        types: vec![],
        all_functions: BTreeMap::new(),
        all_types: BTreeMap::new(),
        all_effects: BTreeMap::new(),
    };
    let iteration = crate::sema::model::iteration::step_declaration();
    visitor.all_types.insert(iteration.name.clone(), iteration);
    visitor.statements(&program.statements);
    Collected {
        functions: visitor.functions,
        types: visitor.types,
        all_functions: visitor.all_functions,
        all_types: visitor.all_types,
        all_effects: visitor.all_effects,
    }
}
struct Collector {
    functions: Vec<Function>,
    types: Vec<TypeDeclaration>,
    all_functions: BTreeMap<String, Function>,
    all_types: BTreeMap<String, TypeDeclaration>,
    all_effects: BTreeMap<String, EffectDeclaration>,
}
impl Collector {
    fn statements(&mut self, statements: &[Stmt]) {
        for statement in statements {
            match &statement.kind {
                StmtKind::Function(function) => self.function(function),
                StmtKind::Type(declaration) => {
                    self.all_types
                        .insert(declaration.name.clone(), declaration.clone());
                    if matches!(
                        declaration.value.as_ref().map(|value| &value.kind),
                        Some(TypeKind::TypeFunction { .. })
                    ) {
                        self.types.push(declaration.clone());
                    }
                    self.generics(&declaration.generics);
                    if let Some(value) = &declaration.value {
                        self.ty(value);
                    }
                    for variant in &declaration.variants {
                        self.generics(&variant.generics);
                        if let Some(value) = &variant.payload {
                            self.ty(value);
                        }
                        if let Some(value) = &variant.result {
                            self.ty(value);
                        }
                    }
                }
                StmtKind::Effect(declaration) => {
                    self.all_effects
                        .insert(declaration.name.clone(), declaration.clone());
                    self.generics(&declaration.generics);
                    for operation in &declaration.operations {
                        self.function(operation);
                    }
                    for member in &declaration.members {
                        self.ty(member);
                    }
                }
                StmtKind::Binding(binding) => {
                    self.pattern(&binding.pattern);
                    if let Some(ty) = &binding.ty {
                        self.ty(ty);
                    }
                    self.expr(&binding.value);
                    if let Some(value) = &binding.fallback {
                        self.expr(value);
                    }
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression)
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.expr(target);
                    self.expr(value);
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        self.expr(&arm.operation);
                        self.parameters(&arm.parameters);
                        self.expr(&arm.body);
                    }
                }
                StmtKind::Use(_) => {}
            }
        }
    }
    fn function(&mut self, function: &Function) {
        self.all_functions
            .insert(function.name.clone(), function.clone());
        if function.is_meta {
            self.functions.push(function.clone());
        }
        self.generics(&function.generics);
        self.parameters(&function.parameters);
        if let Some(result) = &function.return_type {
            self.ty(result);
        }
        self.statements(&function.signature_where);
        if let Some(body) = &function.body {
            self.block(body);
        }
    }
    fn block(&mut self, block: &Block) {
        self.statements(&block.where_items);
        self.statements(&block.statements);
    }
    fn generics(&mut self, parameters: &[GenericParameter]) {
        for parameter in parameters {
            if let Some(ty) = &parameter.bound {
                self.ty(ty);
            }
            if let Some(ty) = &parameter.default {
                self.ty(ty);
            }
        }
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
    fn ty(&mut self, ty: &TypeExpr) {
        match &ty.kind {
            TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                for argument in arguments {
                    self.ty(argument);
                }
            }
            TypeKind::Optional(inner)
            | TypeKind::Rest(inner)
            | TypeKind::KeyOf(inner)
            | TypeKind::Projection { base: inner, .. } => self.ty(inner),
            TypeKind::Array { length, element } => {
                if let Some(length) = length {
                    self.expr(length);
                }
                self.ty(element);
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
            TypeKind::Mapped { keys, value, .. } => {
                self.expr(keys);
                self.ty(value);
            }
            TypeKind::Computation(value) => self.expr(value),
            TypeKind::Error => {}
        }
    }
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Tuple(patterns)
            | PatternKind::Alternative(patterns)
            | PatternKind::Constructor {
                arguments: patterns,
                ..
            } => {
                for pattern in patterns {
                    self.pattern(pattern);
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
            PatternKind::Value(value) => self.expr(value),
            _ => {}
        }
    }
    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block),
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                ..
            } => {
                self.parameters(parameters);
                if let Some(ty) = return_type {
                    self.ty(ty);
                }
                self.expr(body);
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
                    self.expr(match member {
                        RecordMember::Field(field) => &field.value,
                        RecordMember::Spread(value) => value,
                    });
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression);
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
