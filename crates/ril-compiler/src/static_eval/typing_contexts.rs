use super::*;
pub(super) fn collect(
    evaluator: &Evaluator,
    program: &Program,
) -> BTreeMap<String, bounds::BoundEnvironment> {
    let checker = Typer::new(evaluator, Some(Ty::Infer));
    let globals = checker.globals();
    let mut visitor = Visitor {
        checker,
        contexts: BTreeMap::new(),
        scope: bounds::BoundEnvironment::captured(globals.clone()),
    };
    visitor.statements(&program.statements, globals, false);
    visitor.contexts
}
struct Visitor<'a> {
    checker: Typer<'a>,
    contexts: BTreeMap<String, bounds::BoundEnvironment>,
    scope: bounds::BoundEnvironment,
}
impl Visitor<'_> {
    fn parameter_default(
        &mut self,
        parameters: &[Parameter],
        index: usize,
        env: &Env,
        static_phase: bool,
    ) {
        if let Some(default) = &parameters[index].default {
            let mut scope = env.clone();
            let mut forbidden = BTreeSet::new();
            for parameter in &parameters[index..] {
                application::binding_names(&parameter.pattern, &mut forbidden);
            }
            for name in forbidden {
                scope.insert(name.clone(), Ty::ForbiddenDefault(name));
            }
            self.expr(default, scope, static_phase);
        }
    }
    fn statements(&mut self, statements: &[Stmt], mut env: Env, static_phase: bool) {
        let entry_const_shadows = self.checker.const_shadows.borrow().clone();
        // Hoisted definitions see the lexical binding types, including declarations
        // appearing later. Actual evaluation still rejects an uninitialized capture.
        for statement in statements {
            if let StmtKind::Binding(binding) = &statement.kind {
                let expected = binding
                    .ty
                    .as_ref()
                    .and_then(|ty| self.checker.ty(ty, &env).ok());
                let mut ty = if static_phase || binding.is_meta {
                    let context = binding
                        .ty
                        .as_ref()
                        .and_then(|syntax| self.checker.context_for_syntax(syntax, &env).ok());
                    self.checker
                        .expr_result_expected(
                            &binding.value,
                            &mut env.clone(),
                            expected.as_ref(),
                            context.as_ref(),
                        )
                        .unwrap_or(Ty::Unknown)
                } else {
                    Ty::Unknown
                };
                if let Some(syntax) = &binding.ty
                    && let Ok(expected) = self.checker.ty(syntax, &env)
                {
                    ty = with_interfaces(ty, &expected);
                }
                if self.checker.bind(&binding.pattern, ty, &mut env).is_err() {
                    self.unavailable(&binding.pattern, &mut env);
                }
            }
        }
        for statement in statements {
            match &statement.kind {
                StmtKind::Function(function) => {
                    let mut captured = self.scope.clone();
                    captured.values = env.clone();
                    let _ = self.checker.apply_const_shadows(&mut captured);
                    if function.is_meta {
                        self.contexts
                            .insert(function.name.clone(), captured.clone());
                    }
                    let scope = self
                        .checker
                        .function_generic_environment(function, &captured)
                        .ok();
                    let mut child = scope
                        .as_ref()
                        .map_or_else(|| env.clone(), |scope| scope.values.clone());
                    if scope.is_none() {
                        for generic in &function.generics {
                            child.insert(generic.name.clone(), Ty::TypeParameter);
                        }
                    }
                    let previous_scope =
                        std::mem::replace(&mut self.scope, scope.unwrap_or(captured));
                    let previous_environment = self
                        .checker
                        .bound_environment
                        .replace(std::sync::Arc::new(self.scope.clone()));
                    let previous_const_shadows =
                        self.checker.const_shadows.replace(BTreeSet::new());
                    for (index, parameter) in function.parameters.iter().enumerate() {
                        self.parameter_default(
                            &function.parameters,
                            index,
                            &child,
                            function.is_meta,
                        );
                        let ty = if function.is_meta {
                            parameter
                                .ty
                                .as_ref()
                                .and_then(|ty| self.checker.ty(ty, &child).ok())
                                .unwrap_or(Ty::Unknown)
                        } else {
                            Ty::Unknown
                        };
                        if self
                            .checker
                            .bind(&parameter.pattern, ty, &mut child)
                            .is_err()
                        {
                            self.unavailable(&parameter.pattern, &mut child);
                        }
                    }
                    self.statements(&function.signature_where, child.clone(), function.is_meta);
                    if let Some(body) = &function.body {
                        self.block(body, child, function.is_meta);
                    }
                    self.scope = previous_scope;
                    self.checker.bound_environment = previous_environment;
                    *self.checker.const_shadows.borrow_mut() = previous_const_shadows;
                }
                StmtKind::Type(declaration) => {
                    if let Some(TypeExpr {
                        kind: TypeKind::TypeFunction { parameters, body },
                        ..
                    }) = &declaration.value
                    {
                        let mut captured = self.scope.clone();
                        captured.values = env.clone();
                        let _ = self.checker.apply_const_shadows(&mut captured);
                        self.contexts.insert(declaration.name.clone(), captured);
                        let mut child = env.clone();
                        for parameter in parameters {
                            let ty = if parameter
                                .name
                                .chars()
                                .next()
                                .is_some_and(char::is_uppercase)
                            {
                                parameter
                                    .bound
                                    .as_ref()
                                    .filter(|bound| {
                                        matches!(bound.kind, TypeKind::KindArrow { .. })
                                    })
                                    .map_or(Ty::TypeParameter, |bound| {
                                        Ty::Constructor(types::kind_arity(bound))
                                    })
                            } else {
                                parameter
                                    .bound
                                    .as_ref()
                                    .and_then(|ty| self.checker.ty(ty, &child).ok())
                                    .unwrap_or(Ty::Unknown)
                            };
                            child.insert(parameter.name.clone(), ty);
                        }
                        self.expr(body, child, true);
                    }
                }
                StmtKind::Binding(binding) => {
                    self.expr(&binding.value, env.clone(), static_phase || binding.is_meta);
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback, env.clone(), static_phase);
                    }
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression, env.clone(), static_phase)
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.expr(target, env.clone(), static_phase);
                    self.expr(value, env.clone(), static_phase);
                }
                _ => {}
            }
        }
        *self.checker.const_shadows.borrow_mut() = entry_const_shadows;
    }
    fn block(&mut self, block: &Block, env: Env, static_phase: bool) {
        let statements: Vec<_> = block
            .where_items
            .iter()
            .chain(&block.statements)
            .cloned()
            .collect();
        self.statements(&statements, env, static_phase);
    }
    fn unavailable(&self, pattern: &Pattern, env: &mut Env) {
        match &pattern.kind {
            PatternKind::Name(name) => {
                env.insert(name.clone(), Ty::Unknown);
            }
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    self.unavailable(item, env);
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    self.unavailable(&field.pattern, env);
                }
            }
            PatternKind::Mode { pattern, .. } => self.unavailable(pattern, env),
            _ => {}
        }
    }
    fn expr(&mut self, expr: &Expr, env: Env, static_phase: bool) {
        let entry_const_shadows = self.checker.const_shadows.borrow().clone();
        match &expr.kind {
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block, env, static_phase),
            ExprKind::Lambda {
                parameters, body, ..
            } => {
                let mut child = env;
                for (index, parameter) in parameters.iter().enumerate() {
                    self.parameter_default(parameters, index, &child, static_phase);
                    let ty = parameter
                        .ty
                        .as_ref()
                        .and_then(|ty| self.checker.ty(ty, &child).ok())
                        .unwrap_or(Ty::Unknown);
                    if self
                        .checker
                        .bind(&parameter.pattern, ty, &mut child)
                        .is_err()
                    {
                        self.unavailable(&parameter.pattern, &mut child);
                    }
                }
                self.expr(body, child, static_phase);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, env.clone(), static_phase);
                self.expr(then_branch, env.clone(), static_phase);
                if let Some(branch) = else_branch {
                    self.expr(branch, env, static_phase);
                }
            }
            ExprKind::Match { value, arms, .. } => {
                let value_ty = self
                    .checker
                    .expr(value, &mut env.clone())
                    .unwrap_or(Ty::Unknown);
                self.expr(value, env.clone(), static_phase);
                for arm in arms {
                    let arm_const_shadows = self.checker.const_shadows.borrow().clone();
                    let mut child = env.clone();
                    if self
                        .checker
                        .bind(&arm.pattern, value_ty.clone(), &mut child)
                        .is_err()
                    {
                        self.unavailable(&arm.pattern, &mut child);
                    }
                    if let Some(guard) = &arm.guard {
                        self.expr(guard, child.clone(), static_phase);
                    }
                    self.expr(&arm.body, child, static_phase);
                    *self.checker.const_shadows.borrow_mut() = arm_const_shadows;
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(item, env.clone(), static_phase);
                }
            }
            ExprKind::Map(entries) => {
                for (key, value) in entries {
                    self.expr(key, env.clone(), static_phase);
                    self.expr(value, env.clone(), static_phase);
                }
            }
            ExprKind::Record { members, .. } => {
                for member in members {
                    self.expr(
                        match member {
                            RecordMember::Field(field) => &field.value,
                            RecordMember::Spread(value) => value,
                        },
                        env.clone(),
                        static_phase,
                    );
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression, env.clone(), static_phase);
                    }
                }
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee, env.clone(), static_phase);
                for argument in arguments {
                    self.expr(&argument.value, env.clone(), static_phase);
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Field { base: operand, .. }
            | ExprKind::Generic { base: operand, .. } => self.expr(operand, env, static_phase),
            ExprKind::Binary { left, right, .. }
            | ExprKind::Index {
                base: left,
                index: right,
                ..
            }
            | ExprKind::ComputedField {
                base: left,
                key: right,
            } => {
                self.expr(left, env.clone(), static_phase);
                self.expr(right, env, static_phase);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(value, env, static_phase),
            ExprKind::While { condition, body } => {
                self.expr(condition, env.clone(), static_phase);
                self.block(body, env, static_phase);
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expr(iterable, env.clone(), static_phase);
                let mut child = env;
                let element = static_phase
                    .then(|| {
                        self.checker
                            .iteration_type(iterable, &mut child.clone())
                            .ok()
                    })
                    .flatten();
                if element
                    .is_none_or(|(ty, _, _)| self.checker.bind(pattern, ty, &mut child).is_err())
                {
                    self.unavailable(pattern, &mut child);
                }
                self.block(body, child, static_phase);
            }
            _ => {}
        }
        *self.checker.const_shadows.borrow_mut() = entry_const_shadows;
    }
}
