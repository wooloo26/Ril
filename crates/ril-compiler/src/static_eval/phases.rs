//! Evaluation-family checks use the same lexical shadowing rules as values.
use super::*;

pub(super) fn validate(evaluator: &Evaluator, program: &Program, output: &mut Evaluation) {
    Validator {
        evaluator,
        locals: BTreeSet::new(),
    }
    .validate_statements(&program.statements, false, output);
}
struct Validator<'a> {
    evaluator: &'a Evaluator,
    locals: BTreeSet<String>,
}
impl Validator<'_> {
    fn nominal_constructor(&self, name: &str) -> bool {
        !self.locals.contains(name)
            && self
                .evaluator
                .declarations
                .get(name)
                .is_some_and(|declaration| declaration.nominal)
    }
    fn bind_pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.locals.insert(name.clone());
            }
            PatternKind::Tuple(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    self.bind_pattern(item);
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    self.bind_pattern(&field.pattern);
                }
                if let Some(name) = rest_binding {
                    self.locals.insert(name.clone());
                }
            }
            PatternKind::Mode { pattern, .. } => self.bind_pattern(pattern),
            _ => {}
        }
    }
    fn parameters(&mut self, parameters: &[Parameter], phase: bool, output: &mut Evaluation) {
        for parameter in parameters {
            if let Some(default) = &parameter.default {
                self.validate_phase(default, phase, output);
            }
            self.bind_pattern(&parameter.pattern);
        }
    }
    fn block(&mut self, block: &Block, phase: bool, output: &mut Evaluation) {
        let saved = self.locals.clone();
        self.validate_statements(&block.statements, phase, output);
        self.validate_statements(&block.where_items, phase, output);
        self.locals = saved;
    }
    fn validate_statements(
        &mut self,
        statements: &[Stmt],
        static_phase: bool,
        output: &mut Evaluation,
    ) {
        for statement in statements {
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.validate_phase(&binding.value, static_phase || binding.is_meta, output);
                    if let Some(fallback) = &binding.fallback {
                        self.validate_phase(fallback, static_phase || binding.is_meta, output);
                    }
                    self.bind_pattern(&binding.pattern);
                }
                StmtKind::Function(function) => {
                    let saved = self.locals.clone();
                    self.locals
                        .extend(function.generics.iter().map(|generic| generic.name.clone()));
                    self.parameters(&function.parameters, function.is_meta, output);
                    self.validate_statements(&function.signature_where, function.is_meta, output);
                    if let Some(body) = &function.body {
                        self.block(body, function.is_meta, output);
                    }
                    self.locals = saved;
                }
                StmtKind::Type(declaration) => {
                    if let Some(TypeExpr {
                        kind: TypeKind::TypeFunction { parameters, body },
                        ..
                    }) = &declaration.value
                    {
                        let saved = self.locals.clone();
                        self.locals.extend(
                            declaration
                                .generics
                                .iter()
                                .chain(parameters)
                                .map(|generic| generic.name.clone()),
                        );
                        self.validate_phase(body, true, output);
                        self.locals = saved;
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.validate_phase(target, static_phase, output);
                    self.validate_phase(value, static_phase, output);
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.validate_phase(expression, static_phase, output)
                }
                StmtKind::Handler(arms) => {
                    if static_phase {
                        output.failure(
                            Failure::Diagnostic(
                                "E0810",
                                "static computations cannot install run-time handlers".into(),
                            ),
                            statement.span,
                        );
                    }
                    for arm in arms {
                        let saved = self.locals.clone();
                        self.parameters(&arm.parameters, static_phase, output);
                        self.validate_phase(&arm.body, static_phase, output);
                        self.locals = saved;
                    }
                }
                StmtKind::Effect(effect) => {
                    for operation in &effect.operations {
                        let saved = self.locals.clone();
                        self.locals
                            .extend(effect.generics.iter().map(|generic| generic.name.clone()));
                        self.parameters(&operation.parameters, false, output);
                        self.locals = saved;
                    }
                }
                StmtKind::Use(_) => {}
            }
        }
    }
    fn validate_test_phase(
        &mut self,
        pattern: &Pattern,
        static_phase: bool,
        output: &mut Evaluation,
    ) {
        match &pattern.kind {
            PatternKind::Value(value) => self.validate_phase(value, static_phase, output),
            PatternKind::Tuple(patterns)
            | PatternKind::Alternative(patterns)
            | PatternKind::Constructor {
                arguments: patterns,
                ..
            } => {
                for pattern in patterns {
                    self.validate_test_phase(pattern, static_phase, output);
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    self.validate_test_phase(&field.pattern, static_phase, output);
                }
            }
            _ => {}
        }
    }
    fn validate_phase(&mut self, expression: &Expr, static_phase: bool, output: &mut Evaluation) {
        if let Some(name) = expression_name(expression).filter(|name| !self.locals.contains(name)) {
            if let Some(function) = self.evaluator.functions.get(&name) {
                if function.is_meta != static_phase {
                    output.failure(
                        Failure::Diagnostic(
                            "E0810",
                            "callable value belongs to a different evaluation family".into(),
                        ),
                        expression.span,
                    );
                }
            } else if static_phase
                && (primitive_type(&name) || self.evaluator.declarations.contains_key(&name))
                && !self.nominal_constructor(&name)
            {
                output.failure(
                    Failure::Diagnostic(
                        "E0319",
                        "a bare type name is not a type value; use type<T>".into(),
                    ),
                    expression.span,
                );
            }
        }
        match &expression.kind {
            ExprKind::Call { callee, arguments } => {
                if let Some(name) =
                    expression_name(callee).filter(|name| !self.locals.contains(name))
                {
                    let normalized = name.strip_prefix("Prelude::").unwrap_or(&name);
                    if !static_phase
                        && normalized == "byte_size"
                        && !self.evaluator.functions.contains_key(&name)
                    {
                        output.failure(
                            Failure::Diagnostic(
                                "E0810",
                                "byte_size is a static-only callable".into(),
                            ),
                            expression.span,
                        );
                    }
                    if static_phase
                        && !self.evaluator.functions.contains_key(&name)
                        && !self.nominal_constructor(&name)
                        && name.contains("::")
                        && !builtins::static_builtin(normalized)
                        && !matches!(normalized, "Some" | "Ok" | "Err")
                    {
                        output.failure(
                            Failure::Diagnostic(
                                "E0810",
                                "library callable is run-time-only".into(),
                            ),
                            expression.span,
                        );
                    }
                }
                self.validate_phase(callee, static_phase, output);
                for argument in arguments {
                    self.validate_phase(&argument.value, static_phase, output);
                }
            }
            ExprKind::Generic { base, .. } => {
                if !static_phase
                    && expression_name(base).is_some_and(|name| {
                        !self.locals.contains(&name)
                            && self.evaluator.declarations.get(&name).is_some_and(|decl| {
                                matches!(
                                    decl.value.as_ref().map(|value| &value.kind),
                                    Some(TypeKind::TypeFunction { .. })
                                )
                            })
                    })
                {
                    output.failure(
                        Failure::Diagnostic(
                            "E0810",
                            "type function invocation is not an ordinary run-time call".into(),
                        ),
                        expression.span,
                    );
                }
                // A type-function application uses its declaration as a callee;
                // that is not a bare type used as an ordinary value.
                if !expression_name(base)
                    .is_some_and(|name| self.evaluator.declarations.contains_key(&name))
                {
                    self.validate_phase(base, static_phase, output);
                }
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => {
                self.block(block, static_phase, output);
            }
            ExprKind::Lambda {
                parameters, body, ..
            } => {
                let saved = self.locals.clone();
                self.parameters(parameters, static_phase, output);
                self.validate_phase(body, static_phase, output);
                self.locals = saved;
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.validate_phase(condition, static_phase, output);
                let saved = self.locals.clone();
                self.validate_phase(then_branch, static_phase, output);
                self.locals = saved;
                if let Some(branch) = else_branch {
                    self.validate_phase(branch, static_phase, output);
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.validate_phase(value, static_phase, output);
                for arm in arms {
                    let saved = self.locals.clone();
                    self.validate_test_phase(&arm.pattern, static_phase, output);
                    self.bind_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        self.validate_phase(guard, static_phase, output);
                    }
                    self.validate_phase(&arm.body, static_phase, output);
                    self.locals = saved;
                }
            }
            ExprKind::Is { value, pattern } => {
                self.validate_phase(value, static_phase, output);
                self.validate_test_phase(pattern, static_phase, output);
            }
            ExprKind::Unary { operator, operand } if operator != "typeof" => {
                self.validate_phase(operand, static_phase, output)
            }
            ExprKind::Binary { left, right, .. } => {
                self.validate_phase(left, static_phase, output);
                let saved = self.locals.clone();
                self.validate_phase(right, static_phase, output);
                self.locals = saved;
            }
            ExprKind::While { condition, body } => {
                self.validate_phase(condition, static_phase, output);
                let saved = self.locals.clone();
                self.block(body, static_phase, output);
                self.locals = saved;
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.validate_phase(iterable, static_phase, output);
                let saved = self.locals.clone();
                self.bind_pattern(pattern);
                self.block(body, static_phase, output);
                self.locals = saved;
            }
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.validate_phase(base, static_phase, output);
                }
                self.validate_phase(recipe, static_phase, output);
            }
            ExprKind::Range { start, end, .. } => {
                for endpoint in start.iter().chain(end) {
                    self.validate_phase(endpoint, static_phase, output);
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.validate_phase(item, static_phase, output);
                }
            }
            ExprKind::Map(entries) => {
                for (key, value) in entries {
                    self.validate_phase(key, static_phase, output);
                    self.validate_phase(value, static_phase, output);
                }
            }
            ExprKind::Record { members, .. } => {
                for member in members {
                    match member {
                        RecordMember::Field(field) => {
                            self.validate_phase(&field.value, static_phase, output)
                        }
                        RecordMember::Spread(value) => {
                            self.validate_phase(value, static_phase, output)
                        }
                    }
                }
            }
            ExprKind::Field { base, .. } => self.validate_phase(base, static_phase, output),
            ExprKind::Index { base, index, .. } => {
                self.validate_phase(base, static_phase, output);
                self.validate_phase(index, static_phase, output);
            }
            ExprKind::ComputedField { base, key } => {
                self.validate_phase(base, static_phase, output);
                self.validate_phase(key, static_phase, output);
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.validate_phase(expression, static_phase, output);
                    }
                }
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.validate_phase(value, static_phase, output),
            // These type operands are checked without executing an ordinary
            // value expression. `typeof` in particular cannot invoke its body.
            ExprKind::TypeValue(_)
            | ExprKind::KeyOf(_)
            | ExprKind::Unary { .. }
            | ExprKind::Literal(_)
            | ExprKind::Name(_)
            | ExprKind::Path(_)
            | ExprKind::Accessor(_)
            | ExprKind::Ambient
            | ExprKind::Error
            | ExprKind::Control { value: None, .. } => {}
        }
    }
}
