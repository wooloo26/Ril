//! Check the two `where` tiers before lexical names are rewritten. Confinement
//! runs afterwards, when aliases and local nominal declarations have identities.
use super::transform::type_names;
use super::*;

pub(super) fn validate(program: &Program) -> Vec<Diagnostic> {
    let mut checker = ScopeChecker {
        diagnostics: vec![],
    };
    checker.statements(&program.statements, &BTreeSet::new());
    checker.diagnostics
}

struct ScopeChecker {
    diagnostics: Vec<Diagnostic>,
}
impl ScopeChecker {
    fn error(&mut self, code: &str, span: Span, message: &str) {
        self.diagnostics.push(Diagnostic {
            code: code.into(),
            severity: Severity::Error,
            message: message.into(),
            labels: vec![Label {
                span,
                message: message.into(),
            }],
            causes: vec![],
        });
    }
    fn statements(&mut self, statements: &[Stmt], parent: &BTreeSet<String>) {
        let mut scope = parent.clone();
        scope.extend(declared_names(statements));
        for statement in statements {
            match &statement.kind {
                StmtKind::Function(function) => self.function(function, &scope),
                StmtKind::Binding(binding) => {
                    self.expr(&binding.value, &scope);
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback, &scope);
                    }
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
                        self.expr(&arm.body, &scope);
                    }
                }
                _ => {}
            }
        }
    }
    fn function(&mut self, function: &Function, outer: &BTreeSet<String>) {
        let mut signature = outer.clone();
        signature.extend(declared_names(&function.signature_where));
        signature.extend(function.generics.iter().map(|generic| generic.name.clone()));
        let body_names = function
            .body
            .as_ref()
            .map_or(BTreeSet::new(), |body| declared_names(&body.where_items));
        let signature_names = declared_names(&function.signature_where);
        for name in signature_names.intersection(&body_names) {
            self.error(
                "E0203",
                function.span,
                &format!("{name} is declared in both where tiers"),
            );
        }
        let unavailable: BTreeSet<_> = body_names.difference(&signature).cloned().collect();
        for ty in function
            .parameters
            .iter()
            .filter_map(|parameter| parameter.ty.as_ref())
            .chain(function.return_type.iter())
            .chain(
                function
                    .generics
                    .iter()
                    .filter_map(|generic| generic.bound.as_ref()),
            )
        {
            let mut names = BTreeSet::new();
            type_names(ty, &mut names);
            if !names.is_disjoint(&unavailable) {
                self.error(
                    "E0706",
                    ty.span,
                    "a function signature cannot reference a type from its body where clause",
                );
            }
        }
        for statement in &function.signature_where {
            if let StmtKind::Type(declaration) = &statement.kind {
                let mut names = BTreeSet::new();
                if let Some(value) = &declaration.value {
                    type_names(value, &mut names);
                }
                for generic in &declaration.generics {
                    if let Some(bound) = &generic.bound {
                        type_names(bound, &mut names);
                    }
                    if let Some(default) = &generic.default {
                        type_names(default, &mut names);
                    }
                }
                for generic in &declaration.generics {
                    names.remove(&generic.name);
                }
                if !names.is_disjoint(&unavailable) {
                    self.error(
                        "E0705",
                        declaration.span,
                        "signature where declarations cannot depend on body where declarations",
                    );
                }
            }
        }
        self.statements(&function.signature_where, &signature);
        if let Some(body) = &function.body {
            self.block(body, &signature);
        }
    }
    fn block(&mut self, block: &Block, parent: &BTreeSet<String>) {
        let mut scope = parent.clone();
        scope.extend(declared_names(&block.where_items));
        self.statements(&block.where_items, &scope);
        self.statements(&block.statements, &scope);
    }
    fn expr(&mut self, expression: &Expr, scope: &BTreeSet<String>) {
        match &expression.kind {
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block, scope),
            ExprKind::Lambda { body, .. } => self.expr(body, scope),
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
            ExprKind::Record { members, .. } => {
                for member in members {
                    self.expr(
                        match member {
                            RecordMember::Field(field) => &field.value,
                            RecordMember::Spread(value) => value,
                        },
                        scope,
                    );
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression, scope);
                    }
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Field { base: operand, .. }
            | ExprKind::Generic { base: operand, .. } => self.expr(operand, scope),
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
                    self.expr(&argument.value, scope);
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
            ExprKind::Match { value, arms, .. } => {
                self.expr(value, scope);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.expr(guard, scope);
                    }
                    self.expr(&arm.body, scope);
                }
            }
            ExprKind::While { condition, body } => {
                self.expr(condition, scope);
                self.block(body, scope);
            }
            ExprKind::For { iterable, body, .. } => {
                self.expr(iterable, scope);
                self.block(body, scope);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(value, scope),
            _ => {}
        }
    }
}

fn declared_names(statements: &[Stmt]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for statement in statements {
        match &statement.kind {
            StmtKind::Type(declaration) => {
                names.insert(declaration.name.clone());
            }
            StmtKind::Effect(declaration) => {
                names.insert(declaration.name.clone());
            }
            StmtKind::Use(import) => {
                if let Some(alias) = &import.alias {
                    names.insert(alias.clone());
                }
                names.extend(
                    import
                        .members
                        .iter()
                        .map(|member| member.alias.as_ref().unwrap_or(&member.name).clone()),
                );
            }
            _ => {}
        }
    }
    names
}

pub(super) fn confinement(evaluator: &Evaluator, output: &mut Evaluation) {
    let functions = definitions::collect(&output.program).all_functions;
    for function in functions.values() {
        let Some(result) = &function.return_type else {
            continue;
        };
        let mut local = BTreeSet::new();
        for statement in &function.signature_where {
            if let StmtKind::Type(declaration) = &statement.kind {
                local.insert(declaration.name.clone());
            }
        }
        if let Some(body) = &function.body {
            for statement in &body.where_items {
                if let StmtKind::Type(declaration) = &statement.kind {
                    local.insert(declaration.name.clone());
                }
            }
        }
        let generic: BTreeSet<_> = function
            .generics
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect();
        if escaping(
            result,
            &local,
            &generic,
            &evaluator.declarations,
            &BTreeMap::new(),
            &mut BTreeSet::new(),
        ) {
            output.failure(
                Failure::Diagnostic(
                    "E0315",
                    "returned value or callable type contains a function-local nominal identity"
                        .into(),
                ),
                result.span,
            );
        }
    }
}

fn escaping(
    ty: &TypeExpr,
    local: &BTreeSet<String>,
    generic: &BTreeSet<String>,
    declarations: &BTreeMap<String, TypeDeclaration>,
    substitutions: &BTreeMap<String, TypeExpr>,
    seen: &mut BTreeSet<String>,
) -> bool {
    let child = |ty: &TypeExpr, seen: &mut BTreeSet<String>| {
        escaping(ty, local, generic, declarations, substitutions, seen)
    };
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            let name = path.join("::");
            if let Some(value) = substitutions.get(&name) {
                let mut remaining = substitutions.clone();
                remaining.remove(&name);
                return escaping(value, local, generic, declarations, &remaining, seen);
            }
            if generic.contains(&name) {
                return false;
            }
            let Some(declaration) = declarations.get(&name) else {
                return arguments
                    .iter()
                    .any(|argument| child(argument, &mut seen.clone()));
            };
            if declaration.nominal || declaration.opaque || !declaration.variants.is_empty() {
                return local.contains(&name)
                    || arguments
                        .iter()
                        .any(|argument| child(argument, &mut seen.clone()));
            }
            if !seen.insert(name.clone()) {
                return false;
            }
            let mut actual = substitutions.clone();
            for (index, parameter) in declaration.generics.iter().enumerate() {
                if let Some(value) = arguments.get(index).or(parameter.default.as_ref()) {
                    actual.insert(parameter.name.clone(), value.clone());
                }
            }
            let result = declaration
                .value
                .as_ref()
                .is_some_and(|value| escaping(value, local, generic, declarations, &actual, seen));
            seen.remove(&name);
            result
        }
        TypeKind::Array { element: inner, .. }
        | TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Projection { base: inner, .. }
        | TypeKind::ComputedProjection { base: inner, .. } => child(inner, seen),
        TypeKind::Tuple(items) => items.iter().any(|item| child(item, &mut seen.clone())),
        TypeKind::Map { key, value } => {
            child(key, &mut seen.clone()) || child(value, &mut seen.clone())
        }
        TypeKind::Record { fields, row } => {
            fields
                .iter()
                .any(|field| child(&field.ty, &mut seen.clone()))
                || row
                    .as_ref()
                    .is_some_and(|row| child(row, &mut seen.clone()))
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            parameters.iter().any(|parameter| {
                parameter
                    .ty
                    .as_ref()
                    .is_some_and(|ty| child(ty, &mut seen.clone()))
            }) || result
                .as_ref()
                .is_some_and(|result| child(result, &mut seen.clone()))
        }
        _ => false,
    }
}
