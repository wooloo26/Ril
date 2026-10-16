//! Static budgets do not certify a halt declaration. All reached symbolic/meta
//! helpers must have a finite dependency proof even when never evaluated.
use super::*;
#[path = "termination_loops.rs"]
mod loops;
#[derive(Default)]
struct Dependencies {
    calls: BTreeSet<String>,
    unknown: bool,
    divergent: bool,
}

pub(super) fn verify(evaluator: &Evaluator, output: &mut Evaluation) {
    let mut definitions = BTreeMap::new();
    for function in &output.static_definitions {
        let mut visitor = Visitor {
            evaluator,
            dependencies: Dependencies::default(),
            aliases: BTreeMap::new(),
            types: BTreeSet::new(),
            finite_sources: function
                .parameters
                .iter()
                .filter(|parameter| parameter.ty.as_ref().is_some_and(loops::collection_type))
                .filter_map(|parameter| match &parameter.pattern.kind {
                    PatternKind::Name(name) => Some(name.clone()),
                    _ => None,
                })
                .collect(),
            parameters: function
                .generics
                .iter()
                .filter(|parameter| {
                    matches!(
                        parameter.bound.as_ref().map(|bound| &bound.kind),
                        Some(TypeKind::KindArrow { .. })
                    )
                })
                .map(|parameter| parameter.name.clone())
                .collect(),
        };
        if let Some(body) = &function.body {
            visitor.block(body);
        } else {
            visitor.dependencies.unknown = true;
        }
        for parameter in &function.parameters {
            if let Some(default) = &parameter.default {
                visitor.expr(default);
            }
        }
        definitions.insert(
            function.name.clone(),
            (function.is_halt, function.span, visitor.dependencies),
        );
    }
    for declaration in &output.type_functions {
        let Some(TypeExpr {
            kind: TypeKind::TypeFunction { body, parameters },
            ..
        }) = &declaration.value
        else {
            continue;
        };
        let mut visitor = Visitor {
            evaluator,
            dependencies: Dependencies::default(),
            aliases: BTreeMap::new(),
            types: BTreeSet::new(),
            finite_sources: parameters
                .iter()
                .filter(|parameter| parameter.bound.as_ref().is_some_and(loops::collection_type))
                .map(|parameter| parameter.name.clone())
                .collect(),
            parameters: parameters
                .iter()
                .filter(|parameter| {
                    matches!(
                        parameter.bound.as_ref().map(|bound| &bound.kind),
                        Some(TypeKind::KindArrow { .. })
                    )
                })
                .map(|parameter| parameter.name.clone())
                .collect(),
        };
        for parameter in parameters {
            if let Some(bound) = &parameter.bound {
                visitor.ty(bound);
            }
            if let Some(default) = &parameter.default {
                visitor.ty(default);
            }
        }
        visitor.expr(body);
        definitions.insert(
            declaration.name.clone(),
            (declaration.is_halt, declaration.span, visitor.dependencies),
        );
    }
    let mut finite = BTreeSet::new();
    loop {
        let previous = finite.len();
        for (name, (_, _, dependencies)) in &definitions {
            if !dependencies.unknown
                && !dependencies.divergent
                && dependencies.calls.iter().all(|name| finite.contains(name))
            {
                finite.insert(name.clone());
            }
        }
        if finite.len() == previous {
            break;
        }
    }
    for (name, (halt, span, dependencies)) in definitions {
        let proved = finite.contains(&name);
        output.static_termination.insert(
            name,
            crate::termination::Judgment {
                may_diverge: dependencies.divergent,
                unresolved: !proved,
                callable_parameters: BTreeSet::new(),
            },
        );
        if halt && !proved {
            output.failure(
                Failure::Diagnostic(
                    "E0820",
                    "halt static computation includes a helper without a finite symbolic proof"
                        .into(),
                ),
                span,
            );
        }
    }
}
struct Visitor<'a> {
    evaluator: &'a Evaluator,
    dependencies: Dependencies,
    aliases: BTreeMap<String, Expr>,
    types: BTreeSet<String>,
    parameters: BTreeSet<String>,
    finite_sources: BTreeSet<String>,
}
impl Visitor<'_> {
    fn callable(&mut self, expr: &Expr, seen: &mut BTreeSet<String>) {
        match &expr.kind {
            ExprKind::Lambda { body, .. } => self.expr(body),
            ExprKind::Name(name) => {
                if !seen.insert(name.clone()) {
                    self.dependencies.unknown = true;
                    return;
                }
                if let Some(value) = self.aliases.get(name).cloned() {
                    self.callable(&value, seen);
                } else if self
                    .evaluator
                    .functions
                    .get(name)
                    .is_some_and(|function| function.is_meta)
                    || self
                        .evaluator
                        .declarations
                        .get(name)
                        .is_some_and(|declaration| {
                            matches!(
                                declaration.value.as_ref().map(|value| &value.kind),
                                Some(TypeKind::TypeFunction { .. })
                            )
                        })
                {
                    self.dependencies.calls.insert(name.clone());
                } else if !builtins::static_builtin(name.strip_prefix("Prelude::").unwrap_or(name))
                    && !matches!(
                        name.strip_prefix("Prelude::").unwrap_or(name),
                        "Some" | "Ok" | "Err"
                    )
                {
                    self.dependencies.unknown = true;
                }
            }
            ExprKind::Path(path) => self.callable(
                &Expr {
                    hir_id: None,
                    kind: ExprKind::Name(path.join("::")),
                    span: expr.span,
                },
                seen,
            ),
            ExprKind::Generic { base, .. } => self.callable(base, seen),
            _ => self.dependencies.unknown = true,
        }
    }
    fn block(&mut self, block: &Block) {
        let saved = self.aliases.clone();
        for statement in &block.statements {
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.expr(&binding.value);
                    if let PatternKind::Name(name) = &binding.pattern.kind {
                        self.aliases.insert(name.clone(), binding.value.clone());
                    }
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback);
                    }
                }
                StmtKind::Expr { expression, .. } => self.expr(expression),
                StmtKind::Function(_) | StmtKind::Type(_) => {}
                _ => self.dependencies.unknown = true,
            }
            if !loops::continues_statement(statement) {
                break;
            }
        }
        self.aliases = saved;
    }
    fn ty(&mut self, ty: &TypeExpr) {
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                for argument in arguments {
                    self.ty(argument);
                }
                let name = path.join("::");
                if self.parameters.contains(&name) {
                    self.dependencies.unknown = true;
                }
                if let Some(declaration) = self.evaluator.declarations.get(&name) {
                    if matches!(
                        declaration.value.as_ref().map(|value| &value.kind),
                        Some(TypeKind::TypeFunction { .. })
                    ) {
                        self.dependencies.calls.insert(name);
                    } else if !declaration.nominal
                        && !declaration.opaque
                        && self.types.insert(name.clone())
                    {
                        if let Some(value) = &declaration.value {
                            self.ty(value);
                        }
                        self.types.remove(&name);
                    }
                }
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.ty(item);
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
                for parameter in parameters {
                    if let Some(ty) = &parameter.ty {
                        self.ty(ty);
                    }
                    if let Some(default) = &parameter.default {
                        self.expr(default);
                    }
                }
                if let Some(result) = result {
                    self.ty(result);
                }
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
            TypeKind::TypeFunction { .. } | TypeKind::Error => {}
        }
    }
    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Call { callee, arguments } => {
                self.callable(callee, &mut BTreeSet::new());
                for argument in arguments {
                    self.expr(&argument.value);
                }
                if let Some(name) = expression_name(callee) {
                    let index = match name.as_str() {
                        "Array::map" | "Array::filter" | "Array::find" | "Array::any"
                        | "Array::all" | "Array::for_each" => Some(1),
                        "Array::fold" => Some(2),
                        _ => None,
                    };
                    if let Some(index) = index
                        && let Some(argument) = arguments.get(index)
                    {
                        self.callable(&argument.value, &mut BTreeSet::new());
                    }
                }
            }
            ExprKind::Generic { base, arguments } => {
                self.callable(base, &mut BTreeSet::new());
                for argument in arguments {
                    self.ty(argument);
                }
            }
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => self.ty(ty),
            ExprKind::Block(block) => self.block(block),
            ExprKind::Loop(block) => {
                self.dependencies.divergent |= loops::repeats(block);
                self.block(block);
            }
            ExprKind::While { condition, body } => {
                self.expr(condition);
                if loops::boolean(condition) != Some(false) {
                    self.dependencies.divergent |= loops::repeats(body);
                    self.block(body);
                }
            }
            ExprKind::For { iterable, body, .. } => {
                self.expr(iterable);
                if !self.finite_source(iterable, &mut BTreeSet::new()) && loops::repeats(body) {
                    self.dependencies.divergent = true;
                }
                self.block(body);
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
            ExprKind::Record { members, .. } => {
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
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                if !matches!(condition.kind, ExprKind::Literal(Literal::Bool(false))) {
                    self.expr(then_branch);
                }
                if !matches!(condition.kind, ExprKind::Literal(Literal::Bool(true)))
                    && let Some(branch) = else_branch
                {
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
            ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
                self.expr(operand)
            }
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
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(value),
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
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Type { ty, .. } => self.ty(ty),
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
            PatternKind::Record { fields, ty, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                for field in fields {
                    self.pattern(&field.pattern);
                }
            }
            PatternKind::Mode { pattern, .. } => self.pattern(pattern),
            PatternKind::Value(value) => self.expr(value),
            _ => {}
        }
    }
}
