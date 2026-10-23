//! Admission before owned snapshots. Shared Arc collection payloads are not
//! traversed: their actual Clone operation copies only the immutable handle.
//! Owned syntax/capture traversal has independent implementation stack/work
//! allowances and never expands a declaration EnvironmentId.
use super::*;

struct Meter<'a>(&'a budget::Budget);
impl Meter<'_> {
    fn node(&self, depth: usize) -> Result<()> {
        if depth > 128 {
            return Err(Failure::Unsupported(
                "static clone admission exceeds its implementation nesting allowance".into(),
            ));
        }
        self.0.work(1)
    }
    fn text(&self, value: &str) -> Result<()> {
        self.0.work(value.len() as u64)
    }
    fn strings<'a>(&self, values: impl Iterator<Item = &'a String>) -> Result<()> {
        for value in values {
            self.0.work(1)?;
            self.text(value)?;
        }
        Ok(())
    }
    fn annotations(&self, values: &[Annotation]) -> Result<()> {
        for value in values {
            self.text(&value.text)?;
        }
        Ok(())
    }
    fn values(&self, values: &BTreeMap<String, StaticValue>, depth: usize) -> Result<()> {
        self.node(depth)?;
        for (name, value) in values {
            self.text(name)?;
            self.value(value, depth + 1)?;
        }
        Ok(())
    }
    fn environment(&self, value: &environments::Environment, depth: usize) -> Result<()> {
        self.values(&value.values, depth)?;
        self.strings(value.declarations.keys())?;
        value.types.admit_clone(self.0)
    }
    fn value(&self, value: &StaticValue, depth: usize) -> Result<()> {
        self.node(depth)?;
        match value {
            StaticValue::String(value) => self.text(value),
            StaticValue::Bytes(value) => self.0.work(value.len() as u64),
            StaticValue::BigInteger(value) => self.0.work(value.bits().div_ceil(8)),
            StaticValue::Type(value) => self.ty(value, depth + 1),
            StaticValue::Callable(value) => self.callable(value, depth + 1),
            StaticValue::Result(value) => {
                self.value(&value.payload, depth + 1)?;
                if let Some(ty) = &value.ty {
                    self.ty(ty, depth + 1)?;
                }
                Ok(())
            }
            StaticValue::Variant(name, values, _) => {
                self.text(name)?;
                for value in values {
                    self.value(value, depth + 1)?;
                }
                Ok(())
            }
            StaticValue::Record(value) => self.strings(value.mutable_fields.iter()),
            StaticValue::Array(_)
            | StaticValue::ArrayWindow(_)
            | StaticValue::Tuple(_)
            | StaticValue::Map(_)
            | StaticValue::Integer(_)
            | StaticValue::TypedInteger(..)
            | StaticValue::Float(..)
            | StaticValue::Bool(_)
            | StaticValue::Unit => Ok(()),
        }
    }
    fn callable(&self, mut value: &StaticCallable, depth: usize) -> Result<()> {
        self.node(depth)?;
        // Tail-return interfaces can form long delegation chains. Traverse the
        // owned target iteratively, while admitting each actually cloned view.
        let mut delegation = 0;
        while let StaticCallable::View(view) = value {
            delegation += 1;
            if delegation > 2048 {
                return Err(Failure::Unsupported(
                    "static callable clone delegation exceeds its implementation stack allowance"
                        .into(),
                ));
            }
            self.node(depth)?;
            self.ty(&view.signature, depth + 1)?;
            self.environment(&view.captured, depth + 1)?;
            value = &view.target;
        }
        match value {
            StaticCallable::Prepared(_) => Ok(()),
            StaticCallable::Named { name, .. } | StaticCallable::Builtin(name) => self.text(name),
            StaticCallable::View(_) => unreachable!("delegation chain was peeled"),
            StaticCallable::Lambda {
                parameters,
                return_type,
                body,
                captured,
            } => {
                for parameter in parameters {
                    self.parameter(parameter, depth + 1)?;
                }
                if let Some(ty) = return_type {
                    self.ty(ty, depth + 1)?;
                }
                self.expr(body, depth + 1)?;
                self.environment(captured, depth + 1)
            }
        }
    }
    fn literal(&self, value: &Literal) -> Result<()> {
        match value {
            Literal::Integer(value)
            | Literal::Float(value)
            | Literal::String(value)
            | Literal::RawString(value)
            | Literal::Bytes(value) => self.text(value),
            _ => Ok(()),
        }
    }
    fn parameter(&self, value: &Parameter, depth: usize) -> Result<()> {
        self.node(depth)?;
        self.pattern(&value.pattern, depth + 1)?;
        if let Some(ty) = &value.ty {
            self.ty(ty, depth + 1)?;
        }
        if let Some(value) = &value.default {
            self.expr(value, depth + 1)?;
        }
        Ok(())
    }
    fn generic(&self, value: &GenericParameter, depth: usize) -> Result<()> {
        self.node(depth)?;
        self.text(&value.name)?;
        for ty in value.bound.iter().chain(&value.default) {
            self.ty(ty, depth + 1)?;
        }
        Ok(())
    }
    fn function(&self, value: &Function, depth: usize) -> Result<()> {
        self.node(depth)?;
        self.text(&value.name)?;
        self.annotations(&value.annotations)?;
        for parameter in &value.generics {
            self.generic(parameter, depth + 1)?;
        }
        for parameter in &value.parameters {
            self.parameter(parameter, depth + 1)?;
        }
        for statement in &value.signature_where {
            self.statement(statement, depth + 1)?;
        }
        if let Some(ty) = &value.return_type {
            self.ty(ty, depth + 1)?;
        }
        if let Some(body) = &value.body {
            self.block(body, depth + 1)?;
        }
        Ok(())
    }
    fn block(&self, value: &Block, depth: usize) -> Result<()> {
        self.node(depth)?;
        for statement in value.where_items.iter().chain(&value.statements) {
            self.statement(statement, depth + 1)?;
        }
        Ok(())
    }
    fn type_declaration(&self, value: &TypeDeclaration, depth: usize) -> Result<()> {
        self.node(depth)?;
        self.text(&value.name)?;
        for parameter in &value.generics {
            self.generic(parameter, depth + 1)?;
        }
        if let Some(ty) = &value.value {
            self.ty(ty, depth + 1)?;
        }
        for variant in &value.variants {
            self.text(&variant.name)?;
            self.annotations(&variant.annotations)?;
            for parameter in &variant.generics {
                self.generic(parameter, depth + 1)?;
            }
            for ty in variant.payload.iter().chain(&variant.result) {
                self.ty(ty, depth + 1)?;
            }
        }
        Ok(())
    }
    fn effect_declaration(&self, value: &EffectDeclaration, depth: usize) -> Result<()> {
        self.text(&value.name)?;
        for parameter in &value.generics {
            self.generic(parameter, depth + 1)?;
        }
        for function in &value.operations {
            self.function(function, depth + 1)?;
        }
        for ty in &value.members {
            self.ty(ty, depth + 1)?;
        }
        Ok(())
    }
    fn statement(&self, value: &Stmt, depth: usize) -> Result<()> {
        self.node(depth)?;
        match &value.kind {
            StmtKind::Binding(value) => {
                self.pattern(&value.pattern, depth + 1)?;
                if let Some(ty) = &value.ty {
                    self.ty(ty, depth + 1)?;
                }
                self.expr(&value.value, depth + 1)?;
                if let Some(value) = &value.fallback {
                    self.expr(value, depth + 1)?;
                }
            }
            StmtKind::Function(value) => self.function(value, depth + 1)?,
            StmtKind::Type(value) => self.type_declaration(value, depth + 1)?,
            StmtKind::Effect(value) => self.effect_declaration(value, depth)?,
            StmtKind::Use(value) => {
                self.strings(value.path.iter())?;
                if let Some(alias) = &value.alias {
                    self.text(alias)?;
                }
                for member in &value.members {
                    self.text(&member.name)?;
                    if let Some(alias) = &member.alias {
                        self.text(alias)?;
                    }
                }
            }
            StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                self.expr(expression, depth + 1)?
            }
            StmtKind::Assignment {
                target,
                operator,
                value,
            } => {
                self.text(operator)?;
                self.expr(target, depth + 1)?;
                self.expr(value, depth + 1)?;
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    self.node(depth + 1)?;
                    self.expr(&arm.operation, depth + 2)?;
                    for parameter in &arm.parameters {
                        self.parameter(parameter, depth + 2)?;
                    }
                    self.expr(&arm.body, depth + 2)?;
                }
            }
        }
        Ok(())
    }
    fn ty(&self, value: &TypeExpr, depth: usize) -> Result<()> {
        self.node(depth)?;
        self.text(&value.text)?;
        match &value.kind {
            TypeKind::Name { path, arguments } => {
                self.strings(path.iter())?;
                for ty in arguments {
                    self.ty(ty, depth + 1)?;
                }
            }
            TypeKind::Optional(ty) | TypeKind::Rest(ty) | TypeKind::KeyOf(ty) => {
                self.ty(ty, depth + 1)?
            }
            TypeKind::Array { length, element } => {
                self.ty(element, depth + 1)?;
                if let Some(value) = length {
                    self.expr(value, depth + 1)?;
                }
            }
            TypeKind::Map { key, value }
            | TypeKind::KindArrow {
                parameter: key,
                result: value,
            } => {
                self.ty(key, depth + 1)?;
                self.ty(value, depth + 1)?;
            }
            TypeKind::Tuple(values) => {
                for value in values {
                    self.ty(value, depth + 1)?;
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.text(&field.name)?;
                    self.ty(&field.ty, depth + 1)?;
                }
                if let Some(ty) = row {
                    self.ty(ty, depth + 1)?;
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                self.annotations(annotations)?;
                for parameter in parameters {
                    self.parameter(parameter, depth + 1)?;
                }
                if let Some(ty) = result {
                    self.ty(ty, depth + 1)?;
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                for parameter in parameters {
                    self.generic(parameter, depth + 1)?;
                }
                self.expr(body, depth + 1)?;
            }
            TypeKind::Projection { base, field } => {
                self.ty(base, depth + 1)?;
                self.text(field)?;
            }
            TypeKind::ComputedProjection { base, key } => {
                self.ty(base, depth + 1)?;
                self.expr(key, depth + 1)?;
            }
            TypeKind::Computation(value) => self.expr(value, depth + 1)?,
            TypeKind::Mapped {
                binder,
                keys,
                value,
                ..
            } => {
                self.text(binder)?;
                self.expr(keys, depth + 1)?;
                self.ty(value, depth + 1)?;
            }
            TypeKind::Error => {}
        }
        Ok(())
    }
    fn expr(&self, value: &Expr, depth: usize) -> Result<()> {
        self.node(depth)?;
        match &value.kind {
            ExprKind::Literal(value) => self.literal(value)?,
            ExprKind::Name(name) => self.text(name)?,
            ExprKind::Path(path) => self.strings(path.iter())?,
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    match part {
                        StringPart::Text(text) => self.text(text)?,
                        StringPart::Interpolation {
                            expression, format, ..
                        } => {
                            self.expr(expression, depth + 1)?;
                            if let Some(format) = format {
                                self.text(format)?;
                            }
                        }
                    }
                }
            }
            ExprKind::Generic { base, arguments } => {
                self.expr(base, depth + 1)?;
                for ty in arguments {
                    self.ty(ty, depth + 1)?;
                }
            }
            ExprKind::Tuple(values) | ExprKind::Array(values) => {
                for value in values {
                    self.expr(value, depth + 1)?;
                }
            }
            ExprKind::Map(values) => {
                for (key, value) in values {
                    self.expr(key, depth + 1)?;
                    self.expr(value, depth + 1)?;
                }
            }
            ExprKind::Record {
                ty,
                fields,
                spread,
                members,
            } => {
                if let Some(ty) = ty {
                    self.ty(ty, depth + 1)?;
                }
                if let Some(value) = spread {
                    self.expr(value, depth + 1)?;
                }
                for field in fields {
                    self.text(&field.name)?;
                    self.expr(&field.value, depth + 1)?;
                }
                for member in members {
                    match member {
                        RecordMember::Field(field) => {
                            self.text(&field.name)?;
                            self.expr(&field.value, depth + 1)?;
                        }
                        RecordMember::Spread(value) => self.expr(value, depth + 1)?,
                    }
                }
            }
            ExprKind::Unary { operator, operand } => {
                self.text(operator)?;
                self.expr(operand, depth + 1)?;
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                self.text(operator)?;
                self.expr(left, depth + 1)?;
                self.expr(right, depth + 1)?;
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee, depth + 1)?;
                for argument in arguments {
                    if let Some(label) = &argument.label {
                        self.text(label)?;
                    }
                    self.expr(&argument.value, depth + 1)?;
                }
            }
            ExprKind::Field { base, field, .. } => {
                self.expr(base, depth + 1)?;
                self.text(field)?;
            }
            ExprKind::ComputedField { base, key }
            | ExprKind::Index {
                base, index: key, ..
            } => {
                self.expr(base, depth + 1)?;
                self.expr(key, depth + 1)?;
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                body,
            } => {
                self.annotations(annotations)?;
                for parameter in parameters {
                    self.parameter(parameter, depth + 1)?;
                }
                if let Some(ty) = return_type {
                    self.ty(ty, depth + 1)?;
                }
                self.expr(body, depth + 1)?;
            }
            ExprKind::Accessor(parts) => {
                for part in parts {
                    self.text(&part.field)?;
                }
            }
            ExprKind::Block(body) | ExprKind::Loop(body) => self.block(body, depth + 1)?,
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, depth + 1)?;
                self.expr(then_branch, depth + 1)?;
                if let Some(value) = else_branch {
                    self.expr(value, depth + 1)?;
                }
            }
            ExprKind::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                self.expr(value, depth + 1)?;
                self.pattern(pattern, depth + 1)?;
                self.expr(then_branch, depth + 1)?;
                if let Some(value) = else_branch {
                    self.expr(value, depth + 1)?;
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.expr(value, depth + 1)?;
                for arm in arms {
                    self.pattern(&arm.pattern, depth + 1)?;
                    if let Some(guard) = &arm.guard {
                        self.expr(guard, depth + 1)?;
                    }
                    self.expr(&arm.body, depth + 1)?;
                }
            }
            ExprKind::Is { value, pattern } => {
                self.expr(value, depth + 1)?;
                self.pattern(pattern, depth + 1)?;
            }
            ExprKind::While { condition, body } => {
                self.expr(condition, depth + 1)?;
                self.block(body, depth + 1)?;
            }
            ExprKind::WhileLet {
                pattern,
                value,
                body,
            } => {
                self.expr(value, depth + 1)?;
                self.pattern(pattern, depth + 1)?;
                self.block(body, depth + 1)?;
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expr(iterable, depth + 1)?;
                self.pattern(pattern, depth + 1)?;
                self.block(body, depth + 1)?;
            }
            ExprKind::Control { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, depth + 1)?;
                }
            }
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => self.ty(ty, depth + 1)?,
            ExprKind::Derive { base, recipe } => {
                if let Some(base) = base {
                    self.expr(base, depth + 1)?;
                }
                self.expr(recipe, depth + 1)?;
            }
            ExprKind::Range { start, end, .. } => {
                for value in start.iter().chain(end) {
                    self.expr(value, depth + 1)?;
                }
            }
            ExprKind::Ambient | ExprKind::Error => {}
        }
        Ok(())
    }
    fn pattern(&self, value: &Pattern, depth: usize) -> Result<()> {
        self.node(depth)?;
        match &value.kind {
            PatternKind::Name(name) | PatternKind::Rest(Some(name)) => self.text(name)?,
            PatternKind::Literal(value) => self.literal(value)?,
            PatternKind::Tuple(values)
            | PatternKind::Array(values)
            | PatternKind::Alternative(values) => {
                for value in values {
                    self.pattern(value, depth + 1)?;
                }
            }
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                self.strings(path.iter())?;
                for value in arguments {
                    self.pattern(value, depth + 1)?;
                }
            }
            PatternKind::Record {
                ty,
                fields,
                rest_binding,
                ..
            } => {
                if let Some(ty) = ty {
                    self.ty(ty, depth + 1)?;
                }
                if let Some(name) = rest_binding {
                    self.text(name)?;
                }
                for field in fields {
                    self.text(&field.name)?;
                    self.pattern(&field.pattern, depth + 1)?;
                }
            }
            PatternKind::Mode { pattern, .. } => self.pattern(pattern, depth + 1)?,
            PatternKind::Type { ty, binder } => {
                self.ty(ty, depth + 1)?;
                if let Some(name) = binder {
                    self.text(name)?;
                }
            }
            PatternKind::Value(value) => self.expr(value, depth + 1)?,
            PatternKind::Wildcard | PatternKind::Rest(None) | PatternKind::Error => {}
        }
        Ok(())
    }
}
pub(super) fn values(
    budget: &budget::Budget,
    values: &BTreeMap<String, StaticValue>,
) -> Result<()> {
    Meter(budget).values(values, 0)
}
pub(super) fn declarations(
    budget: &budget::Budget,
    values: &BTreeMap<String, environments::EnvironmentId>,
) -> Result<()> {
    Meter(budget).strings(values.keys())
}
pub(super) fn type_declarations(
    budget: &budget::Budget,
    values: &BTreeMap<String, TypeDeclaration>,
) -> Result<()> {
    let meter = Meter(budget);
    for (name, declaration) in values {
        meter.text(name)?;
        meter.type_declaration(declaration, 0)?;
    }
    Ok(())
}
pub(super) fn environment(
    budget: &budget::Budget,
    value: &environments::Environment,
) -> Result<()> {
    Meter(budget).environment(value, 0)
}
pub(super) fn value(budget: &budget::Budget, value: &StaticValue) -> Result<()> {
    Meter(budget).value(value, 0)
}
pub(super) fn callable(budget: &budget::Budget, value: &StaticCallable) -> Result<()> {
    Meter(budget).callable(value, 0)
}
pub(super) fn function(budget: &budget::Budget, value: &Function) -> Result<()> {
    Meter(budget).function(value, 0)
}
pub(super) fn statement(budget: &budget::Budget, value: &Stmt) -> Result<()> {
    Meter(budget).statement(value, 0)
}
pub(super) fn effect_declaration(budget: &budget::Budget, value: &EffectDeclaration) -> Result<()> {
    let meter = Meter(budget);
    meter.node(0)?;
    meter.effect_declaration(value, 0)
}
pub(super) fn expression(budget: &budget::Budget, value: &Expr) -> Result<()> {
    Meter(budget).expr(value, 0)
}
pub(super) fn type_syntax(budget: &budget::Budget, value: &TypeExpr) -> Result<()> {
    Meter(budget).ty(value, 0)
}
pub(super) fn parameter(budget: &budget::Budget, value: &Parameter) -> Result<()> {
    Meter(budget).parameter(value, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parameter_default_handler_clone_preflights_all_owned_arm_syntax() {
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        };
        let name = |text: &str| Expr {
            kind: ExprKind::Name(text.into()),
            span,
            hir_id: None,
        };
        let parameter = Parameter {
            pattern: Pattern {
                kind: PatternKind::Wildcard,
                span,
                hir_id: None,
            },
            mode: ParameterMode::Read,
            ty: None,
            default: Some(Expr {
                kind: ExprKind::Block(Block {
                    statements: vec![Stmt {
                        kind: StmtKind::Handler(vec![HandlerArm {
                            operation: name("operation"),
                            parameters: vec![Parameter {
                                pattern: Pattern {
                                    kind: PatternKind::Name("input".into()),
                                    span,
                                    hir_id: None,
                                },
                                mode: ParameterMode::Read,
                                ty: Some(TypeExpr {
                                    text: "int".into(),
                                    kind: TypeKind::Name {
                                        path: vec!["int".into()],
                                        arguments: vec![],
                                    },
                                    span,
                                    hir_id: None,
                                }),
                                default: Some(name("fallback")),
                                span,
                            }],
                            body: name("answer"),
                            span,
                        }]),
                        span,
                        hir_id: None,
                    }],
                    where_items: vec![],
                    span,
                }),
                span,
                hir_id: None,
            }),
            span,
        };
        let budget = budget::Budget::with_work(4096);
        assert!(super::parameter(&budget, &parameter).is_ok());
        let cost = 4096 - budget.work_remaining();
        assert!(cost > 0);
        let exact = budget::Budget::with_work(cost);
        assert!(super::parameter(&exact, &parameter).is_ok());
        assert_eq!(exact.work_remaining(), 0);
        for work in [0, cost - 1] {
            let budget = budget::Budget::with_work(work);
            assert!(matches!(
                super::parameter(&budget, &parameter),
                Err(Failure::Unsupported(_))
            ));
        }

        let grow: [fn(&mut HandlerArm); 5] = [
            |arm| arm.operation.kind = ExprKind::Name("operation".repeat(128)),
            |arm| arm.parameters[0].pattern.kind = PatternKind::Name("input".repeat(128)),
            |arm| arm.parameters[0].ty.as_mut().unwrap().text = "int".repeat(128),
            |arm| {
                arm.parameters[0].default.as_mut().unwrap().kind =
                    ExprKind::Name("fallback".repeat(128));
            },
            |arm| arm.body.kind = ExprKind::Name("answer".repeat(128)),
        ];
        for grow in grow {
            let mut larger = parameter.clone();
            let ExprKind::Block(block) = &mut larger.default.as_mut().unwrap().kind else {
                unreachable!()
            };
            let StmtKind::Handler(arms) = &mut block.statements[0].kind else {
                unreachable!()
            };
            grow(&mut arms[0]);
            assert!(matches!(
                super::parameter(&budget::Budget::with_work(cost), &larger),
                Err(Failure::Unsupported(_))
            ));
        }
    }

    #[test]
    fn shared_collection_clone_cost_does_not_unfold_its_binary_graph() {
        let mut value = StaticValue::Integer(7);
        for id in 0..64 {
            value = StaticValue::Array(StaticCollection {
                id,
                source_type: None,
                values: std::sync::Arc::new(vec![value.clone(), value]),
            });
        }
        let values = [("shared".into(), value)].into();
        let mut budget = budget::Budget::new(std::num::NonZeroU64::new(1).unwrap());
        budget.enter_root();
        for _ in 0..1000 {
            super::values(&budget, &values).unwrap_or_else(|_| panic!("Arc copy is constant work"));
        }
        assert!(budget.event(budget::Event::FunctionEntry).is_ok());
        assert!(matches!(
            budget.event(budget::Event::LoopIteration),
            Err(Failure::Diagnostic("E0811", _))
        ));
    }
    #[test]
    fn deep_string_snapshots_fail_admission_without_consuming_language_events() {
        let values = [("large".into(), StaticValue::String("x".repeat(1_048_576)))].into();
        let mut budget = budget::Budget::new(std::num::NonZeroU64::new(1).unwrap());
        budget.enter_root();
        let mut refused = false;
        for _ in 0..100 {
            if let Err(Failure::Unsupported(why)) = super::values(&budget, &values) {
                assert!(why.contains("work allowance"));
                refused = true;
                break;
            }
        }
        assert!(refused, "owned bytes must be charged before a snapshot");
        assert!(budget.event(budget::Event::FunctionEntry).is_ok());
        assert!(matches!(
            budget.event(budget::Event::LoopIteration),
            Err(Failure::Diagnostic("E0811", _))
        ));
    }
}
