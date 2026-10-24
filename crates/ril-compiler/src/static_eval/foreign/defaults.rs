//! Specialize default expressions without changing their run-time evaluation.
//! Only static binders are substituted; ordinary lexical binders mask them.
use super::*;

pub(crate) fn instantiate_defaults_bounded(
    function: &Function,
    arguments: &[TypeExpr],
    parameters: &mut [Parameter],
    instance: &str,
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
    work: &mut usize,
) -> std::result::Result<(), ArgumentNormalizationError> {
    let mut budget = super::super::budget::Budget::default();
    let root = budget.enter_root();
    budget.restrict_work(u64::try_from(*work).unwrap_or(u64::MAX));
    if let Err(error) = super::super::clone_work::type_declarations(&budget, declarations) {
        *work = usize::try_from(budget.work_remaining()).unwrap_or(usize::MAX);
        budget.leave_root(root);
        return Err(failure(error));
    }
    let mut evaluator = evaluator(declarations, layout);
    evaluator.budget = budget;
    let result = (|| {
        evaluator.bind_type_arguments(&function.generics, arguments, &function.name)?;
        for parameter in parameters {
            if let Some(default) = &mut parameter.default {
                super::super::clone_work::expression(&evaluator.budget, default)?;
                super::super::scopes::specialize_expression(default, instance);
                expression(&mut evaluator, default)?;
            }
            mask(&mut evaluator, &parameter.pattern)?;
        }
        Ok(())
    })();
    *work = usize::try_from(evaluator.budget.work_remaining()).unwrap_or(usize::MAX);
    evaluator.budget.leave_root(root);
    result.map_err(failure)
}

fn mask(evaluator: &mut Evaluator, pattern: &Pattern) -> Result<()> {
    match &pattern.kind {
        PatternKind::Name(name) | PatternKind::Rest(Some(name)) => {
            evaluator.values.remove(name);
        }
        PatternKind::Wildcard
        | PatternKind::Rest(None)
        | PatternKind::Literal(_)
        | PatternKind::Value(_)
        | PatternKind::Error => {}
        PatternKind::Tuple(items)
        | PatternKind::Array(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                mask(evaluator, item)?;
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                mask(evaluator, &field.pattern)?;
            }
            if let Some(name) = rest_binding {
                evaluator.values.remove(name);
            }
        }
        PatternKind::Mode { pattern, .. } => mask(evaluator, pattern)?,
        PatternKind::Type { ty, binder } => {
            if let Some(name) = binder {
                evaluator.values.remove(name);
            }
            mask_type_binders(evaluator, ty);
        }
    }
    Ok(())
}

fn mask_type_binders(evaluator: &mut Evaluator, syntax: &TypeExpr) {
    match &syntax.kind {
        TypeKind::Name { path, arguments } => {
            if let Some(name) = path.first().and_then(|name| name.strip_prefix("let ")) {
                evaluator.values.remove(name);
            }
            for argument in arguments {
                mask_type_binders(evaluator, argument);
            }
        }
        TypeKind::Tuple(items) => {
            for item in items {
                mask_type_binders(evaluator, item);
            }
        }
        TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Array { element: inner, .. } => mask_type_binders(evaluator, inner),
        TypeKind::Map { key, value } => {
            mask_type_binders(evaluator, key);
            mask_type_binders(evaluator, value);
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                mask_type_binders(evaluator, &field.ty);
            }
            if let Some(row) = row {
                mask_type_binders(evaluator, row);
            }
        }
        _ => {}
    }
}

fn pattern(evaluator: &mut Evaluator, pattern: &mut Pattern, binding: bool) -> Result<()> {
    match &mut pattern.kind {
        PatternKind::Name(name) if !binding => {
            if let Some(constant) = evaluator.values.get(name).cloned() {
                pattern.kind = PatternKind::Value(Box::new(
                    evaluator.const_value_expr(constant, pattern.span)?,
                ));
            }
        }
        PatternKind::Tuple(items)
        | PatternKind::Array(items)
        | PatternKind::Alternative(items)
        | PatternKind::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                self::pattern(evaluator, item, binding)?;
            }
        }
        PatternKind::Record {
            ty: syntax, fields, ..
        } => {
            if let Some(syntax) = syntax {
                ty(evaluator, syntax)?;
            }
            for field in fields {
                self::pattern(evaluator, &mut field.pattern, binding)?;
            }
        }
        PatternKind::Mode { pattern, .. } => self::pattern(evaluator, pattern, binding)?,
        PatternKind::Type { ty: syntax, .. } => {
            let outer = evaluator.snapshot_values()?;
            mask_type_binders(evaluator, syntax);
            ty(evaluator, syntax)?;
            evaluator.values = outer;
        }
        PatternKind::Value(value) => expression(evaluator, value)?,
        PatternKind::Name(_)
        | PatternKind::Rest(_)
        | PatternKind::Literal(_)
        | PatternKind::Wildcard
        | PatternKind::Error => {}
    }
    Ok(())
}

fn parameters(evaluator: &mut Evaluator, parameters: &mut [Parameter]) -> Result<()> {
    for parameter in parameters {
        pattern(evaluator, &mut parameter.pattern, true)?;
        if let Some(syntax) = &mut parameter.ty {
            ty(evaluator, syntax)?;
        }
        if let Some(default) = &mut parameter.default {
            expression(evaluator, default)?;
        }
        mask(evaluator, &parameter.pattern)?;
    }
    Ok(())
}

fn generics(evaluator: &mut Evaluator, generics: &mut [GenericParameter]) -> Result<()> {
    for generic in generics {
        if let Some(bound) = &mut generic.bound {
            ty(evaluator, bound)?;
        }
        if let Some(default) = &mut generic.default {
            argument(evaluator, default)?;
        }
        evaluator.values.remove(&generic.name);
    }
    Ok(())
}

fn argument(evaluator: &mut Evaluator, argument: &mut TypeExpr) -> Result<()> {
    if let TypeKind::Computation(value) = &mut argument.kind {
        expression(evaluator, value)?;
    } else if let TypeKind::Name { path, arguments } = &argument.kind
        && arguments.is_empty()
        && let Some(constant) = evaluator.values.get(&path.join("::")).cloned()
        && !matches!(constant, StaticValue::Type(_))
    {
        argument.kind = TypeKind::Computation(Box::new(
            evaluator.const_value_expr(constant, argument.span)?,
        ));
    } else {
        ty(evaluator, argument)?;
    }
    Ok(())
}

fn function(evaluator: &mut Evaluator, function: &mut Function) -> Result<()> {
    let outer = evaluator.snapshot_values()?;
    generics(evaluator, &mut function.generics)?;
    for item in &mut function.signature_where {
        declaration(evaluator, item)?;
    }
    parameters(evaluator, &mut function.parameters)?;
    if let Some(syntax) = &mut function.return_type {
        ty(evaluator, syntax)?;
    }
    if let Some(body) = &mut function.body {
        block(evaluator, body)?;
    }
    evaluator.values = outer;
    Ok(())
}

fn declaration(evaluator: &mut Evaluator, statement: &mut Stmt) -> Result<()> {
    let outer = evaluator.snapshot_values()?;
    match &mut statement.kind {
        StmtKind::Function(value) => function(evaluator, value)?,
        StmtKind::Type(value) => {
            generics(evaluator, &mut value.generics)?;
            if let Some(syntax) = &mut value.value {
                ty(evaluator, syntax)?;
            }
            for variant in &mut value.variants {
                let parent = evaluator.snapshot_values()?;
                generics(evaluator, &mut variant.generics)?;
                if let Some(syntax) = &mut variant.payload {
                    ty(evaluator, syntax)?;
                }
                if let Some(syntax) = &mut variant.result {
                    ty(evaluator, syntax)?;
                }
                evaluator.values = parent;
            }
            evaluator
                .declarations
                .insert(value.name.clone(), value.clone());
        }
        StmtKind::Effect(value) => {
            generics(evaluator, &mut value.generics)?;
            for member in &mut value.members {
                ty(evaluator, member)?;
            }
            for operation in &mut value.operations {
                function(evaluator, operation)?;
            }
        }
        _ => {}
    }
    evaluator.values = outer;
    Ok(())
}

fn ty(evaluator: &mut Evaluator, syntax: &mut TypeExpr) -> Result<()> {
    let mut names = BTreeSet::new();
    super::super::transform::type_names(syntax, &mut names);
    if names.iter().any(|name| evaluator.values.contains_key(name)) {
        *syntax = evaluator.resolve_type(syntax, &mut vec![])?;
    }
    Ok(())
}

fn block(evaluator: &mut Evaluator, block: &mut Block) -> Result<()> {
    let saved = evaluator.snapshot_values()?;
    let saved_declarations = evaluator.declarations.clone();
    for statement in block.where_items.iter().chain(&block.statements) {
        if let StmtKind::Type(declaration) = &statement.kind {
            evaluator
                .declarations
                .insert(declaration.name.clone(), declaration.clone());
        }
    }
    // Hoisted helpers capture this block's ordinary bindings, including those
    // initialized later. Their bodies cannot substitute an outer static binder
    // for such a capture; invocation still checks its initialization normally.
    for statement in &block.statements {
        if let StmtKind::Binding(binding) = &statement.kind {
            mask(evaluator, &binding.pattern)?;
        }
    }
    for statement in block.where_items.iter_mut().chain(&mut block.statements) {
        declaration(evaluator, statement)?;
    }
    evaluator.values = evaluator.copy_values(&saved)?;
    for statement in &mut block.statements {
        match &mut statement.kind {
            StmtKind::Binding(binding) if !binding.is_meta => {
                if let Some(syntax) = &mut binding.ty {
                    ty(evaluator, syntax)?;
                }
                pattern(evaluator, &mut binding.pattern, true)?;
                expression(evaluator, &mut binding.value)?;
                if let Some(fallback) = &mut binding.fallback {
                    expression(evaluator, fallback)?;
                }
                mask(evaluator, &binding.pattern)?;
            }
            StmtKind::Expr {
                expression: value, ..
            } => expression(evaluator, value)?,
            StmtKind::Assignment { target, value, .. } => {
                // A static argument is never an assignable run-time place.
                // Leave such an illegal target to ordinary default checking.
                expression(evaluator, target)?;
                expression(evaluator, value)?;
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    expression(evaluator, &mut arm.operation)?;
                    let outer = evaluator.snapshot_values()?;
                    parameters(evaluator, &mut arm.parameters)?;
                    expression(evaluator, &mut arm.body)?;
                    evaluator.values = outer;
                }
            }
            StmtKind::HandlerApplication(value) => expression(evaluator, value)?,
            StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_) | StmtKind::Use(_) => {}
            StmtKind::Binding(_) => return Err(Failure::Unsupported(
                "a static default binding requires compile-time evaluation before specialization"
                    .into(),
            )),
        }
    }
    evaluator.values = saved;
    evaluator.declarations = saved_declarations;
    Ok(())
}

fn expression(evaluator: &mut Evaluator, value: &mut Expr) -> Result<()> {
    match &mut value.kind {
        ExprKind::Name(name) => {
            if let Some(constant) = evaluator.values.get(name).cloned() {
                *value = evaluator.const_value_expr(constant, value.span)?;
            }
        }
        ExprKind::Literal(_)
        | ExprKind::Path(_)
        | ExprKind::Accessor(_)
        | ExprKind::Ambient
        | ExprKind::Error => {}
        ExprKind::Generic { base, arguments } => {
            expression(evaluator, base)?;
            for argument in arguments {
                self::argument(evaluator, argument)?;
            }
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                expression(evaluator, item)?;
            }
        }
        ExprKind::Map(entries) => {
            for (key, value) in entries {
                expression(evaluator, key)?;
                expression(evaluator, value)?;
            }
        }
        ExprKind::Record {
            ty: syntax,
            members,
        } => {
            if let Some(syntax) = syntax {
                ty(evaluator, syntax)?;
            }

            for member in members {
                match member {
                    RecordMember::Field(field) => expression(evaluator, &mut field.value)?,
                    RecordMember::Spread(spread) => expression(evaluator, spread)?,
                }
            }
        }
        ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
            expression(evaluator, operand)?
        }
        ExprKind::Binary { left, right, .. } => {
            expression(evaluator, left)?;
            expression(evaluator, right)?;
        }
        ExprKind::Call { callee, arguments } => {
            expression(evaluator, callee)?;
            for argument in arguments {
                expression(evaluator, &mut argument.value)?;
            }
        }
        ExprKind::ComputedField { base, key }
        | ExprKind::Index {
            base, index: key, ..
        } => {
            expression(evaluator, base)?;
            expression(evaluator, key)?;
        }
        ExprKind::Lambda {
            parameters,
            return_type,
            body,
            ..
        } => {
            let saved = evaluator.snapshot_values()?;
            self::parameters(evaluator, parameters)?;
            if let Some(syntax) = return_type {
                ty(evaluator, syntax)?;
            }
            expression(evaluator, body)?;
            evaluator.values = saved;
        }
        ExprKind::Block(body) | ExprKind::Loop(body) => block(evaluator, body)?,
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression(evaluator, condition)?;
            expression(evaluator, then_branch)?;
            if let Some(other) = else_branch {
                expression(evaluator, other)?;
            }
        }
        ExprKind::IfLet {
            pattern: binder,
            value,
            then_branch,
            else_branch,
        } => {
            expression(evaluator, value)?;
            pattern(evaluator, binder, true)?;
            let saved = evaluator.snapshot_values()?;
            mask(evaluator, binder)?;
            expression(evaluator, then_branch)?;
            evaluator.values = saved;
            if let Some(other) = else_branch {
                expression(evaluator, other)?;
            }
        }
        ExprKind::While { condition, body } => {
            expression(evaluator, condition)?;
            block(evaluator, body)?;
        }
        ExprKind::WhileLet {
            pattern: binder,
            value,
            body,
        } => {
            expression(evaluator, value)?;
            pattern(evaluator, binder, true)?;
            let saved = evaluator.snapshot_values()?;
            mask(evaluator, binder)?;
            block(evaluator, body)?;
            evaluator.values = saved;
        }
        ExprKind::For {
            iterable,
            pattern,
            body,
        } => {
            expression(evaluator, iterable)?;
            let saved = evaluator.snapshot_values()?;
            self::pattern(evaluator, pattern, true)?;
            mask(evaluator, pattern)?;
            block(evaluator, body)?;
            evaluator.values = saved;
        }
        ExprKind::Control { value, .. } => {
            if let Some(value) = value {
                expression(evaluator, value)?;
            }
        }
        ExprKind::TypeValue(syntax) | ExprKind::KeyOf(syntax) => ty(evaluator, syntax)?,
        ExprKind::Derive { base, recipe } => {
            if let Some(base) = base {
                expression(evaluator, base)?;
            }
            expression(evaluator, recipe)?;
        }
        ExprKind::Range { start, end, .. } => {
            for value in start.iter_mut().chain(end) {
                expression(evaluator, value)?;
            }
        }
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation {
                    expression: value, ..
                } = part
                {
                    expression(evaluator, value)?;
                }
            }
        }
        ExprKind::Match { value, arms, .. } => {
            expression(evaluator, value)?;
            for arm in arms {
                let outer = evaluator.snapshot_values()?;
                pattern(evaluator, &mut arm.pattern, true)?;
                mask(evaluator, &arm.pattern)?;
                if let Some(guard) = &mut arm.guard {
                    expression(evaluator, guard)?;
                }
                expression(evaluator, &mut arm.body)?;
                evaluator.values = outer;
            }
        }
        ExprKind::Is {
            value,
            pattern: test,
        } => {
            expression(evaluator, value)?;
            pattern(evaluator, test, false)?;
        }
    }
    Ok(())
}
