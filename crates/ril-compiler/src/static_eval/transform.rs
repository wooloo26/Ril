use super::*;

impl Evaluator {
    fn with_transform_scope<T>(
        &mut self,
        action: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let environment = self.capture_environment()?;
        let visibility = self.publications.snapshot(&self.budget)?;
        let result = action(self);
        self.install_environment(environment);
        self.publications.restore(visibility);
        result
    }
    fn mask_runtime_name(&mut self, name: &str) -> Result<()> {
        self.publications.bind_name(name, &self.budget)?;
        self.values.remove(name);
        self.type_environment.mask_const(name);
        Ok(())
    }
    fn mask_runtime_pattern(&mut self, pattern: &Pattern) -> Result<()> {
        for name in publication::pattern_names(pattern, &self.budget)? {
            self.mask_runtime_name(name)?;
        }
        Ok(())
    }
    fn mask_condition(&mut self, condition: &Expr, truth: bool) -> Result<()> {
        for name in publication::condition_names(condition, truth, &self.budget)? {
            self.mask_runtime_name(name)?;
        }
        Ok(())
    }
    fn publish_static_pattern(&mut self, pattern: &Pattern) -> Result<()> {
        for name in publication::pattern_names(pattern, &self.budget)? {
            self.publications.bind_name(name, &self.budget)?;
            if let Some(id) = self.values.get(name).and_then(StaticValue::collection_id) {
                self.publications.publish(id, name, &self.budget)?;
            }
        }
        Ok(())
    }
    fn transform_child_block(
        &mut self,
        block: &mut Block,
        output: &mut Evaluation,
        symbolic: &BTreeSet<String>,
    ) -> Result<()> {
        self.with_transform_scope(|evaluator| {
            evaluator.enter_block(block)?;
            evaluator.transform_statements(&mut block.where_items, output, false, symbolic);
            evaluator.transform_statements(&mut block.statements, output, false, symbolic);
            evaluator.exit_block();
            Ok(())
        })
    }
    pub(super) fn transform_program(&mut self, output: &mut Evaluation) {
        let original = output.program.clone();
        for statement in &original.statements {
            match &statement.kind {
                StmtKind::Function(function) => {
                    self.validate_generics(&function.generics, true, output);
                    if function.is_meta {
                        if !function.annotations.is_empty() {
                            output.failure(
                                Failure::Diagnostic(
                                    "E0813",
                                    "meta functions cannot declare effect or capability rows"
                                        .into(),
                                ),
                                function.span,
                            );
                        }
                        if function.return_type.as_ref().is_some_and(type_token_type) {
                            output.failure(
                                Failure::Diagnostic(
                                    "E0812",
                                    "meta functions cannot declare a type-valued result".into(),
                                ),
                                function.span,
                            );
                        }
                    }
                }
                StmtKind::Type(declaration) => {
                    self.validate_generics(&declaration.generics, false, output);
                    if let Some(TypeExpr {
                        kind: TypeKind::TypeFunction { parameters, .. },
                        ..
                    }) = &declaration.value
                    {
                        self.validate_generics(parameters, false, output);
                    }
                }
                _ => {}
            }
        }
        phases::validate(self, &original, output);
        let mut statements = std::mem::take(&mut output.program.statements);
        self.transform_statements(&mut statements, output, true, &BTreeSet::new());
        output.program.statements = statements;
    }
    fn validate_generics(
        &mut self,
        parameters: &[GenericParameter],
        function: bool,
        output: &mut Evaluation,
    ) {
        let mut default_seen = false;
        for (index, parameter) in parameters.iter().enumerate() {
            if let Some(default) = &parameter.default {
                if function {
                    output.failure(
                        Failure::Diagnostic(
                            "E0317",
                            "function generic parameters cannot have defaults".into(),
                        ),
                        parameter.span,
                    );
                }
                default_seen = true;
                let mut references = BTreeSet::new();
                type_names(default, &mut references);
                if parameters[index..]
                    .iter()
                    .any(|later| references.contains(&later.name))
                {
                    output.failure(
                        Failure::Diagnostic(
                            "E0320",
                            "generic default references itself or a later parameter".into(),
                        ),
                        parameter.span,
                    );
                }
            } else if default_seen {
                output.failure(
                    Failure::Diagnostic("E0316", "generic defaults must be trailing".into()),
                    parameter.span,
                );
            }
        }
    }
    fn transform_statements(
        &mut self,
        statements: &mut Vec<Stmt>,
        output: &mut Evaluation,
        top: bool,
        symbolic: &BTreeSet<String>,
    ) {
        let mut remove = BTreeSet::new();
        for (index, statement) in statements.iter_mut().enumerate() {
            let result = (|| {
                match &mut statement.kind {
                    StmtKind::Binding(binding) if binding.is_meta => {
                        if let Some(ty) = &mut binding.ty {
                            *ty = self.resolve_type(ty, &mut vec![])?;
                        }
                        let value = self.evaluation_root(|evaluator| {
                            typing::verify_binding(evaluator, binding)?;
                            let initializer =
                                record_contexts::expression(&binding.value, binding.ty.as_ref());
                            let mut value = evaluator.expression_expected(
                                &initializer,
                                false,
                                binding.ty.as_ref(),
                            )?;
                            if let Some(ty) = &binding.ty {
                                evaluator.retain_constant_shape(&value, ty)?;
                                value = evaluator.ascribe_application_value(value, ty)?;
                            }
                            Ok(value)
                        })?;
                        self.bind_static_pattern(&binding.pattern, &value)?;
                        self.refresh_local_functions()?;
                        if top && let PatternKind::Name(name) = &binding.pattern.kind {
                            self.global_values
                                .insert(name.clone(), self.copy_static_value(&value)?);
                        }
                        if matches!(value, StaticValue::Type(_) | StaticValue::Callable(_)) {
                            remove.insert(index);
                        } else {
                            binding.value = if top
                                && (reference_value(&value)
                                    || matches!(value, StaticValue::Variant(..)))
                            {
                                self.materialize_graph(&value, binding.value.span)?
                            } else {
                                self.materialize(value, binding.value.span)?
                            };
                            binding.is_meta = false;
                        }
                        self.publish_static_pattern(&binding.pattern)?;
                    }
                    StmtKind::Binding(binding) => {
                        if let Some(ty) = &mut binding.ty {
                            self.transform_type(ty, symbolic)?;
                            self.constructor_context(ty, &mut binding.value);
                        }
                        self.transform_expr(&mut binding.value, output, symbolic);
                        if let Some(fallback) = &mut binding.fallback {
                            self.transform_expr(fallback, output, symbolic);
                        }
                        self.mask_runtime_pattern(&binding.pattern)?;
                    }
                    StmtKind::Type(declaration) => {
                        for variant in &declaration.variants {
                            for parameter in &variant.generics {
                                if variant.result.as_ref().is_none_or(|result| {
                                    !constructor_parameter_recoverable(
                                        result,
                                        &parameter.name,
                                        &self.declarations,
                                    )
                                }) {
                                    output.failure(Failure::Diagnostic("E0354","variant-local parameter is not rigidly recoverable from the constructor result".into()),variant.span);
                                }
                            }
                        }
                        if matches!(
                            declaration.value.as_ref().map(|value| &value.kind),
                            Some(TypeKind::TypeFunction { .. })
                        ) {
                            remove.insert(index);
                        } else {
                            let mut child = symbolic.clone();
                            child.extend(
                                declaration
                                    .generics
                                    .iter()
                                    .map(|parameter| parameter.name.clone()),
                            );
                            for parameter in &mut declaration.generics {
                                if let Some(bound) = &mut parameter.bound {
                                    self.transform_type(bound, &child)?;
                                }
                            }
                            if let Some(value) = &mut declaration.value {
                                let mut names = BTreeSet::new();
                                type_names(value, &mut names);
                                if declaration.generics.is_empty()
                                    && !declaration.nominal
                                    && !declaration.opaque
                                    && declaration.variants.is_empty()
                                    && names.is_disjoint(&child)
                                {
                                    let owner = TypeExpr {
                                        hir_id: None,
                                        kind: TypeKind::Name {
                                            path: vec![declaration.name.clone()],
                                            arguments: vec![],
                                        },
                                        text: declaration.name.clone(),
                                        span: declaration.span,
                                    };
                                    *value = self.resolve_type(&owner, &mut vec![])?;
                                } else {
                                    self.transform_type(value, &child)?;
                                }
                            }
                            for variant in &mut declaration.variants {
                                let mut child = child.clone();
                                child.extend(
                                    variant
                                        .generics
                                        .iter()
                                        .map(|parameter| parameter.name.clone()),
                                );
                                if let Some(payload) = &mut variant.payload {
                                    self.transform_type(payload, &child)?;
                                }
                                if let Some(result) = &mut variant.result {
                                    self.transform_type(result, &child)?;
                                }
                            }
                        }
                    }
                    StmtKind::Function(function) => {
                        if function.is_meta {
                            // This is declaration elaboration, before a later
                            // static call starts its own evaluation root.
                            let saved = self.capture_environment()?;
                            let signature = self.static_signature(function);
                            self.install_environment(saved);
                            let signature = signature?;
                            function.parameters = signature.parameters;
                            function.return_type = signature.result;
                            self.functions
                                .insert(function.name.clone(), function.clone());
                            if let Some(definition) = output
                                .static_definitions
                                .iter_mut()
                                .find(|definition| definition.name == function.name)
                            {
                                definition.parameters = function.parameters.clone();
                                definition.return_type = function.return_type.clone();
                            }
                            remove.insert(index);
                        } else {
                            self.with_transform_scope(|evaluator| {
                                let mut child = symbolic.clone();
                                for generic in &function.generics {
                                    child.insert(generic.name.clone());
                                    evaluator.mask_runtime_name(&generic.name)?;
                                }
                                for parameter in &mut function.parameters {
                                    if let Some(ty) = &mut parameter.ty {
                                        evaluator.transform_type(ty, &child)?;
                                    }
                                    if let Some(default) = &mut parameter.default {
                                        evaluator.transform_expr(default, output, &child);
                                    }
                                    evaluator.mask_runtime_pattern(&parameter.pattern)?;
                                }
                                if let Some(result) = &mut function.return_type {
                                    evaluator.transform_type(result, &child)?;
                                }
                                evaluator.transform_statements(
                                    &mut function.signature_where,
                                    output,
                                    false,
                                    &child,
                                );
                                if let Some(body) = &mut function.body {
                                    evaluator.transform_child_block(body, output, &child)?;
                                    if let Some(expected) = &function.return_type {
                                        evaluator.constructor_block_context(expected, body, true);
                                    }
                                }
                                Ok(())
                            })?;
                        }
                    }
                    StmtKind::Expr { expression, .. }
                    | StmtKind::HandlerApplication(expression) => {
                        self.transform_expr(expression, output, symbolic)
                    }
                    StmtKind::Assignment { target, value, .. } => {
                        self.transform_expr(target, output, symbolic);
                        self.transform_expr(value, output, symbolic);
                    }
                    StmtKind::Handler(arms) => {
                        for arm in arms {
                            self.transform_expr(&mut arm.operation, output, symbolic);
                            self.with_transform_scope(|evaluator| {
                                for parameter in &mut arm.parameters {
                                    if let Some(ty) = &mut parameter.ty {
                                        evaluator.transform_type(ty, symbolic)?;
                                    }
                                    evaluator.mask_runtime_pattern(&parameter.pattern)?;
                                }
                                evaluator.transform_expr(&mut arm.body, output, symbolic);
                                Ok(())
                            })?;
                        }
                    }
                    StmtKind::Effect(declaration) => {
                        self.validate_generics(&declaration.generics, false, output);
                        let mut child = symbolic.clone();
                        child.extend(
                            declaration
                                .generics
                                .iter()
                                .map(|parameter| parameter.name.clone()),
                        );
                        for operation in &mut declaration.operations {
                            for parameter in &mut operation.parameters {
                                if let Some(ty) = &mut parameter.ty {
                                    self.transform_type(ty, &child)?;
                                }
                            }
                            if let Some(result) = &mut operation.return_type {
                                self.transform_type(result, &child)?;
                            }
                        }
                    }
                    StmtKind::Use(_) => {}
                }
                Ok(())
            })();
            if let Err(failure) = result {
                output.failure(failure, statement.span);
            }
        }
        let mut index = 0;
        statements.retain(|_| {
            let keep = !remove.contains(&index);
            index += 1;
            keep
        });
    }
    fn bind_static_pattern(&mut self, pattern: &Pattern, value: &StaticValue) -> Result<()> {
        if self.match_pattern(pattern, value)? {
            Ok(())
        } else {
            Err(Failure::Diagnostic(
                "E0301",
                "static binding pattern mismatch".into(),
            ))
        }
    }
    fn transform_type(&mut self, ty: &mut TypeExpr, symbolic: &BTreeSet<String>) -> Result<()> {
        self.evaluation_root(|evaluator| evaluator.transform_type_within_root(ty, symbolic))
    }
    fn transform_type_within_root(
        &mut self,
        ty: &mut TypeExpr,
        symbolic: &BTreeSet<String>,
    ) -> Result<()> {
        let mut names = BTreeSet::new();
        type_names(ty, &mut names);
        if names.iter().any(|name| symbolic.contains(name)) {
            return Ok(());
        }
        match &mut ty.kind {
            TypeKind::Name { path, arguments } => {
                let full = path.join("::");
                let normalized = full.strip_prefix("Prelude::").unwrap_or(&full);
                let arity = match normalized {
                    "Option" | "Immut" | "Set" | "type" => Some(1),
                    "Result" => Some(2),
                    _ => None,
                };
                if arity.is_some_and(|arity| arguments.len() != arity) {
                    return Err(Failure::Diagnostic(
                        "E0340",
                        "generic type argument arity differs".into(),
                    ));
                }
                let computed = self
                    .declarations
                    .get(&path.join("::"))
                    .is_some_and(|declaration| {
                        !declaration.generics.is_empty()
                            || matches!(
                                declaration.value.as_ref().map(|value| &value.kind),
                                Some(
                                    TypeKind::TypeFunction { .. }
                                        | TypeKind::Mapped { .. }
                                        | TypeKind::Projection { .. }
                                        | TypeKind::ComputedProjection { .. }
                                )
                            )
                    })
                    || matches!(
                        path.join("::").as_str(),
                        "Array::Elem" | "Map::Key" | "Map::Value" | "Set::Elem"
                    );
                if computed {
                    *ty = self.resolve_type(ty, &mut Vec::new())?;
                } else {
                    for argument in arguments {
                        self.transform_type(argument, symbolic)?;
                    }
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.transform_type(&mut field.ty, symbolic)?;
                }
                if let Some(row) = row {
                    self.transform_type(row, symbolic)?;
                }
            }
            TypeKind::Tuple(items) => {
                for item in items {
                    self.transform_type(item, symbolic)?;
                }
            }
            TypeKind::Optional(inner) | TypeKind::Rest(inner) => {
                self.transform_type(inner, symbolic)?
            }
            TypeKind::Array { length, element } => {
                if let Some(length) = length {
                    let value = self.expression(length)?;
                    let StaticValue::Integer(value) = value else {
                        return Err(Failure::Diagnostic(
                            "E0323",
                            "fixed array length requires int".into(),
                        ));
                    };
                    if value < 0 {
                        return Err(Failure::Diagnostic(
                            "E0815",
                            "fixed array length cannot be negative".into(),
                        ));
                    }
                    **length = self.materialize(StaticValue::Integer(value), length.span)?;
                }
                self.transform_type(element, symbolic)?;
            }
            TypeKind::Map { key, value } => {
                self.transform_type(key, symbolic)?;
                self.transform_type(value, symbolic)?;
            }
            TypeKind::Callable {
                parameters, result, ..
            } => {
                for parameter in parameters {
                    if let Some(ty) = &mut parameter.ty {
                        self.transform_type(ty, symbolic)?;
                    }
                }
                if let Some(result) = result {
                    self.transform_type(result, symbolic)?;
                }
            }
            TypeKind::Mapped { .. }
            | TypeKind::Projection { .. }
            | TypeKind::ComputedProjection { .. } => {
                *ty = self.resolve_type(ty, &mut Vec::new())?
            }
            TypeKind::Computation(expression) if matches!(&expression.kind,ExprKind::Unary { operator,.. } if operator == "typeof") =>
            {
                let ExprKind::Unary { operand, .. } = &expression.kind else {
                    unreachable!()
                };
                // Runtime local names are handled in their lexical semantic
                // environment. Static failure cannot make them ambient values.
                if let Ok(inferred) = typing::type_of(self, operand) {
                    *ty = inferred;
                }
            }
            TypeKind::Computation(_) => {
                return Err(Failure::Diagnostic(
                    "E0318",
                    "a concrete value is not a bare type".into(),
                ));
            }
            _ => {}
        }
        Ok(())
    }
    /// Expected types supply arguments only after ordinary lexical selection
    /// has already identified the same declaration. They never select an
    /// abbreviated variant from a different declaration's candidate set.
    fn constructor_context(&self, expected: &TypeExpr, value: &mut Expr) {
        match &mut value.kind {
            ExprKind::Block(block) => {
                self.constructor_block_context(expected, block, true);
                return;
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            }
            | ExprKind::IfLet {
                then_branch,
                else_branch,
                ..
            } => {
                self.constructor_context(expected, then_branch);
                if let Some(other) = else_branch {
                    self.constructor_context(expected, other);
                }
                return;
            }
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.constructor_context(expected, &mut arm.body);
                }
                return;
            }
            ExprKind::Control {
                operation: ControlOperation::Return,
                value: Some(value),
            } => {
                self.constructor_context(expected, value);
                return;
            }
            ExprKind::Lambda { body, .. } => {
                if let TypeKind::Callable {
                    result: Some(result),
                    ..
                } = &expected.kind
                {
                    self.constructor_context(result, body);
                }
                return;
            }
            _ => {}
        }
        let TypeKind::Name { path, arguments } = &expected.kind else {
            return;
        };
        let owner = path.join("::");
        let Some(declaration) = self.declarations.get(&owner) else {
            return;
        };
        if declaration.generics.is_empty() || arguments.len() != declaration.generics.len() {
            return;
        }
        let selected = match &mut value.kind {
            ExprKind::Call { callee, .. } => &mut **callee,
            ExprKind::Name(_) | ExprKind::Path(_) => value,
            _ => return,
        };
        let Some(name) = expression_name(selected) else {
            return;
        };
        let same = declaration.nominal && name == owner
            || declaration
                .variants
                .iter()
                .any(|variant| name == format!("{owner}::{}", variant.name));
        if same && !matches!(selected.kind, ExprKind::Generic { .. }) {
            *selected = Expr {
                hir_id: None,
                kind: ExprKind::Generic {
                    base: Box::new(selected.clone()),
                    arguments: arguments.clone(),
                },
                span: selected.span,
            };
        }
    }
    fn constructor_block_context(
        &self,
        expected: &TypeExpr,
        block: &mut Block,
        tail_expected: bool,
    ) {
        if tail_expected
            && let Some(Stmt {
                kind:
                    StmtKind::Expr {
                        expression,
                        terminated: false,
                    },
                ..
            }) = block.statements.last_mut()
        {
            self.constructor_context(expected, expression);
        }
        for statement in &mut block.statements {
            if let StmtKind::Expr { expression, .. } = &mut statement.kind {
                match &mut expression.kind {
                    ExprKind::Control {
                        operation: ControlOperation::Return,
                        value: Some(value),
                    } => self.constructor_context(expected, value),
                    ExprKind::Block(block) => {
                        self.constructor_block_context(expected, block, false)
                    }
                    ExprKind::If {
                        then_branch,
                        else_branch,
                        ..
                    }
                    | ExprKind::IfLet {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        if let ExprKind::Block(block) = &mut then_branch.kind {
                            self.constructor_block_context(expected, block, false);
                        }
                        if let Some(other) = else_branch
                            && let ExprKind::Block(block) = &mut other.kind
                        {
                            self.constructor_block_context(expected, block, false);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    fn transform_test(
        &mut self,
        pattern: &mut Pattern,
        output: &mut Evaluation,
        symbolic: &BTreeSet<String>,
    ) -> Result<()> {
        match &mut pattern.kind {
            PatternKind::Value(value) => self.transform_expr(value, output, symbolic),
            PatternKind::Tuple(patterns)
            | PatternKind::Array(patterns)
            | PatternKind::Alternative(patterns)
            | PatternKind::Constructor {
                arguments: patterns,
                ..
            } => {
                for pattern in patterns {
                    self.transform_test(pattern, output, symbolic)?;
                }
            }
            PatternKind::Record { ty, fields, .. } => {
                if let Some(ty) = ty {
                    self.transform_type(ty, symbolic)?;
                }
                for field in fields {
                    self.transform_test(&mut field.pattern, output, symbolic)?;
                }
            }
            PatternKind::Type { ty, .. } => self.transform_type(ty, symbolic)?,
            _ => {}
        }
        Ok(())
    }
    fn transform_expr(
        &mut self,
        expression: &mut Expr,
        output: &mut Evaluation,
        symbolic: &BTreeSet<String>,
    ) {
        let result = (|| {
            match &mut expression.kind {
                ExprKind::Accessor(path) => {
                    expression.kind = accessor_lambda(path, expression.span).kind;
                }
                ExprKind::TypeValue(ty) => self.transform_type(ty, symbolic)?,
                ExprKind::KeyOf(ty) => {
                    let mut names = BTreeSet::new();
                    type_names(ty, &mut names);
                    if names.iter().all(|name| !symbolic.contains(name)) {
                        let value = self.keyof(ty)?;
                        *expression = self.materialize(value, expression.span)?;
                    }
                }
                ExprKind::Generic { base, arguments } => {
                    self.transform_expr(base, output, symbolic);
                    let owner = expression_name(base).and_then(|name| {
                        self.declarations
                            .get(&name)
                            .filter(|declaration| declaration.nominal)
                            .or_else(|| {
                                name.rsplit_once("::").and_then(|(owner, variant)| {
                                    self.declarations.get(owner).filter(|declaration| {
                                        declaration
                                            .variants
                                            .iter()
                                            .any(|member| member.name == variant)
                                    })
                                })
                            })
                            .map(|declaration| declaration.name.clone())
                    });
                    if let Some(owner) = owner {
                        let ty = TypeExpr {
                            hir_id: None,
                            text: String::new(),
                            kind: TypeKind::Name {
                                path: vec![owner],
                                arguments: arguments.clone(),
                            },
                            span: expression.span,
                        };
                        let mut names = BTreeSet::new();
                        type_names(&ty, &mut names);
                        for argument in arguments.iter() {
                            if let TypeKind::Computation(value) = &argument.kind
                                && let ExprKind::Name(name) = &value.kind
                            {
                                names.insert(name.clone());
                            }
                        }
                        if names.is_disjoint(symbolic) {
                            let normalized = self.resolve_type(&ty, &mut vec![])?;
                            if let TypeKind::Name {
                                arguments: normalized,
                                ..
                            } = normalized.kind
                            {
                                *arguments = normalized;
                            }
                        }
                    } else if let Some(effect) = expression_name(base)
                        .and_then(|name| self.effect_declarations.get(&name).cloned())
                    {
                        for (argument, parameter) in arguments.iter_mut().zip(&effect.generics) {
                            let mut names = BTreeSet::new();
                            type_names(argument, &mut names);
                            if !names.is_disjoint(symbolic) {
                                continue;
                            }
                            if parameter
                                .name
                                .chars()
                                .next()
                                .is_some_and(char::is_lowercase)
                                || matches!(
                                    parameter.bound.as_ref().map(|bound| &bound.kind),
                                    Some(TypeKind::KeyOf(_))
                                )
                            {
                                let value = self.value_argument(argument)?;
                                argument.kind = TypeKind::Computation(Box::new(
                                    self.const_value_expr(value, argument.span)?,
                                ));
                            } else {
                                self.transform_type(argument, symbolic)?;
                            }
                        }
                    } else if let Some(function) = expression_name(base).and_then(|name| {
                        self.functions
                            .get(&name)
                            .filter(|function| function.body.is_none())
                            .cloned()
                    }) {
                        let mut names = BTreeSet::new();
                        for argument in arguments.iter() {
                            type_names(argument, &mut names);
                            if let TypeKind::Computation(value) = &argument.kind {
                                value_names(value, &mut names);
                            }
                        }
                        if names.is_disjoint(symbolic) {
                            let saved = self.capture_environment()?;
                            let normalized = self.bind_type_arguments(
                                &function.generics,
                                arguments,
                                &function.name,
                            );
                            self.install_environment(saved);
                            *arguments = normalized?;
                        }
                    } else {
                        for argument in arguments {
                            self.transform_type(argument, symbolic)?;
                        }
                    }
                }
                ExprKind::Block(block) | ExprKind::Loop(block) => {
                    self.transform_child_block(block, output, symbolic)?;
                }
                ExprKind::Lambda {
                    parameters,
                    return_type,
                    body,
                    ..
                } => {
                    self.with_transform_scope(|evaluator| {
                        for parameter in parameters {
                            if let Some(ty) = &mut parameter.ty {
                                evaluator.transform_type(ty, symbolic)?;
                            }
                            if let Some(default) = &mut parameter.default {
                                evaluator.transform_expr(default, output, symbolic);
                            }
                            evaluator.mask_runtime_pattern(&parameter.pattern)?;
                        }
                        if let Some(result) = return_type {
                            evaluator.transform_type(result, symbolic)?;
                        }
                        evaluator.transform_expr(body, output, symbolic);
                        Ok(())
                    })?;
                }
                ExprKind::Call { callee, arguments } => {
                    self.transform_expr(callee, output, symbolic);
                    for argument in arguments {
                        self.transform_expr(&mut argument.value, output, symbolic);
                    }
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    self.transform_expr(condition, output, symbolic);
                    self.with_transform_scope(|evaluator| {
                        evaluator.mask_condition(condition, true)?;
                        evaluator.transform_expr(then_branch, output, symbolic);
                        Ok(())
                    })?;
                    if let Some(branch) = else_branch {
                        self.with_transform_scope(|evaluator| {
                            evaluator.mask_condition(condition, false)?;
                            evaluator.transform_expr(branch, output, symbolic);
                            Ok(())
                        })?;
                    }
                }
                ExprKind::IfLet {
                    pattern,
                    value,
                    then_branch,
                    else_branch,
                } => {
                    self.transform_expr(value, output, symbolic);
                    self.transform_test(pattern, output, symbolic)?;
                    self.with_transform_scope(|evaluator| {
                        evaluator.mask_runtime_pattern(pattern)?;
                        evaluator.transform_expr(then_branch, output, symbolic);
                        Ok(())
                    })?;
                    if let Some(branch) = else_branch {
                        self.transform_expr(branch, output, symbolic);
                    }
                }
                ExprKind::Match { value, arms, .. } => {
                    self.transform_expr(value, output, symbolic);
                    for arm in arms {
                        self.transform_test(&mut arm.pattern, output, symbolic)?;
                        self.with_transform_scope(|evaluator| {
                            evaluator.mask_runtime_pattern(&arm.pattern)?;
                            if let Some(guard) = &mut arm.guard {
                                evaluator.transform_expr(guard, output, symbolic);
                            }
                            evaluator.transform_expr(&mut arm.body, output, symbolic);
                            Ok(())
                        })?;
                    }
                }
                ExprKind::Unary { operand, .. } => self.transform_expr(operand, output, symbolic),
                ExprKind::Binary {
                    operator,
                    left,
                    right,
                } => {
                    self.transform_expr(left, output, symbolic);
                    if operator == "&&" || operator == "||" {
                        self.with_transform_scope(|evaluator| {
                            evaluator.mask_condition(left, operator == "&&")?;
                            evaluator.transform_expr(right, output, symbolic);
                            Ok(())
                        })?;
                    } else {
                        self.transform_expr(right, output, symbolic);
                    }
                }
                ExprKind::Tuple(items) | ExprKind::Array(items) => {
                    for item in items {
                        self.transform_expr(item, output, symbolic);
                    }
                }
                ExprKind::Map(entries) => {
                    for (key, value) in entries {
                        self.transform_expr(key, output, symbolic);
                        self.transform_expr(value, output, symbolic);
                    }
                }
                ExprKind::Record { ty, members } => {
                    if let Some(ty) = ty {
                        self.transform_type(ty, symbolic)?;
                    }

                    for member in members {
                        match member {
                            RecordMember::Field(field) => {
                                self.transform_expr(&mut field.value, output, symbolic)
                            }
                            RecordMember::Spread(value) => {
                                self.transform_expr(value, output, symbolic)
                            }
                        }
                    }
                }
                ExprKind::Field { base, .. } => self.transform_expr(base, output, symbolic),
                ExprKind::ComputedField { base, key } => {
                    self.transform_expr(base, output, symbolic);
                    self.transform_expr(key, output, symbolic);
                    if let ExprKind::Name(name) = &key.kind
                        && !symbolic.contains(name)
                        && let Some(
                            value @ (StaticValue::String(_)
                            | StaticValue::Integer(_)
                            | StaticValue::TypedInteger(..)),
                        ) = self.values.get(name).cloned()
                    {
                        **key = self.materialize(value, key.span)?;
                    }
                }
                ExprKind::Index { base, index, .. } => {
                    self.transform_expr(base, output, symbolic);
                    self.transform_expr(index, output, symbolic);
                }
                ExprKind::Interpolated(parts) => {
                    for part in parts {
                        if let StringPart::Interpolation { expression, .. } = part {
                            self.transform_expr(expression, output, symbolic);
                        }
                    }
                }
                ExprKind::Control {
                    value: Some(value), ..
                } => self.transform_expr(value, output, symbolic),
                ExprKind::Is { value, pattern } => {
                    self.transform_expr(value, output, symbolic);
                    self.transform_test(pattern, output, symbolic)?;
                }
                ExprKind::While { condition, body } => {
                    self.transform_expr(condition, output, symbolic);
                    self.with_transform_scope(|evaluator| {
                        evaluator.mask_condition(condition, true)?;
                        evaluator.transform_child_block(body, output, symbolic)
                    })?;
                }
                ExprKind::WhileLet {
                    pattern,
                    value,
                    body,
                } => {
                    self.transform_expr(value, output, symbolic);
                    self.transform_test(pattern, output, symbolic)?;
                    self.with_transform_scope(|evaluator| {
                        evaluator.mask_runtime_pattern(pattern)?;
                        evaluator.transform_child_block(body, output, symbolic)
                    })?;
                }
                ExprKind::For {
                    iterable,
                    pattern,
                    body,
                } => {
                    self.transform_expr(iterable, output, symbolic);
                    self.transform_test(pattern, output, symbolic)?;
                    self.with_transform_scope(|evaluator| {
                        evaluator.mask_runtime_pattern(pattern)?;
                        evaluator.transform_child_block(body, output, symbolic)
                    })?;
                }
                ExprKind::Range { start, end, .. } => {
                    if let Some(start) = start {
                        self.transform_expr(start, output, symbolic);
                    }
                    if let Some(end) = end {
                        self.transform_expr(end, output, symbolic);
                    }
                }
                _ => {}
            }
            Ok(())
        })();
        if let Err(failure) = result {
            output.failure(failure, expression.span);
        }
    }
}
fn type_token_type(ty: &TypeExpr) -> bool {
    matches!(&ty.kind,TypeKind::Name{path,..}if path==&["type"])
}
pub(super) fn accessor_lambda(path: &[AccessorSegment], span: Span) -> Expr {
    let name = format!("ril__accessor_{}_{}_{}", span.file.0, span.start, span.end);
    let origin = Span {
        file: span.file,
        start: span.start + 1,
        end: span.start + 1,
    };
    let mut projected = Expr {
        hir_id: None,
        kind: ExprKind::Name(name.clone()),
        span: origin,
    };
    for segment in path {
        projected = Expr {
            hir_id: None,
            kind: ExprKind::Field {
                base: Box::new(projected),
                field: segment.field.clone(),
                safe: segment.safe,
            },
            span: Span {
                file: span.file,
                start: origin.start,
                end: segment.span.end,
            },
        };
    }
    Expr {
        hir_id: None,
        kind: ExprKind::Lambda {
            parameters: vec![Parameter {
                pattern: Pattern {
                    hir_id: None,
                    kind: PatternKind::Name(name),
                    span: origin,
                },
                mode: ParameterMode::Read,
                ty: None,
                default: None,
                span: origin,
            }],
            return_type: None,
            annotations: vec![],
            body: Box::new(projected),
        },
        span,
    }
}
pub(super) fn type_names(ty: &TypeExpr, names: &mut BTreeSet<String>) {
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            if path.len() == 1 {
                names.insert(path[0].clone());
            }
            for argument in arguments {
                type_names(argument, names);
            }
        }
        TypeKind::Optional(inner) | TypeKind::KeyOf(inner) | TypeKind::Rest(inner) => {
            type_names(inner, names)
        }
        TypeKind::Array { element, length } => {
            type_names(element, names);
            if let Some(length) = length {
                value_names(length, names);
            }
        }
        TypeKind::Map { key, value } => {
            type_names(key, names);
            type_names(value, names);
        }
        TypeKind::Tuple(items) => {
            for item in items {
                type_names(item, names);
            }
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                type_names(&field.ty, names);
            }
            if let Some(row) = row {
                type_names(row, names);
            }
        }
        TypeKind::Projection { base, .. } => type_names(base, names),
        TypeKind::ComputedProjection { base, key } => {
            type_names(base, names);
            value_names(key, names);
        }
        TypeKind::Computation(value) => value_names(value, names),
        TypeKind::Mapped { keys, value, .. } => {
            value_names(keys, names);
            type_names(value, names);
        }
        TypeKind::KindArrow { parameter, result } => {
            type_names(parameter, names);
            type_names(result, names);
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                if let Some(ty) = &parameter.ty {
                    type_names(ty, names);
                }
            }
            if let Some(result) = result {
                type_names(result, names);
            }
        }
        _ => {}
    }
}

fn test_names(pattern: &Pattern, names: &mut BTreeSet<String>) {
    match &pattern.kind {
        PatternKind::Value(value) => value_names(value, names),
        PatternKind::Tuple(patterns)
        | PatternKind::Array(patterns)
        | PatternKind::Alternative(patterns)
        | PatternKind::Constructor {
            arguments: patterns,
            ..
        } => {
            for pattern in patterns {
                test_names(pattern, names);
            }
        }
        PatternKind::Record { ty, fields, .. } => {
            if let Some(ty) = ty {
                type_names(ty, names);
            }
            for field in fields {
                test_names(&field.pattern, names);
            }
        }
        PatternKind::Type { ty, .. } => type_names(ty, names),
        _ => {}
    }
}
fn value_names(value: &Expr, names: &mut BTreeSet<String>) {
    let block = |block: &Block, names: &mut BTreeSet<String>| {
        for statement in block.where_items.iter().chain(&block.statements) {
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    value_names(&binding.value, names);
                    if let Some(ty) = &binding.ty {
                        type_names(ty, names);
                    }
                    if let Some(fallback) = &binding.fallback {
                        value_names(fallback, names);
                    }
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    value_names(expression, names)
                }
                StmtKind::Assignment { target, value, .. } => {
                    value_names(target, names);
                    value_names(value, names);
                }
                _ => {}
            }
        }
    };
    match &value.kind {
        ExprKind::Name(name) => {
            names.insert(name.clone());
        }
        ExprKind::Path(path) => {
            if let Some(name) = path.first() {
                names.insert(name.clone());
            }
        }
        ExprKind::Generic { base, arguments } => {
            value_names(base, names);
            for argument in arguments {
                type_names(argument, names);
            }
        }
        ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
            value_names(operand, names)
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
            value_names(left, names);
            value_names(right, names);
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                value_names(item, names);
            }
        }
        ExprKind::Map(entries) => {
            for (key, value) in entries {
                value_names(key, names);
                value_names(value, names);
            }
        }
        ExprKind::Record { ty, members, .. } => {
            if let Some(ty) = ty {
                type_names(ty, names);
            }
            for member in members {
                match member {
                    RecordMember::Field(field) => value_names(&field.value, names),
                    RecordMember::Spread(value) => value_names(value, names),
                }
            }
        }
        ExprKind::Call { callee, arguments } => {
            value_names(callee, names);
            for argument in arguments {
                value_names(&argument.value, names);
            }
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            value_names(condition, names);
            value_names(then_branch, names);
            if let Some(value) = else_branch {
                value_names(value, names);
            }
        }
        ExprKind::IfLet {
            pattern,
            value,
            then_branch,
            else_branch,
        } => {
            value_names(value, names);
            test_names(pattern, names);
            value_names(then_branch, names);
            if let Some(branch) = else_branch {
                value_names(branch, names);
            }
        }
        ExprKind::Match { value, arms, .. } => {
            value_names(value, names);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    value_names(guard, names);
                }
                value_names(&arm.body, names);
            }
        }
        ExprKind::Is { value, pattern } => {
            value_names(value, names);
            test_names(pattern, names);
        }
        ExprKind::Block(value) | ExprKind::Loop(value) => block(value, names),
        ExprKind::While { condition, body } => {
            value_names(condition, names);
            block(body, names);
        }
        ExprKind::WhileLet {
            pattern,
            value,
            body,
        } => {
            value_names(value, names);
            test_names(pattern, names);
            block(body, names);
        }
        ExprKind::For { iterable, body, .. } => {
            value_names(iterable, names);
            block(body, names);
        }
        ExprKind::Lambda {
            parameters,
            return_type,
            body,
            ..
        } => {
            for parameter in parameters {
                if let Some(ty) = &parameter.ty {
                    type_names(ty, names);
                }
            }
            if let Some(ty) = return_type {
                type_names(ty, names);
            }
            value_names(body, names);
        }
        ExprKind::Control {
            value: Some(value), ..
        } => value_names(value, names),
        ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => type_names(ty, names),
        ExprKind::Derive { base, recipe } => {
            if let Some(base) = base {
                value_names(base, names);
            }
            value_names(recipe, names);
        }
        ExprKind::Range { start, end, .. } => {
            for value in start.iter().chain(end) {
                value_names(value, names);
            }
        }
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation { expression, .. } = part {
                    value_names(expression, names);
                }
            }
        }
        _ => {}
    }
}
