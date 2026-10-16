//! Complete static expression schemas come from declaration syntax and explicit
//! immutable metadata. Cardinality and the erased callback Ty are never used
//! to recover fixed dimensions or invocation modes.
use super::*;
use crate::sema::model::SourceTypeWitness;
use std::sync::Arc;

pub(super) fn named_target(callee: &Expr) -> Option<(String, &[TypeExpr])> {
    match &callee.kind {
        ExprKind::Generic { base, arguments } => Some((expression_name(base)?, arguments)),
        _ => Some((expression_name(callee)?, &[])),
    }
}

impl Typer<'_> {
    pub(super) fn named_application(
        &self,
        function: &Function,
        explicit: &[TypeExpr],
        arguments: &[Argument],
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
    ) -> Result<Ty> {
        let (scope, actual) = self.named_application_scope(
            function,
            explicit,
            arguments,
            env,
            expected,
            result_context,
        )?;
        if actual.contains(&Ty::Never) {
            return Ok(Ty::Never);
        }
        let declared = function
            .return_type
            .as_ref()
            .map_or(Ok(Ty::Unit), |syntax| self.bound_type(syntax, &scope))?;
        let plan = application::StaticApplicationPlan::new(
            &function
                .parameters
                .iter()
                .map(application::ParameterSpec::from)
                .collect::<Vec<_>>(),
            arguments.iter().map(|argument| argument.label.clone()),
        )?;
        if function.generics.is_empty() {
            Ok(declared)
        } else {
            self.application_return_interface(function, &scope, &actual, &plan, &declared)
        }
    }

    fn named_application_scope(
        &self,
        function: &Function,
        explicit: &[TypeExpr],
        arguments: &[Argument],
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
    ) -> Result<(bounds::BoundEnvironment, Vec<Ty>)> {
        let instance = self
            .application_sequence
            .get()
            .checked_add(1)
            .ok_or_else(|| {
                Failure::Unsupported("static type application activation identity exhausted".into())
            })?;
        self.application_sequence.set(instance);
        self.named_application_scope_at(
            function,
            explicit,
            arguments,
            env,
            applications::ExpectedResult {
                ordinary: expected,
                source: result_context,
            },
            instance,
        )
    }
    pub(super) fn named_application_scope_at(
        &self,
        function: &Function,
        explicit: &[TypeExpr],
        arguments: &[Argument],
        env: &mut Env,
        expected: applications::ExpectedResult<'_>,
        instance: u64,
    ) -> Result<(bounds::BoundEnvironment, Vec<Ty>)> {
        let applications::ExpectedResult {
            ordinary: expected,
            source: result_context,
        } = expected;
        if arguments
            .iter()
            .any(|argument| argument.mode != ParameterMode::Read)
            || function
                .parameters
                .iter()
                .any(|parameter| parameter.mode != ParameterMode::Read)
        {
            return Err(Failure::Diagnostic(
                "E0810",
                "static call cannot acquire ordinary write authority".into(),
            ));
        }
        if !function.is_meta && !self.unevaluated {
            return Err(Failure::Diagnostic(
                "E0810",
                "ordinary callable used in static family".into(),
            ));
        }
        let captured = self
            .function_contexts
            .get(&function.name)
            .cloned()
            .unwrap_or_else(|| bounds::BoundEnvironment::captured(self.globals()));
        let mut caller = self
            .bound_environment
            .as_deref()
            .cloned()
            .unwrap_or_else(|| bounds::BoundEnvironment::captured(env.clone()));
        caller.values = env.clone();
        self.apply_const_shadows(&mut caller)?;
        let mut formal_scope = self.function_generic_environment(function, &captured)?;
        for (parameter, syntax) in function.generics.iter().zip(explicit) {
            if formal_scope
                .const_binders
                .get(&parameter.name)
                .is_some_and(Option::is_some)
            {
                self.select_const_argument(&parameter.name, syntax, &caller, &mut formal_scope)?;
                continue;
            }
            let id = formal_scope.type_binders[&parameter.name].clone();
            let actual = self.bound_type(syntax, &caller)?;
            let schema = self.complete_source_syntax(syntax, &caller)?;
            self.select_type_argument(&id, &actual, schema, &caller, &mut formal_scope)?;
        }
        let descriptors = function
            .parameters
            .iter()
            .map(application::ParameterSpec::from)
            .collect::<Vec<_>>();
        let plan = application::StaticApplicationPlan::new(
            &descriptors,
            arguments.iter().map(|argument| argument.label.clone()),
        )?;
        let mut actual_types = Vec::with_capacity(arguments.len());
        let mut actual_schemas = Vec::with_capacity(arguments.len());
        let generic_result = function
            .return_type
            .as_ref()
            .map(|syntax| self.bound_type(syntax, &formal_scope))
            .transpose()?
            .is_some_and(|ty| contains_generic_type(&ty));
        if generic_result
            && expected.is_some_and(|ty| numeric_type(ty).is_some())
            && arguments
                .iter()
                .any(|argument| self.rigid_numeric_peer(&argument.value, env).is_none())
        {
            return Err(Failure::Unsupported(
                "static generic result context requires complete numeric application preparation"
                    .into(),
            ));
        }
        for (index, argument) in arguments.iter().enumerate() {
            let formal = plan
                .slots
                .iter()
                .position(|slot| *slot == application::ArgumentSlot::Explicit(index))
                .and_then(|index| function.parameters[index].ty.as_ref());
            let context = formal
                .map(|syntax| {
                    let ordinary = self.bound_type(syntax, &formal_scope)?;
                    self.application_argument_context(syntax, ordinary, &formal_scope)
                })
                .transpose()?;
            let source_context = formal
                .map(|syntax| self.result_context(syntax, &formal_scope))
                .transpose()?;
            let actual = self.expr_result_expected(
                &argument.value,
                env,
                context.as_ref(),
                source_context.as_ref(),
            )?;
            let mut schema = self.expression_source_schema_expected(
                &argument.value,
                &actual,
                env,
                &caller,
                source_context.as_ref(),
                0,
            )?;
            // A literal is received in its declared formal construction
            // context. An existing dynamic variable never takes this path.
            if matches!(argument.value.kind, ExprKind::Array(_))
                && let Some(TypeExpr {
                    kind:
                        TypeKind::Array {
                            length: Some(length),
                            ..
                        },
                    ..
                }) = formal
                && let Some(actual_schema) = &schema
                && let TypeKind::Array { element, .. } = &actual_schema.syntax.kind
            {
                let contextual = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: argument.value.span,
                    kind: TypeKind::Array {
                        element: element.clone(),
                        length: Some(length.clone()),
                    },
                };
                schema = self.complete_source_syntax(&contextual, &formal_scope)?;
            }
            actual_types.push(actual);
            actual_schemas.push(schema);
        }
        let scope = self.check_function_application(
            function,
            applications::TypeApplication {
                actual_types: &actual_types,
                actual_schemas: &actual_schemas,
                plan: &plan,
                captured: &captured,
                caller: &caller,
                explicit,
                expected: result_context,
                instance,
            },
        )?;
        Ok((scope, actual_types))
    }

    pub(super) fn expression_source_schema(
        &self,
        expression: &Expr,
        actual: &Ty,
        env: &Env,
        scope: &bounds::BoundEnvironment,
        depth: usize,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        self.expression_source_schema_expected(expression, actual, env, scope, None, depth)
    }
    pub(super) fn expression_source_schema_expected(
        &self,
        expression: &Expr,
        actual: &Ty,
        env: &Env,
        scope: &bounds::BoundEnvironment,
        result_context: Option<&applications::ResultContext>,
        depth: usize,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        self.schema_work.work(1)?;
        if depth >= 64 {
            return Err(Failure::Unsupported(
                "static expression schema traversal allowance".into(),
            ));
        }
        if let Some(name) = expression_name(expression) {
            if let Some(witness) = self.schema_bindings.borrow().get(&name) {
                return Ok(witness.clone());
            }
            if let Some(value) = self.evaluator.global_values.get(&name) {
                if let Some(witness) = source_types::view(value) {
                    return Ok(Some(witness.clone()));
                }
                if let StaticValue::Result(produced) = value
                    && let Some(syntax) = &produced.ty
                {
                    return self.complete_source_syntax(syntax, scope);
                }
            }
            if let Some(function) = self.evaluator.functions.get(&name) {
                clone_work::function(&self.schema_work, function)?;
                let mut parameters = function.parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                return self.complete_source_syntax(
                    &TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        span: expression.span,
                        kind: TypeKind::Callable {
                            parameters,
                            result: function.return_type.clone().map(Box::new),
                            annotations: function.annotations.clone(),
                        },
                    },
                    scope,
                );
            }
        }
        let syntax = match &expression.kind {
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => {
                if let Some(schema) = self.coalescing_source_schema_expected(
                    coalescing::CoalescingOperands { left, right },
                    actual,
                    env,
                    scope,
                    result_context,
                    depth,
                )? {
                    return Ok(Some(schema));
                }
                return applications::lossless_syntax(actual, expression.span)
                    .map(|syntax| self.complete_source_syntax(&syntax, scope))
                    .transpose()
                    .map(Option::flatten);
            }
            ExprKind::Record {
                ty: Some(syntax), ..
            } => return self.complete_source_syntax(syntax, scope),
            ExprKind::Record { members, .. } => {
                let mut fields = BTreeMap::new();
                let explicit = members
                    .iter()
                    .filter_map(|member| match member {
                        RecordMember::Field(field) => Some(field.name.as_str()),
                        _ => None,
                    })
                    .collect::<BTreeSet<_>>();
                for member in members {
                    match member {
                        RecordMember::Field(field) => {
                            let Ty::Record(actual_fields) = actual else {
                                return Ok(None);
                            };
                            let Some((mutable, ty)) = actual_fields.get(&field.name) else {
                                return Ok(None);
                            };
                            let context = self.child_result_context(
                                result_context,
                                applications::ResultProjection::Record(field.name.clone()),
                            )?;
                            let Some(schema) = self.expression_source_schema_expected(
                                &field.value,
                                ty,
                                env,
                                scope,
                                context.as_ref(),
                                depth + 1,
                            )?
                            else {
                                return Ok(None);
                            };
                            fields.insert(
                                field.name.clone(),
                                TypeField {
                                    name: field.name.clone(),
                                    mutable: *mutable,
                                    ty: schema.syntax.clone(),
                                    span: field.span,
                                },
                            );
                        }
                        RecordMember::Spread(value) => {
                            let ty = self.expr(value, &mut env.clone())?;
                            let Some(schema) =
                                self.expression_source_schema(value, &ty, env, scope, depth + 1)?
                            else {
                                return Ok(None);
                            };
                            let TypeKind::Record {
                                fields: extra,
                                row: None,
                            } = &schema.syntax.kind
                            else {
                                return Ok(None);
                            };
                            for field in extra {
                                if !explicit.contains(field.name.as_str()) {
                                    let mut field = field.clone();
                                    if let Ty::Record(actual) = actual
                                        && let Some((mutable, _)) = actual.get(&field.name)
                                    {
                                        field.mutable = *mutable;
                                    }
                                    fields.insert(field.name.clone(), field);
                                }
                            }
                        }
                    }
                }
                TypeKind::Record {
                    fields: fields.into_values().collect(),
                    row: None,
                }
            }
            ExprKind::Tuple(values) => {
                let mut items = Vec::new();
                let types = match actual {
                    Ty::Tuple(items) => items.as_slice(),
                    Ty::Unit if values.is_empty() => &[],
                    _ => return Ok(None),
                };
                for (index, (value, ty)) in values.iter().zip(types).enumerate() {
                    let context = self.child_result_context(
                        result_context,
                        applications::ResultProjection::Tuple(index),
                    )?;
                    let Some(schema) = self.expression_source_schema_expected(
                        value,
                        ty,
                        env,
                        scope,
                        context.as_ref(),
                        depth + 1,
                    )?
                    else {
                        return Ok(None);
                    };
                    items.push(schema.syntax.clone());
                }
                TypeKind::Tuple(items)
            }
            ExprKind::Array(values) if values.is_empty() => {
                if let Some(context) = result_context
                    && let Some(schema) = context.closed_schema()
                    && matches!(schema.syntax.kind, TypeKind::Array { .. })
                    && matches!(context.ordinary(), Ty::Array(_, None | Some(0)))
                {
                    return Ok(Some(schema.clone()));
                }
                return Ok(None);
            }
            ExprKind::Map(entries) if entries.is_empty() => {
                if let Some(context) = result_context
                    && let Some(schema) = context.closed_schema()
                    && matches!(schema.syntax.kind, TypeKind::Map { .. })
                {
                    return Ok(Some(schema.clone()));
                }
                return Ok(None);
            }
            ExprKind::Array(values) if !values.is_empty() => {
                let context = self.child_result_context(
                    result_context,
                    applications::ResultProjection::ArrayElement,
                )?;
                let Ty::Array(ty, _) = actual else {
                    return Ok(None);
                };
                let mut element: Option<Arc<SourceTypeWitness>> = None;
                for value in values {
                    let Some(schema) = self.expression_source_schema_expected(
                        value,
                        ty,
                        env,
                        scope,
                        context.as_ref(),
                        depth + 1,
                    )?
                    else {
                        return Ok(None);
                    };
                    if element.as_ref().is_some_and(|old| old.key != schema.key) {
                        return Ok(None);
                    }
                    element = Some(schema);
                }
                TypeKind::Array {
                    length: None,
                    element: Box::new(element.unwrap().syntax.clone()),
                }
            }
            ExprKind::Map(entries) if !entries.is_empty() => {
                let key_context = self
                    .child_result_context(result_context, applications::ResultProjection::MapKey)?;
                let value_context = self.child_result_context(
                    result_context,
                    applications::ResultProjection::MapValue,
                )?;
                let Ty::Map(key_type, value_type) = actual else {
                    return Ok(None);
                };
                let mut key_schema: Option<Arc<SourceTypeWitness>> = None;
                let mut value_schema: Option<Arc<SourceTypeWitness>> = None;
                for (key, value) in entries {
                    let Some(key) = self.expression_source_schema_expected(
                        key,
                        key_type,
                        env,
                        scope,
                        key_context.as_ref(),
                        depth + 1,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(value) = self.expression_source_schema_expected(
                        value,
                        value_type,
                        env,
                        scope,
                        value_context.as_ref(),
                        depth + 1,
                    )?
                    else {
                        return Ok(None);
                    };
                    if key_schema.as_ref().is_some_and(|old| old.key != key.key)
                        || value_schema
                            .as_ref()
                            .is_some_and(|old| old.key != value.key)
                    {
                        return Ok(None);
                    }
                    key_schema = Some(key);
                    value_schema = Some(value);
                }
                TypeKind::Map {
                    key: Box::new(key_schema.unwrap().syntax.clone()),
                    value: Box::new(value_schema.unwrap().syntax.clone()),
                }
            }
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let parent = self.expr(base, &mut env.clone())?;
                if let Some(schema) =
                    self.expression_source_schema(base, &parent, env, scope, depth + 1)?
                {
                    return match &schema.syntax.kind {
                        TypeKind::Record { fields, .. } => fields
                            .iter()
                            .find(|value| value.name == *field)
                            .map(|field| self.complete_source_syntax(&field.ty, scope))
                            .unwrap_or(Ok(None)),
                        TypeKind::Tuple(items) => field
                            .parse::<usize>()
                            .ok()
                            .and_then(|index| items.get(index))
                            .map(|syntax| self.complete_source_syntax(syntax, scope))
                            .unwrap_or(Ok(None)),
                        _ => Ok(None),
                    };
                }
                if let Some(view) = self.bound_view(&parent, scope)
                    && let Some(field) = view.fields.get(field)
                {
                    return self.complete_source_syntax(&field.syntax, scope);
                }
                return Ok(None);
            }
            ExprKind::Index {
                base, safe: false, ..
            } => {
                let parent = self.expr(base, &mut env.clone())?;
                let Some(schema) =
                    self.expression_source_schema(base, &parent, env, scope, depth + 1)?
                else {
                    return Ok(None);
                };
                return match &schema.syntax.kind {
                    TypeKind::Array { element, .. } => self.complete_source_syntax(element, scope),
                    TypeKind::Map { value, .. } => self.complete_source_syntax(
                        &TypeExpr {
                            hir_id: None,
                            kind: TypeKind::Optional(value.clone()),
                            text: String::new(),
                            span: expression.span,
                        },
                        scope,
                    ),
                    _ => Ok(None),
                };
            }
            ExprKind::Lambda {
                parameters,
                return_type: Some(result),
                annotations,
                ..
            } => {
                let mut parameters = parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                TypeKind::Callable {
                    parameters,
                    result: Some(Box::new(result.clone())),
                    annotations: annotations.clone(),
                }
            }
            ExprKind::Call { callee, arguments } => {
                if let Some(name) = expression_name(callee)
                    && matches!(name.as_str(), "Some" | "Prelude::Some")
                    && !self.evaluator.functions.contains_key(&name)
                    && !env.contains_key(&name)
                    && !self.evaluator.declarations.contains_key(&name)
                    && arguments.len() == 1
                    && let Ty::Optional(payload) = actual
                    && let Some(child) = self.expression_source_schema_expected(
                        &arguments[0].value,
                        payload,
                        env,
                        scope,
                        self.child_result_context(
                            result_context,
                            applications::ResultProjection::OptionalPayload,
                        )?
                        .as_ref(),
                        depth + 1,
                    )?
                {
                    return self.complete_source_syntax(
                        &TypeExpr {
                            hir_id: None,
                            text: String::new(),
                            span: expression.span,
                            kind: TypeKind::Optional(Box::new(child.syntax.clone())),
                        },
                        scope,
                    );
                }
                if let Some((name, explicit)) = named_target(callee)
                    && let Some(function) = self.evaluator.functions.get(&name)
                {
                    let (selected, _) = self.named_application_scope(
                        function,
                        explicit,
                        arguments,
                        &mut env.clone(),
                        result_context.map(|context| context.ordinary()),
                        result_context,
                    )?;
                    return function
                        .return_type
                        .as_ref()
                        .map(|syntax| self.complete_source_syntax(syntax, &selected))
                        .unwrap_or_else(|| {
                            self.complete_source_syntax(
                                &TypeExpr {
                                    hir_id: None,
                                    kind: TypeKind::Tuple(vec![]),
                                    text: String::new(),
                                    span: expression.span,
                                },
                                &selected,
                            )
                        });
                }
                return applications::lossless_syntax(actual, expression.span)
                    .map(|syntax| self.complete_source_syntax(&syntax, scope))
                    .transpose()
                    .map(Option::flatten);
            }
            _ => {
                return applications::lossless_syntax(actual, expression.span)
                    .map(|syntax| self.complete_source_syntax(&syntax, scope))
                    .transpose()
                    .map(Option::flatten);
            }
        };
        self.complete_source_syntax(
            &TypeExpr {
                hir_id: None,
                kind: syntax,
                text: String::new(),
                span: expression.span,
            },
            scope,
        )
    }

    pub(super) fn bind_source_schema(
        &self,
        pattern: &Pattern,
        schema: Option<Arc<SourceTypeWitness>>,
    ) -> Result<()> {
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.schema_bindings
                    .borrow_mut()
                    .insert(name.clone(), schema);
            }
            PatternKind::Tuple(patterns) => {
                for (index, pattern) in patterns.iter().enumerate() {
                    let child = schema
                        .as_ref()
                        .and_then(|schema| match &schema.syntax.kind {
                            TypeKind::Tuple(items) => items.get(index),
                            _ => None,
                        })
                        .map(|syntax| {
                            self.complete_source_syntax(
                                syntax,
                                &bounds::BoundEnvironment::default(),
                            )
                        })
                        .transpose()?
                        .flatten();
                    self.bind_source_schema(pattern, child)?;
                }
            }
            PatternKind::Mode { pattern, .. } => self.bind_source_schema(pattern, schema)?,
            _ => {}
        }
        Ok(())
    }
}
