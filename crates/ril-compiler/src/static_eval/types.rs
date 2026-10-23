use super::*;

#[path = "named_type_selections.rs"]
mod named_type_selections;

/// A transparent alias denotes an evaluated type, not an instruction to repeat
/// its defining computation whenever metadata traverses that type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct TypeInstanceKey {
    declaration: String,
    environment: Option<environments::EnvironmentId>,
    arguments: Vec<String>,
}

impl TypeInstanceKey {
    pub(super) fn new(
        declaration: String,
        environment: Option<environments::EnvironmentId>,
        arguments: &[TypeExpr],
    ) -> Self {
        Self {
            declaration,
            environment,
            arguments: arguments.iter().map(type_key).collect(),
        }
    }
}

impl Evaluator {
    pub(super) fn resolve_type(
        &mut self,
        ty: &TypeExpr,
        seen: &mut Vec<String>,
    ) -> Result<TypeExpr> {
        self.evaluation_root(|evaluator| evaluator.resolve_type_within_root(ty, seen))
    }
    fn resolve_type_within_root(
        &mut self,
        ty: &TypeExpr,
        seen: &mut Vec<String>,
    ) -> Result<TypeExpr> {
        self.charge()?;
        if self.type_depth + self.call_depth >= 64 {
            return Err(Failure::Unsupported(
                "type evaluation exceeds the interpreter stack allowance".into(),
            ));
        }
        self.type_depth += 1;
        let result = self.resolve_type_inner(ty, seen);
        self.type_depth -= 1;
        result
    }
    fn resolve_type_inner(&mut self, ty: &TypeExpr, seen: &mut Vec<String>) -> Result<TypeExpr> {
        let kind = match &ty.kind {
            TypeKind::Name { path, arguments } => {
                let full = path.join("::");
                let name = full.strip_prefix("Prelude::").unwrap_or(&full).to_owned();
                if ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(&name).is_some()
                    && !arguments.is_empty()
                {
                    return Err(Failure::Diagnostic(
                        "E0340",
                        "intrinsic atomic type has no generic arguments".into(),
                    ));
                }
                if let Some(StaticValue::Type(value)) = self
                    .values
                    .get(&full)
                    .or_else(|| (full == name).then(|| self.values.get(&name)).flatten())
                {
                    clone_work::type_syntax(&self.budget, value)?;
                    let mut value = value.clone();
                    if arguments.is_empty() {
                        return Ok(value);
                    }
                    if let TypeKind::Name {
                        arguments: applied, ..
                    } = &mut value.kind
                        && applied.is_empty()
                    {
                        *applied = arguments.clone();
                        return self.resolve_type(&value, seen);
                    }
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "a bound data type is not a type constructor".into(),
                    ));
                }
                if matches!(
                    name.as_str(),
                    "Array::Elem" | "Map::Key" | "Map::Value" | "Set::Elem"
                ) {
                    if arguments.len() != 1 {
                        return Err(Failure::Diagnostic(
                            "E0340",
                            "type extractor requires one argument".into(),
                        ));
                    }
                    let argument = self.resolve_type(&arguments[0], seen)?;
                    self.budget.event(budget::Event::TypeFunctionEntry)?;
                    return match (name.as_str(), argument.kind) {
                        ("Array::Elem", TypeKind::Array { element, .. }) => Ok(*element),
                        ("Map::Key", TypeKind::Map { key, .. }) => Ok(*key),
                        ("Map::Value", TypeKind::Map { value, .. }) => Ok(*value),
                        (
                            "Set::Elem",
                            TypeKind::Name {
                                path,
                                mut arguments,
                            },
                        ) if normalized_path(&path) == "Set" && arguments.len() == 1 => {
                            Ok(arguments.remove(0))
                        }
                        _ => Err(Failure::Diagnostic(
                            "E0301",
                            "type extractor does not admit the supplied shape".into(),
                        )),
                    };
                }
                if let Some(declaration) = self
                    .declarations
                    .get(&full)
                    .or_else(|| {
                        (full == name)
                            .then(|| self.declarations.get(&name))
                            .flatten()
                    })
                    .cloned()
                {
                    if matches!(
                        declaration.value.as_ref().map(|value| &value.kind),
                        Some(TypeKind::TypeFunction { .. })
                    ) {
                        return self.invoke_type(ty, seen);
                    }
                    let environment = self.function_environments.get(&declaration.name).copied();
                    let saved = self.capture_environment()?;
                    let result = (|| {
                        let actual = self.bind_type_arguments(
                            &declaration.generics,
                            arguments,
                            &declaration.name,
                        )?;
                        if declaration.nominal
                            || declaration.opaque
                            || !declaration.variants.is_empty()
                        {
                            return Ok(TypeExpr {
                                hir_id: None,
                                text: ty.text.clone(),
                                kind: TypeKind::Name {
                                    path: vec![declaration.name.clone()],
                                    arguments: actual,
                                },
                                span: ty.span,
                            });
                        }
                        let Some(value) = &declaration.value else {
                            return Ok(ty.clone());
                        };
                        if seen.contains(&declaration.name) {
                            return Err(Failure::Diagnostic(
                                "E0313",
                                "unguarded structural type alias cycle".into(),
                            ));
                        }
                        let instance = TypeInstanceKey {
                            declaration: declaration.name.clone(),
                            environment,
                            arguments: actual.iter().map(type_key).collect(),
                        };
                        if let Some(resolved) = self.alias_instances.get(&instance) {
                            return Ok(resolved.clone());
                        }
                        seen.push(declaration.name.clone());
                        let result = self.resolve_type(value, seen);
                        seen.pop();
                        if let Ok(resolved) = &result {
                            self.alias_instances.insert(instance, resolved.clone());
                        }
                        result
                    })();
                    self.install_environment(saved);
                    return result;
                }
                let expected = match name.as_str() {
                    "Option" | "Immut" | "Set" | "type" => Some(1),
                    "Result" => Some(2),
                    _ => None,
                };
                if expected.is_some_and(|expected| arguments.len() != expected) {
                    return Err(Failure::Diagnostic(
                        "E0340",
                        format!("{name} has a different generic arity"),
                    ));
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        if matches!(name.as_str(), "Option" | "Result") {
                            self.resolve_guarded_type(argument, seen)
                        } else {
                            self.resolve_type(argument, seen)
                        }
                    })
                    .collect::<Result<_>>()?;
                TypeKind::Name {
                    path: if full.starts_with("Prelude::") {
                        vec!["Prelude".into(), name]
                    } else {
                        path.clone()
                    },
                    arguments,
                }
            }
            TypeKind::Optional(inner) => {
                TypeKind::Optional(Box::new(self.resolve_guarded_type(inner, seen)?))
            }
            TypeKind::Array { length, element } => {
                let length = if let Some(length) = length {
                    let value = self.expression(length)?;
                    let StaticValue::Integer(value) = value else {
                        return Err(Failure::Diagnostic(
                            "E0323",
                            "fixed length requires int".into(),
                        ));
                    };
                    if value < 0 {
                        return Err(Failure::Diagnostic(
                            "E0815",
                            "fixed array length cannot be negative".into(),
                        ));
                    }
                    Some(Box::new(
                        self.materialize(StaticValue::Integer(value), length.span)?,
                    ))
                } else {
                    None
                };
                TypeKind::Array {
                    length,
                    element: Box::new(self.resolve_type(element, seen)?),
                }
            }
            TypeKind::Map { key, value } => TypeKind::Map {
                key: Box::new(self.resolve_type(key, seen)?),
                value: Box::new(self.resolve_type(value, seen)?),
            },
            TypeKind::Tuple(items) => TypeKind::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_type(item, seen))
                    .collect::<Result<_>>()?,
            ),
            TypeKind::Record { fields, row } => {
                let mut output = vec![];
                let mut names = BTreeSet::new();
                for field in fields {
                    if !names.insert(field.name.clone()) {
                        return Err(Failure::Diagnostic(
                            "E0210",
                            "duplicate record field".into(),
                        ));
                    }
                    output.push(TypeField {
                        name: field.name.clone(),
                        mutable: field.mutable,
                        ty: self.resolve_type(&field.ty, seen)?,
                        span: field.span,
                    });
                }
                let mut remaining = None;
                if let Some(row) = row {
                    let expanded = self.resolve_type(row, seen)?;
                    if let TypeKind::Record { fields, row } = expanded.kind {
                        for field in fields {
                            if !names.insert(field.name.clone()) {
                                return Err(Failure::Diagnostic(
                                    "E0212",
                                    "explicit record field overlaps its row".into(),
                                ));
                            }
                            output.push(field);
                        }
                        // Expanding an alias can expose known fields while its
                        // remainder is still symbolic. Keep that exact tail:
                        // knowing the outer shell never proves it is empty.
                        remaining = row;
                    } else {
                        remaining = Some(Box::new(expanded));
                    }
                }
                TypeKind::Record {
                    fields: output,
                    row: remaining,
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                let mut parameters = parameters.clone();
                for parameter in &mut parameters {
                    if let Some(ty) = &parameter.ty {
                        parameter.ty = Some(self.resolve_type(ty, seen)?);
                    }
                }
                TypeKind::Callable {
                    parameters,
                    result: result
                        .as_ref()
                        .map(|result| self.resolve_type(result, seen).map(Box::new))
                        .transpose()?,
                    annotations: annotations.clone(),
                }
            }
            TypeKind::Projection { base, field } => {
                return self.project_type(base, StaticValue::String(field.clone()), ty.span, seen);
            }
            TypeKind::ComputedProjection { base, key } => {
                let key = self.expression(key)?;
                return self.project_type(base, key, ty.span, seen);
            }
            TypeKind::Mapped {
                binder,
                keys,
                value,
                tuple,
            } => {
                let keys = self.expression(keys)?;
                let Some(keys) = keys.array_items() else {
                    return Err(Failure::Diagnostic(
                        if *tuple { "E0342" } else { "E0341" },
                        "mapped keys must be a static array of the required key sort".into(),
                    ));
                };
                let saved = self.capture_environment()?;
                let result = (|| {
                    let mut fields = vec![];
                    let mut items = vec![];
                    let mut names = BTreeSet::new();
                    for key in keys {
                        let key = self.copy_static_value(key)?;
                        self.budget.event(budget::Event::LoopIteration)?;
                        self.values.insert(binder.clone(), key.clone());
                        let field = self.resolve_type(value, seen)?;
                        if *tuple {
                            if !matches!(key, StaticValue::Integer(_)) {
                                return Err(Failure::Diagnostic(
                                    "E0342",
                                    "mapped tuple requires []int".into(),
                                ));
                            }
                            items.push(field);
                        } else {
                            let StaticValue::String(name) = key else {
                                return Err(Failure::Diagnostic(
                                    "E0341",
                                    "mapped record requires []str".into(),
                                ));
                            };
                            if !valid_label(&name) {
                                return Err(Failure::Diagnostic(
                                    "E0102",
                                    "mapped field label is not an admitted identifier".into(),
                                ));
                            }
                            if !names.insert(name.clone()) {
                                return Err(Failure::Diagnostic(
                                    "E0210",
                                    "duplicate mapped field label".into(),
                                ));
                            }
                            fields.push(TypeField {
                                name,
                                mutable: false,
                                ty: field,
                                span: ty.span,
                            });
                        }
                    }
                    self.budget.event(budget::Event::LoopIteration)?;
                    if *tuple {
                        if items.len() == 1 {
                            return Err(Failure::Diagnostic(
                                "E0343",
                                "Ril has no one-element tuples".into(),
                            ));
                        }
                        Ok(TypeKind::Tuple(items))
                    } else {
                        Ok(TypeKind::Record { fields, row: None })
                    }
                })();
                self.install_environment(saved);
                result?
            }
            TypeKind::Computation(expression) if matches!(&expression.kind,ExprKind::Unary { operator,.. } if operator == "typeof") =>
            {
                let ExprKind::Unary { operand, .. } = &expression.kind else {
                    unreachable!()
                };
                return typing::type_of(self, operand);
            }
            TypeKind::Computation(_) => {
                return Err(Failure::Diagnostic(
                    "E0318",
                    "a concrete value cannot be a bare type".into(),
                ));
            }
            TypeKind::TypeFunction { .. }
            | TypeKind::KindArrow { .. }
            | TypeKind::Rest(_)
            | TypeKind::KeyOf(_) => return Ok(ty.clone()),
            TypeKind::Error => {
                return Err(Failure::Unsupported(
                    "invalid type syntax reached static evaluation".into(),
                ));
            }
        };
        Ok(TypeExpr {
            hir_id: None,
            text: ty.text.clone(),
            kind,
            span: ty.span,
        })
    }
    fn resolve_guarded_type(&mut self, ty: &TypeExpr, seen: &mut Vec<String>) -> Result<TypeExpr> {
        if let TypeKind::Name { path, .. } = &ty.kind
            && seen.contains(&path.join("::"))
        {
            return Ok(ty.clone());
        }
        self.resolve_type(ty, seen)
    }
    pub(super) fn bind_type_arguments(
        &mut self,
        parameters: &[GenericParameter],
        arguments: &[TypeExpr],
        declaration: &str,
    ) -> Result<Vec<TypeExpr>> {
        let captured = self.function_environments.get(declaration).copied();
        self.bind_type_arguments_captured(parameters, arguments, declaration, captured)
    }
    pub(super) fn bind_type_arguments_captured(
        &mut self,
        parameters: &[GenericParameter],
        arguments: &[TypeExpr],
        declaration: &str,
        captured: Option<environments::EnvironmentId>,
    ) -> Result<Vec<TypeExpr>> {
        let loops = self.loop_frames.clone();
        let result = self.evaluation_root(|evaluator| {
            evaluator.bind_type_arguments_within_root(parameters, arguments, declaration, captured)
        });
        self.loop_frames = loops;
        result
    }
    fn bind_type_arguments_within_root(
        &mut self,
        parameters: &[GenericParameter],
        arguments: &[TypeExpr],
        declaration: &str,
        captured: Option<environments::EnvironmentId>,
    ) -> Result<Vec<TypeExpr>> {
        if arguments.len() > parameters.len() {
            return Err(Failure::Diagnostic(
                "E0340",
                "too many static arguments".into(),
            ));
        }
        let mut actual = vec![];
        let caller = self.capture_environment()?;
        let caller_loops = self.loop_frames.clone();
        let mut bound = self.declaration_environment(captured)?;
        let named_meta = self
            .functions
            .get(declaration)
            .is_some_and(|function| function.is_meta);
        if named_meta {
            bound
                .types
                .enter_named(declaration, parameters, &self.budget)?;
        } else {
            bound.types.enter(declaration, parameters, &self.budget)?;
        }
        for parameter in parameters {
            bound.values.remove(&parameter.name);
        }
        for name in
            bound
                .types
                .prepare_rows(declaration, parameters, &self.declarations, &self.budget)?
        {
            bound.values.remove(&name);
        }
        let preselected = self.preselect_named_type_arguments(
            parameters,
            arguments,
            declaration,
            &caller,
            &mut bound,
        )?;
        for (index, parameter) in parameters.iter().enumerate() {
            let argument = arguments
                .get(index)
                .or(parameter.default.as_ref())
                .ok_or_else(|| Failure::Diagnostic("E0340", "missing static argument".into()))?;
            self.install_environment(if index < arguments.len() {
                self.copy_environment(&caller)?
            } else {
                self.copy_environment(&bound)?
            });
            self.loop_frames = if index < arguments.len() {
                caller_loops.clone()
            } else {
                vec![]
            };
            let value = if parameter
                .name
                .chars()
                .next()
                .is_some_and(char::is_lowercase)
                || matches!(
                    parameter.bound.as_ref().map(|bound| &bound.kind),
                    Some(TypeKind::KeyOf(_))
                ) {
                let value = self.value_argument(argument)?;
                self.loop_frames.clear();
                self.install_environment(self.copy_environment(&bound)?);
                if let Some(bound) = &parameter.bound {
                    let bound = self.resolve_type(bound, &mut Vec::new())?;
                    self.check_sort(&bound, &value)?;
                }
                bound = self.capture_environment()?;
                value
            } else if matches!(
                parameter.bound.as_ref().map(|bound| &bound.kind),
                Some(TypeKind::KindArrow { .. })
            ) {
                let constructor = if let TypeKind::Name { path, arguments } = &argument.kind
                    && arguments.is_empty()
                    && let Some(StaticValue::Type(constructor)) = self.values.get(&path.join("::"))
                {
                    constructor.clone()
                } else {
                    argument.clone()
                };
                let TypeKind::Name {
                    path,
                    arguments: applied,
                } = &constructor.kind
                else {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "higher-kinded argument requires a named type constructor".into(),
                    ));
                };
                if !applied.is_empty() {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "higher-kinded argument must be an unapplied constructor".into(),
                    ));
                }
                let name = normalized_path(path);
                let expected = kind_arity(parameter.bound.as_ref().unwrap());
                let actual = match name.as_str() { "Option" | "Set" | "Immut" | "Array::Elem" | "Map::Key" | "Map::Value" | "Set::Elem" => Some(1), "Result" => Some(2), _ => self.declarations.get(&path.join("::")).and_then(|declaration| {
                    let parameters = if let Some(TypeExpr { kind: TypeKind::TypeFunction { parameters, .. }, .. }) = &declaration.value { parameters } else { &declaration.generics };
                    parameters.iter().all(|parameter| parameter.name.chars().next().is_some_and(char::is_uppercase) && parameter.bound.as_ref().is_none_or(|bound| matches!(&bound.kind, TypeKind::Name { path, arguments } if path == &["Type"] && arguments.is_empty()))).then_some(parameters.len())
                }) };
                if actual != Some(expected) {
                    return Err(Failure::Diagnostic(
                        "E0306",
                        "argument does not have the required higher kind".into(),
                    ));
                }
                StaticValue::Type(constructor)
            } else {
                let actual = if let Some(selected) = &preselected {
                    clone_work::type_syntax(&self.budget, &selected[index])?;
                    selected[index].clone()
                } else {
                    self.resolve_type(argument, &mut Vec::new())?
                };
                self.loop_frames.clear();
                self.install_environment(self.copy_environment(&bound)?);
                if let Some(bound) = &parameter.bound {
                    self.check_type_bound(bound, &actual)?;
                }
                bound = self.capture_environment()?;
                StaticValue::Type(actual)
            };
            let normalized = match &value {
                StaticValue::Type(ty) => {
                    clone_work::type_syntax(&self.budget, ty)?;
                    if parameter
                        .name
                        .chars()
                        .next()
                        .is_some_and(char::is_uppercase)
                        && !matches!(
                            parameter.bound.as_ref().map(|bound| &bound.kind),
                            Some(TypeKind::KindArrow { .. } | TypeKind::KeyOf(_))
                        )
                        && let Some(witness) = self.source_type_witness(ty.clone())?
                    {
                        bound
                            .types
                            .select_type(&parameter.name, witness, &self.budget)?;
                    }
                    ty.clone()
                }
                _ => TypeExpr {
                    hir_id: None,
                    text: argument.text.clone(),
                    kind: TypeKind::Computation(Box::new(
                        self.const_value_expr(value.clone(), argument.span)?,
                    )),
                    span: argument.span,
                },
            };
            if named_meta
                && typing::const_int::parameter_sort(parameter)?
                    == typing::bounds::StaticParameterSort::ConstInt
            {
                let StaticValue::Integer(value) = &value else {
                    return Err(Failure::Diagnostic(
                        "E0323",
                        "static scalar int argument has the wrong value sort".into(),
                    ));
                };
                bound.types.select_const(&parameter.name, *value)?;
            }
            bound.values.insert(parameter.name.clone(), value);
            actual.push(normalized);
        }
        self.install_environment(bound);
        Ok(actual)
    }
    fn check_type_bound(&mut self, bound: &TypeExpr, actual: &TypeExpr) -> Result<()> {
        if matches!(&bound.kind, TypeKind::Name { path, arguments } if path == &["Type"] && arguments.is_empty())
        {
            return Ok(());
        }
        let expected = self.resolve_type(bound, &mut Vec::new())?;
        if let TypeKind::Record { fields, row } = &expected.kind {
            let TypeKind::Record {
                fields: actual_fields,
                row: None,
            } = &actual.kind
            else {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "type argument does not satisfy its record shape bound".into(),
                ));
            };
            for field in fields {
                if !actual_fields.iter().any(|actual| {
                    actual.name == field.name
                        && actual.mutable == field.mutable
                        && type_key(&actual.ty) == type_key(&field.ty)
                }) {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "type argument lacks a required bounded field".into(),
                    ));
                }
            }
            let remainder = TypeExpr {
                hir_id: None,
                text: String::new(),
                kind: TypeKind::Record {
                    fields: actual_fields
                        .iter()
                        .filter(|field| !fields.iter().any(|required| required.name == field.name))
                        .cloned()
                        .collect(),
                    row: None,
                },
                span: actual.span,
            };
            if let Some(row) = row {
                if let TypeKind::Name { path, arguments } = &row.kind
                    && path.len() == 1
                    && arguments.is_empty()
                    && !self.declarations.contains_key(&path[0])
                    && !self.values.contains_key(&path[0])
                {
                    clone_work::type_syntax(&self.budget, &remainder)?;
                    if let Some(witness) = self.source_type_witness(remainder.clone())? {
                        self.type_environment
                            .select_row(&path[0], witness, &self.budget)?;
                    }
                    self.values
                        .insert(path[0].clone(), StaticValue::Type(remainder));
                    return Ok(());
                }
                let row = self.resolve_type(row, &mut Vec::new())?;
                if type_key(&row) != type_key(&remainder) {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "type argument row differs from its bound".into(),
                    ));
                }
                if let TypeKind::Record {
                    row: Some(original_row),
                    ..
                } = &bound.kind
                    && let TypeKind::Name { path, arguments } = &original_row.kind
                    && path.len() == 1
                    && arguments.is_empty()
                {
                    clone_work::type_syntax(&self.budget, &row)?;
                    if let Some(witness) = self.source_type_witness(row.clone())? {
                        self.type_environment
                            .select_row(&path[0], witness, &self.budget)?;
                    }
                }
            } else if actual_fields.len() != fields.len() {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "type argument has fields outside its closed bound".into(),
                ));
            }
            return Ok(());
        }
        if type_key(&expected) == type_key(actual) {
            Ok(())
        } else {
            Err(Failure::Diagnostic(
                "E0301",
                "type argument does not satisfy its declared bound".into(),
            ))
        }
    }
    pub(super) fn const_value_expr(&self, value: StaticValue, span: Span) -> Result<Expr> {
        let kind = match value {
            StaticValue::Float(value, narrow) => {
                // Static type arguments identify every NaN of one width by
                // the same canonical NaN. Ordinary constant bits are unchanged.
                ExprKind::Literal(Literal::Float(committed_float::encode(
                    if value.is_nan() { f64::NAN } else { value },
                    narrow,
                )))
            }
            StaticValue::Record(fields) => {
                if !fields.mutable_fields.is_empty() {
                    return Err(Failure::Unsupported(
                        "static argument record slot modes need a complete reified type".into(),
                    ));
                }
                let fields = fields
                    .into_iter()
                    .map(|(name, value)| {
                        Ok(RecordField {
                            name,
                            value: self.const_value_expr(value, span)?,
                            span,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                let members = fields.iter().cloned().map(RecordMember::Field).collect();
                ExprKind::Record {
                    ty: None,
                    fields,
                    spread: None,
                    members,
                }
            }
            StaticValue::Array(values) => ExprKind::Array(
                values
                    .into_iter()
                    .map(|value| self.const_value_expr(value, span))
                    .collect::<Result<_>>()?,
            ),
            StaticValue::Tuple(values) => ExprKind::Tuple(
                values
                    .into_iter()
                    .map(|value| self.const_value_expr(value, span))
                    .collect::<Result<_>>()?,
            ),
            StaticValue::Map(entries) => ExprKind::Map(
                entries
                    .into_iter()
                    .map(|(key, value)| {
                        Ok((
                            self.const_value_expr(key, span)?,
                            self.const_value_expr(value, span)?,
                        ))
                    })
                    .collect::<Result<_>>()?,
            ),
            value => return self.materialize(value, span),
        };
        Ok(Expr {
            hir_id: None,
            kind,
            span,
        })
    }
    pub(super) fn value_argument(&mut self, argument: &TypeExpr) -> Result<StaticValue> {
        match &argument.kind {
            TypeKind::Computation(value) => self.expression(value),
            TypeKind::Tuple(items) => {
                if items.is_empty() {
                    return Ok(StaticValue::Unit);
                }
                let values = items
                    .iter()
                    .map(|item| self.value_argument(item))
                    .collect::<Result<_>>()?;
                Ok(self.tuple(values))
            }
            TypeKind::Name { path, arguments } if arguments.is_empty() => {
                self.static_name(&path.join("::"))
            }
            _ => Err(Failure::Diagnostic(
                "E0323",
                "type argument does not have the required value sort".into(),
            )),
        }
    }
    fn check_sort(&mut self, bound: &TypeExpr, value: &StaticValue) -> Result<()> {
        if let TypeKind::KeyOf(base) = &bound.kind {
            let StaticValue::Array(keys) = self.keyof(base)? else {
                unreachable!()
            };
            if keys.iter().any(|key| static_equal(key, value)) {
                return Ok(());
            }
            return Err(Failure::Diagnostic(
                "E0323",
                "static key is not a member of keyof the supplied shape".into(),
            ));
        }
        let valid = match (&bound.kind, value) {
            (TypeKind::Tuple(items), StaticValue::Unit) => items.is_empty(),
            (TypeKind::Tuple(types), StaticValue::Tuple(items)) if types.len() == items.len() => {
                for (ty, value) in types.iter().zip(items.iter()) {
                    self.check_sort(ty, value)?;
                }
                true
            }
            (TypeKind::Optional(inner), StaticValue::Variant(name, payload, _)) => {
                match (
                    name.strip_prefix("Prelude::").unwrap_or(name),
                    payload.as_slice(),
                ) {
                    ("None", []) => true,
                    ("Some", [value]) => {
                        self.check_sort(inner, value)?;
                        true
                    }
                    _ => false,
                }
            }
            (TypeKind::Name { path, arguments }, _)
                if normalized_path(path) == "Option" && arguments.len() == 1 =>
            {
                let optional = TypeExpr {
                    hir_id: None,
                    kind: TypeKind::Optional(Box::new(arguments[0].clone())),
                    text: bound.text.clone(),
                    span: bound.span,
                };
                self.check_sort(&optional, value)?;
                true
            }
            (TypeKind::Name { path, arguments }, _)
                if normalized_path(path) == "Immut" && arguments.len() == 1 =>
            {
                self.check_sort(&arguments[0], value)?;
                true
            }
            (TypeKind::Name { path, .. }, StaticValue::Integer(_)) => {
                normalized_path(path) == "int"
            }
            (TypeKind::Name { path, .. }, StaticValue::TypedInteger(_, bits, signed)) => {
                normalized_path(path) == format!("{}{bits}", if *signed { 'i' } else { 'u' })
            }
            (TypeKind::Name { path, .. }, StaticValue::BigInteger(_)) => {
                normalized_path(path) == "bigint"
            }
            (TypeKind::Name { path, .. }, StaticValue::Float(_, narrow)) => {
                normalized_path(path) == if *narrow { "f32" } else { "f64" }
            }
            (TypeKind::Name { path, .. }, StaticValue::Bool(_)) => normalized_path(path) == "bool",
            (TypeKind::Name { path, .. }, StaticValue::String(_)) => normalized_path(path) == "str",
            (TypeKind::Name { path, .. }, StaticValue::Bytes(_)) => {
                normalized_path(path) == "bytes"
            }
            (TypeKind::Array { element, length }, array) if array.array_items().is_some() => {
                let items = array
                    .array_items()
                    .expect("the match guard admitted an array view");
                if let Some(length) = length {
                    let StaticValue::Integer(length) = self.expression(length)? else {
                        return Err(Failure::Diagnostic(
                            "E0323",
                            "fixed array sort length must be int".into(),
                        ));
                    };
                    if usize::try_from(length).ok() != Some(items.len()) {
                        return Err(Failure::Diagnostic(
                            "E0323",
                            "static array argument length differs from its admitted sort".into(),
                        ));
                    }
                }
                for item in items {
                    self.check_sort(element, item)?;
                }
                true
            }
            (TypeKind::Map { key, value: ty }, StaticValue::Map(entries)) => {
                for (k, v) in entries {
                    self.check_sort(key, k)?;
                    self.check_sort(ty, v)?;
                }
                true
            }
            (TypeKind::Record { fields, .. }, StaticValue::Record(values)) => {
                for field in fields {
                    if field.mutable != values.mutable_fields.contains(&field.name) {
                        return Err(Failure::Unsupported(
                            "static record sort conversion needs a slot-mode witness".into(),
                        ));
                    }
                    let Some(value) = values.get(&field.name) else {
                        return Err(Failure::Diagnostic(
                            "E0323",
                            "static record argument is missing a field".into(),
                        ));
                    };
                    self.check_sort(&field.ty, value)?;
                }
                fields.len() == values.len()
            }
            _ => false,
        };
        if valid {
            Ok(())
        } else {
            Err(Failure::Diagnostic(
                "E0323",
                "static argument violates its value sort".into(),
            ))
        }
    }
    pub(super) fn keyof(&mut self, ty: &TypeExpr) -> Result<StaticValue> {
        let expanded = self.resolve_type(ty, &mut Vec::new())?;
        let mut names = match expanded.kind {
            TypeKind::Record { fields, .. } => fields
                .into_iter()
                .map(|field| field.name)
                .collect::<Vec<_>>(),
            TypeKind::Tuple(items) => {
                return Ok(self.array(
                    (0..items.len())
                        .map(|index| StaticValue::Integer(index as i128))
                        .collect(),
                ));
            }
            TypeKind::Name { path, .. } => {
                let Some(declaration) = self.declarations.get(&path.join("::")).cloned() else {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "keyof requires a product or sum shape".into(),
                    ));
                };
                if !declaration.variants.is_empty() {
                    declaration
                        .variants
                        .into_iter()
                        .map(|variant| variant.name)
                        .collect()
                } else if let Some(value) = declaration.value {
                    return self.keyof(&value);
                } else {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "keyof cannot inspect this nominal shape".into(),
                    ));
                }
            }
            _ => {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "keyof requires a product or sum shape".into(),
                ));
            }
        };
        names.sort();
        Ok(self.array(names.into_iter().map(StaticValue::String).collect()))
    }
    pub(super) fn project_type(
        &mut self,
        base: &TypeExpr,
        key: StaticValue,
        span: Span,
        seen: &mut Vec<String>,
    ) -> Result<TypeExpr> {
        let expanded = self.resolve_type(base, seen)?;
        match expanded.kind {
            TypeKind::Record { fields, .. } => {
                let StaticValue::String(name) = key else {
                    return Err(Failure::Diagnostic(
                        "E0323",
                        "record type projection requires a string key".into(),
                    ));
                };
                fields
                    .into_iter()
                    .find(|field| field.name == name)
                    .map(|field| field.ty)
                    .ok_or_else(|| {
                        Failure::Diagnostic("E0336", "projected record field does not exist".into())
                    })
            }
            TypeKind::Tuple(mut items) => {
                let index = match key {
                    StaticValue::Integer(index) => index,
                    StaticValue::String(index) => index.parse().map_err(|_| {
                        Failure::Diagnostic(
                            "E0323",
                            "tuple type projection requires an integer".into(),
                        )
                    })?,
                    _ => {
                        return Err(Failure::Diagnostic(
                            "E0323",
                            "tuple type projection requires an integer".into(),
                        ));
                    }
                };
                if index < 0 || index as usize >= items.len() {
                    Err(Failure::Diagnostic(
                        "E0312",
                        "tuple type index out of bounds".into(),
                    ))
                } else {
                    Ok(items.remove(index as usize))
                }
            }
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                let Some(declaration) = self.declarations.get(&name).cloned() else {
                    return Err(Failure::Diagnostic(
                        "E0337",
                        "type does not admit projection".into(),
                    ));
                };
                let StaticValue::String(field) = key else {
                    return Err(Failure::Diagnostic(
                        "E0323",
                        "nominal projection requires a static name".into(),
                    ));
                };
                let saved = self.capture_environment()?;
                let result = (|| {
                    self.bind_type_arguments(&declaration.generics, &arguments, &declaration.name)?;
                    if !declaration.variants.is_empty() {
                        let Some(variant) = declaration
                            .variants
                            .iter()
                            .find(|variant| variant.name == field)
                        else {
                            return Err(Failure::Diagnostic(
                                "E0336",
                                "sum has no such constructor".into(),
                            ));
                        };
                        if let Some(result) = &variant.result {
                            // Local parameters shadow enclosing parameters,
                            // including a same-spelled outer generic argument.
                            for parameter in &variant.generics {
                                self.values.remove(&parameter.name);
                            }
                            let actual = TypeExpr {
                                hir_id: None,
                                text: name.clone(),
                                kind: TypeKind::Name {
                                    path: path.clone(),
                                    arguments: arguments.clone(),
                                },
                                span,
                            };
                            let generic: BTreeSet<_> = variant
                                .generics
                                .iter()
                                .map(|parameter| parameter.name.clone())
                                .collect();
                            let pattern = self.resolve_type(result, &mut Vec::new())?;
                            if !self.match_type(&pattern, &actual, &generic)? {
                                return Err(Failure::Diagnostic(
                                    "E0301",
                                    "GADT constructor result is incompatible with this instance"
                                        .into(),
                                ));
                            }
                            let resolved = self.resolve_type(result, &mut Vec::new())?;
                            if type_key(&resolved) != type_key(&actual) {
                                return Err(Failure::Diagnostic("E0301","constructor result equation does not equal the selected instance".into()));
                            }
                            for parameter in &variant.generics {
                                let Some(StaticValue::Type(actual)) =
                                    self.values.get(&parameter.name).cloned()
                                else {
                                    return Err(Failure::Unsupported("constructor result did not recover a complete local type parameter".into()));
                                };
                                if let Some(bound) = &parameter.bound {
                                    self.check_type_bound(bound, &actual)?;
                                }
                            }
                        }
                        let payload = variant
                            .payload
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(|| unit_type(span));
                        self.resolve_type(&payload, &mut Vec::new())
                    } else if let Some(value) = &declaration.value {
                        self.project_type(value, StaticValue::String(field), span, &mut Vec::new())
                    } else {
                        Err(Failure::Diagnostic(
                            "E0337",
                            "type has no constituent projection".into(),
                        ))
                    }
                })();
                self.install_environment(saved);
                result
            }
            _ => Err(Failure::Diagnostic(
                "E0337",
                "type does not admit constituent projection".into(),
            )),
        }
    }
    pub(super) fn match_type(
        &mut self,
        pattern: &TypeExpr,
        actual: &TypeExpr,
        generic: &BTreeSet<String>,
    ) -> Result<bool> {
        if let TypeKind::Name { path, arguments } = &pattern.kind
            && path.len() == 1
            && (path[0].starts_with("let ") || generic.contains(&path[0]))
        {
            if !arguments.is_empty() {
                return Err(Failure::Diagnostic(
                    "E0306",
                    "type-pattern constructor head must be rigid".into(),
                ));
            }
            let name = path[0].strip_prefix("let ").unwrap_or(&path[0]);
            if name == "_" {
                return Ok(true);
            }
            if let Some(StaticValue::Type(previous)) = self.values.get(name) {
                return Ok(type_key(previous) == type_key(actual));
            }
            self.values
                .insert(name.into(), StaticValue::Type(actual.clone()));
            return Ok(true);
        }
        match (&pattern.kind, &actual.kind) {
            (TypeKind::Computation(left), TypeKind::Computation(right)) => {
                let left = self.expression(left)?;
                let right = self.expression(right)?;
                Ok(static_equal(&left, &right))
            }
            (TypeKind::Name { path, arguments }, TypeKind::Optional(inner))
                if normalized_path(path) == "Option" && arguments.len() == 1 =>
            {
                self.match_type(&arguments[0], inner, generic)
            }
            (TypeKind::Optional(inner), TypeKind::Name { path, arguments })
                if normalized_path(path) == "Option" && arguments.len() == 1 =>
            {
                self.match_type(inner, &arguments[0], generic)
            }
            (
                TypeKind::Name {
                    path: a,
                    arguments: aargs,
                },
                TypeKind::Name {
                    path: b,
                    arguments: bargs,
                },
            ) => {
                if normalized_path(a) != normalized_path(b) || aargs.len() != bargs.len() {
                    return Ok(false);
                }
                for (a, b) in aargs.iter().zip(bargs) {
                    if !self.match_type(a, b, generic)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (TypeKind::Optional(a), TypeKind::Optional(b)) => self.match_type(a, b, generic),
            (TypeKind::Tuple(a), TypeKind::Tuple(b)) => {
                let rest = a
                    .last()
                    .is_some_and(|ty| matches!(ty.kind, TypeKind::Rest(_)));
                let fixed = a.len() - usize::from(rest);
                if (!rest && a.len() != b.len())
                    || (rest && (b.len() < fixed || b.len() - fixed == 1))
                {
                    return Ok(false);
                }
                for (a, b) in a[..fixed].iter().zip(b) {
                    if !self.match_type(a, b, generic)? {
                        return Ok(false);
                    }
                }
                if let Some(TypeExpr {
                    kind: TypeKind::Rest(pattern),
                    ..
                }) = a.last()
                {
                    let actual = TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        kind: TypeKind::Tuple(b[fixed..].to_vec()),
                        span: actual.span,
                    };
                    self.match_type(pattern, &actual, generic)
                } else {
                    Ok(true)
                }
            }
            (
                TypeKind::Array {
                    element: a,
                    length: left,
                },
                TypeKind::Array {
                    element: b,
                    length: right,
                },
            ) => {
                if let Some(left) = left {
                    let Some(right) = right else {
                        return Ok(false);
                    };
                    let left = self.expression(left)?;
                    let right = self.expression(right)?;
                    if !static_equal(&left, &right) {
                        return Ok(false);
                    }
                }
                self.match_type(a, b, generic)
            }
            (TypeKind::Map { key: a, value: b }, TypeKind::Map { key: c, value: d }) => {
                Ok(self.match_type(a, c, generic)? && self.match_type(b, d, generic)?)
            }
            (
                TypeKind::Callable {
                    parameters: a,
                    result: ar,
                    ..
                },
                TypeKind::Callable {
                    parameters: b,
                    result: br,
                    ..
                },
            ) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    if a.mode != b.mode {
                        return Ok(false);
                    }
                    match (&a.ty, &b.ty) {
                        (Some(a), Some(b)) if self.match_type(a, b, generic)? => {}
                        (None, None) => {}
                        _ => return Ok(false),
                    }
                }
                match (ar, br) {
                    (Some(a), Some(b)) => self.match_type(a, b, generic),
                    (None, None) => Ok(true),
                    _ => Ok(false),
                }
            }
            (TypeKind::Record { fields: a, row }, TypeKind::Record { fields: b, .. }) => {
                if row.is_none() && a.len() != b.len() {
                    return Ok(false);
                }
                for field in a {
                    let Some(actual) = b.iter().find(|actual| actual.name == field.name) else {
                        return Ok(false);
                    };
                    if field.mutable != actual.mutable
                        || !self.match_type(&field.ty, &actual.ty, generic)?
                    {
                        return Ok(false);
                    }
                }
                if let Some(row) = row {
                    let actual = TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        kind: TypeKind::Record {
                            fields: b
                                .iter()
                                .filter(|field| !a.iter().any(|pattern| pattern.name == field.name))
                                .cloned()
                                .collect(),
                            row: None,
                        },
                        span: actual.span,
                    };
                    self.match_type(row, &actual, generic)
                } else {
                    Ok(true)
                }
            }
            _ => Ok(type_key(pattern) == type_key(actual)),
        }
    }
}

pub(super) fn kind_arity(ty: &TypeExpr) -> usize {
    if let TypeKind::KindArrow { parameter, result } = &ty.kind {
        let inputs = if let TypeKind::Tuple(items) = &parameter.kind {
            items.len()
        } else {
            1
        };
        inputs + kind_arity(result)
    } else {
        0
    }
}
pub(super) fn type_key(ty: &TypeExpr) -> String {
    match &ty.kind {
        TypeKind::Name { path, arguments } => format!(
            "{}<{}>",
            normalized_path(path),
            arguments.iter().map(type_key).collect::<Vec<_>>().join(",")
        ),
        TypeKind::Optional(inner) => format!("Option<{}>", type_key(inner)),
        TypeKind::Array { length, element } => format!(
            "[{}]{}",
            length
                .as_ref()
                .map(|length| expression_key(length))
                .unwrap_or_default(),
            type_key(element)
        ),
        TypeKind::Map { key, value } => format!("[{}:{}]", type_key(key), type_key(value)),
        TypeKind::Tuple(items) => format!(
            "({})",
            items.iter().map(type_key).collect::<Vec<_>>().join(",")
        ),
        TypeKind::Record { fields, row } => {
            let mut fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}:{}",
                        if field.mutable { "mut " } else { "" },
                        field.name,
                        type_key(&field.ty)
                    )
                })
                .collect::<Vec<_>>();
            fields.sort();
            format!(
                "{{{};{}}}",
                fields.join(","),
                row.as_ref().map(|row| type_key(row)).unwrap_or_default()
            )
        }
        TypeKind::Callable {
            parameters,
            result,
            annotations,
        } => format!(
            "fn({})->{}{}",
            parameters
                .iter()
                .map(|parameter| format!(
                    "{:?}:{}",
                    parameter.mode,
                    parameter.ty.as_ref().map(type_key).unwrap_or_default()
                ))
                .collect::<Vec<_>>()
                .join(","),
            result
                .as_ref()
                .map(|result| type_key(result))
                .unwrap_or_default(),
            annotations
                .iter()
                .map(|annotation| annotation.text.replace(' ', ""))
                .collect::<String>()
        ),
        TypeKind::Computation(value) => format!("const({})", expression_key(value)),
        TypeKind::Projection { base, field } => format!("{}.{}", type_key(base), field),
        TypeKind::ComputedProjection { base, key } => {
            format!("{}.({})", type_key(base), expression_key(key))
        }
        _ => format!("{:?}", ty.kind),
    }
}
fn expression_key(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Literal(Literal::Integer(text)) => {
            let raw = text.replace('_', "");
            let suffix = [
                "bigint", "int", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
            ]
            .into_iter()
            .find(|suffix| raw.ends_with(suffix))
            .unwrap_or("int");
            let digits = raw.strip_suffix(suffix).unwrap_or(&raw);
            let (sign, digits) = digits
                .strip_prefix('-')
                .map_or(("", digits), |digits| ("-", digits));
            let (radix, digits) = if let Some(digits) = digits
                .strip_prefix("0x")
                .or_else(|| digits.strip_prefix("0X"))
            {
                (16, digits)
            } else if let Some(digits) = digits
                .strip_prefix("0o")
                .or_else(|| digits.strip_prefix("0O"))
            {
                (8, digits)
            } else if let Some(digits) = digits
                .strip_prefix("0b")
                .or_else(|| digits.strip_prefix("0B"))
            {
                (2, digits)
            } else {
                (10, digits)
            };
            num_bigint::BigInt::parse_bytes(format!("{sign}{digits}").as_bytes(), radix)
                .map_or_else(
                    || format!("invalid-int:{raw}"),
                    |value| format!("{suffix}:{value}"),
                )
        }
        ExprKind::Literal(Literal::String(text)) => {
            crate::lower::decode_text(&text[1..text.len() - 1]).map_or_else(
                |_| format!("invalid-string:{text}"),
                |value| format!("str:{value:?}"),
            )
        }
        ExprKind::Literal(Literal::RawString(text)) => {
            format!("str:{:?}", &text[1..text.len() - 1])
        }
        ExprKind::Literal(Literal::Bytes(text)) => {
            crate::lower::decode_bytes(&text[2..text.len() - 1]).map_or_else(
                |_| format!("invalid-bytes:{text}"),
                |value| format!("bytes:{value:?}"),
            )
        }
        ExprKind::Interpolated(parts)
            if parts.iter().all(|part| matches!(part, StringPart::Text(_))) =>
        {
            format!(
                "str:{:?}",
                parts
                    .iter()
                    .map(|part| if let StringPart::Text(text) = part {
                        text.as_str()
                    } else {
                        unreachable!()
                    })
                    .collect::<String>()
            )
        }
        ExprKind::Literal(Literal::Float(text)) => {
            match committed_float::decode(text) {
                Ok(Some(value)) => {
                    return if value.width == 32 {
                        format!("f32:{:08x}", value.bits)
                    } else {
                        format!("f64:{:016x}", value.bits)
                    };
                }
                Err(()) => return "invalid-committed-float".into(),
                Ok(None) => {}
            }
            let narrow = text.ends_with("f32");
            let raw = text
                .trim_end_matches("f32")
                .trim_end_matches("f64")
                .replace('_', "");
            if narrow {
                raw.parse::<f32>()
                    .map(|value| {
                        format!(
                            "f32:{:08x}",
                            if value.is_nan() {
                                0x7fc0_0000
                            } else {
                                value.to_bits()
                            }
                        )
                    })
                    .unwrap_or_else(|_| text.clone())
            } else {
                raw.parse::<f64>()
                    .map(|value| {
                        format!(
                            "f64:{:016x}",
                            if value.is_nan() {
                                0x7ff8_0000_0000_0000
                            } else {
                                value.to_bits()
                            }
                        )
                    })
                    .unwrap_or_else(|_| text.clone())
            }
        }
        ExprKind::Literal(literal) => format!("{literal:?}"),
        ExprKind::Array(items) | ExprKind::Tuple(items) => format!(
            "{:?}:{}",
            std::mem::discriminant(&expr.kind),
            items
                .iter()
                .map(expression_key)
                .collect::<Vec<_>>()
                .join(",")
        ),
        ExprKind::Map(entries) => format!(
            "map:{}",
            entries
                .iter()
                .map(|(key, value)| format!("{}:{}", expression_key(key), expression_key(value)))
                .collect::<Vec<_>>()
                .join(",")
        ),
        ExprKind::Record { fields, .. } => {
            let mut fields = fields
                .iter()
                .map(|field| format!("{}:{}", field.name, expression_key(&field.value)))
                .collect::<Vec<_>>();
            fields.sort();
            fields.join(",")
        }
        ExprKind::Name(name) => name.clone(),
        ExprKind::Path(path) => normalized_path(path),
        ExprKind::Call { callee, arguments } => format!(
            "call:{}({})",
            expression_key(callee),
            arguments
                .iter()
                .map(|argument| expression_key(&argument.value))
                .collect::<Vec<_>>()
                .join(",")
        ),
        ExprKind::Unary { operator, operand } => format!("{operator}({})", expression_key(operand)),
        ExprKind::TypeValue(ty) => type_key(ty),
        _ => format!("{:?}", expr.kind),
    }
}
fn normalized_path(path: &[String]) -> String {
    let name = path.join("::");
    name.strip_prefix("Prelude::").unwrap_or(&name).into()
}
fn valid_label(name: &str) -> bool {
    !name.is_empty()
        && !name.contains("__")
        && !name.ends_with('_')
        && name
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !ril_syntax::is_reserved_identifier(name)
}
fn unit_type(span: Span) -> TypeExpr {
    TypeExpr {
        hir_id: None,
        text: "()".into(),
        kind: TypeKind::Tuple(vec![]),
        span,
    }
}

#[cfg(test)]
mod row_tests {
    use super::*;

    #[test]
    fn expanding_nested_row_aliases_preserves_the_rigid_remainder() {
        let parsed = ril_syntax::parse(
            "type Inner<R>={id:int,..R}\ntype Outer<R>={flag:bool,..Inner<R>}\nfn example<R>(value:Outer<R>){}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let definitions = super::super::definitions::collect(&parsed.program);
        let mut evaluator = Evaluator {
            type_environment: Default::default(),
            type_application_sequence: 0,
            effect_declarations: BTreeMap::new(),
            layout: TargetLayout::POINTER64,
            values: BTreeMap::new(),
            global_values: BTreeMap::new(),
            budget: Default::default(),
            declarations: definitions.all_types,
            functions: definitions.all_functions,
            function_environments: BTreeMap::new(),
            environments: vec![],
            alias_instances: BTreeMap::new(),
            static_signatures: BTreeMap::new(),
            active_functions: vec![],
            type_depth: 0,
            call_depth: 0,
            tail_returns: false,
            tail_types: false,
            numeric_return: None,
            results: Default::default(),
            result_site: None,
            expression_depth: 0,
            loop_frames: vec![],
            next_loop_target: 0,
            type_calls: BTreeSet::new(),
            next_collection: 0,
            publications: Default::default(),
            constants: Default::default(),
        };
        let StmtKind::Function(function) = &parsed.program.statements[2].kind else {
            panic!()
        };
        let Ok(expanded) =
            evaluator.resolve_type(function.parameters[0].ty.as_ref().unwrap(), &mut Vec::new())
        else {
            panic!("valid symbolic row alias did not expand")
        };
        let TypeKind::Record { fields, row } = expanded.kind else {
            panic!()
        };
        assert_eq!(
            fields
                .iter()
                .map(|field| field.name.as_str())
                .collect::<Vec<_>>(),
            ["flag", "id"]
        );
        assert!(
            matches!(&row.as_ref().unwrap().kind,TypeKind::Name {path,arguments} if path==&["R"] && arguments.is_empty())
        );
    }
}
