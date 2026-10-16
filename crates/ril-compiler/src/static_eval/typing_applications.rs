//! Pure declaration-wide type applications. Closed schema witnesses and rigid
//! caller promises are distinct; neither evaluated payloads nor storage lengths
//! can turn an unresolved type into a closed one.
use super::*;
use crate::sema::model::{
    SourceTypeWitness,
    rows::{OpenTail, Row, RowIdentity, RowTail, Solver},
};
use bounds::{BoundEnvironment, StaticBinderId, StaticRowId};
use std::sync::Arc;

#[path = "typing_bound_dependencies.rs"]
mod bound_dependencies;
#[path = "typing_result_context.rs"]
mod result_context;
#[path = "typing_symbolic_aliases.rs"]
mod symbolic_aliases;
#[path = "typing_template_inference.rs"]
mod template_inference;
pub(in crate::static_eval) use result_context::{ResultContext, ResultProjection};

/// Ordinary receiving hints and complete source constraints keep their
/// distinct meanings, even when transported as one call preparation input.
#[derive(Clone, Copy, Default)]
pub(in crate::static_eval) struct ExpectedResult<'a> {
    pub ordinary: Option<&'a Ty>,
    pub source: Option<&'a ResultContext>,
}

#[derive(Clone, Copy)]
pub(super) struct ApplicationInference<'a> {
    pub caller: &'a BoundEnvironment,
    pub declaration: &'a str,
}

#[derive(Debug, Clone)]
pub(super) struct SchemaField {
    pub syntax: Arc<TypeExpr>,
    pub key: crate::sema::effect_identity::ArgumentKey,
}
impl PartialEq for SchemaField {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl Eq for SchemaField {}

pub(super) struct TypeApplication<'a> {
    pub actual_types: &'a [Ty],
    pub actual_schemas: &'a [Option<Arc<SourceTypeWitness>>],
    pub plan: &'a application::StaticApplicationPlan,
    pub captured: &'a BoundEnvironment,
    pub caller: &'a BoundEnvironment,
    pub explicit: &'a [TypeExpr],
    pub expected: Option<&'a ResultContext>,
    /// Identity of this real activation, rather than a source span or syntax.
    pub instance: u64,
}

fn missing(reason: &str) -> Failure {
    Failure::Unsupported(reason.into())
}
fn mismatch(reason: &str) -> Failure {
    Failure::Diagnostic("E0301", reason.into())
}
fn normalized_path(path: &[String]) -> String {
    path.strip_prefix(&["Prelude".into()])
        .unwrap_or(path)
        .join("::")
}

impl Typer<'_> {
    pub(super) fn complete_source_syntax(
        &self,
        syntax: &TypeExpr,
        scope: &BoundEnvironment,
    ) -> Result<Option<Arc<SourceTypeWitness>>> {
        self.reject_const_dependent_type(syntax, scope)?;
        let syntax = self.scoped_source_syntax(syntax, scope)?;
        let Some(syntax) = crate::sema::checker::normalize_closed_source_syntax(
            &syntax,
            &self.evaluator.declarations,
            self.evaluator.layout,
        ) else {
            return Ok(None);
        };
        let witness = SourceTypeWitness {
            key: normalized_argument_key(&syntax),
            syntax,
        };
        Ok(witness.validate_closed().then(|| Arc::new(witness)))
    }

    /// Registered symbolic identities are retained as internal type names.
    /// This output is not a closed SourceTypeWitness.
    pub(super) fn scoped_source_syntax(
        &self,
        syntax: &TypeExpr,
        scope: &BoundEnvironment,
    ) -> Result<TypeExpr> {
        self.reject_const_dependent_type(syntax, scope)?;
        fn visit(
            syntax: &TypeExpr,
            scope: &BoundEnvironment,
            depth: usize,
            nodes: &mut usize,
            active: &mut BTreeSet<StaticBinderId>,
        ) -> Result<TypeExpr> {
            *nodes += 1;
            if depth >= 64 || *nodes > 4096 {
                return Err(missing(
                    "static complete type substitution exceeds its finite traversal allowance",
                ));
            }
            if let TypeKind::Name { path, arguments } = &syntax.kind
                && path.len() == 1
                && arguments.is_empty()
            {
                let name = &path[0];
                if let Some(id) = scope
                    .type_binders
                    .get(name)
                    .or_else(|| scope.type_ids.get(name))
                {
                    if let Some(actual) = scope.selected_types.get(id) {
                        return Ok(actual.syntax.clone());
                    }
                    if let Some(Ty::Generic(actual)) = scope.type_arguments.get(id)
                        && actual != &id.key()
                    {
                        if !active.insert(id.clone()) {
                            return Err(missing("cyclic static type selection"));
                        }
                        let mut selected = syntax.clone();
                        selected.kind = TypeKind::Name {
                            path: vec![actual.clone()],
                            arguments: vec![],
                        };
                        let result = visit(&selected, scope, depth + 1, nodes, active);
                        active.remove(id);
                        return result;
                    }
                    let mut selected = syntax.clone();
                    selected.kind = TypeKind::Name {
                        path: vec![id.key()],
                        arguments: vec![],
                    };
                    return Ok(selected);
                }
                if let Some(id) = scope.row_context.get(name) {
                    if let Some(actual) = scope.selected_rows.get(id) {
                        return Ok(actual.syntax.clone());
                    }
                    if let Some(row) = scope.rows.get(id)
                        && let RowIdentity::Binder(identity) = &row.identity
                    {
                        let mut selected = syntax.clone();
                        selected.kind = TypeKind::Name {
                            path: vec![identity.clone()],
                            arguments: vec![],
                        };
                        return Ok(selected);
                    }
                }
            }
            let mut output = syntax.clone();
            let mut child = |value: &TypeExpr| visit(value, scope, depth + 1, nodes, active);
            match &mut output.kind {
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    for value in arguments {
                        *value = child(value)?;
                    }
                }
                TypeKind::Optional(value) | TypeKind::Array { element: value, .. } => {
                    **value = child(value)?
                }
                TypeKind::Map { key, value } => {
                    **key = child(key)?;
                    **value = child(value)?;
                }
                TypeKind::Record { fields, row } => {
                    for field in fields.iter_mut() {
                        field.ty = child(&field.ty)?;
                    }
                    if let Some(tail) = row {
                        let actual = child(tail)?;
                        if let TypeKind::Record {
                            fields: extra,
                            row: tail,
                        } = actual.kind
                        {
                            for field in extra {
                                if fields.iter().any(|old| old.name == field.name) {
                                    return Err(mismatch(
                                        "selected static row overlaps a required field",
                                    ));
                                }
                                fields.push(field);
                            }
                            *row = tail;
                        } else {
                            **tail = actual;
                        }
                    }
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        if let Some(ty) = &mut parameter.ty {
                            *ty = child(ty)?;
                        }
                    }
                    if let Some(result) = result {
                        **result = child(result)?;
                    }
                }
                _ => {}
            }
            Ok(output)
        }
        let budget = budget::Budget::default();
        clone_work::type_syntax(&budget, syntax)?;
        visit(syntax, scope, 0, &mut 0, &mut BTreeSet::new())
    }

    fn schema_field(&self, syntax: &TypeExpr, scope: &BoundEnvironment) -> Result<SchemaField> {
        let syntax = self.scoped_source_syntax(syntax, scope)?;
        let closed = crate::sema::checker::normalize_closed_source_syntax(
            &syntax,
            &self.evaluator.declarations,
            self.evaluator.layout,
        );
        let syntax = if let Some(closed) = closed {
            closed
        } else if let Some(expanded) = self.symbolic_alias_syntax(&syntax, scope)? {
            expanded.syntax
        } else {
            syntax
        };
        let key = effects::bounded_argument_key(&syntax, &BTreeMap::new())
            .ok_or_else(|| missing("static row field has no complete scoped type key"))?;
        Ok(SchemaField {
            syntax: Arc::new(syntax),
            key,
        })
    }

    pub(super) fn select_type_argument(
        &self,
        id: &StaticBinderId,
        actual: &Ty,
        schema: Option<Arc<SourceTypeWitness>>,
        caller: &BoundEnvironment,
        scope: &mut BoundEnvironment,
    ) -> Result<()> {
        let mut actual = erase_constants(caller.canonical_type(actual.clone()));
        let schema = match schema {
            Some(schema) => {
                let checked = self
                    .complete_source_syntax(&schema.syntax, &BoundEnvironment::default())?
                    .ok_or_else(|| missing("static actual schema is not a closed declared type"))?;
                if checked.key != schema.key {
                    return Err(missing(
                        "static actual schema key disagrees with its syntax",
                    ));
                }
                let declared = self.bound_type(&checked.syntax, &BoundEnvironment::default())?;
                require_invariant(
                    &without_storage_lengths(actual),
                    &without_storage_lengths(declared.clone()),
                )?;
                actual = declared;
                Some(schema)
            }
            None if matches!(&actual, Ty::Generic(identity) if caller.type_ids.contains_key(identity)) => {
                None
            }
            None => lossless_syntax(&actual, self.evaluator.functions[&id.declaration].span)
                .map(|syntax| self.complete_source_syntax(&syntax, caller))
                .transpose()?
                .flatten(),
        };
        if schema.is_none()
            && !matches!(&actual, Ty::Generic(identity) if caller.type_ids.contains_key(identity))
        {
            return Err(missing(
                "static generic selection requires a complete declared schema",
            ));
        }
        if let Some(old) = scope.type_arguments.get(id) {
            require_invariant(&actual, old)?;
            match (scope.selected_types.get(id), &schema) {
                (Some(left), Some(right)) if left.key == right.key => {}
                (None, None) if old == &actual => {}
                _ => {
                    return Err(mismatch(
                        "one static generic parameter has inconsistent complete selections",
                    ));
                }
            }
        } else {
            scope.type_arguments.insert(id.clone(), actual);
            if let Some(schema) = schema {
                scope.selected_types.insert(id.clone(), schema);
            }
        }
        Ok(())
    }

    fn infer_application_type(
        &self,
        formal: &TypeExpr,
        actual: &Ty,
        schema: Option<Arc<SourceTypeWitness>>,
        inference: ApplicationInference<'_>,
        scope: &mut BoundEnvironment,
        depth: usize,
    ) -> Result<()> {
        let ApplicationInference {
            caller,
            declaration,
        } = inference;
        if depth >= 64 {
            return Err(missing("static generic inference traversal allowance"));
        }
        if let TypeKind::Name { path, arguments } = &formal.kind
            && path.len() == 1
            && arguments.is_empty()
            && let Some(id) = scope
                .type_binders
                .get(&path[0])
                .or_else(|| scope.type_ids.get(&path[0]))
                .cloned()
        {
            if id.declaration == declaration {
                return self.select_type_argument(&id, actual, schema, caller, scope);
            }
            // A captured binder is a rigid dependency, never a variable for
            // this application to solve. The final receiving/bound checks
            // require its already captured selection or symbolic identity.
            return Ok(());
        }
        if let Some(expanded) = self.symbolic_alias_syntax(formal, scope)? {
            return self.infer_application_type(
                &expanded.syntax,
                actual,
                schema,
                inference,
                scope,
                depth + 1,
            );
        }
        if self.infer_application_template_children(
            formal,
            actual,
            schema.as_ref(),
            inference,
            scope,
            depth,
        )? {
            return Ok(());
        }
        let closed = schema.as_ref().map(|witness| &witness.syntax.kind);
        let child_schema = |syntax: Option<&TypeExpr>| {
            syntax
                .map(|syntax| self.complete_source_syntax(syntax, caller))
                .transpose()
                .map(Option::flatten)
        };
        match (&formal.kind, actual) {
            (TypeKind::Array { element, .. }, Ty::Array(actual, _)) => {
                let child = if let Some(TypeKind::Array { element, .. }) = closed {
                    Some(element.as_ref())
                } else {
                    None
                };
                self.infer_application_type(
                    element,
                    actual,
                    child_schema(child)?,
                    inference,
                    scope,
                    depth + 1,
                )?;
            }
            (TypeKind::Optional(formal), Ty::Optional(actual)) => {
                let child = if let Some(TypeKind::Optional(value)) = closed {
                    Some(value.as_ref())
                } else {
                    None
                };
                self.infer_application_type(
                    formal,
                    actual,
                    child_schema(child)?,
                    inference,
                    scope,
                    depth + 1,
                )?;
            }
            (TypeKind::Tuple(formals), Ty::Tuple(actuals)) if formals.len() == actuals.len() => {
                for (index, (formal, actual)) in formals.iter().zip(actuals).enumerate() {
                    let child = if let Some(TypeKind::Tuple(values)) = closed {
                        values.get(index)
                    } else {
                        None
                    };
                    self.infer_application_type(
                        formal,
                        actual,
                        child_schema(child)?,
                        inference,
                        scope,
                        depth + 1,
                    )?;
                }
            }
            (TypeKind::Record { fields, row: None }, Ty::Record(actuals)) => {
                for formal in fields {
                    let actual = actuals
                        .get(&formal.name)
                        .ok_or_else(|| mismatch("static argument is missing a required field"))?;
                    let child = if let Some(TypeKind::Record { fields, .. }) = closed {
                        fields
                            .iter()
                            .find(|field| field.name == formal.name)
                            .map(|field| &field.ty)
                    } else {
                        None
                    };
                    self.infer_application_type(
                        &formal.ty,
                        &actual.1,
                        child_schema(child)?,
                        inference,
                        scope,
                        depth + 1,
                    )?;
                }
            }
            (TypeKind::Name { path, arguments }, Ty::Result(ok, error))
                if normalized_path(path) == "Result" && arguments.len() == 2 =>
            {
                for (index, actual) in [ok.as_ref(), error.as_ref()].into_iter().enumerate() {
                    let child = if let Some(TypeKind::Name { arguments, .. }) = closed {
                        arguments.get(index)
                    } else {
                        None
                    };
                    self.infer_application_type(
                        &arguments[index],
                        actual,
                        child_schema(child)?,
                        inference,
                        scope,
                        depth + 1,
                    )?;
                }
            }
            (TypeKind::Name { path, arguments }, Ty::Optional(actual))
                if normalized_path(path) == "Option" && arguments.len() == 1 =>
            {
                let child = match closed {
                    Some(TypeKind::Optional(value)) => Some(value.as_ref()),
                    Some(TypeKind::Name { arguments, .. }) => arguments.first(),
                    _ => None,
                };
                self.infer_application_type(
                    &arguments[0],
                    actual,
                    child_schema(child)?,
                    inference,
                    scope,
                    depth + 1,
                )?;
            }
            _ => {}
        }
        Ok(())
    }

    fn actual_bound_shape(
        &self,
        id: &StaticBinderId,
        scope: &BoundEnvironment,
        caller: &BoundEnvironment,
    ) -> Result<Row<SchemaField>> {
        if let Some(schema) = scope.selected_types.get(id) {
            let TypeKind::Record { fields, row: None } = &schema.syntax.kind else {
                return Err(mismatch(
                    "static type argument does not satisfy its structural bound",
                ));
            };
            return Ok(Row::closed(
                fields
                    .iter()
                    .map(|field| {
                        Ok((
                            field.name.clone(),
                            (field.mutable, self.schema_field(&field.ty, scope)?),
                        ))
                    })
                    .collect::<Result<_>>()?,
            ));
        }
        let Some(actual @ Ty::Generic(_)) = scope.type_arguments.get(id) else {
            return Err(missing(
                "static structural argument has no complete schema or rigid caller bound",
            ));
        };
        let view = self
            .bound_view(actual, caller)
            .ok_or_else(|| missing("static caller parameter has no structural bound promise"))?;
        let mut fields = view
            .fields
            .iter()
            .map(|(name, field)| {
                Ok((
                    name.clone(),
                    (field.mutable, self.schema_field(&field.syntax, caller)?),
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        if let Some(row_id) = &view.row {
            if let Some(selected) = caller.row_arguments.get(row_id) {
                for (name, field) in &selected.fields {
                    if fields.insert(name.clone(), field.clone()).is_some() {
                        return Err(mismatch("static caller row overlaps its known fields"));
                    }
                }
                return Ok(Row {
                    fields,
                    tail: selected.tail.clone(),
                });
            }
            return Ok(Row::open(
                fields,
                self.bound_row_identity(actual, caller)
                    .ok_or_else(|| missing("static caller row identity is unavailable"))?,
            ));
        }
        Ok(Row::closed(fields))
    }

    pub(super) fn check_function_application(
        &self,
        function: &Function,
        application: TypeApplication<'_>,
    ) -> Result<BoundEnvironment> {
        let TypeApplication {
            actual_types,
            actual_schemas,
            plan,
            captured,
            caller,
            explicit,
            expected,
            instance,
        } = application;
        let admission = budget::Budget::default();
        caller.admit_with_types(&admission, actual_types)?;
        if actual_types.len() != actual_schemas.len()
            || plan.slots.len() != function.parameters.len()
        {
            return Err(missing(
                "static type application does not cover its real argument plan",
            ));
        }
        if actual_types.len() > 4096 {
            return Err(missing(
                "static type application exceeds its finite argument allowance",
            ));
        }
        for schema in actual_schemas.iter().flatten() {
            let checked = self
                .complete_source_syntax(&schema.syntax, &BoundEnvironment::default())?
                .ok_or_else(|| missing("static argument root schema is not complete"))?;
            if checked.key != schema.key {
                return Err(missing("static argument root schema key is inconsistent"));
            }
        }
        if explicit.len() > function.generics.len() {
            return Err(Failure::Diagnostic(
                "E0340",
                "too many static type arguments".into(),
            ));
        }
        let mut scope = self.function_generic_environment(function, captured)?;
        scope.type_ids.extend(caller.type_ids.clone());
        scope.const_ids.extend(caller.const_ids.clone());
        for (id, selected) in &caller.const_arguments {
            if id.declaration != function.name {
                scope.const_arguments.insert(id.clone(), selected.clone());
            }
        }
        scope.views.extend(caller.views.clone());
        scope.rows.extend(caller.rows.clone());
        // A recursive application reuses the lexical declarations, while its
        // selected residual and type arguments belong to this new activation.
        scope
            .selected_rows
            .retain(|id, _| id.declaration != function.name);
        scope
            .row_arguments
            .retain(|id, _| id.declaration != function.name);
        for (index, parameter) in function.generics.iter().enumerate() {
            if scope
                .const_binders
                .get(&parameter.name)
                .is_some_and(Option::is_some)
            {
                if let Some(syntax) = explicit.get(index) {
                    self.select_const_argument(&parameter.name, syntax, caller, &mut scope)?;
                }
                continue;
            }
            let id = scope.type_binders[&parameter.name].clone();
            scope.selected_types.remove(&id);
            scope.type_arguments.remove(&id);
            if let Some(syntax) = explicit.get(index) {
                let actual = self.bound_type(syntax, caller)?;
                let schema = self.complete_source_syntax(syntax, caller)?;
                self.select_type_argument(&id, &actual, schema, caller, &mut scope)?;
            }
        }
        for (parameter, slot) in function.parameters.iter().zip(&plan.slots) {
            if let application::ArgumentSlot::Explicit(index) = slot {
                let actual = actual_types
                    .get(*index)
                    .ok_or_else(|| missing("static argument plan index is invalid"))?;
                let formal = parameter
                    .ty
                    .as_ref()
                    .ok_or_else(|| missing("static parameter has no declared type"))?;
                self.infer_application_type(
                    formal,
                    actual,
                    actual_schemas[*index].clone(),
                    ApplicationInference {
                        caller,
                        declaration: &function.name,
                    },
                    &mut scope,
                    0,
                )?;
            }
        }
        for parameter in &function.generics {
            if let Some(Some(id)) = scope.const_binders.get(&parameter.name) {
                if !scope.const_arguments.contains_key(id)
                    && let Some(default) = &parameter.default
                {
                    let lexical = scope.clone();
                    self.select_const_argument(&parameter.name, default, &lexical, &mut scope)?;
                }
                continue;
            }
            let id = scope.type_binders[&parameter.name].clone();
            if !scope.type_arguments.contains_key(&id)
                && let Some(default) = &parameter.default
            {
                let actual = self.bound_type(default, &scope)?;
                let schema = self.complete_source_syntax(default, &scope)?;
                self.select_type_argument(&id, &actual, schema, caller, &mut scope)?;
            }
        }
        self.infer_bound_type_dependencies(function, caller, &mut scope)?;
        self.infer_application_result_context(function, expected, &mut scope)?;
        self.infer_bound_type_dependencies(function, caller, &mut scope)?;
        let flexible: BTreeMap<_, _> = scope
            .rows
            .iter()
            .filter(|(id, row)| {
                id.declaration == function.name
                    && row
                        .declared_type
                        .as_ref()
                        .is_none_or(|ty| ty.declaration == function.name)
            })
            .map(|(id, _)| {
                (
                    id.clone(),
                    RowIdentity::Fresh {
                        owner: format!(
                            "static:{}:{}:activation:{}:row:{}",
                            function.name.len(),
                            function.name,
                            instance,
                            id.ordinal
                        ),
                        ordinal: 0,
                    },
                )
            })
            .collect();
        let mut solver = Solver::new(
            format!("static:{}:{instance}", function.name),
            flexible.values().cloned(),
        );
        for row in caller.rows.values() {
            solver
                .declare_rigid(row.identity.clone(), row.lacks.clone())
                .map_err(row_failure)?;
        }
        for (id, row) in &scope.rows {
            if !flexible.contains_key(id) {
                solver
                    .declare_rigid(row.identity.clone(), row.lacks.clone())
                    .map_err(row_failure)?;
            }
        }
        let mut solved_rows = BTreeSet::<StaticRowId>::new();
        for parameter in &function.generics {
            if !scope.type_binders.contains_key(&parameter.name) {
                continue;
            }
            let id = scope.type_binders[&parameter.name].clone();
            let Some(view) = scope.views.get(&id).cloned() else {
                continue;
            };
            let actual = self.actual_bound_shape(&id, &scope, caller)?;
            let mut fields = view
                .fields
                .iter()
                .map(|(name, field)| {
                    Ok((
                        name.clone(),
                        (field.mutable, self.schema_field(&field.syntax, &scope)?),
                    ))
                })
                .collect::<Result<BTreeMap<_, _>>>()?;
            let residual = if let Some(row_id) = &view.row {
                let declaration = &scope.rows[row_id];
                let fixed = declaration
                    .declared_type
                    .as_ref()
                    .and_then(|id| scope.selected_types.get(id))
                    .or_else(|| scope.selected_rows.get(row_id))
                    .cloned();
                if let Some(fixed) = fixed {
                    let TypeKind::Record {
                        fields: extra,
                        row: None,
                    } = &fixed.syntax.kind
                    else {
                        return Err(mismatch(
                            "static residual selection is not a closed structural record",
                        ));
                    };
                    let mut fixed_fields = BTreeMap::new();
                    for field in extra {
                        let selected = self.schema_field(&field.ty, &scope)?;
                        if fields
                            .insert(field.name.clone(), (field.mutable, selected.clone()))
                            .is_some()
                        {
                            return Err(mismatch("static residual overlaps a required field"));
                        }
                        fixed_fields.insert(field.name.clone(), (field.mutable, selected));
                    }
                    scope
                        .row_arguments
                        .insert(row_id.clone(), Row::closed(fixed_fields));
                    scope.selected_rows.insert(row_id.clone(), fixed.clone());
                    solved_rows.insert(row_id.clone());
                    None
                } else {
                    Some(OpenTail {
                        identity: flexible
                            .get(row_id)
                            .cloned()
                            .unwrap_or_else(|| declaration.identity.clone()),
                        lacks: declaration.lacks.clone(),
                    })
                }
            } else {
                None
            };
            crate::sema::record_bound_shapes::entail(
                &mut solver,
                &fields,
                residual.as_ref(),
                &actual,
            )
            .map_err(row_failure)?;
            if let Some(row_id) = &view.row
                && let Some(tail) = residual
            {
                let remainder = solver
                    .normalize(&Row::open(BTreeMap::new(), tail))
                    .map_err(row_failure)?;
                scope.row_arguments.insert(row_id.clone(), remainder);
                solved_rows.insert(row_id.clone());
            }
        }
        for row_id in solved_rows {
            let row = solver
                .normalize(&scope.row_arguments[&row_id])
                .map_err(row_failure)?;
            if let RowTail::Closed = &row.tail {
                let syntax = row_syntax(&row, function.span)?;
                let witness = self
                    .complete_source_syntax(&syntax, &scope)?
                    .ok_or_else(|| {
                        missing("closed static residual has unresolved member syntax")
                    })?;
                scope.selected_rows.insert(row_id.clone(), witness.clone());
                if let Some(id) = &scope.rows[&row_id].declared_type {
                    let actual =
                        self.ty_seen(&witness.syntax, &scope.values, &mut BTreeSet::new())?;
                    scope.type_arguments.insert(id.clone(), actual);
                    scope.selected_types.insert(id.clone(), witness);
                }
            }
            scope.row_arguments.insert(row_id, row);
        }
        for parameter in &function.generics {
            if let Some(Some(id)) = scope.const_binders.get(&parameter.name) {
                if !scope.const_arguments.contains_key(id) {
                    return Err(Failure::Diagnostic(
                        "E0344",
                        "static int parameter has no selected value argument".into(),
                    ));
                }
                continue;
            }
            let id = &scope.type_binders[&parameter.name];
            if !scope.type_arguments.contains_key(id) {
                if scope
                    .row_context
                    .get(&parameter.name)
                    .and_then(|row| scope.row_arguments.get(row))
                    .is_some_and(|row| matches!(row.tail, RowTail::Open(_)))
                {
                    return Err(missing(
                        "static composite open residual needs its complete symbolic type selection",
                    ));
                }
                return Err(Failure::Diagnostic(
                    "E0344",
                    "static generic argument is not determined by the application constraints"
                        .into(),
                ));
            }
        }
        for (parameter, slot) in function.parameters.iter().zip(&plan.slots) {
            if let application::ArgumentSlot::Explicit(index) = slot {
                let syntax = parameter.ty.as_ref().unwrap();
                let formal = self.bound_type(syntax, &scope)?;
                let whole_type_parameter = matches!(&syntax.kind, TypeKind::Name { path, arguments }
                    if path.len() == 1 && arguments.is_empty() && scope.type_binders.contains_key(&path[0]));
                if let Some(actual_schema) = &actual_schemas[*index] {
                    let required_schema = self
                        .complete_source_syntax(syntax, &scope)?
                        .ok_or_else(|| missing("static formal root schema remains unresolved"))?;
                    if !schema_receives(&actual_schema.syntax, &required_schema.syntax, false, 0) {
                        return Err(mismatch(
                            "complete static argument schema does not satisfy its formal dimensions, modes or qualifications",
                        ));
                    }
                } else if !whole_type_parameter && contains_erased_source_information(&formal) {
                    return Err(missing(
                        "static formal array or callable requires the complete root schema",
                    ));
                }
                let actual = if whole_type_parameter {
                    actual_schemas[*index]
                        .as_ref()
                        .map(|schema| self.bound_type(&schema.syntax, caller))
                        .transpose()?
                        .unwrap_or_else(|| caller.canonical_type(actual_types[*index].clone()))
                } else {
                    caller.canonical_type(actual_types[*index].clone())
                };
                require(&actual, &formal)?;
            }
        }
        self.check_application_result_context(function, expected, &scope)?;
        Ok(scope)
    }
}

fn row_failure(error: crate::sema::model::rows::RowError) -> Failure {
    use crate::sema::model::rows::RowError;
    match error {
        RowError::Budget | RowError::UnprovedAbsence { .. } | RowError::Rigid(_) => {
            missing("static row entailment needs an unresolved rigid-row proof")
        }
        _ => mismatch("static type arguments do not satisfy one shared residual equation"),
    }
}
pub(in crate::static_eval::typing) fn contains_erased_source_information(ty: &Ty) -> bool {
    match ty {
        Ty::Array(..) | Ty::Callable(..) => true,
        Ty::Map(key, value) | Ty::Result(key, value) => {
            contains_erased_source_information(key) || contains_erased_source_information(value)
        }
        Ty::Optional(inner) => contains_erased_source_information(inner),
        Ty::Tuple(items) => items.iter().any(contains_erased_source_information),
        Ty::Record(fields) => fields
            .values()
            .any(|(_, ty)| contains_erased_source_information(ty)),
        _ => false,
    }
}
pub(in crate::static_eval::typing) fn schema_receives(
    actual: &TypeExpr,
    expected: &TypeExpr,
    invariant: bool,
    depth: usize,
) -> bool {
    if depth >= 64 {
        return false;
    }
    if normalized_argument_key(actual) == normalized_argument_key(expected) {
        return true;
    }
    match (&actual.kind, &expected.kind) {
        (
            TypeKind::Array {
                element: actual,
                length: actual_length,
            },
            TypeKind::Array {
                element: expected,
                length: expected_length,
            },
        ) => {
            let length_matches = match (actual_length, expected_length) {
                (_, None) if !invariant => true,
                (None, None) => true,
                (Some(actual), Some(expected)) => actual.kind == expected.kind,
                _ => false,
            };
            length_matches && schema_receives(actual, expected, invariant, depth + 1)
        }
        (TypeKind::Optional(actual), TypeKind::Optional(expected)) => {
            schema_receives(actual, expected, invariant, depth + 1)
        }
        (TypeKind::Tuple(actual), TypeKind::Tuple(expected)) if actual.len() == expected.len() => {
            actual
                .iter()
                .zip(expected)
                .all(|(a, e)| schema_receives(a, e, invariant, depth + 1))
        }
        (
            TypeKind::Record {
                fields: actual,
                row: None,
            },
            TypeKind::Record {
                fields: expected,
                row: None,
            },
        ) if actual.len() == expected.len() => expected.iter().all(|expected| {
            actual
                .iter()
                .find(|actual| actual.name == expected.name)
                .is_some_and(|actual| {
                    actual.mutable == expected.mutable
                        && schema_receives(
                            &actual.ty,
                            &expected.ty,
                            invariant || expected.mutable,
                            depth + 1,
                        )
                })
        }),
        (TypeKind::Map { key: ak, value: av }, TypeKind::Map { key: ek, value: ev }) => {
            schema_receives(ak, ek, invariant, depth + 1)
                && schema_receives(av, ev, invariant, depth + 1)
        }
        (
            TypeKind::Name {
                path: actual_path,
                arguments: actual,
            },
            TypeKind::Name {
                path: expected_path,
                arguments: expected,
            },
        ) if actual_path == expected_path && actual.len() == expected.len() => actual
            .iter()
            .zip(expected)
            .all(|(a, e)| schema_receives(a, e, invariant, depth + 1)),
        _ => false,
    }
}
fn without_storage_lengths(ty: Ty) -> Ty {
    match ty {
        Ty::Array(inner, _) => Ty::Array(Box::new(without_storage_lengths(*inner)), None),
        Ty::Optional(inner) => Ty::Optional(Box::new(without_storage_lengths(*inner))),
        Ty::Map(key, value) => Ty::Map(
            Box::new(without_storage_lengths(*key)),
            Box::new(without_storage_lengths(*value)),
        ),
        Ty::Result(ok, error) => Ty::Result(
            Box::new(without_storage_lengths(*ok)),
            Box::new(without_storage_lengths(*error)),
        ),
        Ty::Tuple(items) => Ty::Tuple(items.into_iter().map(without_storage_lengths).collect()),
        Ty::Record(fields) => Ty::Record(
            fields
                .into_iter()
                .map(|(name, (mutable, ty))| (name, (mutable, without_storage_lengths(ty))))
                .collect(),
        ),
        Ty::Callable(parameters, result, interfaces) => Ty::Callable(
            parameters
                .into_iter()
                .map(without_storage_lengths)
                .collect(),
            Box::new(without_storage_lengths(*result)),
            interfaces,
        ),
        ty => ty,
    }
}
fn row_syntax(row: &Row<SchemaField>, span: Span) -> Result<TypeExpr> {
    if !row.is_closed() {
        return Err(missing("an open static residual is not a closed type"));
    }
    Ok(TypeExpr {
        text: String::new(),
        span,
        kind: TypeKind::Record {
            fields: row
                .fields
                .iter()
                .map(|(name, (mutable, field))| ril_syntax::ast::TypeField {
                    name: name.clone(),
                    mutable: *mutable,
                    ty: (*field.syntax).clone(),
                    span,
                })
                .collect(),
            row: None,
        },
    })
}

/// This deliberately has no Array or Callable arm. Their erased Ty stores
/// insufficient information to reconstruct a declared complete schema.
pub(super) fn lossless_syntax(ty: &Ty, span: Span) -> Option<TypeExpr> {
    let kind = match ty {
        Ty::Generic(identity) => TypeKind::Name {
            path: vec![identity.clone()],
            arguments: vec![],
        },
        Ty::Unit => TypeKind::Tuple(vec![]),
        Ty::Bool | Ty::String | Ty::Bytes | Ty::Never | Ty::IntegerConstant(_) | Ty::Number(_) => {
            return reify_type(ty, span).ok();
        }
        Ty::Tuple(items) => TypeKind::Tuple(
            items
                .iter()
                .map(|ty| lossless_syntax(ty, span))
                .collect::<Option<_>>()?,
        ),
        Ty::Record(fields) => TypeKind::Record {
            fields: fields
                .iter()
                .map(|(name, (mutable, ty))| {
                    Some(ril_syntax::ast::TypeField {
                        name: name.clone(),
                        mutable: *mutable,
                        ty: lossless_syntax(ty, span)?,
                        span,
                    })
                })
                .collect::<Option<_>>()?,
            row: None,
        },
        Ty::Optional(inner) => TypeKind::Optional(Box::new(lossless_syntax(inner, span)?)),
        Ty::Result(ok, error) => TypeKind::Name {
            path: vec!["Result".into()],
            arguments: vec![lossless_syntax(ok, span)?, lossless_syntax(error, span)?],
        },
        _ => return None,
    };
    Some(TypeExpr {
        kind,
        text: String::new(),
        span,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn evaluator(source: &str) -> Evaluator {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let collected = definitions::collect(&parsed.program);
        Evaluator {
            type_environment: Default::default(),
            type_application_sequence: 0,
            layout: TargetLayout::POINTER64,
            values: BTreeMap::new(),
            global_values: BTreeMap::new(),
            budget: budget::Budget::default(),
            declarations: collected.all_types,
            effect_declarations: collected.all_effects,
            functions: collected.all_functions,
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
        }
    }
    fn unexpected(failure: Failure) -> ! {
        match failure {
            Failure::Diagnostic(code, reason) => panic!("{code}: {reason}"),
            Failure::Unsupported(reason) => panic!("not implemented: {reason}"),
            _ => panic!("unexpected static control flow"),
        }
    }
    fn closed_application(
        checker: &Typer<'_>,
        name: &str,
        aliases: &[&str],
        instance: u64,
    ) -> Result<BoundEnvironment> {
        let function = &checker.evaluator.functions[name];
        let caller = BoundEnvironment::default();
        let schemas = aliases
            .iter()
            .map(|name| {
                checker.complete_source_syntax(
                    checker.evaluator.declarations[*name]
                        .value
                        .as_ref()
                        .unwrap(),
                    &caller,
                )
            })
            .collect::<Result<Vec<_>>>()?;
        let actual = schemas
            .iter()
            .map(|schema| checker.bound_type(&schema.as_ref().unwrap().syntax, &caller))
            .collect::<Result<Vec<_>>>()?;
        let plan = application::StaticApplicationPlan::new(
            &function
                .parameters
                .iter()
                .map(application::ParameterSpec::from)
                .collect::<Vec<_>>(),
            aliases.iter().map(|_| None),
        )?;
        checker.check_function_application(
            function,
            TypeApplication {
                actual_types: &actual,
                actual_schemas: &schemas,
                plan: &plan,
                captured: &caller,
                caller: &caller,
                explicit: &[],
                expected: None,
                instance,
            },
        )
    }
    #[test]
    fn complete_closed_argument_selects_exact_shared_residual_and_return_type() {
        let evaluator = evaluator(
            "type Input={id:int,mut tag:str}\nmeta fn read<T:{id:int,..R}>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let scope = closed_application(&checker, "read", &["Input"], 17)
            .unwrap_or_else(|failure| unexpected(failure));
        let row = &scope.selected_rows[&scope.row_context["R"]];
        assert!(
            matches!(&row.syntax.kind, TypeKind::Record { fields, row: None }
            if fields.len() == 1 && fields[0].name == "tag" && fields[0].mutable)
        );
        let returned = checker
            .complete_source_syntax(
                evaluator.functions["read"].return_type.as_ref().unwrap(),
                &scope,
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert_eq!(
            returned.key,
            scope.selected_types[&scope.type_binders["T"]].key
        );
    }
    #[test]
    fn one_application_cannot_select_two_different_shared_residuals() {
        let evaluator = evaluator(
            "type Left={id:int,tag:str}\ntype Right={flag:bool,tag:int}\nmeta fn both<T:{id:int,..R},U:{flag:bool,..R}>(left:T,right:U)->int{left.id}",
        );
        let checker = Typer::new(&evaluator, None);
        assert!(matches!(
            closed_application(&checker, "both", &["Left", "Right"], 19),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }
    #[test]
    fn identical_erased_storage_does_not_erase_empty_array_dimensions() {
        let evaluator = evaluator(
            "type Left=[0][2]int\ntype Right=[0][3]int\nmeta fn same<T>(left:T,right:T)->T{left}",
        );
        let checker = Typer::new(&evaluator, None);
        assert!(matches!(
            closed_application(&checker, "same", &["Left", "Right"], 23),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }
    #[test]
    fn rigid_caller_tail_stays_open_and_each_real_activation_is_separate() {
        let evaluator = evaluator(
            "meta fn caller<U:{id:int,tag:str,..S}>(value:U)->int{value.id}\nmeta fn read<T:{id:int,..R}>(value:T)->int{value.id}",
        );
        let checker = Typer::new(&evaluator, None);
        let caller = checker
            .function_generic_environment(
                &evaluator.functions["caller"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let actual = checker
            .bound_type(
                evaluator.functions["caller"].parameters[0]
                    .ty
                    .as_ref()
                    .unwrap(),
                &caller,
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let function = &evaluator.functions["read"];
        let plan = application::StaticApplicationPlan::new(
            &[application::ParameterSpec::from(&function.parameters[0])],
            [None],
        )
        .unwrap_or_else(|failure| unexpected(failure));
        for instance in [29, 31] {
            let scope = checker
                .check_function_application(
                    function,
                    TypeApplication {
                        actual_types: std::slice::from_ref(&actual),
                        actual_schemas: &[None],
                        plan: &plan,
                        captured: &BoundEnvironment::default(),
                        caller: &caller,
                        explicit: &[],
                        expected: None,
                        instance,
                    },
                )
                .unwrap_or_else(|failure| unexpected(failure));
            let row_id = &scope.row_context["R"];
            assert!(!scope.selected_rows.contains_key(row_id));
            assert!(
                matches!(&scope.row_arguments[row_id].tail, RowTail::Open(tail)
                if tail.identity == caller.rows[&caller.row_context["S"]].identity)
            );
            assert!(scope.row_arguments[row_id].fields.contains_key("tag"));
        }
    }
    fn last_initializer(source: &str) -> Expr {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let StmtKind::Binding(binding) = &parsed.program.statements.last().unwrap().kind else {
            panic!("binding required")
        };
        binding.value.clone()
    }
    #[test]
    fn named_structural_application_checks_real_arguments_without_evaluating_the_body() {
        let source = "meta fn read<T:{id:int,..R}>(value:T)->int{value.id}\nmeta let ANSWER=read(.{id:7,tag:\"ok\"})";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert_eq!(
            checker
                .expr(&last_initializer(source), &mut Env::new())
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("int".into())
        );
    }
    #[test]
    fn named_forwarding_keeps_the_callers_rigid_generic_identity() {
        let source = "meta fn outer<U:{id:int,tag:str,..S}>(value:U)->int{read(value)}\nmeta fn read<T:{id:int,..R}>(value:T)->int{value.id}";
        let evaluator = evaluator(source);
        let initial = Typer::new(&evaluator, None);
        let scope = initial
            .function_generic_environment(
                &evaluator.functions["outer"],
                &bounds::BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let checker = Typer::with_bound_environment(&evaluator, None, Arc::new(scope.clone()));
        let mut env = scope.values.clone();
        env.insert(
            "value".into(),
            checker
                .bound_type(
                    evaluator.functions["outer"].parameters[0]
                        .ty
                        .as_ref()
                        .unwrap(),
                    &scope,
                )
                .unwrap_or_else(|failure| unexpected(failure)),
        );
        let body = evaluator.functions["outer"].body.as_ref().unwrap();
        assert_eq!(
            checker
                .block_expected(body, &mut env, None)
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("int".into())
        );
    }
    #[test]
    fn local_annotations_preserve_complete_empty_array_schema_in_named_inference() {
        let source = "meta fn same<T>(left:T,right:T)->T{left}\nmeta let ANSWER={let left:[0][2]int=[];let right:[0][3]int=[];same(left,right)}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert!(matches!(
            checker.expr(&last_initializer(source), &mut Env::new()),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }
    #[test]
    fn lexical_unknown_schema_shadows_a_same_named_complete_global() {
        let mut evaluator =
            evaluator("type Matrix=[0][2]int\nmeta fn accept<T>(value:T)->T{value}");
        let schema = {
            let checker = Typer::new(&evaluator, None);
            checker
                .complete_source_syntax(
                    evaluator.declarations["Matrix"].value.as_ref().unwrap(),
                    &BoundEnvironment::default(),
                )
                .unwrap_or_else(|failure| unexpected(failure))
                .unwrap()
        };
        evaluator.global_values.insert(
            "value".into(),
            StaticValue::Array(StaticCollection {
                id: 0,
                values: Arc::new(vec![]),
                source_type: Some(schema.clone()),
            }),
        );
        let checker = Typer::new(&evaluator, None);
        let expression = Expr {
            kind: ExprKind::Name("value".into()),
            span: schema.syntax.span,
        };
        let ty = checker
            .bound_type(&schema.syntax, &BoundEnvironment::default())
            .unwrap_or_else(|failure| unexpected(failure));
        let mut env = Env::new();
        assert!(
            checker
                .expression_source_schema(&expression, &ty, &env, &BoundEnvironment::default(), 0)
                .unwrap_or_else(|failure| unexpected(failure))
                .is_some()
        );
        checker
            .bind(
                &Pattern {
                    kind: PatternKind::Name("value".into()),
                    span: schema.syntax.span,
                },
                ty.clone(),
                &mut env,
            )
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(
            checker
                .expression_source_schema(&expression, &ty, &env, &BoundEnvironment::default(), 0)
                .unwrap_or_else(|failure| unexpected(failure))
                .is_none()
        );
        checker
            .bind_source_schema(
                &Pattern {
                    kind: PatternKind::Name("value".into()),
                    span: schema.syntax.span,
                },
                Some(schema.clone()),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            checker
                .expression_source_schema(&expression, &ty, &env, &BoundEnvironment::default(), 0)
                .unwrap_or_else(|failure| unexpected(failure))
                .unwrap()
                .key,
            schema.key
        );
    }
    #[test]
    fn a_dynamic_root_does_not_become_fixed_when_its_current_backing_has_two_items() {
        let evaluator = evaluator("type Dynamic=[]int\nmeta fn first<T>(value:[2]T)->T{value[0]}");
        let checker = Typer::new(&evaluator, None);
        let scope = BoundEnvironment::default();
        let schema = checker
            .complete_source_syntax(
                evaluator.declarations["Dynamic"].value.as_ref().unwrap(),
                &scope,
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        let function = &evaluator.functions["first"];
        let plan = application::StaticApplicationPlan::new(
            &[application::ParameterSpec::from(&function.parameters[0])],
            [None],
        )
        .unwrap_or_else(|failure| unexpected(failure));
        let actual = [Ty::Array(Box::new(Ty::Number("int".into())), Some(2))];
        assert!(matches!(
            checker.check_function_application(
                function,
                TypeApplication {
                    actual_types: &actual,
                    actual_schemas: &[Some(schema)],
                    plan: &plan,
                    captured: &scope,
                    caller: &scope,
                    explicit: &[],
                    expected: None,
                    instance: 37,
                }
            ),
            Err(Failure::Diagnostic("E0301", _))
        ));
        assert!(matches!(
            checker.check_function_application(
                function,
                TypeApplication {
                    actual_types: &actual,
                    actual_schemas: &[None],
                    plan: &plan,
                    captured: &scope,
                    caller: &scope,
                    explicit: &[],
                    expected: None,
                    instance: 41,
                }
            ),
            Err(Failure::Unsupported(_))
        ));
    }
    #[test]
    fn nested_callable_modes_are_checked_against_the_complete_root_schema() {
        let evaluator =
            evaluator("meta fn accept<T>(operation:fn(value:int)->int,other:T)->T{other}");
        let checker = Typer::new(&evaluator, None);
        let scope = BoundEnvironment::default();
        let function = &evaluator.functions["accept"];
        let declared = function.parameters[0].ty.as_ref().unwrap();
        let actual_ty = checker
            .bound_type(declared, &scope)
            .unwrap_or_else(|failure| unexpected(failure));
        let mut changed = declared.clone();
        let TypeKind::Callable { parameters, .. } = &mut changed.kind else {
            unreachable!()
        };
        parameters[0].mode = ParameterMode::Mut;
        let schema = checker
            .complete_source_syntax(&changed, &scope)
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        let plan = application::StaticApplicationPlan::new(
            &function
                .parameters
                .iter()
                .map(application::ParameterSpec::from)
                .collect::<Vec<_>>(),
            [None, None],
        )
        .unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(
            checker.check_function_application(
                function,
                TypeApplication {
                    actual_types: &[actual_ty, Ty::Number("int".into())],
                    actual_schemas: &[Some(schema), None],
                    plan: &plan,
                    captured: &scope,
                    caller: &scope,
                    explicit: &[],
                    expected: None,
                    instance: 43,
                }
            ),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }
    #[test]
    fn a_fresh_literal_receives_the_formals_declared_fixed_construction_context() {
        let source = "meta fn first<T>(value:[2]T)->T{value[0]}\nmeta let ANSWER=first([1,2])";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert_eq!(
            checker
                .expr(&last_initializer(source), &mut Env::new())
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("int".into())
        );
    }
    fn evaluated_initializer(source: &str) -> Result<StaticValue> {
        let mut evaluator = evaluator(source);
        let expression = last_initializer(source);
        evaluator.evaluation_root(|evaluator| {
            let functions = evaluator
                .functions
                .values()
                .filter(|function| function.generics.is_empty())
                .cloned()
                .collect::<Vec<_>>();
            for function in functions {
                evaluator.static_signature(&function)?;
            }
            evaluator.expression(&expression)
        })
    }
    #[test]
    fn actual_named_structural_application_runs_with_complete_selected_types() {
        let value = evaluated_initializer("meta fn read<T:{id:int,..R}>(value:T)->int{value.id}\nmeta let ANSWER=read(.{id:7,tag:\"ok\"})")
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(value, StaticValue::Integer(7)));
        let value = evaluated_initializer(
            "meta fn first<T>(value:[2]T)->T{value[0]}\nmeta let ANSWER=first([7,8])",
        )
        .unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(value, StaticValue::Integer(7)));
    }
    #[test]
    fn actual_generic_receiving_keeps_the_second_callables_labels_and_defaults() {
        let source = "meta fn first(left:int=1)->int{left}\nmeta fn second(right:int=2)->int{right}\nmeta fn choose<T>(left:T,right:T)->T{right}\nmeta let ANSWER={let callback=choose(first,second);callback(right:7)+callback()}";
        let value = evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(value, StaticValue::Integer(9)));
    }
    #[test]
    fn actual_generic_alias_wrapping_keeps_nested_callable_interfaces() {
        let source = "type Box<T>={item:T}\nmeta fn first(left:int=1)->int{left}\nmeta fn second(right:int=2)->int{right}\nmeta fn wrap<T>(left:T,right:T)->Box<T>{.{item:right}}\nmeta let ANSWER={let wrapped=wrap(first,second);wrapped.item(right:7)+wrapped.item()}";
        let value = evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(value, StaticValue::Integer(9)));
    }
    #[test]
    fn pure_generic_return_summary_keeps_the_returned_callables_interface() {
        let source = "meta fn first(left:int=1)->int{left}\nmeta fn second(right:int=2)->int{right}\nmeta fn choose<T>(left:T,right:T)->T{right}\nmeta let ANSWER={let callback=choose(first,second);callback(right:7)+callback()}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert_eq!(
            checker
                .expr(&last_initializer(source), &mut Env::new())
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("int".into())
        );
    }
    #[test]
    fn pure_generic_alias_result_summary_keeps_nested_callable_interfaces() {
        let source = "type Box<T>={item:T}\nmeta fn first(left:int=1)->int{left}\nmeta fn second(right:int=2)->int{right}\nmeta fn wrap<T>(left:T,right:T)->Box<T>{.{item:right}}\nmeta let ANSWER={let wrapped=wrap(first,second);wrapped.item(right:7)+wrapped.item()}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert_eq!(
            checker
                .expr(&last_initializer(source), &mut Env::new())
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("int".into())
        );
    }
    #[test]
    fn an_explicit_callable_receiving_type_still_replaces_labels_and_erases_defaults() {
        for ending in ["callback(right:7)", "callback()"] {
            let source = format!(
                "meta fn first(left:int=1)->int{{left}}\nmeta fn second(right:int=2)->int{{right}}\nmeta fn choose<T>(left:T,right:T)->T{{right}}\nmeta let ANSWER={{let callback:fn(renamed:int)->int=choose(first,second);{ending}}}"
            );
            let evaluator = evaluator(&source);
            let checker = Typer::new(&evaluator, None);
            let failure = checker.expr(&last_initializer(&source), &mut Env::new());
            assert!(matches!(
                failure,
                Err(Failure::Diagnostic("E0339" | "E0314", _))
            ));
        }
    }
    #[test]
    fn an_immutable_generic_receiving_mask_keeps_actual_nested_interfaces() {
        let evaluator = evaluator(
            "type Wrapped<X>=Immut<{item:X}>\nmeta fn first(left:int=1)->int{left}\nmeta fn second(right:int=2)->int{right}\nmeta fn receiver<T>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let scope = checker
            .function_generic_environment(
                &evaluator.functions["receiver"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let first = checker
            .function_ty("first", &Env::new())
            .unwrap_or_else(|failure| unexpected(failure));
        let second = checker
            .function_ty("second", &Env::new())
            .unwrap_or_else(|failure| unexpected(failure));
        let span = evaluator.functions["receiver"].span;
        let generic = TypeExpr {
            text: String::new(),
            span,
            kind: TypeKind::Name {
                path: vec!["T".into()],
                arguments: vec![],
            },
        };
        let direct = TypeExpr {
            text: String::new(),
            span,
            kind: TypeKind::Name {
                path: vec!["Immut".into()],
                arguments: vec![generic.clone()],
            },
        };
        let received = checker
            .receive_type_interfaces(second.clone(), &direct, &first, &scope)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(received, second);
        let wrapped = TypeExpr {
            text: String::new(),
            span,
            kind: TypeKind::Name {
                path: vec!["Wrapped".into()],
                arguments: vec![generic],
            },
        };
        let received = checker
            .receive_type_interfaces(
                Ty::Record(BTreeMap::from([("item".into(), (false, second.clone()))])),
                &wrapped,
                &Ty::Record(BTreeMap::from([("item".into(), (false, first))])),
                &scope,
            )
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            received,
            Ty::Record(BTreeMap::from([("item".into(), (false, second))]))
        );
    }
    #[test]
    fn an_immutable_explicit_callable_type_still_supplies_its_own_interface() {
        let evaluator = evaluator(
            "meta fn second(right:int=2)->int{right}\nmeta fn receiver<T>(value:T)->T{value}\nmeta fn typed(value:fn(renamed:int)->int)->int{value(1)}",
        );
        let checker = Typer::new(&evaluator, None);
        let scope = checker
            .function_generic_environment(
                &evaluator.functions["receiver"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let actual = checker
            .function_ty("second", &Env::new())
            .unwrap_or_else(|failure| unexpected(failure));
        let syntax = evaluator.functions["typed"].parameters[0]
            .ty
            .as_ref()
            .unwrap();
        let declared = checker
            .bound_type(syntax, &BoundEnvironment::default())
            .unwrap_or_else(|failure| unexpected(failure));
        let wrapped = TypeExpr {
            text: String::new(),
            span: syntax.span,
            kind: TypeKind::Name {
                path: vec!["Immut".into()],
                arguments: vec![syntax.clone()],
            },
        };
        assert_eq!(
            checker
                .receive_type_interfaces(actual, &wrapped, &declared, &scope)
                .unwrap_or_else(|failure| unexpected(failure)),
            declared
        );
    }
    #[test]
    fn fresh_structural_constructor_context_selects_i8_and_the_required_slot_mode() {
        let source = "meta fn read<T:{mut id:i8,..R}>(value:T)->i8{value.id}\nmeta let ANSWER=read(.{id:7,tag:\"ok\"})";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert_eq!(
            checker
                .expr(&last_initializer(source), &mut Env::new())
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("i8".into())
        );
        let value = evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(value, StaticValue::TypedInteger(7, 8, true)));
    }
    #[test]
    fn structural_constructor_context_does_not_reselect_a_stored_int() {
        let source = "meta fn read<T:{mut id:i8,..R}>(value:T)->i8{value.id}\nmeta let ANSWER={let stored=7;read(.{id:stored})}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert!(matches!(
            checker.expr(&last_initializer(source), &mut Env::new()),
            Err(Failure::Diagnostic("E0301", _))
        ));
        assert!(matches!(
            evaluated_initializer(source),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }

    #[test]
    fn bounded_members_select_complete_array_types_without_erasing_inner_dimensions() {
        let evaluator = evaluator(
            "type Input={item:[0][2]int,tag:str}\nmeta fn member<T:{item:U,..R},U>(value:T)->U{value.item}",
        );
        let checker = Typer::new(&evaluator, None);
        let selected = closed_application(&checker, "member", &["Input"], 71)
            .unwrap_or_else(|failure| unexpected(failure));
        let schema = &selected.selected_types[&selected.type_binders["U"]];
        assert!(
            matches!(&schema.syntax.kind, TypeKind::Array { length: Some(_), element }
            if matches!(&element.kind, TypeKind::Array { length: Some(_), .. }))
        );
        let returned = checker
            .complete_source_syntax(
                evaluator.functions["member"].return_type.as_ref().unwrap(),
                &selected,
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert_eq!(returned.key, schema.key);
    }

    #[test]
    fn bounded_member_dependencies_reach_their_fixed_point_in_declaration_independent_order() {
        let evaluator = evaluator(
            "type Input={item:{value:int,detail:str},tag:str}\nmeta fn nested<U:{value:int,..S},T:{item:U,..R}>(value:T)->int{value.item.value}",
        );
        let checker = Typer::new(&evaluator, None);
        let selected = closed_application(&checker, "nested", &["Input"], 73)
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(
            selected
                .type_arguments
                .contains_key(&selected.type_binders["U"])
        );
        assert!(
            selected.row_arguments[&selected.row_context["S"]]
                .fields
                .contains_key("detail")
        );
        assert!(
            selected.row_arguments[&selected.row_context["R"]]
                .fields
                .contains_key("tag")
        );
    }

    #[test]
    fn a_closed_declared_residual_selects_its_own_member_dependencies_and_keeps_row_receipts() {
        let evaluator = evaluator(
            "type Input={id:int,item:int,tag:str}\nmeta fn residual<T:{id:int,..R},R:{item:U,..S},U>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let selected = closed_application(&checker, "residual", &["Input"], 79)
            .unwrap_or_else(|failure| unexpected(failure));
        let row = &selected.row_context["R"];
        let ty = &selected.type_binders["R"];
        assert_eq!(
            selected.selected_rows[row].key,
            selected.selected_types[ty].key
        );
        assert_eq!(selected.row_arguments[row].fields.len(), 2);
        assert_eq!(
            selected.type_arguments[&selected.type_binders["U"]],
            Ty::Number("int".into())
        );
    }

    #[test]
    fn different_members_cannot_select_one_generic_twice() {
        let evaluator = evaluator(
            "type Left={item:int}\ntype Right={item:str}\nmeta fn pair<T:{item:U,..R},V:{item:U,..S},U>(left:T,right:V)->U{left.item}",
        );
        let checker = Typer::new(&evaluator, None);
        assert!(matches!(
            closed_application(&checker, "pair", &["Left", "Right"], 83),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }

    fn symbolic_member_application(
        checker: &Typer<'_>,
        caller_name: &str,
        callee_name: &str,
        explicit: &[TypeExpr],
        instance: u64,
    ) -> Result<(BoundEnvironment, BoundEnvironment)> {
        let caller_function = &checker.evaluator.functions[caller_name];
        let caller =
            checker.function_generic_environment(caller_function, &BoundEnvironment::default())?;
        let actual =
            checker.bound_type(caller_function.parameters[0].ty.as_ref().unwrap(), &caller)?;
        let callee = &checker.evaluator.functions[callee_name];
        let plan = application::StaticApplicationPlan::new(
            &[application::ParameterSpec::from(&callee.parameters[0])],
            [None],
        )?;
        let selected = checker.check_function_application(
            callee,
            TypeApplication {
                actual_types: &[actual],
                actual_schemas: &[None],
                plan: &plan,
                captured: &BoundEnvironment::default(),
                caller: &caller,
                explicit,
                expected: None,
                instance,
            },
        )?;
        Ok((caller, selected))
    }

    #[test]
    fn bounded_member_forwarding_keeps_the_callers_real_generic_identity() {
        let evaluator = evaluator(
            "meta fn caller<X:{item:Y,..S},Y>(value:X)->Y{value.item}\nmeta fn member<T:{item:U,..R},U>(value:T)->U{value.item}",
        );
        let checker = Typer::new(&evaluator, None);
        let (caller, selected) = symbolic_member_application(&checker, "caller", "member", &[], 89)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            selected.type_arguments[&selected.type_binders["U"]],
            Ty::Generic(caller.type_binders["Y"].key())
        );
        assert!(
            !selected
                .selected_types
                .contains_key(&selected.type_binders["U"])
        );
        assert_eq!(
            checker
                .bound_type(
                    evaluator.functions["member"].return_type.as_ref().unwrap(),
                    &selected
                )
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Generic(caller.type_binders["Y"].key())
        );
    }

    #[test]
    fn an_exact_open_residual_forwards_its_declared_caller_type_and_members() {
        let evaluator = evaluator(
            "meta fn caller<T:{id:int,..S},S:{item:V,..Q},V>(value:T)->T{value}\nmeta fn member<U:{id:int,..R},R:{item:W,..P},W>(value:U)->U{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let (caller, selected) = symbolic_member_application(&checker, "caller", "member", &[], 97)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            selected.type_arguments[&selected.type_binders["R"]],
            Ty::Generic(caller.type_binders["S"].key())
        );
        assert_eq!(
            selected.type_arguments[&selected.type_binders["W"]],
            Ty::Generic(caller.type_binders["V"].key())
        );
        assert!(
            !selected
                .selected_rows
                .contains_key(&selected.row_context["R"])
        );
    }

    #[test]
    fn recursive_same_declaration_selection_does_not_resolve_a_rigid_caller_member_as_concrete() {
        let evaluator = evaluator(
            "type Concrete=int\nmeta fn member<T:{item:U,..R},U>(value:T)->U{value.item}",
        );
        let checker = Typer::new(&evaluator, None);
        let (caller, selected) =
            symbolic_member_application(&checker, "member", "member", &[], 101)
                .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            selected.type_arguments[&selected.type_binders["U"]],
            Ty::Generic(caller.type_binders["U"].key())
        );
        let explicit = [
            evaluator.functions["member"].parameters[0]
                .ty
                .clone()
                .unwrap(),
            evaluator.declarations["Concrete"].value.clone().unwrap(),
        ];
        assert!(matches!(
            symbolic_member_application(&checker, "member", "member", &explicit, 103),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }

    #[test]
    fn actual_named_member_inference_and_explicit_preparation_check_all_selected_types() {
        for source in [
            "meta fn member<T:{item:U,..R},U>(value:T)->U{value.item}\nmeta let ANSWER=member(.{item:7,tag:\"selected\"})",
            "meta fn member<T:{item:U,..R},U>(value:T)->U{value.item}\nmeta let ANSWER=member<{item:int},int>(.{item:7})",
        ] {
            assert!(matches!(
                evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure)),
                StaticValue::Integer(7)
            ));
        }
    }

    fn captured_member_application(
        checker: &Typer<'_>,
        captured: &BoundEnvironment,
        instance: u64,
    ) -> Result<BoundEnvironment> {
        let schema = checker
            .complete_source_syntax(
                checker.evaluator.declarations["Input"]
                    .value
                    .as_ref()
                    .unwrap(),
                &BoundEnvironment::default(),
            )?
            .unwrap();
        let actual = checker.bound_type(&schema.syntax, &BoundEnvironment::default())?;
        let function = &checker.evaluator.functions["member"];
        let plan = application::StaticApplicationPlan::new(
            &[application::ParameterSpec::from(&function.parameters[0])],
            [None],
        )?;
        checker.check_function_application(
            function,
            TypeApplication {
                actual_types: &[actual],
                actual_schemas: &[Some(schema)],
                plan: &plan,
                captured,
                caller: captured,
                explicit: &[],
                expected: None,
                instance,
            },
        )
    }

    #[test]
    fn an_unknown_captured_member_type_is_not_selected_by_a_callees_concrete_argument() {
        let evaluator = evaluator(
            "type Input={item:int}\nmeta fn outer<U>(value:U)->U{value}\nmeta fn member<T:{item:U}>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let captured = checker
            .function_generic_environment(
                &evaluator.functions["outer"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(
            captured_member_application(&checker, &captured, 107),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }

    #[test]
    fn a_callee_row_id_does_not_make_its_captured_declared_type_flexible() {
        let evaluator = evaluator(
            "type Input={id:int,tag:str}\nmeta fn outer<R>(value:R)->R{value}\nmeta fn member<T:{id:int,..R}>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let captured = checker
            .function_generic_environment(
                &evaluator.functions["outer"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let declared = checker
            .function_generic_environment(&evaluator.functions["member"], &captured)
            .unwrap_or_else(|failure| unexpected(failure));
        let row = &declared.rows[&declared.row_context["R"]];
        assert_eq!(row.id.declaration, "member");
        assert_eq!(row.declared_type.as_ref().unwrap().declaration, "outer");
        // Unknown captured R cannot be proved equal to the concrete remainder.
        // This is an unresolved proof boundary, never an accepted application.
        assert!(matches!(
            captured_member_application(&checker, &captured, 109),
            Err(Failure::Unsupported(_))
        ));
    }

    #[test]
    fn already_selected_captured_member_and_row_types_remain_fixed_and_receive_matching_inputs() {
        let evaluator = evaluator(
            "type Input={item:int,tag:str}\ntype Scalar=int\ntype Tail={tag:str}\nmeta fn outer<U,R>(value:U)->U{value}\nmeta fn member<T:{item:U,..R}>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let mut captured = checker
            .function_generic_environment(
                &evaluator.functions["outer"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        for (parameter, alias) in [("U", "Scalar"), ("R", "Tail")] {
            let syntax = evaluator.declarations[alias].value.as_ref().unwrap();
            let empty = BoundEnvironment::default();
            let schema = checker
                .complete_source_syntax(syntax, &empty)
                .unwrap_or_else(|failure| unexpected(failure));
            let actual = checker
                .bound_type(syntax, &empty)
                .unwrap_or_else(|failure| unexpected(failure));
            let id = captured.type_binders[parameter].clone();
            checker
                .select_type_argument(&id, &actual, schema, &empty, &mut captured)
                .unwrap_or_else(|failure| unexpected(failure));
        }
        let selected = captured_member_application(&checker, &captured, 113)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            selected.selected_rows[&selected.row_context["R"]].key,
            captured.selected_types[&captured.type_binders["R"]].key
        );
        for parameter in ["U", "R"] {
            let id = &captured.type_binders[parameter];
            assert_eq!(
                selected.selected_types[id].key,
                captured.selected_types[id].key
            );
        }
    }

    #[test]
    fn symbolic_alias_members_select_from_complete_empty_array_element_schemas() {
        let evaluator = evaluator(
            "type Packet<X>={value:X}\ntype Element=[2]int\ntype Input={payload:[0]Packet<Element>}\nmeta fn pass<T:{payload:[0]Packet<U>,..R},U>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let selected = closed_application(&checker, "pass", &["Input"], 127)
            .unwrap_or_else(|failure| unexpected(failure));
        let expected = checker
            .complete_source_syntax(
                evaluator.declarations["Element"].value.as_ref().unwrap(),
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert_eq!(
            selected.selected_types[&selected.type_binders["U"]].key,
            expected.key
        );
    }

    #[test]
    fn map_value_templates_preserve_empty_value_array_dimensions() {
        let evaluator = evaluator(
            "type Element=[0][2]int\ntype Input={items:[str:Element]}\nmeta fn pass<T:{items:[str:U],..R},U>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let selected = closed_application(&checker, "pass", &["Input"], 131)
            .unwrap_or_else(|failure| unexpected(failure));
        let expected = checker
            .complete_source_syntax(
                evaluator.declarations["Element"].value.as_ref().unwrap(),
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert_eq!(
            selected.selected_types[&selected.type_binders["U"]].key,
            expected.key
        );
    }

    #[test]
    fn callable_templates_select_parameter_and_result_types_from_the_complete_signature() {
        let evaluator = evaluator(
            "type Input={handler:fn(right:int)->str}\nmeta fn pass<T:{handler:fn(input:U)->V,..R},U,V>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let selected = closed_application(&checker, "pass", &["Input"], 137)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            selected.type_arguments[&selected.type_binders["U"]],
            Ty::Number("int".into())
        );
        assert_eq!(
            selected.type_arguments[&selected.type_binders["V"]],
            Ty::String
        );
    }

    #[test]
    fn pure_alias_expansion_does_not_turn_registered_symbolic_types_into_closed_witnesses() {
        let evaluator =
            evaluator("type Packet<X>={value:X}\nmeta fn pass<T>(value:Packet<T>)->T{value.value}");
        let checker = Typer::new(&evaluator, None);
        let scope = checker
            .function_generic_environment(
                &evaluator.functions["pass"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let expanded = checker
            .symbolic_alias_syntax(
                evaluator.functions["pass"].parameters[0]
                    .ty
                    .as_ref()
                    .unwrap(),
                &scope,
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert!(
            matches!(&expanded.syntax.kind, TypeKind::Record { fields, row: None }
            if matches!(&fields[0].ty.kind, TypeKind::Name { path, arguments }
                if path == &[scope.type_binders["T"].key()] && arguments.is_empty()))
        );
        assert!(
            checker
                .complete_source_syntax(&expanded.syntax, &scope)
                .unwrap_or_else(|failure| unexpected(failure))
                .is_none()
        );
    }

    #[test]
    fn a_captured_alias_free_name_is_not_reinterpreted_as_a_same_named_callee_binder() {
        let evaluator = evaluator(
            "type Captured={value:Outer}\nmeta fn outer<Outer>(value:Outer)->Outer{value}\nmeta fn inner<T:{payload:Captured,..R},Outer>(value:T)->T{value}",
        );
        let checker = Typer::new(&evaluator, None);
        let captured = checker
            .function_generic_environment(
                &evaluator.functions["outer"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(
            checker.function_generic_environment(&evaluator.functions["inner"], &captured),
            Err(Failure::Unsupported(_))
        ));
    }

    #[test]
    fn actual_alias_map_and_callable_template_applications_use_the_selected_types() {
        for (source, expected) in [
            (
                "type Packet<X>={value:X}\nmeta fn member<T:{payload:Packet<U>,..R},U>(value:T)->U{value.payload.value}\nmeta let ANSWER=member(.{payload:.{value:7}})",
                7,
            ),
            (
                "meta fn pass<T:{items:[str:U],..R},U>(value:T)->T{value}\nmeta let ANSWER=pass(.{items:[\"a\":11]}).items[\"a\"]??0",
                11,
            ),
            (
                "meta fn second(right:int=2)->int{right}\nmeta fn pass<T:{handler:fn(input:U)->V,..R},U,V>(value:T)->T{value}\nmeta let ANSWER={let returned=pass(.{handler:second});returned.handler(right:19)+returned.handler()}",
                21,
            ),
        ] {
            let evaluator = evaluator(source);
            let checker = Typer::new(&evaluator, None);
            assert_eq!(
                erase_constants(
                    checker
                        .expr(&last_initializer(source), &mut Env::new())
                        .unwrap_or_else(|failure| unexpected(failure))
                ),
                Ty::Number("int".into())
            );
            assert!(matches!(
                evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure)),
                StaticValue::Integer(value) if value == expected
            ));
        }
    }

    #[test]
    fn equivalent_symbolic_aliases_forward_the_callers_actual_generic_identity() {
        let evaluator = evaluator(
            "type Packet<X>={value:X}\ntype OtherPacket<Z>={value:Z}\nmeta fn outer<X:{payload:OtherPacket<Y>,..S},Y>(value:X)->Y{value.payload.value}\nmeta fn member<T:{payload:Packet<U>,..R},U>(value:T)->U{value.payload.value}",
        );
        let checker = Typer::new(&evaluator, None);
        let (caller, selected) = symbolic_member_application(&checker, "outer", "member", &[], 139)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(
            selected.type_arguments[&selected.type_binders["U"]],
            Ty::Generic(caller.type_binders["Y"].key())
        );
        assert!(
            !selected
                .selected_types
                .contains_key(&selected.type_binders["U"])
        );
        assert!(
            checker
                .complete_source_syntax(
                    evaluator.functions["member"].return_type.as_ref().unwrap(),
                    &selected
                )
                .unwrap_or_else(|failure| unexpected(failure))
                .is_none()
        );
    }

    #[test]
    fn map_index_source_schema_keeps_the_optional_shell_and_complete_value_type() {
        let source = "meta let ANSWER=[\"a\":[1,2]][\"a\"]";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        let expression = last_initializer(source);
        let mut env = Env::new();
        let actual = checker
            .expr(&expression, &mut env)
            .unwrap_or_else(|failure| unexpected(failure));
        let schema = checker
            .expression_source_schema(&expression, &actual, &env, &BoundEnvironment::default(), 0)
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert!(matches!(&schema.syntax.kind, TypeKind::Optional(value)
            if matches!(&value.kind, TypeKind::Array { length: None, .. })));
    }

    #[test]
    fn optional_fallback_is_lazy_and_callable_returns_stay_inside_the_callable() {
        for (source, expected) in [
            ("meta let ANSWER=Some(7)??{assert(false);9}", 7),
            (
                "meta fn fallback()->int{return 9}\nmeta fn choose(value:?int)->int{value??fallback()}\nmeta let ANSWER=choose(Some(7))+choose(None)",
                16,
            ),
        ] {
            let evaluator = evaluator(source);
            let checker = Typer::new(&evaluator, None);
            assert_eq!(
                erase_constants(
                    checker
                        .expr(&last_initializer(source), &mut Env::new())
                        .unwrap_or_else(|failure| unexpected(failure))
                ),
                Ty::Number("int".into())
            );
            assert!(
                matches!(evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure)), StaticValue::Integer(value) if value==expected)
            );
        }
    }

    #[test]
    fn optional_fallback_preserves_declared_fixed_dimensions_for_fresh_construction() {
        let source = "meta fn first<T>(value:[2]T)->T{value[0]}\nmeta let ANSWER={let missing:?[2]int=None;let selected=missing??[7,9];first(selected)}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert_eq!(
            erase_constants(
                checker
                    .expr(&last_initializer(source), &mut Env::new())
                    .unwrap_or_else(|failure| unexpected(failure))
            ),
            Ty::Number("int".into())
        );
        assert!(matches!(
            evaluated_initializer(source).unwrap_or_else(|failure| unexpected(failure)),
            StaticValue::Integer(7)
        ));
    }

    #[test]
    fn optional_fallback_does_not_promote_existing_dynamic_arrays_to_fixed() {
        let source = "meta let ANSWER={let stored=[7,9];let missing:?[2]int=None;missing??stored}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        assert!(matches!(
            checker.expr(&last_initializer(source), &mut Env::new()),
            Err(Failure::Diagnostic("E0301", _))
        ));
    }

    #[test]
    fn symbolic_alias_structure_keeps_selected_callable_interfaces_out_of_normalization() {
        let source = "type Box<X>={item:X}\nmeta fn left(left:int=1)->int{left}\nmeta fn wrap<T>(value:T)->Box<T>{.{item:value}}";
        let evaluator = evaluator(source);
        let checker = Typer::new(&evaluator, None);
        let mut scope = checker
            .function_generic_environment(
                &evaluator.functions["wrap"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let actual = checker
            .function_ty("left", &Env::new())
            .unwrap_or_else(|failure| unexpected(failure));
        let name = Expr {
            kind: ExprKind::Name("left".into()),
            span: evaluator.functions["left"].span,
        };
        let schema = checker
            .expression_source_schema(&name, &actual, &Env::new(), &BoundEnvironment::default(), 0)
            .unwrap_or_else(|failure| unexpected(failure));
        let id = scope.type_binders["T"].clone();
        checker
            .select_type_argument(
                &id,
                &actual,
                schema,
                &BoundEnvironment::default(),
                &mut scope,
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let before = scope.selected_types[&id].clone();
        let expanded = checker
            .symbolic_alias_syntax(
                evaluator.functions["wrap"].return_type.as_ref().unwrap(),
                &scope,
            )
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert!(
            matches!(&expanded.syntax.kind,TypeKind::Record{fields,row:None}
            if matches!(&fields[0].ty.kind,TypeKind::Name{path,arguments} if path==&[id.key()]&&arguments.is_empty()))
        );
        assert_eq!(scope.selected_types[&id].key, before.key);
        assert!(before.validate_closed());
        assert!(matches!(&actual,Ty::Callable(_,_,interfaces)
            if interfaces[0][0].label.as_deref()==Some("left")&&interfaces[0][0].default));
    }

    #[test]
    fn result_flow_alias_wrapper_preserves_the_returned_actual_callable_interface() {
        let source =
            ril_test::case_bytes("tests/regressions/static.ril::static-generic-callable-wrapper");
        let session = crate::Session::new(source.to_vec());
        let verified = session.verify().unwrap();
        crate::lower::lower_core(&verified).unwrap();
    }

    #[test]
    fn named_generic_callable_signatures_use_the_definitions_real_binders_in_an_empty_caller_scope()
    {
        let source = "type Box<X>={item:X}\nmeta fn wrap<T>(value:T)->Box<T>{.{item:value}}";
        let evaluator = evaluator(source);
        let checker =
            Typer::with_bound_environment(&evaluator, None, Arc::new(BoundEnvironment::default()));
        let scope = checker
            .function_generic_environment(
                &evaluator.functions["wrap"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let signature = checker
            .function_ty("wrap", &Env::new())
            .unwrap_or_else(|failure| unexpected(failure));
        let Ty::Callable(parameters, result, _) = signature else {
            panic!("callable signature")
        };
        assert_eq!(parameters, [Ty::Generic(scope.type_binders["T"].key())]);
        assert!(matches!(result.as_ref(),Ty::Record(fields) if fields["item"].1==parameters[0]));
    }

    #[test]
    fn result_contexts_preserve_full_empty_array_dimensions_without_fixing_dynamic_return_shells() {
        let evaluator = evaluator(
            "type Expected=[][0][2]int\ntype Wrong=[0][2]int\nmeta fn empty<T>()->[]T{[]}",
        );
        let checker = Typer::new(&evaluator, None);
        let caller = BoundEnvironment::default();
        let function = &evaluator.functions["empty"];
        let plan = application::StaticApplicationPlan::new(&[], std::iter::empty())
            .unwrap_or_else(|failure| unexpected(failure));
        for (alias, accepted) in [("Expected", true), ("Wrong", false)] {
            let context = checker
                .result_context(
                    evaluator.declarations[alias].value.as_ref().unwrap(),
                    &caller,
                )
                .unwrap_or_else(|failure| unexpected(failure));
            let result = checker.check_function_application(
                function,
                TypeApplication {
                    actual_types: &[],
                    actual_schemas: &[],
                    plan: &plan,
                    captured: &caller,
                    caller: &caller,
                    explicit: &[],
                    expected: Some(&context),
                    instance: if accepted { 211 } else { 223 },
                },
            );
            if accepted {
                let selected = result.unwrap_or_else(|failure| unexpected(failure));
                let schema = &selected.selected_types[&selected.type_binders["T"]];
                assert!(
                    matches!(&schema.syntax.kind, TypeKind::Array { length: Some(_), element } if matches!(element.kind,TypeKind::Array{length:Some(_),..}))
                );
            } else {
                assert!(matches!(result, Err(Failure::Diagnostic("E0301", _))));
            }
        }
    }

    #[test]
    fn open_result_contexts_forward_real_caller_ids_without_claiming_a_closed_witness() {
        let evaluator = evaluator("meta fn caller<T>()->[]T{[]}\nmeta fn empty<T>()->[]T{[]}");
        let checker = Typer::new(&evaluator, None);
        let caller_function = &evaluator.functions["caller"];
        let caller = checker
            .function_generic_environment(caller_function, &BoundEnvironment::default())
            .unwrap_or_else(|failure| unexpected(failure));
        let context = checker
            .result_context(caller_function.return_type.as_ref().unwrap(), &caller)
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(context.closed_schema().is_none());
        let optional = checker
            .optional_result_context(&context)
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(optional.closed_schema().is_none());
        let projected = checker
            .project_result_context(&optional, ResultProjection::OptionalPayload)
            .unwrap_or_else(|failure| unexpected(failure))
            .unwrap();
        assert_eq!(projected.ordinary(), context.ordinary());
        assert!(projected.closed_schema().is_none());
        let plan = application::StaticApplicationPlan::new(&[], std::iter::empty())
            .unwrap_or_else(|failure| unexpected(failure));
        let selected = checker
            .check_function_application(
                &evaluator.functions["empty"],
                TypeApplication {
                    actual_types: &[],
                    actual_schemas: &[],
                    plan: &plan,
                    captured: &BoundEnvironment::default(),
                    caller: &caller,
                    explicit: &[],
                    expected: Some(&context),
                    instance: 227,
                },
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let selected_id = &selected.type_binders["T"];
        assert_eq!(
            selected.type_arguments[selected_id],
            Ty::Generic(caller.type_binders["T"].key())
        );
        assert!(!selected.selected_types.contains_key(selected_id));
    }

    #[test]
    fn computed_written_lengths_have_normalized_sources_and_preserve_the_original_annotation() {
        let evaluator = evaluator(
            "meta fn shape()->[2]int{[1,2]}\nmeta fn initialize()->[2]f32{[1,2]}\ntype Expected=[len(shape())]f32",
        );
        let checker = Typer::new(&evaluator, None);
        let caller = BoundEnvironment::default();
        let context = checker
            .result_context(
                evaluator.declarations["Expected"].value.as_ref().unwrap(),
                &caller,
            )
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(
            matches!(&context.written().kind,TypeKind::Array{length:Some(length),..} if matches!(length.kind,ExprKind::Call{..}))
        );
        assert!(
            matches!(&context.closed_schema().unwrap().syntax.kind,TypeKind::Array{length:Some(length),..} if matches!(&length.kind,ExprKind::Literal(Literal::Integer(value)) if value=="2"))
        );
        let plan = application::StaticApplicationPlan::new(&[], std::iter::empty())
            .unwrap_or_else(|failure| unexpected(failure));
        checker
            .check_function_application(
                &evaluator.functions["initialize"],
                TypeApplication {
                    actual_types: &[],
                    actual_schemas: &[],
                    plan: &plan,
                    captured: &caller,
                    caller: &caller,
                    explicit: &[],
                    expected: Some(&context),
                    instance: 229,
                },
            )
            .unwrap_or_else(|failure| unexpected(failure));
    }

    #[test]
    fn result_contexts_reuse_frozen_computed_alias_instances_without_reexecuting_their_body() {
        let mut evaluator =
            evaluator("meta fn shape()->[2]int{[1,2]}\ntype Items=[len(shape())]int");
        let source = TypeExpr {
            kind: TypeKind::Name {
                path: vec!["Items".into()],
                arguments: vec![],
            },
            text: "Items".into(),
            span: evaluator.declarations["Items"].span,
        };
        evaluator
            .resolve_type(&source, &mut vec![])
            .unwrap_or_else(|failure| unexpected(failure));
        evaluator.functions.remove("shape");
        let checker = Typer::new(&evaluator, None);
        let context = checker
            .result_context(&source, &BoundEnvironment::default())
            .unwrap_or_else(|failure| unexpected(failure));
        assert!(matches!(&context.written().kind,TypeKind::Name{path,..} if path==&["Items"]));
        assert!(
            matches!(&context.closed_schema().unwrap().syntax.kind,TypeKind::Array{length:Some(length),..} if matches!(&length.kind,ExprKind::Literal(Literal::Integer(value)) if value=="2"))
        );
    }

    #[test]
    fn a_missing_alias_instance_never_interprets_definition_free_values_in_the_caller() {
        let evaluator = evaluator("type Items=[size]int");
        let checker = Typer::new(&evaluator, None);
        let mut caller = BoundEnvironment::default();
        caller.values.insert("size".into(), Ty::IntegerConstant(2));
        let source = TypeExpr {
            kind: TypeKind::Name {
                path: vec!["Items".into()],
                arguments: vec![],
            },
            text: "Items".into(),
            span: evaluator.declarations["Items"].span,
        };
        assert!(matches!(
            checker.result_context(&source, &caller),
            Err(Failure::Unsupported(_))
        ));
        assert!(evaluator.alias_instances.is_empty());
        assert!(caller.selected_types.is_empty());
    }
}
