//! Evaluated arguments may select a previously universally verified template.
//! They are never used to prove the template body or its Result control flow.
use super::*;

fn selected_environment(
    evaluator: &Evaluator,
    environment: &environments::Environment,
) -> Result<bounds::BoundEnvironment> {
    let checker = Typer::new(evaluator, None);
    let mut scope = bounds::BoundEnvironment::captured(
        environment
            .values
            .iter()
            .map(|(name, value)| Ok((name.clone(), checker.value_type(value)?)))
            .collect::<Result<Env>>()?,
    );
    scope.type_binders = environment.types.visible_types().clone();
    scope.const_binders = environment.types.visible_consts().clone();
    for (id, value) in environment.types.const_selections() {
        scope.const_ids.insert(id.key(), id.clone());
        scope
            .const_arguments
            .insert(id.clone(), const_int::ConstIntSelection::Closed(*value));
    }
    for (name, id) in &scope.const_binders {
        if let Some(id) = id {
            scope.const_ids.insert(id.key(), id.clone());
            scope.values.insert(name.clone(), Ty::Number("int".into()));
        }
    }
    scope.selected_types = environment.types.type_selections().clone();
    scope.selected_rows = environment.types.row_selections().clone();
    scope.row_context = environment.types.visible_rows().clone();
    for (id, selected) in &scope.selected_types {
        scope.type_ids.insert(id.key(), id.clone());
        let ty = checker.bound_type(&selected.syntax, &bounds::BoundEnvironment::default())?;
        scope.type_arguments.insert(id.clone(), ty);
    }
    for name in scope.type_binders.keys() {
        scope.values.insert(name.clone(), Ty::TypeParameter);
    }
    for name in scope.row_context.keys() {
        scope
            .values
            .entry(name.clone())
            .or_insert(Ty::TypeParameter);
    }
    let owners = scope
        .type_ids
        .values()
        .map(|id| id.declaration.clone())
        .chain(scope.row_context.values().map(|id| id.declaration.clone()))
        .chain(scope.const_ids.values().map(|id| id.declaration.clone()))
        .collect::<BTreeSet<_>>();
    for owner in owners {
        if let Some(function) = evaluator.functions.get(&owner) {
            let declarations = checker.function_generic_environment(function, &scope)?;
            scope.type_ids.extend(declarations.type_ids);
            scope.views.extend(declarations.views);
            scope.rows.extend(declarations.rows);
        }
    }
    for (id, selected) in &scope.selected_rows {
        let TypeKind::Record { fields, row: None } = &selected.syntax.kind else {
            return Err(Failure::Unsupported(
                "evaluated static row selection is not closed".into(),
            ));
        };
        scope.row_arguments.insert(
            id.clone(),
            crate::sema::model::rows::Row::closed(
                fields
                    .iter()
                    .map(|field| {
                        let key = effects::bounded_argument_key(&field.ty, &BTreeMap::new())
                            .ok_or_else(|| {
                                Failure::Unsupported(
                                    "evaluated static row field key is unavailable".into(),
                                )
                            })?;
                        Ok((
                            field.name.clone(),
                            (
                                field.mutable,
                                applications::SchemaField {
                                    syntax: std::sync::Arc::new(field.ty.clone()),
                                    key,
                                },
                            ),
                        ))
                    })
                    .collect::<Result<BTreeMap<_, _>>>()?,
            ),
        );
    }
    Ok(scope)
}

pub(in crate::static_eval) fn infer_named_type_arguments(
    evaluator: &Evaluator,
    function: &Function,
    captured: &environments::Environment,
    caller: &environments::Environment,
    arguments: &[application::StaticArgument],
    expected: Option<&applications::ResultContext>,
    instance: u64,
) -> Result<Vec<TypeExpr>> {
    let checker = Typer::new(evaluator, None);
    let captured = selected_environment(evaluator, captured)?;
    let caller = selected_environment(evaluator, caller)?;
    let schemas = arguments
        .iter()
        .map(|argument| evaluator.complete_source_type(&argument.value, function.span))
        .collect::<Result<Vec<_>>>()?;
    let types = arguments
        .iter()
        .zip(&schemas)
        .map(|(argument, schema)| match schema {
            Some(schema) => checker.bound_type(&schema.syntax, &caller),
            None => checker.value_type(&argument.value),
        })
        .collect::<Result<Vec<_>>>()?;
    let plan = application::StaticApplicationPlan::new(
        &function
            .parameters
            .iter()
            .map(application::ParameterSpec::from)
            .collect::<Vec<_>>(),
        arguments.iter().map(|argument| argument.label.clone()),
    )?;
    let selected = checker.check_function_application(
        function,
        applications::TypeApplication {
            actual_types: &types,
            actual_schemas: &schemas,
            plan: &plan,
            captured: &captured,
            caller: &caller,
            explicit: &[],
            expected,
            instance,
        },
    )?;
    function
        .generics
        .iter()
        .map(|parameter| {
            if let Some(Some(id)) = selected.const_binders.get(&parameter.name) {
                return match selected.const_arguments.get(id) {
                    Some(const_int::ConstIntSelection::Closed(value)) => {
                        Ok(const_int::argument_syntax(*value, function.span))
                    }
                    _ => Err(Failure::Unsupported(
                        "evaluated static const argument is not closed".into(),
                    )),
                };
            }
            let id = &selected.type_binders[&parameter.name];
            let schema = selected.selected_types.get(id).ok_or_else(|| {
                Failure::Diagnostic(
                    "E0344",
                    "static generic application has no complete selected argument".into(),
                )
            })?;
            clone_work::type_syntax(&evaluator.budget, &schema.syntax)?;
            Ok(schema.syntax.clone())
        })
        .collect()
}

pub(in crate::static_eval) fn expected_result_context(
    evaluator: &Evaluator,
    written: &TypeExpr,
    caller: &environments::Environment,
) -> Result<applications::ResultContext> {
    let lexical = selected_environment(evaluator, caller)?;
    Typer::new(evaluator, None).result_context(written, &lexical)
}
