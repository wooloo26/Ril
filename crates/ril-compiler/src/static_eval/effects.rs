//! Effect instances use ordinary static argument equivalence and substitution.
use super::*;
use crate::sema::effect_identity::{ArgumentKey, StaticBinderSort};

pub(crate) fn bounded_argument_key(
    ty: &TypeExpr,
    binders: &BTreeMap<String, String>,
) -> Option<ArgumentKey> {
    let budget = budget::Budget::default();
    clone_work::type_syntax(&budget, ty).ok()?;
    Some(argument_key(ty, binders))
}

pub(crate) fn argument_key(ty: &TypeExpr, binders: &BTreeMap<String, String>) -> ArgumentKey {
    argument_key_inner(ty, binders, &mut None)
        .expect("unmetered argument key admission is infallible")
}

/// The same key projection borrows its caller's remaining work. Admission
/// covers syntax depth before the recursive builder and every owned output.
pub(crate) fn argument_key_with_work(
    ty: &TypeExpr,
    binders: &BTreeMap<String, String>,
    work: &mut usize,
) -> Option<ArgumentKey> {
    super::charge_type_syntax_clone(ty, work)?;
    argument_key_inner(ty, binders, &mut Some(work))
}

fn key_work(work: &mut Option<&mut usize>, units: usize) -> Option<()> {
    if let Some(work) = work {
        **work = work.checked_sub(units)?;
    }
    Some(())
}

fn key_text(work: &mut Option<&mut usize>, text: &str) -> Option<()> {
    key_work(work, 1usize.checked_add(text.len())?)
}

fn argument_key_inner(
    ty: &TypeExpr,
    binders: &BTreeMap<String, String>,
    work: &mut Option<&mut usize>,
) -> Option<ArgumentKey> {
    key_work(work, 1)?;
    Some(match &ty.kind {
        TypeKind::Name { path, arguments } => {
            key_work(work, path.len().checked_mul(2)?)?;
            for part in path {
                key_text(work, part)?;
            }
            let name = path.join("::");
            key_work(
                work,
                name.len()
                    .checked_add(1)?
                    .checked_mul(binders.len().checked_ilog2().unwrap_or(0) as usize + 1)?,
            )?;
            if arguments.is_empty()
                && let Some(identity) = binders.get(&name)
            {
                key_text(work, identity)?;
                return Some(ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                });
            }
            key_text(work, &name)?;
            let mut values = Vec::new();
            key_work(work, arguments.len())?;
            for argument in arguments {
                values.push(argument_key_inner(argument, binders, work)?);
            }
            ArgumentKey::Name {
                name: name.strip_prefix("Prelude::").unwrap_or(&name).into(),
                arguments: values,
            }
        }
        TypeKind::Optional(inner) => {
            key_work(work, 8)?;
            ArgumentKey::Name {
                name: "Option".into(),
                arguments: vec![argument_key_inner(inner, binders, work)?],
            }
        }
        TypeKind::Array { length, element } => {
            let length = if let Some(length) = length {
                if let Some(remaining) = work {
                    super::charge_expression_syntax_clone(length, remaining)?;
                }
                Some(normalized_argument_key(&TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: length.span,
                    kind: TypeKind::Computation(length.clone()),
                }))
            } else {
                None
            };
            ArgumentKey::Array {
                length,
                element: Box::new(argument_key_inner(element, binders, work)?),
            }
        }
        TypeKind::Map { key, value } => ArgumentKey::Map {
            key: Box::new(argument_key_inner(key, binders, work)?),
            value: Box::new(argument_key_inner(value, binders, work)?),
        },
        TypeKind::Tuple(items) => {
            key_work(work, items.len())?;
            let mut values = Vec::new();
            for item in items {
                values.push(argument_key_inner(item, binders, work)?);
            }
            ArgumentKey::Tuple(values)
        }
        TypeKind::Record { fields, row } => {
            key_work(work, fields.len())?;
            let mut values = Vec::new();
            for field in fields {
                key_work(
                    work,
                    field
                        .name
                        .len()
                        .checked_add(1)?
                        .checked_mul(fields.len().checked_ilog2().unwrap_or(0) as usize + 2)?,
                )?;
                values.push((
                    field.name.clone(),
                    field.mutable,
                    argument_key_inner(&field.ty, binders, work)?,
                ));
            }
            values.sort_by(|a, b| a.0.cmp(&b.0));
            ArgumentKey::Record {
                fields: values,
                row: if let Some(row) = row {
                    Some(Box::new(argument_key_inner(row, binders, work)?))
                } else {
                    None
                },
            }
        }
        TypeKind::Callable {
            parameters,
            result,
            annotations,
        } => {
            key_work(work, parameters.len().checked_add(annotations.len())?)?;
            let mut values = Vec::new();
            for parameter in parameters {
                let key = if let Some(ty) = &parameter.ty {
                    argument_key_inner(ty, binders, work)?
                } else {
                    key_work(work, 8)?;
                    ArgumentKey::Closed("untyped".into())
                };
                values.push((parameter.mode, key));
            }
            let result = if let Some(result) = result {
                argument_key_inner(result, binders, work)?
            } else {
                ArgumentKey::Tuple(vec![])
            };
            let mut annotation_keys = Vec::new();
            for annotation in annotations {
                key_text(work, &annotation.text)?;
                annotation_keys.push(annotation.text.replace(' ', ""));
            }
            ArgumentKey::Callable {
                parameters: values,
                result: Box::new(result),
                annotations: annotation_keys,
            }
        }
        // Closed static leaves retain the existing normalized identity. The
        // outer syntax admission covers their actual expression/string input.
        _ => ArgumentKey::Closed(normalized_argument_key(ty)),
    })
}

pub(crate) fn type_dependencies(ty: &TypeExpr) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    transform::type_names(ty, &mut names);
    names
}

pub(crate) fn enclosing_names(
    declaration: &EffectDeclaration,
    arguments: &[TypeExpr],
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for parameter in &declaration.generics {
        if let Some(bound) = &parameter.bound {
            transform::type_names(bound, &mut names);
        }
        if let Some(default) = &parameter.default {
            transform::type_names(default, &mut names);
        }
    }
    for operation in &declaration.operations {
        for parameter in &operation.parameters {
            if let Some(ty) = &parameter.ty {
                transform::type_names(ty, &mut names);
            }
        }
        if let Some(ty) = &operation.return_type {
            transform::type_names(ty, &mut names);
        }
    }
    for member in &declaration.members {
        transform::type_names(member, &mut names);
    }
    for parameter in &declaration.generics {
        names.remove(&parameter.name);
    }
    for argument in arguments {
        transform::type_names(argument, &mut names);
    }
    names
}

pub(crate) fn mentions_enclosing_binders(
    declaration: &EffectDeclaration,
    arguments: &[TypeExpr],
    types: &BTreeMap<String, TypeDeclaration>,
    enclosing: &BTreeMap<String, String>,
) -> bool {
    let mut pending = enclosing_names(declaration, arguments);
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop_first() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if enclosing.contains_key(&name) {
            return true;
        }
        if let Some(ty) = types.get(&name) {
            let mut dependencies = BTreeSet::new();
            if let Some(value) = &ty.value {
                transform::type_names(value, &mut dependencies);
            }
            for parameter in &ty.generics {
                if let Some(bound) = &parameter.bound {
                    transform::type_names(bound, &mut dependencies);
                }
                if let Some(default) = &parameter.default {
                    transform::type_names(default, &mut dependencies);
                }
            }
            for variant in &ty.variants {
                let mut variant_names = BTreeSet::new();
                if let Some(payload) = &variant.payload {
                    transform::type_names(payload, &mut variant_names);
                }
                if let Some(result) = &variant.result {
                    transform::type_names(result, &mut variant_names);
                }
                for parameter in &variant.generics {
                    variant_names.remove(&parameter.name);
                }
                dependencies.extend(variant_names);
            }
            for parameter in &ty.generics {
                dependencies.remove(&parameter.name);
            }
            pending.extend(dependencies);
        }
    }
    false
}

pub(crate) struct Instance {
    pub declaration: EffectDeclaration,
    pub arguments: Vec<TypeExpr>,
}

pub(crate) fn instantiate_bounded(
    declaration: &EffectDeclaration,
    arguments: &[TypeExpr],
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
    work: &mut usize,
) -> std::result::Result<Instance, ArgumentNormalizationError> {
    let mut argument_budget = budget::Budget::default();
    let root = argument_budget.enter_root();
    argument_budget.restrict_work(u64::try_from(*work).unwrap_or(u64::MAX));
    let allocated = argument_budget.work_remaining();
    let admission = (|| -> Result<()> {
        clone_work::type_declarations(&argument_budget, declarations)?;
        clone_work::effect_declaration(&argument_budget, declaration)?;
        argument_budget.work(arguments.len() as u64)?;
        for argument in arguments {
            clone_work::type_syntax(&argument_budget, argument)?;
        }
        Ok(())
    })();
    if let Err(failure) = admission {
        let accounted = debit_work(work, allocated, &argument_budget);
        argument_budget.leave_root(root);
        accounted?;
        return Err(normalization_error(failure));
    }
    let mut evaluator = Evaluator {
        type_environment: Default::default(),
        type_application_sequence: 0,
        layout,
        values: BTreeMap::new(),
        global_values: BTreeMap::new(),
        budget: argument_budget,
        declarations: declarations.clone(),
        effect_declarations: BTreeMap::new(),
        functions: BTreeMap::new(),
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
    let mut normalize = || -> Result<Instance> {
        let arguments =
            evaluator.bind_type_arguments(&declaration.generics, arguments, &declaration.name)?;
        let mut instance = declaration.clone();
        evaluator
            .budget
            .work(declaration.name.len() as u64 + arguments.len() as u64)?;
        for argument in &arguments {
            clone_work::type_syntax(&evaluator.budget, argument)?;
        }
        instance.name = if declaration.generics.is_empty() {
            declaration.name.clone()
        } else {
            format!(
                "{}<{}>",
                declaration.name,
                arguments
                    .iter()
                    .map(normalized_argument_key)
                    .collect::<Vec<_>>()
                    .join(",")
            )
        };
        instance.generics.clear();
        for operation in &mut instance.operations {
            for parameter in &mut operation.parameters {
                if let Some(ty) = &mut parameter.ty {
                    *ty = evaluator.resolve_type(ty, &mut vec![])?;
                }
            }
            if let Some(ty) = &mut operation.return_type {
                *ty = evaluator.resolve_type(ty, &mut vec![])?;
            }
        }
        // An effect-set member's family names an effect, not a type. Only its
        // static arguments undergo ordinary type/value substitution here.
        for member in &mut instance.members {
            let TypeKind::Name { arguments, .. } = &mut member.kind else {
                return Err(Failure::Diagnostic(
                    "E0204",
                    "effect-set member must name an effect instance".into(),
                ));
            };
            for argument in arguments {
                clone_work::type_syntax(&evaluator.budget, argument)?;
                let bound = if let TypeKind::Name { path, arguments } = &argument.kind
                    && arguments.is_empty()
                {
                    for part in path {
                        evaluator.budget.work(part.len() as u64 + 2)?;
                    }
                    let value = evaluator.values.get(&path.join("::"));
                    if let Some(value) = value {
                        clone_work::value(&evaluator.budget, value)?;
                    }
                    value.cloned()
                } else if let TypeKind::Computation(expression) = &argument.kind {
                    Some(evaluator.expression(expression)?)
                } else {
                    None
                };
                *argument = match bound {
                    Some(StaticValue::Type(ty)) => ty,
                    Some(value) => TypeExpr {
                        hir_id: None,
                        text: argument.text.clone(),
                        span: argument.span,
                        kind: TypeKind::Computation(Box::new(
                            evaluator.const_value_expr(value, argument.span)?,
                        )),
                    },
                    None => evaluator.resolve_type(argument, &mut vec![])?,
                };
            }
        }
        Ok(Instance {
            declaration: instance,
            arguments,
        })
    };
    let result = normalize();
    let accounted = debit_work(work, allocated, &evaluator.budget);
    evaluator.budget.leave_root(root);
    accounted?;
    result.map_err(normalization_error)
}

fn debit_work(
    work: &mut usize,
    allocated: u64,
    budget: &budget::Budget,
) -> std::result::Result<(), ArgumentNormalizationError> {
    let consumed = allocated
        .checked_sub(budget.work_remaining())
        .and_then(|units| usize::try_from(units).ok())
        .ok_or_else(|| {
            ArgumentNormalizationError::Unsupported(
                "static effect interpretation replenished its shared work allowance".into(),
            )
        })?;
    *work = work.checked_sub(consumed).ok_or_else(|| {
        ArgumentNormalizationError::Unsupported(
            "static effect work debit exceeds its caller allowance".into(),
        )
    })?;
    Ok(())
}

fn normalization_error(failure: Failure) -> ArgumentNormalizationError {
    match failure {
        Failure::Diagnostic(code, message) => ArgumentNormalizationError::Diagnostic(code, message),
        Failure::Unsupported(message) => ArgumentNormalizationError::Unsupported(message),
        Failure::Return(_) | Failure::TailCall(_) | Failure::TailType(_) | Failure::Loop(_) => {
            ArgumentNormalizationError::Unsupported(
                "effect argument cannot return from an enclosing callable".into(),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (
        EffectDeclaration,
        Vec<TypeExpr>,
        BTreeMap<String, TypeDeclaration>,
    ) {
        let parsed = ril_syntax::parse("type Item=i8\neff Probe<T>{read(value:[2]T)->T}");
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let StmtKind::Type(item) = &parsed.program.statements[0].kind else {
            panic!("type fixture");
        };
        let StmtKind::Effect(effect) = &parsed.program.statements[1].kind else {
            panic!("effect fixture");
        };
        let name = |value: &str| TypeExpr {
            hir_id: None,
            text: value.into(),
            span: effect.span,
            kind: TypeKind::Name {
                path: vec![value.into()],
                arguments: vec![],
            },
        };
        let mut effect = effect.clone();
        effect.members.push(TypeExpr {
            hir_id: None,
            text: String::new(),
            span: effect.span,
            kind: TypeKind::Name {
                path: vec!["OtherEffect".into()],
                arguments: vec![name("T")],
            },
        });
        (
            effect,
            vec![name("Item")],
            BTreeMap::from([("Item".into(), item.clone())]),
        )
    }

    #[test]
    fn bounded_effect_instantiation_shares_one_root_across_headers_and_members() {
        let (declaration, arguments, types) = fixture();
        let initial = 65_536;
        let mut remaining = initial;
        let Ok(result) = instantiate_bounded(
            &declaration,
            &arguments,
            &types,
            TargetLayout::POINTER64,
            &mut remaining,
        ) else {
            panic!("bounded effect fixture");
        };
        assert!(remaining < initial);
        let parameter = result.declaration.operations[0].parameters[0]
            .ty
            .as_ref()
            .unwrap();
        let TypeKind::Array { element, .. } = &parameter.kind else {
            panic!("array parameter");
        };
        assert!(
            matches!(&element.kind, TypeKind::Name { path, arguments } if path == &["i8"] && arguments.is_empty())
        );
        assert!(
            matches!(&result.declaration.operations[0].return_type.as_ref().unwrap().kind, TypeKind::Name { path, arguments } if path == &["i8"] && arguments.is_empty())
        );
        let TypeKind::Name {
            path,
            arguments: members,
        } = &result.declaration.members[0].kind
        else {
            panic!("effect member");
        };
        assert_eq!(path, &["OtherEffect"]);
        assert!(
            matches!(&members[0].kind, TypeKind::Name { path, arguments } if path == &["i8"] && arguments.is_empty())
        );
        let used = initial - remaining;
        let mut exact = used;
        assert!(
            instantiate_bounded(
                &declaration,
                &arguments,
                &types,
                TargetLayout::POINTER64,
                &mut exact
            )
            .is_ok()
        );
        assert_eq!(exact, 0);
        for units in [0, used - 1] {
            let mut exhausted = units;
            assert!(
                instantiate_bounded(
                    &declaration,
                    &arguments,
                    &types,
                    TargetLayout::POINTER64,
                    &mut exhausted
                )
                .is_err()
            );
            assert!(
                exhausted <= units,
                "a nested root refilled the shared allowance"
            );
        }
        let caller = initial * 1024;
        let mut unborrowed = caller;
        assert!(
            instantiate_bounded(
                &declaration,
                &arguments,
                &types,
                TargetLayout::POINTER64,
                &mut unborrowed
            )
            .is_ok()
        );
        assert_eq!(
            unborrowed,
            caller - used,
            "the interpreter cap consumed unborrowed caller work"
        );
    }

    #[test]
    fn effect_statement_clone_admission_covers_headers_and_members() {
        let (declaration, _, _) = fixture();
        let statement = Stmt {
            hir_id: None,
            span: declaration.span,
            kind: StmtKind::Effect(declaration),
        };
        let mut work = 65_536;
        assert!(super::super::charge_statement_syntax_clone(&statement, &mut work).is_some());
        let used = 65_536 - work;
        let mut exact = used;
        assert!(super::super::charge_statement_syntax_clone(&statement, &mut exact).is_some());
        assert_eq!(exact, 0);
        assert!(super::super::charge_statement_syntax_clone(&statement, &mut 0).is_none());
        let mut larger = statement.clone();
        let StmtKind::Effect(effect) = &mut larger.kind else {
            unreachable!();
        };
        effect.members[0].text = "larger".repeat(used + 1);
        let mut limited = used;
        assert!(super::super::charge_statement_syntax_clone(&larger, &mut limited).is_none());
    }
}
