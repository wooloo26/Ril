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
    let child = |ty: &TypeExpr| argument_key(ty, binders);
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            let name = path.join("::");
            if arguments.is_empty()
                && let Some(identity) = binders.get(&name)
            {
                return ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                };
            }
            ArgumentKey::Name {
                name: name.strip_prefix("Prelude::").unwrap_or(&name).into(),
                arguments: arguments.iter().map(child).collect(),
            }
        }
        TypeKind::Optional(inner) => ArgumentKey::Name {
            name: "Option".into(),
            arguments: vec![child(inner)],
        },
        TypeKind::Array { length, element } => ArgumentKey::Array {
            length: length.as_ref().map(|length| {
                normalized_argument_key(&TypeExpr {
                    text: String::new(),
                    span: length.span,
                    kind: TypeKind::Computation(length.clone()),
                })
            }),
            element: Box::new(child(element)),
        },
        TypeKind::Map { key, value } => ArgumentKey::Map {
            key: Box::new(child(key)),
            value: Box::new(child(value)),
        },
        TypeKind::Tuple(items) => ArgumentKey::Tuple(items.iter().map(child).collect()),
        TypeKind::Record { fields, row } => {
            let mut fields: Vec<_> = fields
                .iter()
                .map(|field| (field.name.clone(), field.mutable, child(&field.ty)))
                .collect();
            fields.sort_by(|a, b| a.0.cmp(&b.0));
            ArgumentKey::Record {
                fields,
                row: row.as_ref().map(|row| Box::new(child(row))),
            }
        }
        TypeKind::Callable {
            parameters,
            result,
            annotations,
        } => ArgumentKey::Callable {
            parameters: parameters
                .iter()
                .map(|p| {
                    (
                        p.mode,
                        p.ty.as_ref()
                            .map(child)
                            .unwrap_or_else(|| ArgumentKey::Closed("untyped".into())),
                    )
                })
                .collect(),
            result: Box::new(
                result
                    .as_ref()
                    .map(|ty| child(ty))
                    .unwrap_or_else(|| ArgumentKey::Tuple(vec![])),
            ),
            annotations: annotations
                .iter()
                .map(|a| a.text.replace(' ', ""))
                .collect(),
        },
        // Only closed forms reach this branch. Symbolic computations and
        // projections require their own normalization proof before admission.
        _ => ArgumentKey::Closed(normalized_argument_key(ty)),
    }
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

pub(crate) fn instantiate(
    declaration: &EffectDeclaration,
    arguments: &[TypeExpr],
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
) -> std::result::Result<Instance, ArgumentNormalizationError> {
    let mut evaluator = Evaluator {
        type_environment: Default::default(),
        type_application_sequence: 0,
        layout,
        values: BTreeMap::new(),
        global_values: BTreeMap::new(),
        budget: Default::default(),
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
                let bound = if let TypeKind::Name { path, arguments } = &argument.kind
                    && arguments.is_empty()
                {
                    evaluator.values.get(&path.join("::")).cloned()
                } else if let TypeKind::Computation(expression) = &argument.kind {
                    Some(evaluator.expression(expression)?)
                } else {
                    None
                };
                *argument = match bound {
                    Some(StaticValue::Type(ty)) => ty,
                    Some(value) => TypeExpr {
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
    normalize().map_err(|failure| match failure {
        Failure::Diagnostic(code, message) => ArgumentNormalizationError::Diagnostic(code, message),
        Failure::Unsupported(message) => ArgumentNormalizationError::Unsupported(message),
        Failure::Return(_) | Failure::TailCall(_) | Failure::TailType(_) | Failure::Loop(_) => {
            ArgumentNormalizationError::Unsupported(
                "effect argument cannot return from an enclosing callable".into(),
            )
        }
    })
}
