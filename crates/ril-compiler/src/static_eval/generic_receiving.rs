//! A declared generic position transports the actual callable interface. A
//! source-written callable type supplies a view instead. Canonical type equality
//! alone cannot distinguish those two receiving operations.
use super::*;

pub(super) struct ReceivingMask {
    pub syntax: TypeExpr,
    pub markers: BTreeSet<String>,
}
impl Evaluator {
    pub(super) fn generic_receiving_mask(
        &self,
        syntax: &TypeExpr,
    ) -> Result<Option<ReceivingMask>> {
        for_types(
            syntax,
            self.type_environment.visible_types(),
            &self.declarations,
            self.layout,
            &self.budget,
        )
    }
}
pub(super) fn for_types(
    syntax: &TypeExpr,
    binders: &BTreeMap<String, typing::bounds::StaticBinderId>,
    type_declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
    budget: &budget::Budget,
) -> Result<Option<ReceivingMask>> {
    let mut substitutions = BTreeMap::new();
    for (index, name) in binders.keys().enumerate() {
        let mut marker = format!("RilStaticGenericPosition{index}");
        while type_declarations.contains_key(&marker) {
            marker.push('X');
        }
        substitutions.insert(name.clone(), marker);
    }
    if substitutions.is_empty() {
        return Ok(None);
    }
    clone_work::type_syntax(budget, syntax)?;
    let mut used = false;
    let masked = replace(syntax, &substitutions, 0, &mut 0, &mut used)?;
    let mut declarations = BTreeMap::new();
    for (name, declaration) in type_declarations {
        budget.work(name.len() as u64 + 1)?;
        for syntax in declaration
            .value
            .iter()
            .chain(
                declaration
                    .generics
                    .iter()
                    .flat_map(|parameter| parameter.bound.iter().chain(&parameter.default)),
            )
            .chain(
                declaration
                    .variants
                    .iter()
                    .flat_map(|variant| variant.payload.iter().chain(&variant.result)),
            )
        {
            clone_work::type_syntax(budget, syntax)?;
        }
        let mut declaration = declaration.clone();
        if let Some(syntax) = &declaration.value {
            let mut visible = substitutions.clone();
            for parameter in &declaration.generics {
                visible.remove(&parameter.name);
            }
            declaration.value = Some(replace(syntax, &visible, 0, &mut 0, &mut used)?);
        }
        declarations.insert(name.clone(), declaration);
    }
    if !used {
        return Ok(None);
    }
    for marker in substitutions.values() {
        declarations.insert(
            marker.clone(),
            TypeDeclaration {
                name: marker.clone(),
                visibility: Visibility::Private,
                is_halt: false,
                generics: vec![],
                value: None,
                variants: vec![],
                opaque: true,
                nominal: true,
                span: syntax.span,
            },
        );
    }
    let syntax =
        crate::sema::checker::normalize_closed_source_syntax(&masked, &declarations, layout)
            .ok_or_else(|| {
                Failure::Unsupported(
                    "generic callable receiving position has no complete pure alias expansion"
                        .into(),
                )
            })?;
    Ok(Some(ReceivingMask {
        syntax,
        markers: substitutions.into_values().collect(),
    }))
}

fn replace(
    syntax: &TypeExpr,
    substitutions: &BTreeMap<String, String>,
    depth: usize,
    nodes: &mut usize,
    used: &mut bool,
) -> Result<TypeExpr> {
    *nodes += 1;
    if depth >= 64 || *nodes > 4096 {
        return Err(Failure::Unsupported(
            "generic receiving mask exceeds its finite syntax allowance".into(),
        ));
    }
    let mut output = syntax.clone();
    if let TypeKind::Name { path, arguments } = &mut output.kind
        && path.len() == 1
        && arguments.is_empty()
        && let Some(marker) = substitutions.get(&path[0])
    {
        *used = true;
        path[0] = marker.clone();
        return Ok(output);
    }
    let mut child = |syntax: &TypeExpr| replace(syntax, substitutions, depth + 1, nodes, used);
    match &mut output.kind {
        TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
            for argument in arguments {
                *argument = child(argument)?;
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
            for field in fields {
                field.ty = child(&field.ty)?;
            }
            if let Some(row) = row {
                **row = child(row)?;
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

pub(super) enum Slot<'a> {
    Element,
    Tuple(usize),
    Field(&'a str),
    MapKey,
    MapValue,
    Optional,
    Success,
    Error,
}
pub(super) fn transparent<'a>(
    mask: Option<(&'a TypeExpr, &'a BTreeSet<String>)>,
) -> Option<(&'a TypeExpr, &'a BTreeSet<String>)> {
    let (mut syntax, markers) = mask?;
    while let TypeKind::Name { path, arguments } = &syntax.kind {
        if arguments.len() == 1 && (path == &["Immut"] || path == &["Prelude", "Immut"]) {
            syntax = &arguments[0];
        } else {
            break;
        }
    }
    Some((syntax, markers))
}
pub(super) fn child<'a>(
    mask: Option<(&'a TypeExpr, &'a BTreeSet<String>)>,
    slot: Slot<'_>,
) -> Option<(&'a TypeExpr, &'a BTreeSet<String>)> {
    let (syntax, markers) = transparent(mask)?;
    let syntax = match (&syntax.kind, slot) {
        (TypeKind::Array { element, .. }, Slot::Element) => element.as_ref(),
        (TypeKind::Tuple(items), Slot::Tuple(index)) => items.get(index)?,
        (TypeKind::Record { fields, .. }, Slot::Field(name)) => {
            &fields.iter().find(|field| field.name == name)?.ty
        }
        (TypeKind::Map { key, .. }, Slot::MapKey) => key.as_ref(),
        (TypeKind::Map { value, .. }, Slot::MapValue) => value.as_ref(),
        (TypeKind::Optional(inner), Slot::Optional) => inner.as_ref(),
        (TypeKind::Name { path, arguments }, Slot::Optional) if matches!(path.as_slice(), [name] if name == "Option") => {
            arguments.first()?
        }
        (TypeKind::Name { path, arguments }, Slot::Success) if matches!(path.as_slice(), [name] if name == "Result") => {
            arguments.first()?
        }
        (TypeKind::Name { path, arguments }, Slot::Error) if matches!(path.as_slice(), [name] if name == "Result") => {
            arguments.get(1)?
        }
        _ => return None,
    };
    Some((syntax, markers))
}
