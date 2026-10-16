//! Rigid constructor result recovery does not invert static computations.
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};
fn replace_type_parameters(syntax: &TypeExpr, arguments: &BTreeMap<String, TypeExpr>) -> TypeExpr {
    let mut syntax = syntax.clone();
    match &mut syntax.kind {
        TypeKind::Name {
            path,
            arguments: nested,
        } => {
            if nested.is_empty()
                && path.len() == 1
                && let Some(argument) = arguments.get(&path[0])
            {
                return argument.clone();
            }
            for ty in nested {
                *ty = replace_type_parameters(ty, arguments);
            }
        }
        TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Array { element: inner, .. } => {
            **inner = replace_type_parameters(inner, arguments);
        }
        TypeKind::Map { key, value } => {
            **key = replace_type_parameters(key, arguments);
            **value = replace_type_parameters(value, arguments);
        }
        TypeKind::Tuple(items) => {
            for ty in items {
                *ty = replace_type_parameters(ty, arguments);
            }
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                field.ty = replace_type_parameters(&field.ty, arguments);
            }
            if let Some(row) = row {
                **row = replace_type_parameters(row, arguments);
            }
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                if let Some(ty) = &mut parameter.ty {
                    *ty = replace_type_parameters(ty, arguments);
                }
            }
            if let Some(result) = result {
                **result = replace_type_parameters(result, arguments);
            }
        }
        // Computation is deliberately not substituted for an inverse proof.
        _ => {}
    }
    syntax
}

pub(super) fn recoverable_parameter(
    syntax: &TypeExpr,
    parameter: &str,
    declarations: &BTreeMap<String, TypeDeclaration>,
    seen: &mut BTreeSet<String>,
    depth: usize,
) -> bool {
    if depth >= 64 {
        return false;
    }
    let descend = |ty: &TypeExpr, seen: &mut BTreeSet<String>| {
        recoverable_parameter(ty, parameter, declarations, seen, depth + 1)
    };
    match &syntax.kind {
        TypeKind::Name { path, arguments } => {
            let name = path.join("::");
            if name == parameter && arguments.is_empty() {
                return true;
            }
            if let Some(declaration) = declarations.get(&name)
                && !declaration.nominal
                && !declaration.opaque
                && declaration.variants.is_empty()
            {
                if !seen.insert(name.clone()) {
                    return false;
                }
                let actual: BTreeMap<_, _> = declaration
                    .generics
                    .iter()
                    .enumerate()
                    .filter_map(|(index, generic)| {
                        arguments
                            .get(index)
                            .or(generic.default.as_ref())
                            .map(|argument| (generic.name.clone(), argument.clone()))
                    })
                    .collect();
                let result = declaration
                    .value
                    .as_ref()
                    .is_some_and(|value| descend(&replace_type_parameters(value, &actual), seen));
                seen.remove(&name);
                return result;
            }
            arguments
                .iter()
                .any(|argument| descend(argument, &mut seen.clone()))
        }
        TypeKind::Optional(inner)
        | TypeKind::Rest(inner)
        | TypeKind::Array { element: inner, .. } => descend(inner, seen),
        TypeKind::Tuple(items) => items.iter().any(|ty| descend(ty, &mut seen.clone())),
        TypeKind::Map { key, value } => descend(key, &mut seen.clone()) || descend(value, seen),
        TypeKind::Record { fields, row } => {
            fields
                .iter()
                .any(|field| descend(&field.ty, &mut seen.clone()))
                || row.as_ref().is_some_and(|row| descend(row, seen))
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            parameters.iter().any(|parameter| {
                parameter
                    .ty
                    .as_ref()
                    .is_some_and(|ty| descend(ty, &mut seen.clone()))
            }) || result.as_ref().is_some_and(|result| descend(result, seen))
        }
        // A computation/projection/type function cannot be inverted to recover
        // a parameter, even when it happens to mention that name syntactically.
        _ => false,
    }
}
