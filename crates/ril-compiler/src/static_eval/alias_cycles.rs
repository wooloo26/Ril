//! Reject only alias expansion edges which do not cross a nominal or sum guard.
use super::*;

pub(super) fn validate(evaluator: &Evaluator, output: &mut Evaluation) {
    let mut edges = BTreeMap::<String, BTreeSet<String>>::new();
    for (name, declaration) in &evaluator.declarations {
        if declaration.nominal || declaration.opaque || !declaration.variants.is_empty() {
            continue;
        }
        if let Some(value) = &declaration.value {
            let mut dependencies = BTreeSet::new();
            collect(value, &evaluator.declarations, &mut dependencies);
            edges.insert(name.clone(), dependencies);
        }
    }
    let mut diagnosed = BTreeSet::new();
    for name in edges.keys() {
        let mut pending = vec![(name.clone(), vec![name.clone()])];
        let mut visited = BTreeSet::new();
        while let Some((current, path)) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            for next in edges.get(&current).into_iter().flatten() {
                if next == name {
                    for member in &path {
                        if diagnosed.insert(member.clone()) {
                            output.failure(
                                Failure::Diagnostic(
                                    "E0313",
                                    "type alias expansion contains an unguarded structural cycle"
                                        .into(),
                                ),
                                evaluator.declarations[member].span,
                            );
                        }
                    }
                } else if edges.contains_key(next) {
                    let mut child = path.clone();
                    child.push(next.clone());
                    pending.push((next.clone(), child));
                }
            }
        }
    }
}

fn collect(
    ty: &TypeExpr,
    declarations: &BTreeMap<String, TypeDeclaration>,
    edges: &mut BTreeSet<String>,
) {
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            let joined = path.join("::");
            let normalized = joined.strip_prefix("Prelude::").unwrap_or(&joined);
            if matches!(normalized, "Option" | "Result")
                || declarations.get(&joined).is_some_and(|declaration| {
                    declaration.nominal || declaration.opaque || !declaration.variants.is_empty()
                })
            {
                return;
            }
            if declarations.contains_key(&joined) {
                edges.insert(joined);
            }
            for argument in arguments {
                collect(argument, declarations, edges);
            }
        }
        TypeKind::Optional(_) | TypeKind::TypeFunction { .. } | TypeKind::KindArrow { .. } => {}
        TypeKind::Array { element, .. } | TypeKind::Rest(element) | TypeKind::KeyOf(element) => {
            collect(element, declarations, edges)
        }
        TypeKind::Tuple(items) => {
            for item in items {
                collect(item, declarations, edges);
            }
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                collect(&field.ty, declarations, edges);
            }
            if let Some(row) = row {
                collect(row, declarations, edges);
            }
        }
        TypeKind::Map { key, value } => {
            collect(key, declarations, edges);
            collect(value, declarations, edges);
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                if let Some(ty) = &parameter.ty {
                    collect(ty, declarations, edges);
                }
            }
            if let Some(result) = result {
                collect(result, declarations, edges);
            }
        }
        TypeKind::Projection { base, .. } | TypeKind::ComputedProjection { base, .. } => {
            collect(base, declarations, edges)
        }
        TypeKind::Mapped { value, .. } => collect(value, declarations, edges),
        TypeKind::Computation(_) | TypeKind::Error => {}
    }
}
