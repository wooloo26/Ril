//! Closed Const arguments enter Source graphs only after ordinary static sort
//! checking. Their normalized identities are opaque values, never type names.
use super::*;

pub(crate) fn static_parameter(parameter: &GenericParameter) -> bool {
    parameter
        .name
        .chars()
        .next()
        .is_some_and(char::is_lowercase)
        || matches!(
            parameter.bound.as_ref().map(|bound| &bound.kind),
            Some(TypeKind::KeyOf(_))
        )
}

pub(crate) fn simple_sort(ty: &TypeExpr) -> bool {
    match &ty.kind {
        TypeKind::Name { path, arguments } => {
            let full = path.join("::");
            let name = full.strip_prefix("Prelude::").unwrap_or(&full);
            (arguments.is_empty()
                && matches!(
                    name,
                    "bool"
                        | "int"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "bigint"
                        | "f32"
                        | "f64"
                        | "str"
                        | "bytes"
                ))
                || (matches!(name, "Option" | "Immut")
                    && arguments.len() == 1
                    && simple_sort(&arguments[0]))
        }
        TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => simple_sort(inner),
        TypeKind::Tuple(items) => items.iter().all(simple_sort),
        TypeKind::Map { key, value } => simple_sort(key) && simple_sort(value),
        TypeKind::Record { fields, row } => {
            row.is_none()
                && fields
                    .iter()
                    .all(|field| !field.mutable && simple_sort(&field.ty))
        }
        _ => false,
    }
}

pub(crate) fn closed_const_nominal_arguments(
    declaration: &TypeDeclaration,
    arguments: &[TypeExpr],
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
    work: &mut usize,
) -> std::result::Result<Option<Vec<crate::sema::effect_identity::ArgumentKey>>, String> {
    *work = work
        .checked_sub(declaration.generics.len() + arguments.len() + 1)
        .ok_or("Const Source arguments exceed their work bound")?;
    // Bound every original syntax tree before classifiers or the static
    // interpreter clone it. This is original declaration ingress only.
    for parameter in &declaration.generics {
        if let Some(bound) = &parameter.bound {
            charge_type_syntax_clone(bound, work)
                .ok_or("Const Source sort exceeds its syntax bound")?;
        }
    }
    for argument in arguments {
        charge_type_syntax_clone(argument, work)
            .ok_or("Const Source argument exceeds its syntax bound")?;
    }
    if !declaration.nominal
        || declaration.opaque
        || declaration.generics.is_empty()
        || arguments.len() != declaration.generics.len()
        || declaration.generics.iter().any(|parameter| {
            !static_parameter(parameter)
                || parameter.default.is_some()
                || !parameter.bound.as_ref().is_some_and(simple_sort)
        })
        || arguments
            .iter()
            .any(|argument| !effects::type_dependencies(argument).is_empty())
    {
        return Ok(None);
    }
    let normalized =
        normalize_constructor_arguments_bounded(declaration, arguments, declarations, layout, work)
            .map_err(|error| match error {
                ArgumentNormalizationError::Diagnostic(code, message) => {
                    format!("{code}: {message}")
                }
                ArgumentNormalizationError::Unsupported(message) => message,
            })?;
    normalized
        .arguments
        .iter()
        .map(|argument| {
            charge_type_syntax_clone(argument, work)
                .ok_or("normalized Const Source exceeds its syntax bound")?;
            let key = effects::bounded_argument_key(argument, &BTreeMap::new())
                .ok_or("normalized Const Source has no complete static identity")?;
            if !matches!(key, crate::sema::effect_identity::ArgumentKey::Closed(_)) {
                return Err("Const Source normalization produced a type argument".into());
            }
            Ok(key)
        })
        .collect::<std::result::Result<Vec<_>, String>>()
        .map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(
        case: &str,
    ) -> (
        TypeDeclaration,
        Vec<TypeExpr>,
        BTreeMap<String, TypeDeclaration>,
    ) {
        let source = ril_test::case_source(case);
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let arguments = parsed
            .program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Function(function) => function.body.as_ref(),
                _ => None,
            })
            .flat_map(|body| &body.statements)
            .find_map(|statement| {
                let StmtKind::Binding(binding) = &statement.kind else {
                    return None;
                };
                let ExprKind::Call { callee, .. } = &binding.value.kind else {
                    return None;
                };
                let ExprKind::Generic { base, arguments } = &callee.kind else {
                    return None;
                };
                matches!(&base.kind, ExprKind::Name(name) if name == "Token")
                    .then(|| arguments.clone())
            })
            .expect("fixture must contain its actual generic Token constructor");
        let declarations: BTreeMap<_, _> = parsed
            .program
            .statements
            .into_iter()
            .filter_map(|statement| match statement.kind {
                StmtKind::Type(declaration) => Some((declaration.name.clone(), declaration)),
                _ => None,
            })
            .collect();
        (declarations["Token"].clone(), arguments, declarations)
    }

    #[test]
    fn constructor_normalization_charges_one_root_for_clone_arguments_and_payload() {
        let (mut declaration, arguments, mut declarations) =
            fixture("tests/regressions/source-transport.ril::const-nominal-formal-value-conflict");
        let element = declaration.value.take().unwrap();
        declaration.value = Some(TypeExpr {
            hir_id: None,
            text: String::new(),
            span: element.span,
            kind: TypeKind::Array {
                length: Some(Box::new(Expr {
                    hir_id: None,
                    span: element.span,
                    kind: ExprKind::Name(declaration.generics[0].name.clone()),
                })),
                element: Box::new(element),
            },
        });
        declarations.insert(declaration.name.clone(), declaration.clone());
        let mut work = 16384;
        let normalized = normalize_constructor_arguments_bounded(
            &declaration,
            &arguments,
            &declarations,
            TargetLayout::POINTER64,
            &mut work,
        )
        .unwrap_or_else(|_| panic!("bounded normalized instance must be available"));
        assert!(normalized.payloads["Token"].is_some());
        let required = 16384 - work;
        assert!(required > 1);
        for allowance in [0, required - 1] {
            let mut remaining = allowance;
            assert!(
                normalize_constructor_arguments_bounded(
                    &declaration,
                    &arguments,
                    &declarations,
                    TargetLayout::POINTER64,
                    &mut remaining,
                )
                .is_err()
            );
            assert!(remaining <= allowance);
        }
    }

    #[test]
    fn const_source_normalization_accounts_for_failure_and_preserves_value_identity() {
        let (declaration, arguments, declarations) =
            fixture("tests/regressions/source-transport.ril::const-nominal-formal-source-graph");
        let mut work = 16384;
        let first = closed_const_nominal_arguments(
            &declaration,
            &arguments,
            &declarations,
            TargetLayout::POINTER64,
            &mut work,
        )
        .unwrap()
        .unwrap();
        assert!(work < 16384);
        let (_, other_arguments, _) =
            fixture("tests/regressions/source-transport.ril::const-nominal-formal-value-conflict");
        let other = closed_const_nominal_arguments(
            &declaration,
            &other_arguments,
            &declarations,
            TargetLayout::POINTER64,
            &mut work,
        )
        .unwrap()
        .unwrap();
        assert_ne!(first, other);
        let (_, wrong_arguments, _) =
            fixture("tests/regressions/source-transport.ril::const-nominal-formal-sort-conflict");
        let before = work;
        assert!(
            closed_const_nominal_arguments(
                &declaration,
                &wrong_arguments,
                &declarations,
                TargetLayout::POINTER64,
                &mut work,
            )
            .is_err()
        );
        assert!(work < before);
    }
}
