//! Owned schemas preserve stream-operation callable modes and latent rows.
use super::*;

pub(super) fn operation_type(syntax: &TypeExpr) -> Option<TypeExpr> {
    let TypeKind::Name { path, arguments } = &syntax.kind else {
        return None;
    };
    let name = path.join("::");
    if !matches!(name.as_str(), "Io::ReadOps" | "Io::WriteOps") || arguments.len() != 1 {
        return None;
    }
    let span = syntax.span;
    let read = name == "Io::ReadOps";
    let named = |name: &str| TypeExpr {
        hir_id: None,
        text: name.into(),
        kind: TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments: vec![],
        },
        span,
    };
    let parameter = |name: &str, ty: TypeExpr, mode| Parameter {
        pattern: Pattern {
            hir_id: None,
            kind: PatternKind::Name(name.into()),
            span,
        },
        mode,
        ty: Some(ty),
        default: None,
        span,
    };
    let result = if read {
        TypeExpr {
            hir_id: None,
            text: String::new(),
            kind: TypeKind::Name {
                path: vec!["Prelude".into(), "Result".into()],
                arguments: vec![named("Io::ReadChunk"), named("Io::IoError")],
            },
            span,
        }
    } else {
        named("Io::WriteProgress")
    };
    let callable = TypeExpr {
        hir_id: None,
        text: String::new(),
        kind: TypeKind::Callable {
            parameters: vec![
                parameter("ril__io_receiver", arguments[0].clone(), ParameterMode::Mut),
                parameter(
                    "ril__io_input",
                    named(if read { "int" } else { "bytes" }),
                    ParameterMode::Read,
                ),
            ],
            result: Some(Box::new(result)),
            annotations: vec![Annotation {
                kind: AnnotationKind::Capability,
                text: "&mut".into(),
                span,
            }],
        },
        span,
    };
    Some(TypeExpr {
        hir_id: None,
        text: String::new(),
        kind: TypeKind::Record {
            fields: vec![TypeField {
                name: if read { "read" } else { "write" }.into(),
                mutable: false,
                ty: callable,
                span,
            }],
            row: None,
        },
        span,
    })
}

/// Only complete data schemas are reified. A semantic callable shape omits
/// modes/rows and therefore cannot supply a source identity by itself.
pub(super) fn data_type(ty: &Ty, span: Span) -> Option<TypeExpr> {
    let kind = match ty {
        Ty::Unit => TypeKind::Tuple(vec![]),
        Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Str | Ty::Bytes | Ty::Never | Ty::Named(_) => {
            let name = match ty {
                Ty::Bool => "bool",
                Ty::Int(name) | Ty::Float(name) | Ty::Named(name) => name,
                Ty::Str => "str",
                Ty::Bytes => "bytes",
                Ty::Never => "never",
                _ => unreachable!(),
            };
            TypeKind::Name {
                path: name.split("::").map(str::to_owned).collect(),
                arguments: vec![],
            }
        }
        Ty::Optional(inner) => TypeKind::Optional(Box::new(data_type(inner, span)?)),
        Ty::Immutable(inner) => TypeKind::Name {
            path: vec!["Prelude".into(), "Immut".into()],
            arguments: vec![data_type(inner, span)?],
        },
        Ty::Array(element) => TypeKind::Array {
            length: None,
            element: Box::new(data_type(element, span)?),
        },
        Ty::Set(element) => TypeKind::Name {
            path: vec!["Prelude".into(), "Set".into()],
            arguments: vec![data_type(element, span)?],
        },
        Ty::Map(key, value) => TypeKind::Map {
            key: Box::new(data_type(key, span)?),
            value: Box::new(data_type(value, span)?),
        },
        Ty::Result(ok, error) => TypeKind::Name {
            path: vec!["Prelude".into(), "Result".into()],
            arguments: vec![data_type(ok, span)?, data_type(error, span)?],
        },
        Ty::Tuple(items) => TypeKind::Tuple(
            items
                .iter()
                .map(|ty| data_type(ty, span))
                .collect::<Option<_>>()?,
        ),
        Ty::Record(fields) => TypeKind::Record {
            fields: fields
                .iter()
                .map(|(name, (mutable, ty))| {
                    Some(TypeField {
                        name: name.clone(),
                        mutable: *mutable,
                        ty: data_type(ty, span)?,
                        span,
                    })
                })
                .collect::<Option<_>>()?,
            row: None,
        },
        _ => return None,
    };
    Some(TypeExpr {
        hir_id: None,
        text: String::new(),
        kind,
        span,
    })
}
