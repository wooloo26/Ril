//! Owned schemas preserve stream-operation callable modes and latent rows.
use super::*;

/// Reify the receiver's declared view, never its backing graph cardinality.
/// Erased Ty is a fallback only when no array/callable identity can be lost.
pub(super) fn receiver_type(value: &Value, ty: &Ty, span: Span) -> Option<TypeExpr> {
    if let Some(witness) = &value.source_type_witness {
        return witness.validate_closed().then(|| witness.syntax.clone());
    }
    fn complete(ty: &Ty) -> bool {
        match ty {
            Ty::Array(_)
            | Ty::Callable(..)
            | Ty::Unknown
            | Ty::Generic(_)
            | Ty::OpenRecord { .. }
            | Ty::Applied { .. }
            | Ty::Projection { .. }
            | Ty::StaticKey(_)
            | Ty::NumericHole(_) => false,
            Ty::Immutable(inner) | Ty::Optional(inner) | Ty::Set(inner) | Ty::Range(inner) => {
                complete(inner)
            }
            Ty::Result(a, b) | Ty::Map(a, b) => complete(a) && complete(b),
            Ty::Tuple(items) => items.iter().all(complete),
            Ty::Record(fields) => fields.values().all(|(_, ty)| complete(ty)),
            _ => true,
        }
    }
    complete(ty).then(|| data_type(ty, span)).flatten()
}

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
        text: name.into(),
        kind: TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments: vec![],
        },
        span,
    };
    let parameter = |name: &str, ty: TypeExpr, mode| Parameter {
        pattern: Pattern {
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
        text: String::new(),
        kind,
        span,
    })
}
