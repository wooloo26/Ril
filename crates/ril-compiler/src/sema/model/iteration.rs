//! One owned standard declaration shared by static contexts and value checking.
use ril_compiler_core::source::{FileId, Span};
use ril_syntax::ast::*;

pub(crate) fn step_declaration() -> TypeDeclaration {
    let span = Span {
        file: FileId(u32::MAX),
        start: 0,
        end: 0,
    };
    let variable = |name: &str| TypeExpr {
        text: name.into(),
        kind: TypeKind::Name {
            path: vec![name.into()],
            arguments: vec![],
        },
        span,
    };
    TypeDeclaration {
        visibility: Visibility::Public,
        is_halt: false,
        name: "Iter::Step".into(),
        generics: ["S", "T"]
            .into_iter()
            .map(|name| GenericParameter {
                name: name.into(),
                bound: None,
                default: None,
                span,
            })
            .collect(),
        value: None,
        variants: vec![
            Variant {
                name: "Done".into(),
                generics: vec![],
                payload: None,
                result: None,
                annotations: vec![],
                span,
            },
            Variant {
                name: "Yielded".into(),
                generics: vec![],
                payload: Some(TypeExpr {
                    text: String::new(),
                    kind: TypeKind::Tuple(vec![variable("T"), variable("S")]),
                    span,
                }),
                result: None,
                annotations: vec![],
                span,
            },
        ],
        opaque: false,
        nominal: false,
        span,
    }
}
