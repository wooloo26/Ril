use ril_compiler::{
    ast::{ExprKind, PatternKind, StmtKind, TypeKind},
    frontend::{UnitKind, frontend},
    source::FileId,
};
use std::{io, path::Path};

#[test]
fn array_pattern_lengths_parse_type_quotes_as_ordinary_types() {
    let input = r#"
type Select = \T -> match <T> {
    <[byte_size(<[]i64>)]let Item> -> <Item>,
    _ -> <never>,
}
"#;
    let result = frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        if path == Path::new("root.ril") {
            Ok(input.as_bytes().to_vec())
        } else {
            Err(io::Error::from(io::ErrorKind::NotFound))
        }
    })
    .unwrap();
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    assert_eq!(parse.syntax().to_string(), input);
    let StmtKind::Type(declaration) = &parse.program.statements[0].kind else {
        panic!("expected type declaration");
    };
    let TypeKind::TypeFunction { body, .. } = &declaration.value.as_ref().unwrap().kind else {
        panic!("expected type function");
    };
    let ExprKind::Match { arms, .. } = &body.kind else {
        panic!("expected static match");
    };
    let PatternKind::Type(ty) = &arms[0].pattern.kind else {
        panic!("expected type pattern");
    };
    let TypeKind::ArrayPattern {
        length: Some(length),
        element,
    } = &ty.kind
    else {
        panic!("expected array pattern");
    };
    assert!(matches!(&element.kind, TypeKind::TypeBinder(name) if name == "Item"));
    let ExprKind::Call { arguments, .. } = &length.kind else {
        panic!("expected byte_size call");
    };
    let ExprKind::TypeValue(quoted) = &arguments[0].value.kind else {
        panic!("expected ordinary type quote");
    };
    assert!(matches!(&quoted.kind, TypeKind::Array { access: None, .. }));
    let hir = result.hir.as_ref().unwrap();
    let binder = hir
        .definitions
        .iter()
        .position(|definition| definition.name == "Item")
        .unwrap();
    assert!(
        hir.references
            .iter()
            .any(|reference| { reference.path == ["Item"] && reference.definition.0 == binder })
    );
}
