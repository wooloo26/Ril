use ril_compiler::{
    SyntaxKind,
    ast::{ArgumentSort, ExprKind, StmtKind},
    frontend::{Frontend, UnitKind, frontend},
    source::FileId,
};
use std::{io, path::Path};

fn compile(input: &str) -> Frontend {
    frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        if path == Path::new("root.ril") {
            Ok(input.as_bytes().to_vec())
        } else {
            Err(io::Error::from(io::ErrorKind::NotFound))
        }
    })
    .unwrap()
}

#[test]
fn preserves_cst_text_and_recovers_next_statement() {
    let input = "fn recover() -> () {\r\n    let bad = [1, 2)\r\n    let good = 3\r\n}\r\n";
    let result = compile(input);
    let parse = &result.files[&FileId(0)];
    assert_eq!(parse.syntax().to_string(), input);
    assert!(
        parse
            .syntax()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Recovery && node.to_string() == ")")
    );
    let [statement] = &parse.program.statements[..] else {
        panic!("expected one function");
    };
    let StmtKind::Function(function) = &statement.kind else {
        panic!("expected a function");
    };
    assert_eq!(function.body.as_ref().unwrap().statements.len(), 2);
    let diagnostic = &result.diagnostics[0];
    let span = diagnostic.labels[0].span;
    assert_eq!(diagnostic.code, "E0123");
    assert_eq!(result.sources.slice(span).unwrap(), b")");
    assert_eq!(
        result.sources.get(span.file).unwrap().location(span.start),
        (2, 20)
    );
}

#[test]
fn alias_keeps_application_head_until_shadowed_by_a_parameter() {
    let input = r#"
fn target<flag: bool>(x: i64) -> i64 { if flag { x } else { 0 } }
fn apply() -> i64 {
    let alias = target
    alias<true && false>(1)
}
fn compare(target: i64) -> bool { target < 2 && 3 > (1) }
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let application = hir
        .references
        .iter()
        .find(|reference| reference.path == ["alias"] && reference.application.is_some())
        .expect("alias retains the application's head");
    let signature = application.application.as_ref().unwrap();
    assert_eq!(signature.parameters, [ArgumentSort::Value]);
    assert_eq!(hir.definitions[signature.item.0].name, "target");
    assert_eq!(hir.definitions[application.definition.0].name, "alias");
    let compare = hir
        .references
        .iter()
        .find(|reference| {
            reference.path == ["target"]
                && reference.span.start as usize > input.find("fn compare").unwrap()
        })
        .unwrap();
    assert!(compare.application.is_none());

    let StmtKind::Function(function) = &result.files[&FileId(0)].program.statements[2].kind else {
        panic!("expected compare function");
    };
    let StmtKind::Expr { expression, .. } = &function.body.as_ref().unwrap().statements[0].kind
    else {
        panic!("expected a tail expression");
    };
    assert!(matches!(&expression.kind, ExprKind::Binary { operator, .. } if operator == "&&"));
}

#[test]
fn angle_rescanning_preserves_operator_bytes() {
    let input = "type Box<T>= { value: T }\nmeta let SAME = <Box<i64>>==<Box<i64>>\n";
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    let syntax = parse.syntax();
    assert_eq!(syntax.to_string(), input);
    let tokens = syntax
        .descendants_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token);
    assert_eq!(tokens.filter(|token| token.text() == "==").count(), 1);
}
