use ril_compiler::{
    SyntaxKind,
    ast::{ArgumentSort, ControlOperation, ExprKind, StmtKind},
    frontend::{Frontend, UnitKind, frontend},
    hir::{DefinitionKind, ScopeKind},
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

#[test]
fn assignment_keeps_rhs_precedence_and_block_tail() {
    let input = "fn update() -> () {\n    var total = 0\n    total += 1 + 2\n}\n";
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let StmtKind::Function(function) = &result.files[&FileId(0)].program.statements[0].kind else {
        panic!("expected a function");
    };
    let body = function.body.as_ref().unwrap();
    let StmtKind::Expr {
        expression,
        terminated: false,
    } = &body.statements[1].kind
    else {
        panic!("expected a tail expression");
    };
    let ExprKind::Assignment {
        target,
        operator,
        value,
    } = &expression.kind
    else {
        panic!("expected an assignment");
    };
    assert_eq!(operator, "+=");
    assert!(matches!(&target.kind, ExprKind::Name(name) if name == "total"));
    assert!(matches!(&value.kind, ExprKind::Binary { operator, .. } if operator == "+"));
}

#[test]
fn block_where_shadowing_does_not_change_the_signature_type() {
    let input = r#"
type Local = i64
fn sample(argument: Local) -> () {
    let flag: Local = true
    let _ = flag
where
    type Local = bool
}

"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let selected_types: Vec<_> = hir
        .references
        .iter()
        .filter(|reference| reference.path == ["Local"])
        .map(|reference| hir.definitions[reference.definition.0].span.unwrap().start as usize)
        .collect();
    assert_eq!(
        selected_types,
        [
            input.find("type Local = i64").unwrap(),
            input.find("type Local = bool").unwrap(),
        ]
    );
}

#[test]
fn with_header_stops_before_the_remainder_and_return_targets_its_callable() {
    let input = r#"
fn pass<T>(config: i64, action: fn() @& -> T) -> T { action() }
fn sample() -> i64 {
    let value = 1
    with pass(value)
    (value)
    let value = value + 1
    with pass(value)
    return value
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    assert_eq!(parse.syntax().to_string(), input);
    let StmtKind::Function(function) = &parse.program.statements[1].kind else {
        panic!("expected the sample function");
    };
    let body = function.body.as_ref().unwrap();
    let StmtKind::HandlerApplication(call) = &body.statements[1].kind else {
        panic!("expected a with application");
    };
    assert!(matches!(&call.kind, ExprKind::Call { callee, arguments }
        if matches!(&callee.kind, ExprKind::Name(name) if name == "pass") && arguments.len() == 1));
    assert!(
        matches!(&body.statements[2].kind, StmtKind::Expr { expression, .. }
        if matches!(&expression.kind, ExprKind::Name(name) if name == "value"))
    );
    let hir = result.hir.unwrap();
    let [first, second] = &hir.handler_applications[..] else {
        panic!("expected two application sites");
    };
    assert_eq!(first.remainder_scope, second.calling_scope);
    let [transfer] = &hir.control_transfers[..] else {
        panic!("expected one explicit transfer");
    };
    assert_eq!(transfer.operation, ControlOperation::Return);
    assert_eq!(transfer.target, second.remainder_scope);
    assert_eq!(
        hir.scopes[transfer.target.0].kind,
        ScopeKind::HandlerRemainder
    );
    assert_eq!(result.sources.slice(transfer.span).unwrap(), b"return");
}

#[test]
fn system_operations_and_budget_keep_distinct_declaration_roles() {
    let input = r#"
halt fn sample() -> i64 {
    with Fiber::yield() -> resume ()
    with Div::exhausted() -> 0
    with Div::budget<i64>(10)
    42
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let yield_operation = hir
        .references
        .iter()
        .find(|reference| reference.path == ["Fiber", "yield"])
        .unwrap();
    assert_eq!(
        hir.definitions[yield_operation.definition.0].kind,
        DefinitionKind::EffectOperation
    );
    let budget = hir
        .references
        .iter()
        .find(|reference| reference.path == ["Div", "budget"])
        .unwrap();
    assert_eq!(
        budget.application.as_ref().unwrap().parameters,
        [ArgumentSort::Type]
    );
    let [transfer] = &hir.control_transfers[..] else {
        panic!("expected a resume operation");
    };
    assert_eq!(transfer.operation, ControlOperation::Resume);
    assert_eq!(hir.scopes[transfer.target.0].kind, ScopeKind::HandlerArm);
}

#[test]
fn row_constraints_share_named_binders_and_keep_anonymous_inputs_independent() {
    let input = r#"
fn project<T: { ..Rest }, U: { ..Rest }>(
    first: T, second: U, left: { .. }, right: { .. },
) -> { ..Rest } { .{ ..first } }
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let row_definitions: Vec<_> = hir
        .definitions
        .iter()
        .enumerate()
        .filter(|(_, definition)| definition.kind == DefinitionKind::RowParameter)
        .collect();
    let [(named, rest), (_, left), (_, right)] = row_definitions.as_slice() else {
        panic!("expected one named row and two anonymous rows");
    };
    assert_eq!(rest.name, "Rest");
    for definition in [left, right] {
        assert_eq!(
            result.sources.slice(definition.span.unwrap()).unwrap(),
            b".."
        );
    }
    assert_ne!(left.span, right.span);
    let rest_uses: Vec<_> = hir
        .references
        .iter()
        .filter(|reference| reference.path == ["Rest"])
        .map(|reference| reference.definition.0)
        .collect();
    assert_eq!(rest_uses, [*named; 3]);
}

#[test]
fn imported_row_type_is_resolved_before_introducing_an_implicit_binder() {
    let result = frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        let source = match path.to_str() {
            Some("root.ril") => {
                "use schema::{Fields}\nfn retain<T: { ..Fields }>(value: T) -> T { value }"
            }
            Some("schema.d.ril") => "pub type Fields = { name: str }",
            _ => return Err(io::Error::from(io::ErrorKind::NotFound)),
        };
        Ok(source.as_bytes().to_vec())
    })
    .unwrap();
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let row = hir
        .references
        .iter()
        .find(|reference| reference.path == ["Fields"])
        .unwrap();
    let definition = &hir.definitions[row.definition.0];
    assert_eq!(definition.kind, DefinitionKind::Type);
    assert_ne!(definition.span.unwrap().file, FileId(0));
    assert!(
        !hir.definitions
            .iter()
            .any(|definition| definition.kind == DefinitionKind::RowParameter)
    );
}

#[test]
fn storage_modes_share_parameter_identity_and_preserve_qualified_sort() {
    let input =
        "type MemberMode = i64\ntype Storage<T, M: ril/reflect::MemberMode> = ([M]T, [str: M T])\n";
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let qualified = hir
        .references
        .iter()
        .find(|reference| reference.path == ["ril/reflect", "MemberMode"])
        .unwrap();
    assert!(hir.definitions[qualified.definition.0].span.is_none());
    let uses: Vec<_> = hir
        .references
        .iter()
        .filter(|reference| reference.path == ["M"])
        .collect();
    let [array, map] = uses.as_slice() else {
        panic!("expected two storage mode uses");
    };
    assert_eq!(array.definition, map.definition);
    assert_eq!(
        hir.definitions[array.definition.0].kind,
        DefinitionKind::GenericParameter
    );
    assert_eq!(result.sources.slice(map.span).unwrap(), b"M");
}
