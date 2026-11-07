use ril_compiler::{
    SyntaxKind,
    ast::{
        Annotation, AnnotationKind, ArgumentSort, ControlOperation, EffectRow, ExprKind,
        MemberAccess, ParameterMode, RecordMember, ReturnDependencyMode, ReturnMode, StateClause,
        StateMode, StateOwner, StmtKind, StringPart, TypeKind, ValueTestKind,
    },
    frontend::{Frontend, UnitKind, frontend},
    hir::{CallableLayer, CompilationUnitOrigin, DefinitionKind, EffectMember, ScopeKind},
    library::PrimitiveId,
    source::FileId,
    text::{Alignment, Conversion},
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
fn reception_keeps_declared_member_modes_and_explicit_observation_spans() {
    let input = r#"
type Cell = { var count: i64 }
type Slot<T> = { var via item: T, ref observed: T, ^mut shared: T, mut owned: T }
fn example(ref source: Cell) -> () {
    let mut slot = Slot.{ item: ref source }
    slot.item = ref source.count
    let _ = (ref source)
    let _ = (var ref source, source)
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let statements = &result.files[&FileId(0)].program.statements;
    let StmtKind::Type(slot) = &statements[1].kind else {
        panic!("expected Slot declaration");
    };
    let TypeKind::Record { fields, .. } = &slot.value.as_ref().unwrap().kind else {
        panic!("expected record schema");
    };
    for (field, replaceable, access, text) in [
        (&fields[0], true, MemberAccess::Via, "var via"),
        (&fields[1], false, MemberAccess::Ref, "ref"),
        (&fields[2], false, MemberAccess::SharedMut, "^mut"),
        (&fields[3], false, MemberAccess::Mut, "mut"),
    ] {
        let mode = field.mode.unwrap();
        assert_eq!((mode.replaceable, mode.access), (replaceable, access));
        assert_eq!(result.sources.slice(mode.span).unwrap(), text.as_bytes());
    }

    let StmtKind::Function(function) = &statements[2].kind else {
        panic!("expected example function");
    };
    let body = &function.body.as_ref().unwrap().statements;
    let StmtKind::Binding(binding) = &body[0].kind else {
        panic!("expected slot initialization");
    };
    let ExprKind::Record { members, .. } = &binding.initializer.as_ref().unwrap().kind else {
        panic!("expected record initializer");
    };
    let RecordMember::Field(field) = &members[0] else {
        panic!("expected item field");
    };
    let ExprKind::Observe { marker, operand } = &field.value.kind else {
        panic!("expected explicit observation expression");
    };
    assert!(field.mode.is_none());
    assert_eq!(result.sources.slice(*marker).unwrap(), b"ref");
    assert!(matches!(&operand.kind, ExprKind::Name(name) if name == "source"));
    assert!(
        result
            .hir
            .as_ref()
            .unwrap()
            .references
            .iter()
            .any(|reference| { reference.span == operand.span && reference.path == ["source"] })
    );

    let StmtKind::Expr { expression, .. } = &body[1].kind else {
        panic!("expected assignment");
    };
    let ExprKind::Assignment { value, .. } = &expression.kind else {
        panic!("expected assignment expression");
    };
    assert!(matches!(&value.kind, ExprKind::Observe { operand, .. }
        if matches!(&operand.kind, ExprKind::Field { field, .. } if field == "count")));

    let StmtKind::Binding(binding) = &body[2].kind else {
        panic!("expected grouped observation");
    };
    assert!(matches!(
        &binding.initializer.as_ref().unwrap().kind,
        ExprKind::Observe { .. }
    ));
    let StmtKind::Binding(binding) = &body[3].kind else {
        panic!("expected tuple binding");
    };
    let ExprKind::Tuple(items) = &binding.initializer.as_ref().unwrap().kind else {
        panic!("expected tuple");
    };
    assert!(matches!(&items[0].kind, ExprKind::TupleMember { mode, .. }
        if mode.replaceable && mode.access == MemberAccess::Ref));
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

#[test]
fn constructor_test_alias_keeps_tag_identity_without_converting_value_leaves() {
    let input = r#"
use Option::{Some as present}
let WANTED = 42
fn expected(value: i64) -> i64 { value }
fn check(value: ?i64) -> bool {
    value is present(WANTED | expected(value: 0))
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    assert_eq!(parse.syntax().to_string(), input);
    let StmtKind::Function(check) = &parse.program.statements.last().unwrap().kind else {
        panic!("expected check function");
    };
    let StmtKind::Expr { expression, .. } = &check.body.as_ref().unwrap().statements[0].kind else {
        panic!("expected tail expression");
    };
    let ExprKind::Is { test, .. } = &expression.kind else {
        panic!("expected is test");
    };
    let ValueTestKind::Constructor {
        arguments: Some(arguments),
        ..
    } = &test.kind
    else {
        panic!("expected resolved constructor payload test");
    };
    let ValueTestKind::Alternative(alternatives) = &arguments[0].kind else {
        panic!("expected payload alternatives");
    };
    let [constant, call] = alternatives.as_slice() else {
        panic!("expected two alternatives");
    };
    assert!(matches!(&constant.kind, ValueTestKind::Value(value)
        if matches!(&value.kind, ExprKind::Name(name) if name == "WANTED")));
    assert!(matches!(&call.kind, ValueTestKind::Value(value)
        if matches!(&value.kind, ExprKind::Call { arguments, .. }
            if arguments[0].label.as_deref() == Some("value"))));
    let hir = result.hir.unwrap();
    let alias = hir
        .references
        .iter()
        .find(|reference| reference.path == ["present"])
        .unwrap();
    assert_eq!(result.sources.slice(alias.span).unwrap(), b"present");
    assert_eq!(hir.definitions[alias.constructor.unwrap().0].name, "Some");
    let value = hir
        .references
        .iter()
        .find(|reference| reference.path == ["WANTED"])
        .unwrap();
    assert!(value.constructor.is_none());
}

#[test]
fn parenthesis_shape_respects_generic_commas_and_tuple_test_alternatives() {
    let input = r#"
fn select<T, U>(value: T, _other: U) -> T { value }
fn grouped(value: i64) -> bool { value is (select<i64, str>(1, "") | 2) }
fn structured(value: (i64, i64)) -> bool { value is (-3..=-1 | 1..=3, _) }
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    let test = |index: usize| {
        let StmtKind::Function(function) = &parse.program.statements[index].kind else {
            panic!("expected a function");
        };
        let StmtKind::Expr { expression, .. } = &function.body.as_ref().unwrap().statements[0].kind
        else {
            panic!("expected tail expression");
        };
        let ExprKind::Is { test, .. } = &expression.kind else {
            panic!("expected is test");
        };
        &test.kind
    };
    assert!(matches!(test(1), ValueTestKind::Value(expression)
        if matches!(&expression.kind, ExprKind::Binary { operator, .. } if operator == "|")));
    let ValueTestKind::Tuple(elements) = test(2) else {
        panic!("expected a tuple test");
    };
    assert!(
        matches!(&elements[0].kind, ValueTestKind::Alternative(alternatives)
        if alternatives.iter().all(|test| matches!(test.kind, ValueTestKind::Range { .. })))
    );
    assert!(matches!(elements[1].kind, ValueTestKind::Wildcard));
}

#[test]
fn nullary_constructor_import_and_stored_value_have_different_test_roles() {
    let input = r#"
use Option::{None as empty}
let SAVED: ?i64 = None
fn check(value: ?i64) -> bool { value is SAVED | empty }
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let saved = hir
        .references
        .iter()
        .find(|reference| reference.path == ["SAVED"])
        .unwrap();
    assert_eq!(
        hir.definitions[saved.definition.0].kind,
        DefinitionKind::Binding
    );
    assert!(saved.constructor.is_none());
    let empty = hir
        .references
        .iter()
        .find(|reference| reference.path == ["empty"])
        .unwrap();
    assert_eq!(hir.definitions[empty.constructor.unwrap().0].name, "None");
}

#[test]
fn interpolation_reuses_declaration_lookup_and_preserves_cst_and_format_spans() {
    let input = r#"
fn choose<flag: bool>(value: i64) -> i64 { if flag { value } else { 0 } }
fn render(value: i64) -> str {
    let alias = choose
    "前{{缀}} {alias<true && false>(value):🙂^08x} 后"
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    let syntax = parse.syntax();
    assert_eq!(syntax.to_string(), input);
    let node = syntax
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Interpolation)
        .unwrap();
    assert_eq!(node.to_string(), "{alias<true && false>(value):🙂^08x}");
    let StmtKind::Function(render) = &parse.program.statements[1].kind else {
        panic!("expected render function");
    };
    let StmtKind::Expr { expression, .. } = &render.body.as_ref().unwrap().statements[1].kind
    else {
        panic!("expected string expression");
    };
    let ExprKind::Interpolated(parts) = &expression.kind else {
        panic!("expected interpolated string");
    };
    let [
        StringPart::Text(prefix),
        StringPart::Interpolation {
            format: Some(format),
            span,
            ..
        },
        StringPart::Text(suffix),
    ] = parts.as_slice()
    else {
        panic!("expected text around a formatted expression");
    };
    assert_eq!(prefix, "前{缀} ");
    assert_eq!(suffix, " 后");
    assert_eq!(
        result.sources.slice(*span).unwrap(),
        node.to_string().as_bytes()
    );
    assert_eq!(
        result.sources.slice(format.span).unwrap(),
        "🙂^08x".as_bytes()
    );
    assert_eq!(format.spec.fill, Some('🙂'));
    assert_eq!(format.spec.alignment, Some(Alignment::Center));
    assert_eq!(format.spec.width, Some(8));
    assert!(format.spec.leading_zero);
    assert_eq!(format.spec.conversion, Some(Conversion::LowerHex));

    let hir = result.hir.unwrap();
    let applied = hir
        .references
        .iter()
        .find(|reference| reference.path == ["alias"])
        .unwrap();
    let signature = applied.application.as_ref().unwrap();
    assert_eq!(signature.parameters, [ArgumentSort::Value]);
    assert_eq!(hir.definitions[signature.item.0].name, "choose");
}

#[test]
fn invalid_embedded_byte_escape_is_reported_once() {
    let input = r#"let BAD = "é {len(b"\xG0")}""#;
    let result = compile(input);
    let [diagnostic] = &result.diagnostics[..] else {
        panic!(
            "expected one lexical diagnostic, got {:?}",
            result.diagnostics
        );
    };
    assert_eq!(diagnostic.code, "E0110");
    assert_eq!(
        result.sources.slice(diagnostic.labels[0].span).unwrap(),
        b"\\x"
    );
    assert_eq!(result.files[&FileId(0)].syntax().to_string(), input);
}

#[test]
fn interpolation_brace_recovery_preserves_next_declaration() {
    let input = "let BAD = \"é{1\"\nlet GOOD = \"正常\"\n";
    let result = compile(input);
    let [diagnostic] = &result.diagnostics[..] else {
        panic!(
            "expected one lexical diagnostic, got {:?}",
            result.diagnostics
        );
    };
    assert_eq!(diagnostic.code, "E0112");
    assert_eq!(
        result.sources.slice(diagnostic.labels[0].span).unwrap(),
        b"{1"
    );
    let parse = &result.files[&FileId(0)];
    assert_eq!(parse.syntax().to_string(), input);
    assert_eq!(parse.program.statements.len(), 2);
}

#[test]
fn callable_type_retains_independent_row_markers_and_return_dependency_mode() {
    let input = r#"
type Cell = { var count: i64 }
type View = fn(ref item: Cell) @ &return{ref item} & -> new { ref value: Cell }
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let parse = &result.files[&FileId(0)];
    assert_eq!(parse.syntax().to_string(), input);
    let StmtKind::Type(view) = &parse.program.statements[1].kind else {
        panic!("expected callable type declaration");
    };
    let TypeKind::Callable { annotations, .. } = &view.value.as_ref().unwrap().kind else {
        panic!("expected a callable type");
    };
    let [
        Annotation {
            kind: AnnotationKind::Effects(EffectRow::Open),
            span: effects,
        },
        Annotation {
            kind: AnnotationKind::State(StateClause::Return(dependencies)),
            ..
        },
        Annotation {
            kind: AnnotationKind::State(StateClause::Open),
            span: state,
        },
    ] = annotations.as_slice()
    else {
        panic!("expected distinct open markers and contained return sources");
    };
    let [dependency] = dependencies.as_slice() else {
        panic!("expected one return dependency");
    };
    assert_eq!(dependency.mode, ReturnDependencyMode::Ref);
    assert_eq!(result.sources.slice(*effects).unwrap(), b"@");
    assert_eq!(result.sources.slice(*state).unwrap(), b"&");
    assert_eq!(result.sources.slice(dependency.name.span).unwrap(), b"item");
    let hir = result.hir.unwrap();
    let reference = hir
        .references
        .iter()
        .find(|reference| reference.span == dependency.name.span)
        .unwrap();
    assert_eq!(
        hir.definitions[reference.definition.0].kind,
        DefinitionKind::Parameter
    );
}

#[test]
fn state_groups_keep_source_modes_and_the_actual_lexical_owner() {
    let input = r#"
var visits = 0
let LIMIT = 3
fn tick() &up(sub){mut visits, LIMIT} -> () { visits += LIMIT }
fn outer() -> i64 {
    var count = 0
    middle()
where
    fn middle() &up{mut count} -> i64 {
        inner()
    where
        fn inner() &up(outer){mut count} -> i64 {
            count += 1
            count
        }
    }
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let [module, direct, farther] = hir.state_source_groups.as_slice() else {
        panic!("expected module, direct capture, and farther capture groups");
    };
    assert_eq!(module.owner, StateOwner::Module);
    assert!(module.source_layer.is_none());
    assert_eq!(
        module
            .items
            .iter()
            .map(|item| item.mode)
            .collect::<Vec<_>>(),
        [StateMode::Mut, StateMode::Read]
    );
    assert_eq!(
        result.sources.slice(module.items[0].span).unwrap(),
        b"visits"
    );
    let layer = farther.source_layer.unwrap();
    assert_eq!(direct.source_layer, Some(layer));
    assert_eq!(direct.items[0].definition, farther.items[0].definition);
    let Some(CallableLayer::Named(outer)) = hir.scopes[layer.0].callable_layer else {
        panic!("expected a named callable layer");
    };
    assert_eq!(hir.definitions[outer.0].name, "outer");
    let StateOwner::Named { span, .. } = farther.owner else {
        panic!("expected a written owner");
    };
    assert_eq!(result.sources.slice(span).unwrap(), b"outer");
}

#[test]
fn effect_projection_keeps_alias_edges_and_handler_instance_syntax() {
    let input = r#"
eff Read<T> { get() -> T }
eff Inner<T> { Read<T> }
eff Both { Inner<i64>, Inner<str> }
fn demo() -> (i64, str) {
    with {
        Inner<i64>::get() -> resume 7,
        Read<str>::get() -> resume "text",
    }
    let number: i64 = Both::get()
    let text: str = Both::get()
    (number, text)
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let projected = hir
        .references
        .iter()
        .find(|reference| reference.path == ["Both", "get"])
        .unwrap();
    assert_eq!(
        hir.definitions[projected.definition.0].kind,
        DefinitionKind::EffectProjection
    );
    let EffectMember::Projection { alias, operations } = &hir.effect_members[&projected.definition]
    else {
        panic!("expected an effect-set projection");
    };
    let [operation] = operations.as_slice() else {
        panic!("expected one operation declaration");
    };
    let EffectMember::Operation { family: read } = hir.effect_members[operation] else {
        panic!("expected a real effect operation declaration");
    };
    let [integer, text] = hir.effect_aliases[alias].as_slice() else {
        panic!("expected two instance edges");
    };
    assert_eq!(integer.effect, text.effect);
    assert_eq!(hir.definitions[integer.effect.0].name, "Inner");
    assert_eq!(integer.arguments[0].text, "i64");
    assert_eq!(text.arguments[0].text, "str");
    let [inner] = hir.effect_aliases[&integer.effect].as_slice() else {
        panic!("expected the nested effect alias");
    };
    assert_eq!(inner.effect, read);
    let symbolic = hir
        .references
        .iter()
        .find(|reference| reference.span == inner.arguments[0].span)
        .unwrap();
    assert_eq!(
        hir.definitions[symbolic.definition.0].kind,
        DefinitionKind::GenericParameter
    );

    let handled: Vec<_> = hir
        .references
        .iter()
        .filter_map(|reference| {
            let instance = reference.effect_instance.as_ref()?;
            Some((instance, instance.handler?))
        })
        .collect();
    let [(first, first_arm), (second, second_arm)] = handled.as_slice() else {
        panic!("expected two resolved handler targets");
    };
    assert_eq!(first_arm.group, second_arm.group);
    assert_ne!(first_arm.arm, second_arm.arm);
    assert_eq!(first.arguments.as_ref().unwrap()[0].text, "i64");
    assert_eq!(second.arguments.as_ref().unwrap()[0].text, "str");
    assert_eq!(second.operation, *operation);
    assert!(
        hir.control_transfers
            .iter()
            .any(|transfer| transfer.operation == ControlOperation::Resume
                && transfer.target == first_arm.arm)
    );
    assert!(
        hir.control_transfers
            .iter()
            .any(|transfer| transfer.operation == ControlOperation::Resume
                && transfer.target == second_arm.arm)
    );
}

#[test]
fn bundled_numeric_lookup_uses_one_declaration_for_ambient_and_explicit_paths() {
    let input = r#"
use ril/numeric as Conversion
use ril/numeric::{convert as coerce}
fn read(value: u8) -> (?i64, ?i64, ?i64) {
    (Numeric::convert<i64>(value), Conversion::convert<i64>(value), coerce<i64>(value))
}
"#;
    let result = frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        assert_eq!(
            path,
            Path::new("root.ril"),
            "bundled imports must not read project files"
        );
        Ok(input.as_bytes().to_vec())
    })
    .unwrap();
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let conversions: Vec<_> = hir
        .references
        .iter()
        .filter(|reference| {
            hir.primitives.get(&reference.definition) == Some(&PrimitiveId::NumericConvert)
        })
        .collect();
    let [ambient, namespace_alias, selective] = conversions.as_slice() else {
        panic!("expected three uses of the canonical conversion");
    };
    assert_eq!(ambient.definition, namespace_alias.definition);
    assert_eq!(ambient.definition, selective.definition);
    let definition = &hir.definitions[ambient.definition.0];
    assert_eq!(definition.kind, DefinitionKind::Primitive);
    let span = definition.span.unwrap();
    assert_eq!(
        result.sources.get(span.file).unwrap().path(),
        Path::new("ril/numeric.ril")
    );
    assert_eq!(
        result.sources.slice(span).unwrap(),
        b"pub halt fn convert<To, From>(value: From) -> ?To"
    );
}

#[test]
fn canonical_prelude_signatures_retain_modes_and_defaults_under_shadowing() {
    let input = r#"
fn len(value: i64) -> i64 { value }
fn example() -> i64 {
    assert(true)
    len(1)
}
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let local_len = hir
        .references
        .iter()
        .find(|reference| reference.path == ["len"])
        .unwrap();
    assert_eq!(
        hir.definitions[local_len.definition.0].kind,
        DefinitionKind::Function
    );
    assert!(!hir.primitives.contains_key(&local_len.definition));

    let declaration = |primitive| {
        let definition = hir
            .primitives
            .iter()
            .find_map(|(definition, id)| (*id == primitive).then_some(*definition))
            .unwrap();
        let span = hir.definitions[definition.0].span.unwrap();
        let statement = result.files[&span.file]
            .program
            .statements
            .iter()
            .find(|statement| statement.span == span)
            .unwrap();
        let StmtKind::Function(function) = &statement.kind else {
            panic!("expected a primitive function declaration");
        };
        function
    };
    let inner = declaration(PrimitiveId::Inner);
    assert!(matches!(inner.return_mode, ReturnMode::Infer(_)));
    assert_eq!(inner.parameters[0].mode, ParameterMode::Via);
    let assertion = declaration(PrimitiveId::Assert);
    let default = assertion.parameters[1].default.as_ref().unwrap();
    assert_eq!(
        result.sources.slice(default.span).unwrap(),
        b"\"assertion failed\""
    );
    let budget = declaration(PrimitiveId::DivBudget);
    let Some(callback) = &budget.parameters[1].ty else {
        panic!("expected a typed budget callback");
    };
    assert!(
        matches!(&callback.kind, TypeKind::Callable { annotations, .. }
        if matches!(annotations.as_slice(), [
            Annotation { kind: AnnotationKind::Effects(EffectRow::Open), .. },
            Annotation { kind: AnnotationKind::State(StateClause::Open), .. }
        ]))
    );
    let identities: std::collections::BTreeSet<_> = hir.primitives.values().collect();
    assert_eq!(identities.len(), hir.primitives.len());
}

#[test]
fn resolved_constant_arguments_load_nested_imports_once() {
    let root = r#"
fn choose<enabled: bool>(value: i64) -> i64 { if enabled { value } else { 0 } }
fn sample() -> i64 { choose<{ (0); use flags::{ENABLED}; ENABLED }>(7) }
"#;
    let reads = std::cell::RefCell::new(std::collections::BTreeMap::new());
    let result = frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        *reads.borrow_mut().entry(path.to_owned()).or_insert(0) += 1;
        let source = match path.to_str() {
            Some("root.ril") => root,
            Some("flags.ril") => "pub use settings::{ON as ENABLED}",
            Some("settings.ril") => "pub let ON = true",
            _ => return Err(io::Error::from(io::ErrorKind::NotFound)),
        };
        Ok(source.as_bytes().to_vec())
    })
    .unwrap();
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let reads = reads.into_inner();
    assert_eq!(reads.len(), 3);
    assert!(reads.values().all(|count| *count == 1));
    let hir = result.hir.unwrap();
    let enabled = hir
        .references
        .iter()
        .find(|reference| reference.path == ["ENABLED"])
        .unwrap();
    let source = hir.definitions[enabled.definition.0].span.unwrap();
    assert_eq!(
        result.sources.get(source.file).unwrap().path(),
        Path::new("settings.ril")
    );
}

#[test]
fn mapped_modes_and_members_see_binder_but_coordinate_expression_sees_outer_head() {
    let input = r#"
type Schema = { var id: i64 }
type Keys = \token: Type -> token
meta fn fields(_token: Type) -> []str { ["id"] }
type Project = { modeof Schema.(Keys) [fields(Keys< <Schema> >) as Keys]: Schema.(Keys) }
"#;
    let result = compile(input);
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let keys: Vec<_> = hir
        .references
        .iter()
        .filter(|reference| reference.path == ["Keys"])
        .collect();
    let [source, mode, member] = keys.as_slice() else {
        panic!("expected the coordinate source, mode, and member references");
    };
    assert_eq!(
        source.application.as_ref().unwrap().parameters,
        [ArgumentSort::Value]
    );
    assert_eq!(
        hir.definitions[source.definition.0].kind,
        DefinitionKind::Type
    );
    assert_eq!(mode.definition, member.definition);
    assert_eq!(
        hir.definitions[mode.definition.0].kind,
        DefinitionKind::Parameter
    );
}

#[test]
fn malformed_type_quote_preserves_the_following_declaration() {
    for (input, found) in [
        ("meta let BAD = <>\nmeta let GOOD = <i64>\n", b">"),
        ("meta let BAD = <i64, str>\nmeta let GOOD = <i64>\n", b","),
    ] {
        let result = compile(input);
        let [diagnostic] = result.diagnostics.as_slice() else {
            panic!(
                "expected one quote diagnostic, got {:?}",
                result.diagnostics
            );
        };
        assert_eq!(diagnostic.code, "E0120");
        assert_eq!(
            result.sources.slice(diagnostic.labels[0].span).unwrap(),
            found
        );
        let parse = &result.files[&FileId(0)];
        assert_eq!(parse.syntax().to_string(), input);
        assert_eq!(parse.program.statements.len(), 2);
    }
}

#[test]
fn unavailable_authoritative_import_is_a_source_io_error() {
    let root = r#"
fn choose<enabled: bool>(value: i64) -> i64 { if enabled { value } else { 0 } }
fn sample() -> i64 { choose<{ use flags::{ENABLED}; ENABLED }>(7) }
"#;
    let result = frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        if path == Path::new("root.ril") {
            Ok(root.as_bytes().to_vec())
        } else if path == Path::new("flags.ril") {
            Err(io::Error::from(io::ErrorKind::PermissionDenied))
        } else {
            Err(io::Error::from(io::ErrorKind::NotFound))
        }
    });
    let Err(error) = result else {
        panic!("expected failure to read the imported file");
    };
    assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
    assert!(error.to_string().contains("flags.ril"));
}

#[test]
fn hir_keeps_entry_identity_and_foreign_declaration_origins() {
    let root = r#"
use platform/device::{Handle}
use platform/device::Io::{fetch as load, CURRENT}
type Exit = Result<(), str>
fn keep(handle: Handle) -> Handle { handle }
fn main() &up(sub){CURRENT} -> Exit {
    let _ = load(CURRENT)
    Ok()
}
"#;
    let contract = r#"
pub type Handle
pub sub Io {
    use Super::{Handle}
    pub fn fetch(handle: Handle) -> str
    pub let CURRENT: Handle
}
"#;
    let result = frontend(Path::new("root.ril"), UnitKind::Executable, |path| {
        let source = match path.to_str() {
            Some("root.ril") => root,
            Some("platform/device.d.ril") => contract,
            _ => return Err(io::Error::from(io::ErrorKind::NotFound)),
        };
        Ok(source.as_bytes().to_vec())
    })
    .unwrap();
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.unwrap();
    let root_unit = &hir.units[&FileId(0)];
    assert_eq!(
        root_unit.origin,
        CompilationUnitOrigin::User(UnitKind::Executable)
    );
    assert!(root_unit.namespace.is_none());
    let entry = &hir.definitions[hir.entry_point.unwrap().0];
    assert_eq!(entry.name, "main");
    assert_eq!(entry.scope, root_unit.scope);

    let external = hir
        .references
        .iter()
        .find(|reference| reference.path == ["load"])
        .unwrap();
    let definition = &hir.definitions[external.definition.0];
    assert_eq!(definition.kind, DefinitionKind::ForeignFunction);
    let file = definition.span.unwrap().file;
    let unit = &hir.units[&file];
    assert_eq!(unit.origin, CompilationUnitOrigin::User(UnitKind::External));
    assert_eq!(hir.definitions[unit.namespace.unwrap().0].name, "Device");
    let handle = hir
        .references
        .iter()
        .find(|reference| reference.path == ["Handle"])
        .unwrap();
    let handle = &hir.definitions[handle.definition.0];
    assert_eq!(handle.kind, DefinitionKind::ForeignType);
    assert!(handle.constructor_form.is_none());
    let current = &hir.state_source_groups[0].items[0];
    let current = &hir.definitions[current.definition.0];
    assert_eq!(current.kind, DefinitionKind::ForeignConstant);
    assert_eq!(current.span.unwrap().file, file);

    let budget = hir
        .primitives
        .iter()
        .find_map(|(definition, id)| (*id == PrimitiveId::DivBudget).then_some(*definition))
        .unwrap();
    let budget_unit = &hir.units[&hir.definitions[budget.0].span.unwrap().file];
    assert_eq!(budget_unit.origin, CompilationUnitOrigin::Bundled);
    assert_eq!(
        hir.definitions[budget_unit.namespace.unwrap().0].name,
        "Div"
    );
}

#[test]
fn direct_library_and_external_units_check_their_module_file_names() {
    for (path, kind, source, code) in [
        (
            "super.d.ril",
            UnitKind::External,
            "pub type Handle",
            "E0203",
        ),
        (
            "a_b.ril",
            UnitKind::Library,
            "pub fn read() -> i64 { 0 }",
            "E0102",
        ),
    ] {
        let result = frontend(Path::new(path), kind, |_| Ok(source.as_bytes().to_vec())).unwrap();
        assert!(!result.is_ok());
        let [diagnostic] = result.diagnostics.as_slice() else {
            panic!(
                "expected a module name diagnostic, got {:?}",
                result.diagnostics
            );
        };
        assert_eq!(diagnostic.code, code);
        assert_eq!(diagnostic.labels[0].span.file, FileId(0));
    }
}
