use ril_compiler_core::source::FileId;
use ril_syntax::{ast::*, parse, parse_expression, parse_file};

#[test]
fn application_remainders_have_ordinary_callable_declaration_scopes() {
    let accepted =
        "fn example(){let value=1;with first();let value=2;with second();let value=3;value}";
    let parsed = parse(accepted);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.syntax().to_string(), accepted);
    for source in [
        "fn example(){let value=1;let value=2;with first();value}",
        "fn example(){with first();let value=1;let value=2;value}",
        "let VALUE=1;with first();let VALUE=2",
    ] {
        let parsed = parse(source);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0203"),
            "{source}: {:?}",
            parsed.diagnostics
        );
    }
}

#[test]
fn trailing_closures_bind_to_the_pipeline_target() {
    let parsed = parse_expression("[1,2] |> Array::map \\n -> n*2", FileId(0));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ExprKind::Binary {
        operator,
        left,
        right,
    } = parsed.expression.kind
    else {
        panic!()
    };
    assert_eq!(operator, "|>");
    assert!(matches!(left.kind, ExprKind::Array(_)));
    let ExprKind::Call { callee, arguments } = right.kind else {
        panic!()
    };
    assert!(matches!(callee.kind,ExprKind::Path(path) if path==["Array","map"]));
    assert!(matches!(
        arguments.as_slice(),
        [Argument {
            value: Expr {
                kind: ExprKind::Lambda { .. },
                ..
            },
            ..
        }]
    ));
}
#[test]
fn generic_closes_preserve_adjacent_equality_and_assignment_tokens() {
    let expression = parse_expression("type<int>==type<int>", FileId(0));
    assert!(
        expression.diagnostics.is_empty(),
        "{:?}",
        expression.diagnostics
    );
    assert!(matches!(expression.expression.kind,ExprKind::Binary{operator,..} if operator=="=="));
    let expression = parse_expression("type<Wrap<int>>==type<Wrap<int>>", FileId(0));
    assert!(
        expression.diagnostics.is_empty(),
        "{:?}",
        expression.diagnostics
    );
    assert!(matches!(expression.expression.kind,ExprKind::Binary {operator,..} if operator=="=="));
    let source = "type Wrap<T>=T\nfn example(){let value:Wrap<Wrap<int>>=1}";
    let parsed = parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    assert_eq!(parsed.syntax().to_string(), source);
}

#[test]
fn empty_map_call_arguments_are_values_before_label_disambiguation() {
    let parsed = parse_expression("take([:], value: [:])", FileId(0));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ExprKind::Call { arguments, .. } = parsed.expression.kind else {
        panic!()
    };
    assert_eq!(arguments.len(), 2);
    assert!(arguments[0].label.is_none());
    assert_eq!(arguments[1].label.as_deref(), Some("value"));
    assert!(arguments.iter().all(
        |argument| matches!(&argument.value.kind,ExprKind::Map(entries) if entries.is_empty())
    ));
}

#[test]
fn value_test_preserves_mutable_expected_calls_and_nullary_spelling() {
    let grouped = parse_expression("3 is (1 | 2)", FileId(0));
    assert!(grouped.diagnostics.is_empty(), "{:?}", grouped.diagnostics);
    assert!(matches!(
        grouped.expression.kind,
        ExprKind::Is {
            pattern: Pattern {
                kind: PatternKind::Value(_),
                ..
            },
            ..
        }
    ));
    let alternative = parse_expression(
        "value is Ok(mark(0)) | Ok(mark(1)) | Ok(mark(2))",
        FileId(0),
    );
    assert!(
        alternative.diagnostics.is_empty(),
        "{:?}",
        alternative.diagnostics
    );
    assert!(
        matches!(alternative.expression.kind,ExprKind::Is { pattern:Pattern { kind:PatternKind::Alternative(parts),.. },.. } if parts.len()==3)
    );
    let parsed = parse_expression("value is Some(replace(mut cell))", FileId(0));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let ExprKind::Is { pattern, .. } = parsed.expression.kind else {
        panic!()
    };
    let PatternKind::Constructor { arguments, .. } = pattern.kind else {
        panic!()
    };
    let PatternKind::Value(expected) = &arguments[0].kind else {
        panic!()
    };
    let ExprKind::Call { arguments, .. } = &expected.kind else {
        panic!()
    };
    assert_eq!(arguments[0].mode, ParameterMode::Mut);
    for (text, parenthesized) in [("value is None", false), ("value is None()", true)] {
        let parsed = parse_expression(text, FileId(0));
        let ExprKind::Is { pattern, .. } = parsed.expression.kind else {
            panic!()
        };
        assert!(
            matches!(pattern.kind, PatternKind::Constructor { parenthesized: found, .. } if found == parenthesized)
        );
    }
}

fn valid(text: &str) -> ril_syntax::Parse {
    let result = parse(text);
    assert!(result.is_ok(), "{}: {:?}", text, result.diagnostics);
    assert_eq!(result.syntax().to_string(), text);
    result
}

#[test]
fn tracks_binding_and_call_modes_without_erasure() {
    let result = valid(
        "type Cell = { mut count: int }\nfn set(mut cell: Cell, ^mut other: Cell) &^mut { cell.count = other.count }\npub fn demo() { let mut cell = Cell.{ count: 0 }; let mut alias = ^mut cell; set(mut cell, ^mut alias) }",
    );
    let StmtKind::Function(function) = &result.program.statements[1].kind else {
        panic!()
    };
    assert_eq!(function.parameters[0].mode, ParameterMode::Mut);
    assert_eq!(function.parameters[1].mode, ParameterMode::SharedMut);
    assert_eq!(function.annotations[0].text, "&^mut");
    let StmtKind::Function(function) = &result.program.statements[2].kind else {
        panic!()
    };
    let StmtKind::Binding(binding) = &function.body.as_ref().unwrap().statements[1].kind else {
        panic!()
    };
    assert!(matches!(&binding.value.kind,ExprKind::Unary{operator,..} if operator=="^mut"));
}

#[test]
fn precedence_and_layout_preserve_block_values() {
    let result = valid(
        "fn demo() {\nlet value = 1 +\n 2 * 3\nlet data = [1, 2]\n |> Array::map(\\n -> n + 1)\nvalue\n(4)\n}",
    );
    let StmtKind::Function(function) = &result.program.statements[0].kind else {
        panic!()
    };
    let statements = &function.body.as_ref().unwrap().statements;
    assert_eq!(
        statements.len(),
        4,
        "leading parentheses cannot reopen previous statement"
    );
    let StmtKind::Binding(binding) = &statements[0].kind else {
        panic!()
    };
    let ExprKind::Binary {
        operator, right, ..
    } = &binding.value.kind
    else {
        panic!()
    };
    assert_eq!(operator, "+");
    assert!(matches!(&right.kind,ExprKind::Binary{operator,..} if operator=="*"));
}

#[test]
fn generic_types_patterns_handlers_and_hoisted_declarations() {
    valid(
        "type Result<T, E = str> { Ok(T), Err(E) }\neff Ask<T> { ask() -> T }\nfn example(value: Result<int, str>) -> int {\nwith Ask<int>::ask() -> resume 7\nmatch value { Ok(number) if number > 0 -> number, Err(_error) -> 0, _ -> 1 }\nwhere\nfn helper(value: int) -> int { value }\n}",
    );
}

#[test]
fn lossless_trivia_and_source_file_spans() {
    let text =
        "{- outer {- nested -} -}\r\npub fn run() { -- comment\r\n let text = `原样\\n`; text\r\n}";
    let result = parse_file(text, FileId(7));
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    assert_eq!(result.syntax().to_string(), text);
    assert_eq!(result.program.statements[0].span.file, FileId(7));
}

#[test]
fn lexical_failure_codes_are_specific() {
    for (text, code) in [
        ("{- open", "E0106"),
        ("let value = \"open", "E0107"),
        (r#"let value = "\q""#, "E0108"),
        (r#"let value = "\u{D800}""#, "E0109"),
        (r#"let value = b"\xG0""#, "E0110"),
        ("let value = 0b102", "E0111"),
        (r#"let value = "{}""#, "E0112"),
        ("type Record = { if: int }", "E0113"),
    ] {
        let result = parse(text);
        assert!(
            result.diagnostics.iter().any(|d| d.code == code),
            "{text}: {:?}",
            result.diagnostics
        );
        assert_eq!(result.syntax().to_string(), text);
    }
}

#[test]
fn recovers_delimiters_and_retains_later_declarations() {
    for (text, code) in [
        ("let value =", "E0121"),
        ("let values = [1, 2", "E0122"),
        ("let values = (1, 2]", "E0123"),
        ("let values = [1 2]", "E0124"),
    ] {
        let result = parse(text);
        assert!(
            result.diagnostics.iter().any(|d| d.code == code),
            "{text}: {:?}",
            result.diagnostics
        );
        assert_eq!(result.syntax().to_string(), text);
    }
    let result = parse("let value = $\nfn later() { 1 }");
    assert!(
        result
            .program
            .statements
            .iter()
            .any(|s| matches!(&s.kind,StmtKind::Function(f) if f.name=="later"))
    );
}

#[test]
fn type_functions_live_views_defaults_and_scoped_bindings() {
    valid(
        "type Wrap = \\T -> type<Option<T>>\nfn observe(value: int = 7) -> int { let mut working = .{ count: value }; let view observed = working; let scoped mut resource = open(); observed.count }\nfn projected() { let reader = \\.field?.child; let Some(value) = Some(3) else { return }; for [1, 2] as item { assert(item > 0) }; while false { next }; loop { last 3 } }",
    );
}

#[test]
fn isolated_expression_parser_checks_all_tokens() {
    let result = parse_expression("value.field + callback(3)", FileId(4));
    assert!(result.diagnostics.is_empty());
    assert!(matches!(result.expression.kind, ExprKind::Binary { .. }));
    assert!(!parse_expression("1; 2", FileId(0)).diagnostics.is_empty());
}

#[test]
fn static_arguments_preserve_calls_empty_arrays_and_tuple_value_syntax() {
    let parsed = valid(
        "type Choice = Select<(1, Some(\"a\")), ()>\ntype Empty = Select<[]>\ntype Single = Select<[1]>\ntype Fixed = Select<[1]int>\ntype Associative = Select<[str: int]>",
    );
    let arguments: Vec<_> = parsed
        .program
        .statements
        .iter()
        .map(|statement| {
            let StmtKind::Type(declaration) = &statement.kind else {
                panic!()
            };
            let TypeKind::Name { arguments, .. } = &declaration.value.as_ref().unwrap().kind else {
                panic!()
            };
            arguments
        })
        .collect();
    let TypeKind::Tuple(items) = &arguments[0][0].kind else {
        panic!()
    };
    assert!(
        matches!(&items[1].kind,TypeKind::Computation(value) if matches!(value.kind,ExprKind::Call { .. }))
    );
    assert!(
        matches!(&arguments[1][0].kind,TypeKind::Computation(value) if matches!(&value.kind,ExprKind::Array(items) if items.is_empty()))
    );
    assert!(
        matches!(&arguments[2][0].kind,TypeKind::Computation(value) if matches!(&value.kind,ExprKind::Array(items) if items.len() == 1))
    );
    assert!(matches!(
        &arguments[3][0].kind,
        TypeKind::Array {
            length: Some(_),
            ..
        }
    ));
    assert!(matches!(&arguments[4][0].kind, TypeKind::Map { .. }));
}

#[test]
fn fixed_array_lengths_keep_their_expression_sort_until_semantic_checking() {
    for length in ["\"0\"", "`0`", ".{size:1}", "[1]"] {
        let source = format!("fn example(){{let items:[{length}]int=[]}}");
        let parsed = valid(&source);
        let StmtKind::Function(function) = &parsed.program.statements[0].kind else {
            panic!()
        };
        let StmtKind::Binding(binding) = &function.body.as_ref().unwrap().statements[0].kind else {
            panic!()
        };
        assert!(matches!(
            &binding.ty.as_ref().unwrap().kind,
            TypeKind::Array {
                length: Some(_),
                ..
            }
        ));
    }
    let parsed = valid(
        "type Strings=Tag<[\"a\",\"b\"]>\ntype Records=Tag<[.{size:1}]>\ntype Arrays=Tag<[[1]]>\ntype Entries=Tag<[\"a\":1,\"b\":2]>",
    );
    for statement in &parsed.program.statements {
        let StmtKind::Type(declaration) = &statement.kind else {
            panic!()
        };
        let TypeKind::Name { arguments, .. } = &declaration.value.as_ref().unwrap().kind else {
            panic!()
        };
        assert!(matches!(arguments[0].kind, TypeKind::Computation(_)));
    }
}

#[test]
fn reassignable_scoped_binding_reports_the_scoped_resource_diagnostic() {
    for source in [
        "fn example(){var scoped item=resource()}",
        "fn example(){var scoped mut item=resource()}",
        "fn example(){var mut scoped item=resource()}",
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.syntax().to_string(), source);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0532"),
            "{source}: {:?}",
            parsed.diagnostics
        );
        assert!(
            !parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0120"),
            "the invalid mode hid the rest of its binding"
        );
    }
}

#[test]
fn typeof_has_type_context_identity_and_requires_quotation_as_a_value() {
    let parsed = valid(
        "type Inferred = typeof (1 + 2)\nfn example(value: int) { let item: typeof value = value; let token = type<typeof value> }",
    );
    let StmtKind::Type(declaration) = &parsed.program.statements[0].kind else {
        panic!()
    };
    assert!(
        matches!(&declaration.value.as_ref().unwrap().kind,TypeKind::Computation(expression) if matches!(&expression.kind,ExprKind::Unary { operator,.. } if operator == "typeof"))
    );
    let parsed = parse("fn example() { let token = typeof 1 }");
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0319"),
        "{:?}",
        parsed.diagnostics
    );
}

#[test]
fn nesting_budgets_preserve_source_and_report_incomplete_without_syntax_rejection() {
    for source in [
        format!(
            "fn example() {{ {}1{} }}",
            "(".repeat(1000),
            ")".repeat(1000)
        ),
        format!("fn example() {{ {}1 }}", "- ".repeat(1000)),
        format!("type Deep = {}int", "[]".repeat(1000)),
        format!(
            "fn example() {{ {} }}",
            std::iter::repeat_n("1", 1000)
                .collect::<Vec<_>>()
                .join(" + ")
        ),
        format!(
            "fn example(value: int) {{ value{} }}",
            ".field".repeat(1000)
        ),
        format!("fn example() {{ let get=\\{} }}", ".field".repeat(1000)),
        format!(
            "fn example() {{ {}0{} }}",
            "\"{".repeat(1000),
            "}\"".repeat(1000)
        ),
    ] {
        let parsed = parse(&source);
        assert!(
            parsed.incomplete,
            "budget did not stop {} source bytes",
            source.len()
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert_eq!(parsed.syntax().to_string(), source);
    }
}

#[test]
fn source_roles_and_declaration_contexts_are_checked_before_resolution() {
    for (text, code) in [
        ("type HTTPServer = int", "E0102"),
        ("type item = int", "E0101"),
        ("fn Compute() {}", "E0101"),
        ("let count = 1", "E0101"),
        ("meta let count = 1", "E0101"),
        ("fn example() { fn helper() {} }", "E0703"),
        ("fn example() { () where let value = 1 }", "E0702"),
        ("type Item = { id: int, id: int }", "E0210"),
        ("fn example() { let value = .{ id: 1, id: 2 } }", "E0210"),
        (
            "fn example(value: int) { match value { (1 + 2) -> (), _ -> () } }",
            "E0349",
        ),
    ] {
        let parsed = parse(text);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == code),
            "{text}: {:?}",
            parsed.diagnostics
        );
    }
    let result = valid(
        "use helper::answer as renamed\nfn example() { let value = .{ first: 1, ..left, second: 2, ..right }; value }",
    );
    let StmtKind::Function(function) = &result.program.statements[1].kind else {
        panic!()
    };
    let StmtKind::Binding(binding) = &function.body.as_ref().unwrap().statements[0].kind else {
        panic!()
    };
    let ExprKind::Record { members, .. } = &binding.value.kind else {
        panic!()
    };
    assert_eq!(members.len(), 4);
    assert!(matches!(members[1], RecordMember::Spread(_)));
    assert!(matches!(members[3], RecordMember::Spread(_)));
}

#[test]
fn nominal_and_alias_types_retain_different_source_identity() {
    let parsed = valid("type Wrapped(int)\ntype Alias = int\ntype Marker");
    let declarations: Vec<_> = parsed
        .program
        .statements
        .iter()
        .filter_map(|statement| {
            if let StmtKind::Type(declaration) = &statement.kind {
                Some(declaration)
            } else {
                None
            }
        })
        .collect();
    assert!(declarations[0].nominal);
    assert!(!declarations[1].nominal);
    assert!(declarations[2].nominal);
}

#[test]
fn interpolations_are_owned_expressions_with_original_spans() {
    let text =
        r#"fn value() -> str { "literal={{}}; n={first + second:04x}; nested={"{third}"}" }"#;
    let parsed = valid(text);
    let StmtKind::Function(function) = &parsed.program.statements[0].kind else {
        panic!()
    };
    let StmtKind::Expr { expression, .. } = &function.body.as_ref().unwrap().statements[0].kind
    else {
        panic!()
    };
    let ExprKind::Interpolated(parts) = &expression.kind else {
        panic!()
    };
    assert!(matches!(&parts[0],StringPart::Text(text)if text=="literal={}; n="));
    let StringPart::Interpolation {
        expression, format, ..
    } = &parts[1]
    else {
        panic!()
    };
    assert_eq!(format.as_deref(), Some("04x"));
    assert_eq!(
        &text[expression.span.start as usize..expression.span.end as usize],
        "first + second"
    );
}
