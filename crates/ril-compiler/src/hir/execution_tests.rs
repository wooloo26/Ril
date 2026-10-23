use super::*;
use ril_compiler_core::source::{FileId, Span};
use ril_syntax::ast::{self, ParameterMode};

fn span() -> Span {
    Span {
        file: FileId(0),
        start: 7,
        end: 7,
    }
}
fn expr(kind: ast::ExprKind) -> ast::Expr {
    ast::Expr {
        hir_id: None,
        span: span(),
        kind,
    }
}
fn name(text: &str) -> ast::Expr {
    expr(ast::ExprKind::Name(text.into()))
}
fn statement(expression: ast::Expr, terminated: bool) -> ast::Stmt {
    ast::Stmt {
        hir_id: None,
        span: span(),
        kind: ast::StmtKind::Expr {
            expression,
            terminated,
        },
    }
}
fn call(callee: ast::Expr, args: Vec<ast::Expr>) -> ast::Expr {
    expr(ast::ExprKind::Call {
        callee: Box::new(callee),
        arguments: args
            .into_iter()
            .map(|value| ast::Argument {
                label: None,
                mode: ParameterMode::Read,
                value,
                span: span(),
            })
            .collect(),
    })
}
fn lower(expression: ast::Expr) -> (HirProgram, BlockIndex, ExprId) {
    let mut source = ast::Program {
        statements: vec![statement(expression, false)],
    };
    let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
    let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
        unreachable!()
    };
    let root = expression.hir_id.unwrap();
    let blocks = BlockIndex::new(&hir).unwrap();
    (hir, blocks, root)
}
fn pending(cursor: &ExecutionCursor) -> ChildStep {
    let CursorAction::Child(child) = cursor.action(&mut 4096).unwrap() else {
        panic!("a physical child is pending")
    };
    child
}
fn guard(cursor: &ExecutionCursor) -> GuardRequest {
    let CursorAction::Guard(guard) = cursor.action(&mut 4096).unwrap() else {
        panic!("an actual guard decision is pending")
    };
    guard
}
fn take_reduction(cursor: &mut ExecutionCursor) -> Reduction {
    let CursorAction::Reduce(reduction) = cursor.action(&mut 4096).unwrap() else {
        panic!("all required children have completed")
    };
    cursor.reduce(reduction, &mut 4096).unwrap();
    assert_eq!(cursor.action(&mut 4096).unwrap(), CursorAction::Reduced);
    reduction
}

#[test]
fn computed_pipeline_cursor_keeps_original_order_and_a_suspended_child_pending() {
    let syntax = expr(ast::ExprKind::Binary {
        operator: "|>".into(),
        left: Box::new(call(name("left"), vec![])),
        right: Box::new(call(
            call(name("computed"), vec![]),
            vec![call(name("arg"), vec![])],
        )),
    });
    let (hir, _, root) = lower(syntax);
    let expected = hir.application(root).unwrap().unwrap();
    let mut cursor = ApplicationCursor::new(&hir, root, &mut 4096).unwrap();
    assert_eq!(cursor.kind(), ApplicationKind::Pipeline);
    assert_eq!(cursor.len(), 3);
    assert_eq!(
        cursor
            .later_children(&mut 4096)
            .unwrap()
            .iter()
            .map(|child| child.role)
            .collect::<Vec<_>>(),
        [EvaluationRole::Callee, EvaluationRole::Written(0)]
    );
    assert_eq!(cursor.position(), 0);
    assert_eq!(cursor.later_children(&mut 0), Err(ExecutionError::Budget));
    assert_eq!(cursor.position(), 0);
    assert!(matches!(
        cursor.reduce(&mut 4096),
        Err(ExecutionError::UnexpectedReduction)
    ));
    for role in [
        EvaluationRole::Piped,
        EvaluationRole::Callee,
        EvaluationRole::Written(0),
    ] {
        let child = cursor.pending(&mut 4096).unwrap().unwrap();
        assert_eq!(child.root, root);
        assert_eq!(child.role, role);
        assert_eq!(Some(child.expression), expected.expression(role));
        assert_eq!(hir.expression(child.expression).unwrap().info.span, span());
        // Suspension saves this position; querying and cloning cannot consume
        // the current child or start the next source operand.
        let saved = cursor.clone();
        assert_eq!(saved.pending(&mut 4096).unwrap(), Some(child));
        assert_eq!(cursor.pending(&mut 4096).unwrap(), Some(child));
        let mut forged = child;
        forged.expression = root;
        assert_eq!(
            cursor.complete(forged, &mut 4096),
            Err(ExecutionError::UnexpectedChild)
        );
        assert_eq!(cursor.pending(&mut 4096).unwrap(), Some(child));
        cursor.complete(child, &mut 4096).unwrap();
        assert_eq!(
            cursor.complete(child, &mut 4096),
            Err(ExecutionError::UnexpectedChild)
        );
    }
    assert_eq!(cursor.pending(&mut 4096).unwrap(), None);
    assert_eq!(cursor.reduce(&mut 4096).unwrap(), root);
    assert_eq!(
        cursor.reduce(&mut 4096),
        Err(ExecutionError::AlreadyReduced)
    );
}

#[test]
fn nullary_application_and_control_keep_their_own_reduction_identity() {
    let (hir, _, root) = lower(call(name("callee"), vec![]));
    let mut cursor = ApplicationCursor::new(&hir, root, &mut 4096).unwrap();
    assert_eq!(cursor.len(), 1);
    assert!(!cursor.is_empty());
    let callee = cursor.pending(&mut 4096).unwrap().unwrap();
    assert_eq!(callee.role, EvaluationRole::Callee);
    cursor.complete(callee, &mut 4096).unwrap();
    assert_eq!(cursor.reduce(&mut 4096).unwrap(), root);
    let (hir, blocks, root) = lower(expr(ast::ExprKind::Control {
        operation: ast::ControlOperation::Resume,
        value: Some(Box::new(name("offered"))),
    }));
    let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
    let offered = pending(&cursor);
    assert_eq!(offered.role, ChildRole::ControlValue);
    assert_ne!(offered.child, ChildId::Expression(root));
    cursor.complete(offered, &mut 4096).unwrap();
    let reduction = take_reduction(&mut cursor);
    assert_eq!(reduction.root, CursorRoot::Expression(root));
    assert_eq!(reduction.kind, ReductionKind::Control);
}

#[test]
fn lazy_operators_require_typed_decisions_and_never_schedule_a_skipped_right_operand() {
    for (operator, answer, skip) in [
        ("&&", GuardAnswer::Boolean(false), true),
        ("&&", GuardAnswer::Boolean(true), false),
        ("||", GuardAnswer::Boolean(true), true),
        ("||", GuardAnswer::Boolean(false), false),
        ("??", GuardAnswer::PayloadPresent(true), true),
        ("??", GuardAnswer::PayloadPresent(false), false),
    ] {
        let (hir, blocks, root) = lower(expr(ast::ExprKind::Binary {
            operator: operator.into(),
            left: Box::new(name("left")),
            right: Box::new(call(name("right"), vec![])),
        }));
        let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
        let left = pending(&cursor);
        assert_eq!(left.role, ChildRole::BinaryLeft);
        cursor.complete(left, &mut 4096).unwrap();
        let decision = guard(&cursor);
        assert_eq!(
            cursor.choose(decision, GuardAnswer::PatternMatched(false), &mut 4096),
            Err(ExecutionError::UnexpectedGuard)
        );
        assert_eq!(guard(&cursor), decision);
        cursor.choose(decision, answer, &mut 4096).unwrap();
        if !skip {
            let right = pending(&cursor);
            assert_eq!(right.role, ChildRole::BinaryRight);
            cursor.complete(right, &mut 4096).unwrap();
        }
        assert_eq!(
            take_reduction(&mut cursor).kind,
            ReductionKind::Lazy {
                operator: match operator {
                    "&&" => LazyOperator::And,
                    "||" => LazyOperator::Or,
                    _ => LazyOperator::Coalesce,
                },
                evaluated_right: !skip,
            }
        );
    }
}

#[test]
fn if_and_match_only_enter_selected_original_branches() {
    let (hir, blocks, root) = lower(expr(ast::ExprKind::If {
        condition: Box::new(name("condition")),
        then_branch: Box::new(name("yes")),
        else_branch: None,
    }));
    let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
    cursor.complete(pending(&cursor), &mut 4096).unwrap();
    cursor
        .choose(guard(&cursor), GuardAnswer::Boolean(false), &mut 4096)
        .unwrap();
    assert_eq!(
        take_reduction(&mut cursor).kind,
        ReductionKind::If { selected: None }
    );
    let arm = |text: &str, condition: bool| ast::MatchArm {
        pattern: ast::Pattern {
            hir_id: None,
            span: span(),
            kind: ast::PatternKind::Wildcard,
        },
        guard: condition.then(|| name("guard")),
        body: name(text),
        span: span(),
    };
    let (hir, blocks, root) = lower(expr(ast::ExprKind::Match {
        value: Box::new(name("subject")),
        arms: vec![arm("first", true), arm("second", false)],
        type_match: false,
    }));
    let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
    cursor.complete(pending(&cursor), &mut 4096).unwrap();
    let first = guard(&cursor);
    assert!(matches!(first.kind, GuardKind::MatchPattern { arm: 0, .. }));
    cursor
        .choose(first, GuardAnswer::PatternMatched(true), &mut 4096)
        .unwrap();
    let condition = pending(&cursor);
    assert_eq!(condition.role, ChildRole::MatchGuard(0));
    cursor.complete(condition, &mut 4096).unwrap();
    cursor
        .choose(guard(&cursor), GuardAnswer::Boolean(false), &mut 4096)
        .unwrap();
    let second = guard(&cursor);
    assert!(matches!(
        second.kind,
        GuardKind::MatchPattern { arm: 1, .. }
    ));
    assert_eq!(
        cursor.choose(first, GuardAnswer::PatternMatched(true), &mut 4096),
        Err(ExecutionError::UnexpectedGuard)
    );
    cursor
        .choose(second, GuardAnswer::PatternMatched(true), &mut 4096)
        .unwrap();
    let body = pending(&cursor);
    assert_eq!(body.role, ChildRole::MatchBody(1));
    cursor.complete(body, &mut 4096).unwrap();
    assert_eq!(
        take_reduction(&mut cursor).kind,
        ReductionKind::Match { arm: Some(1) }
    );
}

#[test]
fn conditional_binding_cursor_requires_the_original_pattern_decision() {
    let (hir, blocks, root) = lower(expr(ast::ExprKind::IfLet {
        pattern: ast::Pattern {
            hir_id: None,
            span: span(),
            kind: ast::PatternKind::Wildcard,
        },
        value: Box::new(name("subject")),
        then_branch: Box::new(name("yes")),
        else_branch: Some(Box::new(name("no"))),
    }));
    let hir::ExprKind::IfLet { pattern, .. } = hir.expression(root).unwrap().kind else {
        unreachable!()
    };
    let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
    let value = pending(&cursor);
    assert_eq!(value.role, ChildRole::Condition);
    cursor.complete(value, &mut 4096).unwrap();
    let decision = guard(&cursor);
    assert_eq!(decision.kind, GuardKind::IfLet { pattern });
    assert_eq!(
        cursor.choose(decision, GuardAnswer::Boolean(true), &mut 4096),
        Err(ExecutionError::UnexpectedGuard)
    );
    assert_eq!(guard(&cursor), decision);
    for matched in [false, true] {
        let mut selected = cursor.clone();
        selected
            .choose(decision, GuardAnswer::PatternMatched(matched), &mut 4096)
            .unwrap();
        let branch = pending(&selected);
        let role = if matched {
            ChildRole::Then
        } else {
            ChildRole::Else
        };
        assert_eq!(branch.role, role);
        selected.complete(branch, &mut 4096).unwrap();
        assert_eq!(
            take_reduction(&mut selected).kind,
            ReductionKind::If {
                selected: Some(role)
            }
        );
    }
}

#[test]
fn strict_products_and_projections_preserve_child_roles() {
    for (syntax, roles, kind) in [
        (
            expr(ast::ExprKind::Tuple(vec![name("a"), name("b")])),
            vec![ChildRole::Tuple(0), ChildRole::Tuple(1)],
            ReductionKind::Tuple,
        ),
        (
            expr(ast::ExprKind::Array(vec![name("a"), name("b")])),
            vec![ChildRole::Array(0), ChildRole::Array(1)],
            ReductionKind::Array,
        ),
        (
            expr(ast::ExprKind::Map(vec![
                (name("key0"), name("value0")),
                (name("key1"), name("value1")),
            ])),
            vec![
                ChildRole::MapKey(0),
                ChildRole::MapValue(0),
                ChildRole::MapKey(1),
                ChildRole::MapValue(1),
            ],
            ReductionKind::Map,
        ),
        (
            expr(ast::ExprKind::Record {
                ty: None,
                fields: vec![],
                spread: None,
                members: vec![
                    ast::RecordMember::Field(ast::RecordField {
                        name: "first".into(),
                        value: name("first"),
                        span: span(),
                    }),
                    ast::RecordMember::Spread(name("spread")),
                    ast::RecordMember::Field(ast::RecordField {
                        name: "last".into(),
                        value: name("last"),
                        span: span(),
                    }),
                ],
            }),
            vec![
                ChildRole::RecordField(0),
                ChildRole::RecordSpread(1),
                ChildRole::RecordField(2),
            ],
            ReductionKind::Record,
        ),
        (
            expr(ast::ExprKind::ComputedField {
                base: Box::new(name("base")),
                key: Box::new(name("key")),
            }),
            vec![ChildRole::Receiver, ChildRole::ProjectionKey],
            ReductionKind::ComputedField,
        ),
        (
            expr(ast::ExprKind::Index {
                base: Box::new(name("base")),
                index: Box::new(name("index")),
                safe: false,
            }),
            vec![ChildRole::Receiver, ChildRole::Index],
            ReductionKind::Index,
        ),
    ] {
        let (hir, blocks, root) = lower(syntax);
        let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
        let mut previous = None;
        for role in roles {
            let child = pending(&cursor);
            assert_eq!(child.role, role);
            assert_ne!(previous, Some(child.child));
            assert_eq!(child.root, CursorRoot::Expression(root));
            cursor.complete(child, &mut 4096).unwrap();
            previous = Some(child.child);
        }
        assert_eq!(take_reduction(&mut cursor).kind, kind);
    }
}

#[test]
fn block_cursor_keeps_statement_ids_and_only_the_real_structural_tail() {
    let (hir, blocks, root) = lower(expr(ast::ExprKind::Block(ast::Block {
        statements: vec![
            statement(name("first"), true),
            statement(name("tail"), false),
        ],
        where_items: vec![],
        span: span(),
    })));
    let anchor = BlockAnchor::ExpressionBody(root);
    let original = blocks.block(anchor).unwrap();
    let tail = blocks.tail(anchor).unwrap().unwrap();
    let mut cursor = ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096).unwrap();
    for (index, id) in original.statements.iter().enumerate() {
        let child = pending(&cursor);
        assert_eq!(child.root, CursorRoot::Block(anchor));
        assert_eq!(child.child, ChildId::Statement(*id));
        assert_eq!(
            child.role,
            ChildRole::BlockStatement {
                ordinal: index as u32,
                tail: *id == tail.0
            }
        );
        cursor.complete(child, &mut 4096).unwrap();
    }
    assert_eq!(
        take_reduction(&mut cursor).kind,
        ReductionKind::Block { tail: Some(tail) }
    );
}

#[test]
fn block_cursor_rejects_a_cached_tail_from_another_hir_revision() {
    let block = |terminated| {
        expr(ast::ExprKind::Block(ast::Block {
            statements: vec![statement(name("tail"), terminated)],
            where_items: vec![],
            span: span(),
        }))
    };
    for (before, after) in [(false, true), (true, false)] {
        let (_, stale, old_root) = lower(block(before));
        let (hir, _, root) = lower(block(after));
        assert_eq!(root, old_root);
        assert!(matches!(
            ExecutionCursor::expression(&hir, &stale, root, 0, &mut 4096),
            Err(ExecutionError::BlockContext(_))
        ));
    }
}

#[test]
fn pipeline_prepays_its_right_node_query_before_inspecting_its_kind() {
    let (hir, _, root) = lower(expr(ast::ExprKind::Binary {
        operator: "|>".into(),
        left: Box::new(name("left")),
        right: Box::new(expr(ast::ExprKind::Derive {
            base: None,
            recipe: Box::new(name("recipe")),
        })),
    }));
    assert!(matches!(
        ApplicationCursor::new(&hir, root, &mut 1),
        Err(ExecutionError::Budget)
    ));
    assert!(matches!(
        ApplicationCursor::new(&hir, root, &mut 2),
        Err(ExecutionError::Unsupported {
            kind: "copy pipeline",
            ..
        })
    ));
}

#[test]
fn cursor_failures_never_advance_or_turn_unsupported_work_into_empty_completion() {
    let (hir, blocks, root) = lower(call(name("callee"), vec![name("argument")]));
    assert!(matches!(
        ApplicationCursor::new(&hir, root, &mut 0),
        Err(ExecutionError::Budget)
    ));
    let mut cursor = ApplicationCursor::new(&hir, root, &mut 4096).unwrap();
    let child = cursor.pending(&mut 4096).unwrap().unwrap();
    assert_eq!(cursor.complete(child, &mut 0), Err(ExecutionError::Budget));
    assert_eq!(cursor.position(), 0);
    assert_eq!(cursor.pending(&mut 4096).unwrap(), Some(child));
    assert!(matches!(
        ExecutionCursor::expression(&hir, &blocks, root, MAX_DEPTH + 1, &mut 4096),
        Err(ExecutionError::Depth)
    ));
    let (hir, blocks, root) = lower(expr(ast::ExprKind::Loop(ast::Block {
        statements: vec![],
        where_items: vec![],
        span: span(),
    })));
    assert!(matches!(
        ExecutionCursor::expression(&hir, &blocks, root, 0, &mut 4096),
        Err(ExecutionError::Unsupported {
            kind: "loop control",
            ..
        })
    ));
    assert!(matches!(
        ApplicationCursor::new(&hir, root, &mut 4096),
        Err(ExecutionError::NotApplication(_))
    ));
    assert!(matches!(
        ExecutionCursor::expression(&hir, &blocks, ExprId(u32::MAX), 0, &mut 4096),
        Err(ExecutionError::MissingNode(_))
    ));
}
