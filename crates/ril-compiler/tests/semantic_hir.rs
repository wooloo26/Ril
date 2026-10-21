use ril_compiler::hir::nodes::{self as hir, HirLimits, HirProgram, LexicalOwner, NodeId};
use ril_compiler_core::{
    ids::{ExprId, TypeId},
    source::{FileId, Span},
};
use ril_syntax::ast;
use std::collections::BTreeSet;

fn span() -> Span {
    Span {
        file: FileId(7),
        start: 3,
        end: 4,
    }
}
fn name(value: &str) -> ast::Expr {
    ast::Expr {
        hir_id: None,
        kind: ast::ExprKind::Name(value.into()),
        span: span(),
    }
}
fn ty(kind: ast::TypeKind) -> ast::TypeExpr {
    ast::TypeExpr {
        hir_id: None,
        text: String::new(),
        kind,
        span: span(),
    }
}
fn int_type() -> ast::TypeExpr {
    ty(ast::TypeKind::Name {
        path: vec!["int".into()],
        arguments: vec![],
    })
}
fn statement(expression: ast::Expr) -> ast::Stmt {
    ast::Stmt {
        hir_id: None,
        kind: ast::StmtKind::Expr {
            expression,
            terminated: false,
        },
        span: span(),
    }
}
fn parameter(default: &str) -> ast::Parameter {
    ast::Parameter {
        pattern: ast::Pattern {
            hir_id: None,
            kind: ast::PatternKind::Name("value".into()),
            span: span(),
        },
        mode: ast::ParameterMode::Read,
        ty: Some(int_type()),
        default: Some(name(default)),
        span: span(),
    }
}

#[test]
fn equal_spans_are_distinct_occurrences_and_analysis_targets_ids() {
    let original = name("same");
    let source = ast::Program {
        statements: vec![statement(ast::Expr {
            hir_id: None,
            kind: ast::ExprKind::Tuple(vec![original.clone(), original]),
            span: span(),
        })],
    };
    let mut program = HirProgram::lower(&source).unwrap();
    let hir::StmtKind::Expr { expression, .. } =
        program.statement(program.roots()[0]).unwrap().kind
    else {
        panic!()
    };
    let hir::ExprKind::Tuple(items) = &program.expression(expression).unwrap().kind else {
        panic!()
    };
    let (left, right) = (items[0], items[1]);
    assert_ne!(left, right);
    assert_eq!(
        program.expression(left).unwrap().info.span,
        program.expression(right).unwrap().info.span
    );
    assert!(program.set_analyzed_type(NodeId::Expr(left), TypeId(42)));
    assert_eq!(
        program.expression(left).unwrap().info.analyzed_type,
        Some(TypeId(42))
    );
    assert_eq!(program.expression(right).unwrap().info.analyzed_type, None);
    assert!(!program.set_analyzed_type(NodeId::Expr(ExprId(u32::MAX)), TypeId(0)));
    let cloned = program.clone();
    assert_eq!(cloned.expression(left), program.expression(left));
}

#[test]
fn parsed_declarations_generics_and_lambda_owners_are_real_hir_nodes() {
    let parsed = ril_syntax::parse(ril_test::case_source(
        "tests/regressions/semantic-hir.ril::lexical-owners",
    ));
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let program = HirProgram::lower(&parsed.program).unwrap();
    let mut seen = BTreeSet::new();
    let mut lambdas = 0;
    let mut generics = 0;
    program
        .walk(program.node_count(), |id, info| {
            assert!(seen.insert(id));
            assert_eq!(info.origin, hir::NodeOrigin::Source);
            assert_eq!(info.analyzed_type, None);
            match id {
                NodeId::Expr(id) => {
                    if let hir::ExprKind::Lambda {
                        body, parameters, ..
                    } = &program.expression(id).unwrap().kind
                    {
                        lambdas += 1;
                        assert!(matches!(info.owner, LexicalOwner::Declaration(_)));
                        assert_eq!(
                            program.expression(*body).unwrap().info.owner,
                            LexicalOwner::Lambda(id)
                        );
                        assert_eq!(
                            program.pattern(parameters[0].pattern).unwrap().info.owner,
                            LexicalOwner::Lambda(id)
                        );
                    }
                }
                NodeId::Generic(id) => {
                    generics += 1;
                    assert!(matches!(
                        program.generic(id).unwrap().info.owner,
                        LexicalOwner::Declaration(_)
                    ));
                }
                _ => {}
            }
        })
        .unwrap();
    assert_eq!(seen.len(), program.node_count());
    assert_eq!(lambdas, 1);
    assert_eq!(generics, 2);
}

#[test]
fn traversal_reaches_expressions_inside_types_patterns_defaults_and_where_scopes() {
    let function = ast::Function {
        visibility: ast::Visibility::Private,
        is_meta: false,
        is_halt: false,
        name: "example".into(),
        generics: vec![ast::GenericParameter {
            hir_id: None,
            name: "T".into(),
            bound: Some(ty(ast::TypeKind::Array {
                length: Some(Box::new(name("generic_length"))),
                element: Box::new(int_type()),
            })),
            default: Some(ty(ast::TypeKind::Computation(Box::new(name(
                "generic_default",
            ))))),
            span: span(),
        }],
        parameters: vec![ast::Parameter {
            pattern: ast::Pattern {
                hir_id: None,
                kind: ast::PatternKind::Value(Box::new(name("pattern_value"))),
                span: span(),
            },
            mode: ast::ParameterMode::Read,
            ty: Some(ty(ast::TypeKind::Callable {
                parameters: vec![parameter("type_default")],
                result: Some(Box::new(int_type())),
                annotations: vec![],
            })),
            default: Some(name("value_default")),
            span: span(),
        }],
        return_type: Some(ty(ast::TypeKind::Mapped {
            binder: "field".into(),
            keys: Box::new(name("mapped_keys")),
            value: Box::new(ty(ast::TypeKind::ComputedProjection {
                base: Box::new(int_type()),
                key: Box::new(name("projection_key")),
            })),
            tuple: false,
        })),
        annotations: vec![],
        signature_where: vec![statement(name("signature_scope"))],
        body: Some(ast::Block {
            where_items: vec![statement(name("body_scope"))],
            statements: vec![ast::Stmt {
                hir_id: None,
                span: span(),
                kind: ast::StmtKind::Handler(vec![ast::HandlerArm {
                    operation: name("handler_operation"),
                    parameters: vec![parameter("handler_default")],
                    body: name("handler_body"),
                    span: span(),
                }]),
            }],
            span: span(),
        }),
        span: span(),
    };
    let source = ast::Program {
        statements: vec![ast::Stmt {
            hir_id: None,
            kind: ast::StmtKind::Function(function),
            span: span(),
        }],
    };
    let program = HirProgram::lower(&source).unwrap();
    let mut names = BTreeSet::new();
    let mut count = 0;
    program
        .walk(program.node_count(), |id, _| {
            count += 1;
            if let NodeId::Expr(id) = id
                && let hir::ExprKind::Name(name) = &program.expression(id).unwrap().kind
            {
                names.insert(name.as_str());
            }
        })
        .unwrap();
    assert_eq!(count, program.node_count());
    assert_eq!(
        names,
        BTreeSet::from([
            "generic_length",
            "generic_default",
            "pattern_value",
            "type_default",
            "value_default",
            "mapped_keys",
            "projection_key",
            "signature_scope",
            "body_scope",
            "handler_operation",
            "handler_default",
            "handler_body"
        ])
    );
}

#[test]
fn recovery_nodes_exist_without_any_verification_certificate() {
    let source = ast::Program {
        statements: vec![ast::Stmt {
            hir_id: None,
            span: span(),
            kind: ast::StmtKind::Binding(ast::Binding {
                visibility: ast::Visibility::Private,
                is_meta: false,
                mode: ast::BindingMode::Let,
                pattern: ast::Pattern {
                    hir_id: None,
                    kind: ast::PatternKind::Error,
                    span: span(),
                },
                ty: Some(ty(ast::TypeKind::Error)),
                value: ast::Expr {
                    hir_id: None,
                    kind: ast::ExprKind::Error,
                    span: span(),
                },
                fallback: None,
            }),
        }],
    };
    let program = HirProgram::lower(&source).unwrap();
    let mut count = 0;
    program
        .walk(program.node_count(), |_, info| {
            assert_eq!(info.analyzed_type, None);
            count += 1;
        })
        .unwrap();
    assert_eq!(count, 4);
}

#[test]
fn transformed_input_never_claims_an_original_source_or_generated_anchor() {
    let parsed = ril_syntax::parse(ril_test::case_source(
        "tests/regressions/semantic-hir.ril::lexical-owners",
    ));
    let source = HirProgram::lower(&parsed.program).unwrap();
    let transformed =
        HirProgram::lower_transformed(&parsed.program, hir::GeneratedKind::StaticMaterialization)
            .unwrap();
    assert_eq!(source.node_count(), transformed.node_count());
    source
        .walk(source.node_count(), |_, info| {
            assert_eq!(info.origin, hir::NodeOrigin::Source)
        })
        .unwrap();
    transformed
        .walk(transformed.node_count(), |_, info| {
            assert_eq!(
                info.origin,
                hir::NodeOrigin::Transformed {
                    kind: hir::GeneratedKind::StaticMaterialization,
                }
            );
            assert_eq!(info.analyzed_type, None);
        })
        .unwrap();
}

#[test]
fn generated_occurrences_are_explicit_and_failed_minting_is_transactional() {
    let source = ast::Program {
        statements: vec![statement(name("source"))],
    };
    let mut program = HirProgram::lower(&source).unwrap();
    let anchor = NodeId::Stmt(program.roots()[0]);
    let generated = ast::Expr {
        hir_id: None,
        kind: ast::ExprKind::Tuple(vec![name("first"), name("second")]),
        span: span(),
    };
    let before = program.node_count();
    assert!(
        program
            .mint_generated_expr(
                &generated,
                anchor,
                hir::GeneratedKind::Desugaring,
                LexicalOwner::Module,
                HirLimits {
                    nodes: 1,
                    ..Default::default()
                }
            )
            .is_err()
    );
    assert_eq!(program.node_count(), before);
    assert!(program.generated_roots().is_empty());
    let first = program
        .mint_generated_expr(
            &generated,
            anchor,
            hir::GeneratedKind::Desugaring,
            LexicalOwner::Module,
            HirLimits::default(),
        )
        .unwrap();
    let second = program
        .mint_generated_expr(
            &generated,
            anchor,
            hir::GeneratedKind::Desugaring,
            LexicalOwner::Module,
            HirLimits::default(),
        )
        .unwrap();
    assert_ne!(first, second);
    for (generation, root) in [first, second].into_iter().enumerate() {
        program
            .walk_from([NodeId::Expr(root)], 3, |_, info| {
                assert_eq!(
                    info.origin,
                    hir::NodeOrigin::Generated {
                        generation: generation as u32,
                        anchor,
                        kind: hir::GeneratedKind::Desugaring
                    }
                )
            })
            .unwrap();
    }
    assert!(
        program
            .mint_generated_expr(
                &generated,
                NodeId::Expr(ExprId(u32::MAX)),
                hir::GeneratedKind::Desugaring,
                LexicalOwner::Module,
                HirLimits::default()
            )
            .is_err()
    );
}

#[test]
fn lowering_and_walking_reject_exhausted_depth_node_and_text_budgets() {
    let source = ast::Program {
        statements: vec![statement(ast::Expr {
            hir_id: None,
            kind: ast::ExprKind::Tuple(vec![name("first"), name("second")]),
            span: span(),
        })],
    };
    for limits in [
        HirLimits {
            nodes: 2,
            ..Default::default()
        },
        HirLimits {
            depth: 1,
            ..Default::default()
        },
        HirLimits {
            text_bytes: 3,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            HirProgram::lower_with_limits(&source, limits),
            Err(hir::LowerError::Budget(_))
        ));
    }
    let program = HirProgram::lower(&source).unwrap();
    assert_eq!(program.walk(1, |_, _| {}), Err(hir::WalkError::Budget));
    assert_eq!(
        program.walk_from([NodeId::Expr(ExprId(u32::MAX))], 1, |_, _| {}),
        Err(hir::WalkError::MissingNode(NodeId::Expr(ExprId(u32::MAX))))
    );
}

fn block_model() -> ast::Block {
    ast::Block {
        statements: vec![statement(name("first")), statement(name("last"))],
        where_items: vec![statement(name("where_item"))],
        span: span(),
    }
}

fn expression_block(block: ast::Block) -> ast::Expr {
    ast::Expr {
        hir_id: None,
        kind: ast::ExprKind::Block(block),
        span: span(),
    }
}

fn function_statement() -> ast::Stmt {
    ast::Stmt {
        hir_id: None,
        span: span(),
        kind: ast::StmtKind::Function(ast::Function {
            visibility: ast::Visibility::Private,
            is_meta: false,
            is_halt: false,
            name: "declared".into(),
            generics: vec![],
            parameters: vec![],
            return_type: None,
            annotations: vec![],
            signature_where: vec![],
            body: None,
            span: span(),
        }),
    }
}

#[test]
fn real_protected_computation_blocks_keep_their_complete_hir_members_and_tails() {
    use ril_compiler::hir::blocks::BlockIndex;
    use ril_compiler_core::ids::BlockAnchor;

    // The same independent language source exercises the protected body, arm
    // block and ordinary executable entry; no second fixed Ril source exists.
    let parsed = ril_syntax::parse(ril_test::case_source(
        "tests/regressions/effects.ril::non-tail-reference-answer",
    ));
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let mut source = parsed.program;
    let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
    let index = BlockIndex::new(&hir).unwrap();
    let mut functions = 0;
    for statement in &source.statements {
        let ast::StmtKind::Function(function) = &statement.kind else {
            continue;
        };
        let body = function.body.as_ref().unwrap();
        let anchor = BlockAnchor::FunctionBody(statement.hir_id.unwrap());
        assert_eq!(index.source_block(body).unwrap(), Some(anchor));
        assert_eq!(
            index.block(anchor).unwrap().statements,
            body.statements
                .iter()
                .map(|statement| statement.hir_id.unwrap())
                .collect::<Vec<_>>()
        );
        let (tail_statement, tail_expression) = index.tail(anchor).unwrap().unwrap();
        assert!(matches!(hir.statement(tail_statement).unwrap().kind,
            hir::StmtKind::Expr { expression, terminated:false } if expression == tail_expression));
        functions += 1;
        for statement in &body.statements {
            let ast::StmtKind::Handler(arms) = &statement.kind else {
                continue;
            };
            for arm in arms {
                let ast::ExprKind::Block(block) = &arm.body.kind else {
                    continue;
                };
                let anchor = BlockAnchor::ExpressionBody(arm.body.hir_id.unwrap());
                assert_eq!(index.source_block(block).unwrap(), Some(anchor));
                assert!(index.tail(anchor).unwrap().is_some());
            }
        }
    }
    assert_eq!(functions, 2);
    // The index owns only typed member metadata, and remains valid after the
    // construction HIR is no longer borrowed or even retained by this caller.
    drop(hir);
    for statement in &source.statements {
        if let ast::StmtKind::Function(function) = &statement.kind {
            let body = function.body.as_ref().unwrap();
            assert!(index.source_block(body).unwrap().is_some());
        }
    }
}

#[test]
fn block_correspondence_rejects_partial_reordered_and_cross_connected_member_ids() {
    use ril_compiler::hir::blocks::{BlockIndex, BlockIndexError};
    use ril_compiler_core::ids::{BlockAnchor, StmtId};

    let mut source = ast::Program {
        statements: vec![
            statement(expression_block(block_model())),
            statement(expression_block(block_model())),
        ],
    };
    let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
    let index = BlockIndex::new(&hir).unwrap();
    let blocks: Vec<_> = source
        .statements
        .iter()
        .map(|statement| {
            let ast::StmtKind::Expr { expression, .. } = &statement.kind else {
                unreachable!()
            };
            let ast::ExprKind::Block(block) = &expression.kind else {
                unreachable!()
            };
            (
                BlockAnchor::ExpressionBody(expression.hir_id.unwrap()),
                block,
            )
        })
        .collect();
    assert_eq!(blocks[0].1.span, blocks[1].1.span);
    assert_ne!(blocks[0].0, blocks[1].0);
    for (anchor, block) in &blocks {
        assert_eq!(index.source_block(block).unwrap(), Some(*anchor));
    }
    let original = blocks[0].1;
    let mut suffix = original.clone();
    suffix.statements.remove(0);
    assert_eq!(index.source_block(&suffix).unwrap(), None);
    let mut truncated = original.clone();
    truncated.statements.pop();
    assert_eq!(index.source_block(&truncated).unwrap(), None);
    let mut reordered = original.clone();
    reordered.statements.reverse();
    assert_eq!(index.source_block(&reordered).unwrap(), None);
    let mut missing_where = original.clone();
    missing_where.where_items.clear();
    assert_eq!(index.source_block(&missing_where).unwrap(), None);
    let mut changed_roles = original.clone();
    changed_roles
        .statements
        .push(changed_roles.where_items.remove(0));
    assert_eq!(index.source_block(&changed_roles).unwrap(), None);
    let mut crossed = original.clone();
    crossed.statements[1].hir_id = blocks[1].1.statements[1].hir_id;
    assert_eq!(index.source_block(&crossed).unwrap(), None);
    let mut duplicated = original.clone();
    duplicated.where_items[0].hir_id = duplicated.statements[0].hir_id;
    assert!(matches!(
        index.source_block(&duplicated),
        Err(BlockIndexError::DuplicateStatement(_))
    ));
    let mut missing_id = original.clone();
    missing_id.where_items[0].hir_id = None;
    assert_eq!(
        index.source_block(&missing_id),
        Err(BlockIndexError::MissingStatementIdentity)
    );
    let mut outside = original.clone();
    outside.statements[1].hir_id = Some(StmtId(u32::MAX));
    assert_eq!(
        index.source_block(&outside),
        Err(BlockIndexError::MissingNode(NodeId::Stmt(StmtId(u32::MAX))))
    );
    assert!(matches!(
        index.block(BlockAnchor::ExpressionBody(ExprId(u32::MAX))),
        Err(BlockIndexError::UnknownAnchor(_))
    ));
}

#[test]
fn every_direct_block_kind_has_one_anchor_and_control_or_terminated_tails_stay_absent() {
    use ril_compiler::hir::blocks::BlockIndex;
    use ril_compiler_core::ids::BlockAnchor;

    let mut declared = block_model();
    declared.statements.push(function_statement());
    let mut terminated = block_model();
    let ast::StmtKind::Expr {
        terminated: flag, ..
    } = &mut terminated.statements.last_mut().unwrap().kind
    else {
        unreachable!()
    };
    *flag = true;
    let mut returned = block_model();
    returned.statements.push(statement(ast::Expr {
        hir_id: None,
        kind: ast::ExprKind::Control {
            operation: ast::ControlOperation::Return,
            value: Some(Box::new(name("returned"))),
        },
        span: span(),
    }));
    let empty = ast::Block {
        statements: vec![],
        where_items: vec![],
        span: span(),
    };
    let bodies = [
        ast::ExprKind::Block(declared),
        ast::ExprKind::Loop(terminated),
        ast::ExprKind::While {
            condition: Box::new(name("condition")),
            body: returned,
        },
        ast::ExprKind::For {
            iterable: Box::new(name("items")),
            pattern: ast::Pattern {
                hir_id: None,
                kind: ast::PatternKind::Wildcard,
                span: span(),
            },
            body: empty,
        },
    ];
    let mut source = ast::Program {
        statements: bodies
            .into_iter()
            .map(|kind| {
                statement(ast::Expr {
                    hir_id: None,
                    kind,
                    span: span(),
                })
            })
            .collect(),
    };
    let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
    let index = BlockIndex::new(&hir).unwrap();
    for (number, statement) in source.statements.iter().enumerate() {
        let ast::StmtKind::Expr { expression, .. } = &statement.kind else {
            unreachable!()
        };
        let block = match &expression.kind {
            ast::ExprKind::Block(block) | ast::ExprKind::Loop(block) => block,
            ast::ExprKind::While { body, .. } | ast::ExprKind::For { body, .. } => body,
            _ => unreachable!(),
        };
        let anchor = BlockAnchor::ExpressionBody(expression.hir_id.unwrap());
        assert!(index.block(anchor).is_ok());
        if number == 3 {
            assert_eq!(index.source_block(block).unwrap(), None);
        } else {
            assert_eq!(index.source_block(block).unwrap(), Some(anchor));
        }
        let tail = index.tail(anchor).unwrap();
        if number == 0 {
            let expected = &block.statements[1];
            let ast::StmtKind::Expr { expression, .. } = &expected.kind else {
                unreachable!()
            };
            assert_eq!(
                tail,
                Some((expected.hir_id.unwrap(), expression.hir_id.unwrap()))
            );
        } else {
            assert_eq!(tail, None);
        }
    }
}

#[test]
fn block_index_construction_and_queries_charge_shared_work_without_partial_results() {
    use ril_compiler::hir::blocks::{BlockIndex, BlockIndexError};
    use ril_compiler_core::ids::BlockAnchor;

    let mut source = ast::Program {
        statements: vec![statement(expression_block(block_model()))],
    };
    let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
    assert!(matches!(
        BlockIndex::new_with_budget(&hir, &mut 0),
        Err(BlockIndexError::Budget)
    ));
    assert!(matches!(
        BlockIndex::new_with_budget(&hir, &mut 2),
        Err(BlockIndexError::Budget)
    ));
    let mut work = 4096;
    let index = BlockIndex::new_with_budget(&hir, &mut work).unwrap();
    assert!(work < 4096);
    let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
        unreachable!()
    };
    let ast::ExprKind::Block(block) = &expression.kind else {
        unreachable!()
    };
    let anchor = BlockAnchor::ExpressionBody(expression.hir_id.unwrap());
    for _ in 0..3 {
        let before = work;
        assert_eq!(
            index.source_block_with_budget(block, &mut work).unwrap(),
            Some(anchor)
        );
        assert!(index.block_with_budget(anchor, &mut work).is_ok());
        assert!(index.tail_with_budget(anchor, &mut work).unwrap().is_some());
        assert!(work < before);
    }
    assert_eq!(
        index.source_block_with_budget(block, &mut 0),
        Err(BlockIndexError::Budget)
    );
    assert!(matches!(
        index.block_with_budget(anchor, &mut 0),
        Err(BlockIndexError::Budget)
    ));
    assert_eq!(
        index.tail_with_budget(anchor, &mut 0),
        Err(BlockIndexError::Budget)
    );
}
