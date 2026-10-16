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
        kind: ast::ExprKind::Name(value.into()),
        span: span(),
    }
}
fn ty(kind: ast::TypeKind) -> ast::TypeExpr {
    ast::TypeExpr {
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
            span: span(),
            kind: ast::StmtKind::Binding(ast::Binding {
                visibility: ast::Visibility::Private,
                is_meta: false,
                mode: ast::BindingMode::Let,
                pattern: ast::Pattern {
                    kind: ast::PatternKind::Error,
                    span: span(),
                },
                ty: Some(ty(ast::TypeKind::Error)),
                value: ast::Expr {
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
