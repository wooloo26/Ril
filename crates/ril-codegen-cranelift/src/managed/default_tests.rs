//! Core-level default scopes, including source views not yet accepted upstream.
use super::*;
use crate::CraneliftBackend;
use ril_codegen::{
    NativeBackend,
    target::{NATIVE_TARGETS, TargetSpec},
};
use ril_compiler_core::{
    ids::DefinitionId,
    source::{FileId, Span},
};

fn expr(start: u32, kind: ExprKind) -> Expr {
    Expr {
        span: Span {
            file: FileId(0),
            start,
            end: start + 1,
        },
        kind,
    }
}
fn name(value: &str) -> Expr {
    expr(1, ExprKind::Name(value.into()))
}
fn tail(expression: Expr) -> Statement {
    Statement::Expr {
        expression,
        terminated: false,
    }
}
fn parameter(value: &str, default: Option<Expr>) -> core::Parameter {
    core::Parameter {
        pattern: Pattern::Name(value.into()),
        default,
    }
}
fn function(
    id: u32,
    name: &str,
    parameters: Vec<core::Parameter>,
    statements: Vec<Statement>,
) -> core::Function {
    core::Function {
        role: core::FunctionRole::Ordinary,
        definition: DefinitionId(id),
        name: name.into(),
        generic_parameters: vec![],
        parameters,
        body: core::Block { statements },
        span: expr(id, ExprKind::Literal(Literal::Unit)).span,
    }
}
fn module(function: core::Function) -> native::Module {
    ril_codegen::lower::lower_native(&core::Program {
        functions: vec![
            function,
            self::function(
                99,
                "main",
                vec![],
                vec![tail(expr(99, ExprKind::Literal(Literal::Unit)))],
            ),
        ],
        ..Default::default()
    })
    .unwrap()
}

#[test]
fn default_capture_scope_excludes_its_own_slot_later_parameters_and_body_locals() {
    // Unresolved names deliberately model globals with the same spelling as
    // later declarations. Discovering a default must not capture those cells.
    let default = expr(
        10,
        ExprKind::Lambda {
            parameters: vec![],
            body: Box::new(expr(
                11,
                ExprKind::Tuple(vec![
                    name("earlier"),
                    name("action"),
                    name("later"),
                    name("local"),
                ]),
            )),
        },
    );
    let input = module(function(
        0,
        "choose",
        vec![
            parameter("earlier", None),
            parameter("action", Some(default)),
            parameter("later", None),
        ],
        vec![
            Statement::Bind {
                pattern: Pattern::Name("local".into()),
                value: expr(12, ExprKind::Literal(Literal::Unit)),
                scoped: false,
            },
            tail(name("action")),
        ],
    ));
    let prepared = prepare(&input).unwrap();
    let lifted = prepared.lambdas.values().next().unwrap();
    assert_eq!(prepared.captures[lifted], ["earlier"]);
}

#[test]
fn default_blocks_lift_named_and_anonymous_callables_from_managed_and_cps_roots() {
    let helper = function(2, "helper", vec![], vec![tail(name("captured"))]);
    let default = expr(
        10,
        ExprKind::Block(core::Block {
            statements: vec![
                Statement::Bind {
                    pattern: Pattern::Name("captured".into()),
                    value: name("earlier"),
                    scoped: false,
                },
                Statement::Function(helper),
                tail(expr(
                    20,
                    ExprKind::Lambda {
                        parameters: vec![],
                        body: Box::new(expr(
                            21,
                            ExprKind::Call {
                                callback_entry: false,
                                callee: Box::new(name("helper")),
                                arguments: vec![],
                            },
                        )),
                    },
                )),
            ],
        }),
    );
    let choose = function(
        0,
        "choose",
        vec![
            parameter("earlier", None),
            parameter("action", Some(default)),
        ],
        vec![tail(name("action"))],
    );
    let original = module(choose.clone());
    for cps in [false, true] {
        let mut input = original.clone();
        input.functions[0].body = if cps {
            Body::Cps(std::sync::Arc::new(
                ril_codegen::cps::lower(&choose).unwrap(),
            ))
        } else {
            Body::Managed(choose.clone())
        };
        let prepared = prepare(&input).unwrap();
        assert_eq!(
            prepared.lambdas.len(),
            1,
            "CPS metadata is not an executable root"
        );
        assert_eq!(prepared.named.len(), 1);
        for lifted in prepared.lambdas.values().chain(prepared.named.values()) {
            assert_eq!(prepared.captures[lifted].len(), 1);
        }
        for triple in NATIVE_TARGETS {
            CraneliftBackend
                .emit(&input, &TargetSpec::native(triple).unwrap())
                .unwrap();
        }
    }
}
