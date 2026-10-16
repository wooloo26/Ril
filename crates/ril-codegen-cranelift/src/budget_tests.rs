//! These are Core/object tests, not claims that source BudgetProof exists.
use crate::CraneliftBackend;
use object::{Object, ObjectSection, ObjectSymbol};
use ril_codegen::{
    NativeBackend,
    target::{NATIVE_TARGETS, TargetSpec},
};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::DefinitionId,
    source::{FileId, Span},
};
use ril_ir::{
    core::{self, Expr, ExprKind, Pattern, Statement},
    cps::Terminator,
    native::Body,
};

fn span(start: u32) -> Span {
    Span {
        file: FileId(0),
        start,
        end: start + 1,
    }
}
fn expr(kind: ExprKind, start: u32) -> Expr {
    Expr {
        kind,
        span: span(start),
    }
}
fn unit() -> Expr {
    expr(ExprKind::Literal(core::Literal::Unit), 1)
}
fn integer(value: i128) -> Expr {
    expr(
        ExprKind::Literal(core::Literal::Integer {
            value,
            bits: 64,
            signed: true,
        }),
        1,
    )
}
fn function(id: u32, name: &str, statements: Vec<Statement>) -> core::Function {
    core::Function {
        role: core::FunctionRole::Ordinary,
        definition: DefinitionId(id),
        name: name.into(),
        generic_parameters: vec![],
        parameters: vec![],
        body: core::Block { statements },
        span: span(id),
    }
}
fn tail(expression: Expr) -> Statement {
    Statement::Expr {
        expression,
        terminated: false,
    }
}
fn budget(action: Expr) -> Expr {
    expr(
        ExprKind::Budget {
            limit: Box::new(integer(4)),
            action: Box::new(action),
            exhaustion_operation: 29,
            coverage: CauseId(42),
        },
        2,
    )
}
fn emit_both(program: &core::Program) {
    let module = ril_codegen::lower::lower_native(program).unwrap();
    for triple in NATIVE_TARGETS {
        let artifact = CraneliftBackend
            .emit(&module, &TargetSpec::native(triple).unwrap())
            .unwrap();
        let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
        for expected in [
            "ril_rt_require_contract",
            "ril_rt_cps_budget",
            "ril_rt_cps_charge",
            "ril_rt_callable_with_budget",
        ] {
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok(expected) && !symbol.is_definition()),
                "missing {expected} for {triple}"
            );
        }
    }
}
#[test]
fn metered_siblings_keep_normal_entries_and_compile_real_coff_and_elf_budget_edges() {
    let source = core::Program {
        functions: vec![
            function(
                0,
                "main",
                vec![tail(budget(expr(ExprKind::Name("spin".into()), 3)))],
            ),
            function(
                1,
                "spin",
                vec![tail(expr(
                    ExprKind::Loop {
                        body: core::Block::default(),
                        charge: Some(core::ChargeEvent::LoopIteration),
                    },
                    4,
                ))],
            ),
        ],
        ..Default::default()
    };
    let module = ril_codegen::lower::lower_native(&source).unwrap();
    assert!(
        module
            .functions
            .iter()
            .any(|function| matches!(&function.body,Body::Managed(body)if body.name=="spin"))
    );
    let sibling = &module.budget_entries["spin"];
    let graph = module
        .functions
        .iter()
        .find_map(|function| match &function.body {
            Body::Cps(graph) if &graph.name == sibling => Some(graph),
            _ => None,
        })
        .unwrap();
    assert!(graph.metered);
    assert_eq!(
        graph
            .blocks
            .iter()
            .filter(|block| matches!(
                block.terminator,
                Terminator::Charge {
                    event: core::ChargeEvent::FunctionEntry,
                    ..
                }
            ))
            .count(),
        1
    );
    assert_eq!(
        graph
            .blocks
            .iter()
            .filter(|block| matches!(
                block.terminator,
                Terminator::Charge {
                    event: core::ChargeEvent::LoopIteration,
                    ..
                }
            ))
            .count(),
        1
    );
    let main = module
        .functions
        .iter()
        .find_map(|function| match &function.body {
            Body::Cps(graph) if graph.name == "main" => Some(graph),
            _ => None,
        })
        .unwrap();
    assert!(main.blocks.iter().any(|block| matches!(
        block.terminator,
        Terminator::Budget {
            coverage: CauseId(42),
            exhaustion_operation: 29,
            ..
        }
    )));
    emit_both(&source);
}
#[test]
fn dual_entry_closure_lifting_keeps_nested_capture_cell_names_consistent() {
    let inner = expr(
        ExprKind::Lambda {
            parameters: vec![],
            body: Box::new(expr(ExprKind::Name("value".into()), 22)),
        },
        20,
    );
    let action = expr(
        ExprKind::Lambda {
            parameters: vec![],
            body: Box::new(expr(
                ExprKind::Block(core::Block {
                    statements: vec![
                        Statement::Bind {
                            pattern: Pattern::Name("value".into()),
                            value: integer(7),
                            scoped: false,
                        },
                        tail(inner),
                    ],
                }),
                11,
            )),
        },
        10,
    );
    let source = core::Program {
        functions: vec![function(
            0,
            "main",
            vec![
                Statement::Bind {
                    pattern: Pattern::Name("later".into()),
                    value: budget(action),
                    scoped: false,
                },
                Statement::Expr {
                    expression: expr(
                        ExprKind::Call {
                            callback_entry: false,
                            callee: Box::new(expr(ExprKind::Name("later".into()), 30)),
                            arguments: vec![],
                        },
                        31,
                    ),
                    terminated: true,
                },
                tail(unit()),
            ],
        )],
        ..Default::default()
    };
    emit_both(&source);
}

#[test]
fn ordinary_handler_arms_keep_metered_entries_for_later_retention() {
    let action = expr(
        ExprKind::Lambda {
            parameters: vec![],
            body: Box::new(unit()),
        },
        10,
    );
    let source = core::Program {
        functions: vec![function(
            0,
            "main",
            vec![
                Statement::Handle {
                    definition: 0,
                    arms: vec![core::HandlerArm {
                        operation: 29,
                        parameters: vec![],
                        body: unit(),
                    }],
                },
                Statement::Expr {
                    expression: budget(action),
                    terminated: true,
                },
                tail(unit()),
            ],
        )],
        ..Default::default()
    };
    let module = ril_codegen::lower::lower_native(&source).unwrap();
    let prepared = crate::managed::prepare(&module).unwrap();
    let handler_block = |name: &str| {
        let graph = module
            .functions
            .iter()
            .find_map(|function| match &function.body {
                Body::Cps(graph) if graph.name == name => Some(graph),
                _ => None,
            })
            .unwrap();
        let block = graph
            .blocks
            .iter()
            .position(|block| matches!(block.terminator, Terminator::Handle { .. }))
            .unwrap();
        prepared
            .functions
            .iter()
            .find_map(|function| match &function.body {
                Body::CpsBlock {
                    function: graph,
                    block: found,
                } if graph.name == name && found.0 as usize == block => {
                    Some(function.symbol.clone())
                }
                _ => None,
            })
            .unwrap()
    };
    let normal = handler_block("main");
    let metered = handler_block(&module.budget_entries["main"]);
    for triple in NATIVE_TARGETS {
        let artifact = CraneliftBackend
            .emit(&module, &TargetSpec::native(triple).unwrap())
            .unwrap();
        let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
        let imports = |name: &str| {
            let function = object
                .symbols()
                .find(|symbol| symbol.name() == Ok(name))
                .unwrap();
            let index = function.section_index().unwrap();
            let section = object.section_by_index(index).unwrap();
            let start = function.address() - section.address();
            let end = if function.size() != 0 {
                start + function.size()
            } else {
                object
                    .symbols()
                    .filter(|symbol| {
                        symbol.section_index() == Some(index)
                            && symbol.address() > function.address()
                    })
                    .map(|symbol| symbol.address() - section.address())
                    .min()
                    .unwrap_or(section.size())
            };
            section
                .relocations()
                .filter(|(offset, _)| *offset >= start && *offset < end)
                .filter_map(|(_, relocation)| {
                    if let object::RelocationTarget::Symbol(index) = relocation.target() {
                        let name = object.symbol_by_index(index).unwrap().name().unwrap();
                        Some(name.strip_prefix(".refptr.").unwrap_or(name).to_owned())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
        };
        let ordinary = imports(&normal);
        // The immediate ordinary body keeps its CPS callable. Its arm has a
        // paired entry so a retained definition can later run inside a budget.
        assert!(
            ordinary.iter().any(|name| name == "ril_rt_cps_callable"),
            "{triple}: {ordinary:?}"
        );
        assert!(
            ordinary
                .iter()
                .any(|name| name == "ril_rt_callable_with_budget"),
            "{triple}: {ordinary:?}"
        );
        let protected = imports(&metered);
        assert!(
            protected
                .iter()
                .any(|name| name == "ril_rt_callable_with_budget"),
            "{triple}: {protected:?}"
        );
        assert!(
            !protected.iter().any(|name| name == "ril_rt_cps_callable"),
            "{triple}: {protected:?}"
        );
    }
}

#[test]
fn pure_mutual_recursion_has_metered_native_call_edges_instead_of_managed_recursive_calls() {
    let call = |name: &str| {
        expr(
            ExprKind::Call {
                callback_entry: false,
                callee: Box::new(expr(ExprKind::Name(name.into()), 4)),
                arguments: vec![],
            },
            5,
        )
    };
    let source = core::Program {
        functions: vec![
            function(
                0,
                "main",
                vec![tail(budget(expr(ExprKind::Name("first".into()), 3)))],
            ),
            function(1, "first", vec![tail(call("second"))]),
            function(2, "second", vec![tail(call("first"))]),
        ],
        ..Default::default()
    };
    let module = ril_codegen::lower::lower_native(&source).unwrap();
    for name in ["first", "second"] {
        let sibling = &module.budget_entries[name];
        let graph = module
            .functions
            .iter()
            .find_map(|function| match &function.body {
                Body::Cps(graph) if &graph.name == sibling => Some(graph),
                _ => None,
            })
            .unwrap();
        assert!(graph.metered);
        assert!(
            graph
                .blocks
                .iter()
                .any(|block| matches!(block.terminator, Terminator::Call { .. }))
        );
        assert_eq!(
            graph
                .blocks
                .iter()
                .filter(|block| matches!(
                    block.terminator,
                    Terminator::Charge {
                        event: core::ChargeEvent::FunctionEntry,
                        ..
                    }
                ))
                .count(),
            1
        );
    }
    emit_both(&source);
}
