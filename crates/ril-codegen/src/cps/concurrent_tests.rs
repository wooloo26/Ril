use super::*;
use ril_compiler_core::{ids::DefinitionId, source::FileId};

fn span() -> Span {
    Span {
        file: FileId(0),
        start: 0,
        end: 1,
    }
}
fn function(id: u32, name: &str, value: Expr) -> core::Function {
    core::Function {
        role: core::FunctionRole::Ordinary,
        definition: DefinitionId(id),
        name: name.into(),
        generic_parameters: vec![],
        parameters: vec![],
        body: core::Block {
            statements: vec![Statement::Expr {
                expression: value,
                terminated: false,
            }],
        },
        span: span(),
    }
}

#[test]
fn sequence_length_failure_skips_effectful_expected_elements_in_cps() {
    let source = function(
        0,
        "main",
        expression(
            ExprKind::Is {
                value: Box::new(expression(ExprKind::Array(vec![]), span())),
                pattern: Pattern::Array(vec![
                    Pattern::Value(Box::new(expression(
                        ExprKind::Perform {
                            operation: 51,
                            arguments: vec![],
                        },
                        span(),
                    ))),
                    Pattern::Rest(None),
                ]),
            },
            span(),
        ),
    );
    let graph = lower(&source).unwrap();
    let perform = graph
        .blocks
        .iter()
        .position(|block| matches!(block.terminator, Terminator::Perform { operation: 51, .. }))
        .unwrap();
    let shape = graph.blocks.iter().find(|block| block.instructions.iter().any(|instruction| matches!(instruction,
        cps::Instruction::Statement(statement) if matches!(&**statement,
            Statement::Bind { value: Expr { kind: ExprKind::Is { pattern: Pattern::Array(items), .. }, .. }, .. }
            if matches!(items.as_slice(), [Pattern::Wildcard, Pattern::Rest(None)]))
    ))).unwrap();
    let Terminator::Jump(branch) = shape.terminator else {
        panic!("shape result");
    };
    let Terminator::Branch {
        then_block,
        else_block,
        ..
    } = graph.blocks[branch.0 as usize].terminator
    else {
        panic!("shape guard");
    };
    let reaches = |start: BlockId| {
        let mut pending = vec![start];
        let mut seen = BTreeSet::new();
        while let Some(block) = pending.pop() {
            if !seen.insert(block) {
                continue;
            }
            if block.0 as usize == perform {
                return true;
            }
            match &graph.blocks[block.0 as usize].terminator {
                Terminator::Jump(next)
                | Terminator::Charge { next, .. }
                | Terminator::Perform { next, .. }
                | Terminator::Call { next, .. }
                | Terminator::ScopeLeave { next, .. } => pending.push(*next),
                Terminator::Branch {
                    then_block,
                    else_block,
                    ..
                } => pending.extend([*then_block, *else_block]),
                _ => {}
            }
        }
        false
    };
    assert!(reaches(then_block));
    assert!(!reaches(else_block));
}

#[test]
fn concurrency_values_seed_callers_without_user_effects() {
    for builtin in [
        "Concurrent::scope",
        "Concurrent::fork",
        "Concurrent::join",
        "Channel::__bounded_0_10_20",
        "Channel::send",
        "Channel::recv",
        "Channel::detach",
        "Channel::attach",
        "Channel::close",
        "\0ril.control.parallel_run",
    ] {
        let program = core::Program {
            functions: vec![
                function(0, "worker", name(builtin, span())),
                function(
                    1,
                    "main",
                    expression(
                        ExprKind::Call {
                            callback_entry: false,
                            callee: Box::new(name("worker", span())),
                            arguments: vec![],
                        },
                        span(),
                    ),
                ),
            ],
            ..core::Program::default()
        };
        assert_eq!(
            suspending_functions(&program),
            BTreeSet::from(["main".into(), "worker".into(),]),
            "{builtin}"
        );
    }
}

#[test]
fn nested_concurrency_callables_keep_native_continuations() {
    let callback = expression(
        ExprKind::Call {
            callback_entry: false,
            callee: Box::new(name("Concurrent::join", span())),
            arguments: vec![core::Argument {
                label: None,
                value: name("task", span()),
            }],
        },
        span(),
    );
    assert!(lambda_suspends(
        &callback,
        &BTreeSet::new(),
        &BTreeSet::new(),
        &BTreeSet::new()
    ));
    let mut parent = function(0, "parent", unit(span()));
    parent
        .body
        .statements
        .push(Statement::Function(function(1, "nested", callback)));
    let program = core::Program {
        functions: vec![parent],
        ..core::Program::default()
    };
    assert!(suspending_functions(&program).contains("parent"));
}

#[test]
fn unrelated_join_members_do_not_seed_concurrency() {
    let plain = name("String::join", span());
    assert!(!lambda_suspends(
        &plain,
        &BTreeSet::new(),
        &BTreeSet::new(),
        &BTreeSet::new()
    ));
    let program = core::Program {
        functions: vec![function(0, "main", plain)],
        ..core::Program::default()
    };
    assert!(suspending_functions(&program).is_empty());
}

#[test]
fn only_the_direct_scope_body_avoids_retaining_the_handler() {
    let lambda = |start| Expr {
        span: Span {
            start,
            end: start + 1,
            ..span()
        },
        kind: ExprKind::Lambda {
            parameters: vec![],
            body: Box::new(expression(
                ExprKind::Perform {
                    operation: 43,
                    arguments: vec![],
                },
                span(),
            )),
        },
    };
    let scope = |callee: &str, action: Expr| {
        expression(
            ExprKind::Call {
                callback_entry: false,
                callee: Box::new(name(callee, span())),
                arguments: vec![core::Argument {
                    label: None,
                    value: action,
                }],
            },
            span(),
        )
    };
    let tail = |expression| Statement::Expr {
        expression,
        terminated: false,
    };
    let mut source = function(0, "main", unit(span()));
    source.body.statements = vec![
        Statement::Handle {
            definition: 0,
            arms: vec![core::HandlerArm {
                operation: 43,
                parameters: vec![],
                body: expression(
                    ExprKind::Control {
                        operation: core::ControlOperation::Resume,
                        value: None,
                    },
                    span(),
                ),
            }],
        },
        Statement::Bind {
            pattern: Pattern::Name("stored".into()),
            value: lambda(2),
            scoped: false,
        },
        tail(scope("Concurrent::scope", lambda(4))),
        tail(scope("local_scope", lambda(6))),
        tail(scope(
            "Concurrent::scope",
            expression(
                ExprKind::Block(core::Block {
                    statements: vec![tail(lambda(8))],
                }),
                span(),
            ),
        )),
        // Public IR need not have unique spans: the immediate body must not
        // erase the independently stored closure's retained-context marker.
        tail(scope("Concurrent::scope", lambda(2))),
    ];
    let graph = lower(&source).unwrap();
    assert!(!graph.retained_lambdas.contains(&(0, 4, 5)));
    for start in [2, 6, 8] {
        assert!(graph.retained_lambdas.contains(&(0, start, start + 1)));
    }
}
