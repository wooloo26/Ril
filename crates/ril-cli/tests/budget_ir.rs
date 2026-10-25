//! Internal Core -> object -> native execution probes. These hand-built IR
//! fixtures deliberately do not claim source BudgetProof checking or Ril passes.
#![cfg(any(
    all(windows, target_arch = "x86_64"),
    all(target_os = "linux", target_arch = "x86_64")
))]
use ril_codegen::{LinkRequest, Linker, NativeBackend, link::SystemLinker, target::TargetSpec};
use ril_codegen_cranelift::CraneliftBackend;
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::DefinitionId,
    source::{FileId, Span},
};
use ril_ir::core::{self, Expr, ExprKind, Pattern, Statement};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

const EXHAUSTED: u64 = 29;
fn expr(kind: ExprKind, at: u32) -> Expr {
    Expr {
        kind,
        span: Span {
            file: FileId(0),
            start: at,
            end: at + 1,
        },
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
        2,
    )
}
fn name(value: &str) -> Expr {
    expr(ExprKind::Name(value.into()), 3)
}
fn call(value: &str, arguments: Vec<Expr>) -> Expr {
    expr(
        ExprKind::Call {
            callback_entry: false,
            callee: Box::new(name(value)),
            arguments: arguments
                .into_iter()
                .map(|value| core::Argument { label: None, value })
                .collect(),
        },
        4,
    )
}
fn statement(expression: Expr) -> Statement {
    Statement::Expr {
        expression,
        terminated: true,
    }
}
fn tail(expression: Expr) -> Statement {
    Statement::Expr {
        expression,
        terminated: false,
    }
}
fn bind(variable: &str, value: Expr, scoped: bool) -> Statement {
    Statement::Bind {
        pattern: Pattern::Name(variable.into()),
        value,
        scoped,
    }
}
fn function(id: u32, value: &str, statements: Vec<Statement>) -> core::Function {
    core::Function {
        role: core::FunctionRole::Ordinary,
        definition: DefinitionId(id),
        name: value.into(),
        generic_parameters: vec![],
        parameters: vec![],
        body: core::Block { statements },
        span: Span {
            file: FileId(0),
            start: id * 10,
            end: id * 10 + 1,
        },
    }
}
fn handler(answer: Expr) -> Statement {
    static NEXT_HANDLER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    Statement::Handle {
        definition: NEXT_HANDLER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        arms: vec![core::HandlerArm {
            operation: EXHAUSTED,
            parameters: vec![],
            body: answer,
        }],
    }
}
fn budget(limit: i128, action: &str) -> Expr {
    expr(
        ExprKind::Budget {
            limit: Box::new(integer(limit)),
            action: Box::new(name(action)),
            exhaustion_operation: EXHAUSTED,
            coverage: CauseId(42),
        },
        5,
    )
}
fn check_equal(value: Expr, expected: i128) -> Statement {
    statement(call(
        "assert",
        vec![expr(
            ExprKind::Binary {
                operator: "==".into(),
                left: Box::new(value),
                right: Box::new(integer(expected)),
            },
            6,
        )],
    ))
}
fn main_budget(limit: i128, expected: i128) -> core::Function {
    function(
        0,
        "main",
        vec![
            bind(
                "answer",
                expr(
                    ExprKind::Block(core::Block {
                        statements: vec![handler(integer(99)), tail(budget(limit, "action"))],
                    }),
                    13,
                ),
                false,
            ),
            check_equal(name("answer"), expected),
            tail(unit()),
        ],
    )
}
fn main_recovery(main: &mut core::Function, answer: Expr) {
    let Statement::Bind { value, .. } = &mut main.body.statements[0] else {
        panic!("answer binding")
    };
    let ExprKind::Block(block) = &mut value.kind else {
        panic!("budget delimiter")
    };
    block.statements[0] = handler(answer);
}

#[test]
fn internal_ir_nested_named_effect_calls_keep_the_hoisted_capture_cell() {
    let step = function(
        2,
        "step",
        vec![
            Statement::Assign {
                target: name("count"),
                operator: "+=".into(),
                value: expr(
                    ExprKind::Perform {
                        operation: EXHAUSTED,
                        arguments: vec![],
                    },
                    71,
                ),
            },
            tail(name("count")),
        ],
    );
    let action = function(
        1,
        "action",
        vec![
            Statement::Function(step),
            bind("count", integer(3), false),
            statement(call("step", vec![])),
            statement(call("step", vec![])),
            tail(name("count")),
        ],
    );
    let main = function(
        0,
        "main",
        vec![
            handler(expr(
                ExprKind::Control {
                    operation: core::ControlOperation::Resume,
                    value: Some(Box::new(integer(7))),
                },
                72,
            )),
            check_equal(call("action", vec![]), 17),
            tail(unit()),
        ],
    );
    returned(execute(vec![main, action], core::Block::default()));
}

#[test]
fn internal_ir_nested_named_entries_use_the_metered_callable_pair() {
    let action = || {
        function(
            1,
            "action",
            vec![
                Statement::Function(function(2, "child", vec![tail(integer(7))])),
                tail(call("child", vec![])),
            ],
        )
    };
    returned(execute(
        vec![main_budget(2, 7), action()],
        core::Block::default(),
    ));
    returned(execute(
        vec![main_budget(1, 99), action()],
        core::Block::default(),
    ));
}

fn runtime_library(profile: &Path) -> PathBuf {
    let mut libraries = vec![];
    for directory in [profile.to_owned(), profile.join("deps")] {
        for entry in fs::read_dir(directory).unwrap().flatten() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            let matches = if cfg!(windows) {
                name.starts_with("ril_runtime") && name.ends_with(".lib")
            } else {
                name.starts_with("libril_runtime") && name.ends_with(".a")
            };
            if matches {
                libraries.push((entry.metadata().unwrap().modified().unwrap(), entry.path()));
            }
        }
    }
    libraries
        .into_iter()
        .max_by_key(|(time, _)| *time)
        .expect("CLI cargo dependency must produce the runtime static library")
        .1
}
fn execute(functions: Vec<core::Function>, globals: core::Block) -> serde_json::Value {
    let program = core::Program {
        functions,
        globals,
        ..Default::default()
    };
    let module = ril_codegen::lower::lower_native(&program).unwrap();
    let triple = if cfg!(windows) {
        "x86_64-pc-windows-msvc"
    } else {
        "x86_64-unknown-linux-gnu"
    };
    let target = TargetSpec::native(triple).unwrap();
    let artifact = CraneliftBackend.emit(&module, &target).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let object = directory.path().join(if cfg!(windows) {
        "budget.obj"
    } else {
        "budget.o"
    });
    let executable = directory.path().join(if cfg!(windows) {
        "budget.exe"
    } else {
        "budget"
    });
    fs::write(&object, artifact.bytes).unwrap();
    let profile = Path::new(env!("CARGO_BIN_EXE_ril")).parent().unwrap();
    SystemLinker
        .link(&LinkRequest {
            target,
            objects: vec![object],
            runtime_library: runtime_library(profile),
            output: executable.clone(),
        })
        .unwrap();
    let report = directory.path().join("report");
    let stdout = directory.path().join("stdout");
    let stderr = directory.path().join("stderr");
    let mut child = Command::new(executable)
        .env("RIL_EXECUTION_REPORT", &report)
        .stdout(Stdio::from(fs::File::create(&stdout).unwrap()))
        .stderr(Stdio::from(fs::File::create(&stderr).unwrap()))
        .spawn()
        .unwrap();
    let child_id = child.id();
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("internal IR fixture did not terminate");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let report = PathBuf::from(format!("{}.{child_id}", report.display()));
    let raw = fs::read(&report).unwrap_or_else(|error| {
        panic!(
            "missing native report: {error}; exit {status}; stderr {}",
            String::from_utf8_lossy(&fs::read(stderr).unwrap())
        )
    });
    let report: serde_json::Value = serde_json::from_slice(&raw).unwrap();
    assert_eq!(
        status.code().map(i64::from),
        report["exit"].as_i64(),
        "{report}"
    );
    report
}
fn returned(report: serde_json::Value) {
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn internal_ir_zero_skips_the_action_and_one_unit_allows_exactly_its_entry() {
    returned(execute(
        vec![
            main_budget(0, 99),
            function(
                1,
                "action",
                vec![tail(call(
                    "panic",
                    vec![expr(
                        ExprKind::Literal(core::Literal::String("zero action executed".into())),
                        7,
                    )],
                ))],
            ),
        ],
        core::Block::default(),
    ));
    returned(execute(
        vec![
            main_budget(1, 42),
            function(1, "action", vec![tail(integer(42))]),
        ],
        core::Block::default(),
    ));
}
#[test]
fn internal_ir_pure_mutual_recursion_exhausts_twenty_thousand_entries_without_host_recursion() {
    returned(execute(
        vec![
            main_budget(20_000, 99),
            function(1, "action", vec![tail(call("other", vec![]))]),
            function(2, "other", vec![tail(call("action", vec![]))]),
        ],
        core::Block::default(),
    ));
}
#[test]
fn internal_ir_nested_outer_wins_and_recovery_under_a_surviving_outer_is_metered() {
    for (outer, inner, expected) in [(2, 1000, 99), (2, 0, 99), (3, 0, 77)] {
        let main = main_budget(outer, expected);
        returned(execute(
            vec![
                main,
                function(
                    1,
                    "action",
                    vec![handler(integer(77)), tail(budget(inner, "spin"))],
                ),
                function(
                    2,
                    "spin",
                    vec![tail(expr(
                        ExprKind::Loop {
                            body: core::Block::default(),
                            charge: Some(core::ChargeEvent::LoopIteration),
                        },
                        8,
                    ))],
                ),
            ],
            core::Block::default(),
        ));
    }
}
#[test]
fn internal_ir_budget_exhaustion_runs_cleanup_before_recovery_and_preserves_double_fault() {
    let action = || {
        function(
            1,
            "action",
            vec![
                bind(
                    "guard",
                    expr(
                        ExprKind::Record {
                            members: (vec![("on_close".into(), name("cleanup"))])
                                .into_iter()
                                .map(|(name, value)| ril_ir::core::RecordMember::Field(name, value))
                                .collect(),
                        },
                        9,
                    ),
                    true,
                ),
                tail(expr(
                    ExprKind::Loop {
                        body: core::Block::default(),
                        charge: Some(core::ChargeEvent::LoopIteration),
                    },
                    10,
                )),
            ],
        )
    };
    let globals = core::Block {
        statements: vec![bind("trace", integer(0), false)],
    };
    let mut main = main_budget(1, 99);
    main_recovery(
        &mut main,
        expr(
            ExprKind::Block(core::Block {
                statements: vec![check_equal(name("trace"), 1), tail(integer(99))],
            }),
            11,
        ),
    );
    let cleanup = function(
        2,
        "cleanup",
        vec![
            Statement::Assign {
                target: name("trace"),
                operator: "=".into(),
                value: integer(1),
            },
            tail(unit()),
        ],
    );
    returned(execute(vec![main, action(), cleanup], globals));
    let cleanup = function(
        2,
        "cleanup",
        vec![tail(call(
            "panic",
            vec![expr(
                ExprKind::Literal(core::Literal::String("cleanup fault".into())),
                12,
            )],
        ))],
    );
    let failed = execute(
        vec![main_budget(1, 99), action(), cleanup],
        core::Block::default(),
    );
    assert_eq!(failed["runtime"], "double-fault", "{failed}");
    assert!(
        failed["message"]
            .as_str()
            .unwrap()
            .contains("cleanup fault"),
        "{failed}"
    );
}
