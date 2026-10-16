//! AOT object emission for the initial native MIR probe subset.
use cranelift_codegen::{
    ir::{InstBuilder, types},
    isa,
    settings::{self, Configurable},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use ril_codegen::target::TargetSpec;
use ril_codegen::{BackendError, NativeBackend, ObjectArtifact};
use ril_ir::native::{Body, Module as NativeModule};
use std::collections::{HashMap, HashSet};

pub struct CraneliftBackend;

fn codegen(error: impl std::fmt::Display) -> BackendError {
    BackendError::Codegen(error.to_string())
}

impl NativeBackend for CraneliftBackend {
    fn emit(
        &self,
        input: &NativeModule,
        target: &TargetSpec,
    ) -> Result<ObjectArtifact, BackendError> {
        target
            .validate()
            .map_err(|e| BackendError::Target(e.to_string()))?;
        if input.functions.is_empty() {
            return Err(BackendError::InvalidIr("empty module".into()));
        }
        let foreign = crate::managed::foreign::prepare(input)?;
        let input = &foreign.module;
        let mut names = HashSet::new();
        for function in &input.functions {
            let name = &function.symbol;
            if name.is_empty() || name.contains('\0') || !names.insert(name) {
                return Err(BackendError::InvalidIr(format!(
                    "invalid or duplicate symbol: {name:?}"
                )));
            }
        }
        let triple = target
            .triple
            .parse::<target_lexicon::Triple>()
            .map_err(codegen)?;
        let mut flags = settings::builder();
        flags.set("is_pic", "true").map_err(codegen)?;
        let isa = isa::lookup(triple)
            .map_err(codegen)?
            .finish(settings::Flags::new(flags))
            .map_err(codegen)?;
        let builder = ObjectBuilder::new(isa, "ril", default_libcall_names()).map_err(codegen)?;
        let mut module = ObjectModule::new(builder);
        let prepared = crate::managed::prepare(input)?;
        let mut program = crate::managed::ProgramInfo {
            constants: prepared.constants,
            foreign_descriptors: foreign.descriptors,
            foreign_constants: foreign.constants,
            handler_budget_entries: prepared.handler_budget_entries,
            retained_handlers: prepared.retained_handlers,
            operations: input
                .operations
                .iter()
                .map(|operation| (operation.name.clone(), operation.identity))
                .collect(),
            constructors: input
                .constructors
                .iter()
                .cloned()
                .map(|constructor| (constructor.name.clone(), constructor))
                .collect(),
            functions: HashMap::new(),
            symbols: HashMap::new(),
            globals: prepared.globals,
            lambdas: prepared.lambdas,
            named: prepared.named,
            call_signatures: input
                .call_signatures
                .iter()
                .map(|signature| {
                    (
                        (
                            signature.span.file.0,
                            signature.span.start,
                            signature.span.end,
                        ),
                        signature.parameters.clone(),
                    )
                })
                .collect(),
            imports: HashMap::new(),
            next_data: 0,
        };
        let mut declarations = Vec::new();
        for function in &prepared.functions {
            let signature = crate::managed::signature(&module, &function.body);
            let id = module
                .declare_function(&function.symbol, Linkage::Export, &signature)
                .map_err(codegen)?;
            let (name, parameters) = match &function.body {
                Body::Managed(function) => (function.name.clone(), function.parameters.clone()),
                Body::Cps(function) => (function.name.clone(), function.parameters.clone()),
                _ => (function.symbol.clone(), vec![]),
            };
            let captures = prepared.captures.get(&name).cloned().unwrap_or_default();
            let info = crate::managed::FunctionInfo {
                metered_entry_event: match &function.body {
                    Body::Managed(function) => {
                        function.role != ril_ir::core::FunctionRole::Synthetic
                    }
                    Body::Cps(function) => function.role != ril_ir::core::FunctionRole::Synthetic,
                    _ => false,
                },
                budget: None,
                id,
                parameters,
                captures,
                cps: matches!(function.body, Body::Cps(_) | Body::CpsBlock { .. }),
            };
            if program
                .symbols
                .insert(function.symbol.clone(), info.clone())
                .is_some()
            {
                return Err(BackendError::InvalidIr(format!(
                    "duplicate native symbol: {}",
                    function.symbol
                )));
            }
            if !matches!(function.body, Body::Entry { .. } | Body::CpsBlock { .. })
                && program.functions.insert(name.clone(), info).is_some()
            {
                return Err(BackendError::InvalidIr(format!(
                    "duplicate Core function name: {name}"
                )));
            }
            declarations.push((id, signature));
        }
        for (normal, budget) in &prepared.budget_entries {
            let budget = program.functions.get(budget).ok_or_else(|| {
                BackendError::InvalidIr("metered callable entry was not declared".into())
            })?;
            if !budget.cps {
                return Err(BackendError::InvalidIr(
                    "metered callable entry is not CPS".into(),
                ));
            }
            let budget = budget.id;
            let normal = program.functions.get_mut(normal).ok_or_else(|| {
                BackendError::InvalidIr("normal callable entry was not declared".into())
            })?;
            normal.budget = Some(budget);
            let normal = normal.id;
            for info in program
                .symbols
                .values_mut()
                .filter(|info| info.id == normal)
            {
                info.budget = Some(budget);
            }
        }
        for (function, (id, signature)) in prepared.functions.iter().zip(declarations) {
            let mut context = module.make_context();
            context.func.signature = signature;
            let mut frontend = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut context.func, &mut frontend);
            match &function.body {
                Body::ReturnI64(value) => {
                    let entry = builder.create_block();
                    builder.switch_to_block(entry);
                    builder.seal_all_blocks();
                    let value = builder.ins().iconst(types::I64, *value);
                    builder.ins().return_(&[value]);
                }
                Body::Managed(function) => {
                    crate::managed::emit_managed(&mut module, &mut builder, function, &mut program)?
                }
                Body::Foreign(_) => {
                    return Err(BackendError::InvalidIr(
                        "foreign adapter was not prepared".into(),
                    ));
                }
                Body::Cps(function) => crate::managed::emit_cps(
                    &mut module,
                    &mut builder,
                    function,
                    function.entry,
                    &mut program,
                )?,
                Body::CpsBlock { function, block } => crate::managed::emit_cps(
                    &mut module,
                    &mut builder,
                    function,
                    *block,
                    &mut program,
                )?,
                Body::Entry { initializer, entry } => crate::managed::emit_entry(
                    &mut module,
                    &mut builder,
                    initializer,
                    entry,
                    &mut program,
                )?,
            }
            builder.finalize(module.isa().frontend_config());
            module.define_function(id, &mut context).map_err(codegen)?;
        }
        let bytes = module.finish().emit().map_err(codegen)?;
        Ok(ObjectArtifact {
            target: target.clone(),
            format: target.object_format,
            bytes,
            runtime_contract_version: ril_runtime_api::CONTRACT_VERSION,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use object::{Object, ObjectSymbol};
    use ril_ir::native::Function;
    #[test]
    fn emits_real_x64_coff_and_elf_objects() {
        let input = NativeModule {
            global_bindings: Default::default(),
            budget_entries: Default::default(),
            retained_handlers: Default::default(),
            closure_sites: Default::default(),
            nonretaining_adapters: Default::default(),
            specializations: vec![],
            constant_graphs: vec![],
            external_functions: vec![],
            external_constants: vec![],
            foreign_bindings: vec![],
            call_signatures: vec![],
            constructors: vec![],
            operations: vec![],
            functions: vec![Function {
                symbol: "ril_probe".into(),
                body: Body::ReturnI64(42),
            }],
        };
        for triple in ril_codegen::target::NATIVE_TARGETS {
            let target = TargetSpec::native(triple).unwrap();
            let artifact = CraneliftBackend.emit(&input, &target).unwrap();
            let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
            assert_eq!(object.architecture(), object::Architecture::X86_64);
            assert_eq!(
                object.format(),
                match target.object_format {
                    ril_codegen::target::ObjectFormat::Coff => object::BinaryFormat::Coff,
                    ril_codegen::target::ObjectFormat::Elf => object::BinaryFormat::Elf,
                }
            );
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok("ril_probe") && symbol.is_definition())
            );
        }
    }
    #[test]
    fn rejects_empty_or_duplicate_modules() {
        let target = TargetSpec::native(ril_codegen::target::NATIVE_TARGETS[0]).unwrap();
        assert!(
            CraneliftBackend
                .emit(
                    &NativeModule {
                        global_bindings: Default::default(),
                        budget_entries: Default::default(),
                        retained_handlers: Default::default(),
                        closure_sites: Default::default(),
                        nonretaining_adapters: Default::default(),
                        specializations: vec![],
                        constant_graphs: vec![],
                        external_functions: vec![],
                        external_constants: vec![],
                        foreign_bindings: vec![],
                        call_signatures: vec![],
                        operations: vec![],
                        functions: vec![],
                        constructors: vec![]
                    },
                    &target
                )
                .is_err()
        );
        let function = Function {
            symbol: "duplicate".into(),
            body: Body::ReturnI64(0),
        };
        assert!(
            CraneliftBackend
                .emit(
                    &NativeModule {
                        global_bindings: Default::default(),
                        budget_entries: Default::default(),
                        retained_handlers: Default::default(),
                        closure_sites: Default::default(),
                        nonretaining_adapters: Default::default(),
                        specializations: vec![],
                        constant_graphs: vec![],
                        external_functions: vec![],
                        external_constants: vec![],
                        foreign_bindings: vec![],
                        call_signatures: vec![],
                        constructors: vec![],
                        operations: vec![],
                        functions: vec![function.clone(), function]
                    },
                    &target
                )
                .is_err()
        );
    }

    #[test]
    fn rejects_unimplemented_builtin_values_and_calls_before_object_emission() {
        use ril_compiler_core::{
            ids::DefinitionId,
            source::{FileId, Span},
        };
        use ril_ir::core::{self, Expr, ExprKind, Statement};
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let name = Expr {
            kind: ExprKind::Name("__ril_missing_builtin".into()),
            span,
        };
        for expression in [
            name.clone(),
            Expr {
                kind: ExprKind::Call {
                    callback_entry: false,
                    callee: Box::new(name),
                    arguments: vec![],
                },
                span,
            },
        ] {
            let input = NativeModule {
                global_bindings: Default::default(),
                budget_entries: Default::default(),
                retained_handlers: Default::default(),
                closure_sites: Default::default(),
                nonretaining_adapters: Default::default(),
                specializations: vec![],
                constant_graphs: vec![],
                external_functions: vec![],
                external_constants: vec![],
                foreign_bindings: vec![],
                call_signatures: vec![],
                constructors: vec![],
                operations: vec![],
                functions: vec![Function {
                    symbol: "probe".into(),
                    body: Body::Managed(core::Function {
                        role: core::FunctionRole::Ordinary,
                        definition: DefinitionId(0),
                        name: "probe".into(),
                        generic_parameters: vec![],
                        parameters: vec![],
                        span,
                        body: core::Block {
                            statements: vec![Statement::Expr {
                                expression,
                                terminated: false,
                            }],
                        },
                    }),
                }],
            };
            let target = TargetSpec::native(ril_codegen::target::NATIVE_TARGETS[0]).unwrap();
            assert!(matches!(
                CraneliftBackend.emit(&input, &target),
                Err(BackendError::NotImplemented(_))
            ));
        }
    }

    #[test]
    fn rejects_control_builtins_in_a_managed_body_before_object_emission() {
        use ril_compiler_core::{
            ids::DefinitionId,
            source::{FileId, Span},
        };
        use ril_ir::core::{self, Expr, ExprKind, Statement};
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        for builtin in [
            "Concurrent::scope",
            "Concurrent::fork",
            "Concurrent::join",
            "Channel::recv",
            "Parallel::map",
            "Parallel::map_bounded",
            "Parallel::find",
            "Parallel::first",
            "Parallel::any",
            "Parallel::fold",
            "Parallel::join",
            "Parallel::join3",
            "Parallel::for_each",
            "Io::read_buffered",
            "Io::write_buffered",
            "Io::flush",
        ] {
            let input = NativeModule {
                functions: vec![Function {
                    symbol: "probe".into(),
                    body: Body::Managed(core::Function {
                        role: core::FunctionRole::Ordinary,
                        definition: DefinitionId(0),
                        name: "probe".into(),
                        generic_parameters: vec![],
                        parameters: vec![],
                        span,
                        body: core::Block {
                            statements: vec![Statement::Expr {
                                expression: Expr {
                                    kind: ExprKind::Call {
                                        callback_entry: false,
                                        callee: Box::new(Expr {
                                            kind: ExprKind::Name(builtin.into()),
                                            span,
                                        }),
                                        arguments: vec![],
                                    },
                                    span,
                                },
                                terminated: false,
                            }],
                        },
                    }),
                }],
                ..NativeModule::default()
            };
            let target = TargetSpec::native(ril_codegen::target::NATIVE_TARGETS[0]).unwrap();
            let BackendError::NotImplemented(reason) =
                CraneliftBackend.emit(&input, &target).unwrap_err()
            else {
                panic!("managed control builtin was not rejected");
            };
            assert!(
                reason
                    .detail
                    .contains("requires native continuation lowering"),
                "{reason:?}"
            );
        }
    }

    #[test]
    fn scoped_cps_callbacks_use_exit_steps_and_managed_compatibility_remains_guarded() {
        use ril_compiler_core::{
            ids::DefinitionId,
            source::{FileId, Span},
        };
        use ril_ir::core::{self, Expr, ExprKind, Pattern, Statement};
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let cleanup = core::Function {
            role: core::FunctionRole::Ordinary,
            definition: DefinitionId(0),
            name: "cleanup".into(),
            generic_parameters: vec![],
            parameters: vec![],
            span,
            body: core::Block {
                statements: vec![Statement::Expr {
                    expression: Expr {
                        span,
                        kind: ExprKind::Perform {
                            operation: 1,
                            arguments: vec![],
                        },
                    },
                    terminated: false,
                }],
            },
        };
        let main = core::Function {
            role: core::FunctionRole::Ordinary,
            definition: DefinitionId(1),
            name: "main".into(),
            generic_parameters: vec![],
            parameters: vec![],
            span,
            body: core::Block {
                statements: vec![Statement::Bind {
                    pattern: Pattern::Name("guard".into()),
                    value: Expr {
                        span,
                        kind: ExprKind::Record {
                            fields: vec![(
                                "on_close".into(),
                                Expr {
                                    span,
                                    kind: ExprKind::Name("cleanup".into()),
                                },
                            )],
                            spread: None,
                            members: vec![],
                        },
                    },
                    scoped: true,
                }],
            },
        };
        let program = core::Program {
            functions: vec![cleanup, main],
            operations: vec![core::Operation {
                identity: 1,
                name: "Read::get".into(),
                span,
            }],
            ..Default::default()
        };
        let native = ril_codegen::lower::lower_native(&program).unwrap();
        for triple in ril_codegen::target::NATIVE_TARGETS {
            let target = TargetSpec::native(triple).unwrap();
            let artifact = CraneliftBackend.emit(&native, &target).unwrap();
            let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
            assert!(object.symbols().any(|symbol| {
                symbol.name() == Ok("ril_rt_cps_scope_leave_then") && !symbol.is_definition()
            }));

            // Hand-written compatibility IR cannot silently call a CPS cleanup
            // through the synchronous physical-frame ABI.
            let mut compatibility = native.clone();
            let owner = compatibility
                .functions
                .iter_mut()
                .find(|function| matches!(&function.body, Body::Cps(graph) if graph.name == "main"))
                .unwrap();
            owner.body = Body::Managed(program.functions[1].clone());
            let error = CraneliftBackend.emit(&compatibility, &target).unwrap_err();
            let BackendError::NotImplemented(reason) = error else {
                panic!("{error:?}")
            };
            assert!(
                reason.detail.contains("continuation-aware callback ABI"),
                "{reason:?}"
            );
        }
    }

    #[test]
    fn core_names_and_native_symbols_are_separate_resolution_domains() {
        use ril_compiler_core::{
            ids::DefinitionId,
            source::{FileId, Span},
        };
        use ril_ir::core::{self, Expr, ExprKind, Statement};
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let function = |definition, name: &str, expression| core::Function {
            role: core::FunctionRole::Ordinary,
            definition: DefinitionId(definition),
            name: name.into(),
            generic_parameters: vec![],
            parameters: vec![],
            span,
            body: core::Block {
                statements: vec![Statement::Expr {
                    expression,
                    terminated: false,
                }],
            },
        };
        let integer = |value| Expr {
            span,
            kind: ExprKind::Literal(core::Literal::Integer {
                value,
                bits: 64,
                signed: true,
            }),
        };
        let program = core::Program {
            functions: vec![
                function(0, "__ril_fn_1", integer(1)),
                function(1, "second", integer(2)),
                function(
                    2,
                    "main",
                    Expr {
                        span,
                        kind: ExprKind::Call {
                            callback_entry: false,
                            callee: Box::new(Expr {
                                span,
                                kind: ExprKind::Name("__ril_fn_1".into()),
                            }),
                            arguments: vec![],
                        },
                    },
                ),
            ],
            ..Default::default()
        };
        let native = ril_codegen::lower::lower_native(&program).unwrap();
        let target = TargetSpec::native(ril_codegen::target::NATIVE_TARGETS[0]).unwrap();
        let artifact = CraneliftBackend.emit(&native, &target).unwrap();
        let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
        use object::ObjectSection;
        assert!(
            object
                .sections()
                .flat_map(|section| section.relocations())
                .any(|(_, relocation)| {
                    if let object::RelocationTarget::Symbol(index) = relocation.target() {
                        object.symbol_by_index(index).unwrap().name() == Ok("__ril_fn_0")
                    } else {
                        false
                    }
                }),
            "the Core call must relocate to definition 0, whose source name happens to equal definition 1's native symbol"
        );
    }

    #[test]
    fn emits_managed_native_control_flow_for_both_targets() {
        use ril_compiler_core::{
            ids::DefinitionId,
            source::{FileId, Span},
        };
        use ril_ir::core::{self, Expr, ExprKind, Literal, Pattern, Statement};
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let expression = |kind| Expr { kind, span };
        let integer = |value| {
            expression(ExprKind::Literal(Literal::Integer {
                value,
                bits: 64,
                signed: true,
            }))
        };
        let name = |name: &str| expression(ExprKind::Name(name.into()));
        let call = |callee: &str, arguments: Vec<Expr>| {
            expression(ExprKind::Call {
                callback_entry: false,
                callee: Box::new(name(callee)),
                arguments: arguments
                    .into_iter()
                    .map(|value| core::Argument { label: None, value })
                    .collect(),
            })
        };
        let binary = |operator: &str, left: Expr, right: Expr| {
            expression(ExprKind::Binary {
                operator: operator.into(),
                left: Box::new(left),
                right: Box::new(right),
            })
        };
        let function = core::Function {
            role: core::FunctionRole::Ordinary,
            definition: DefinitionId(0),
            name: "main".into(),
            generic_parameters: vec![],
            parameters: vec![],
            span,
            body: core::Block {
                statements: vec![
                    Statement::Bind {
                        pattern: Pattern::Name("sum".into()),
                        value: integer(0),
                        scoped: false,
                    },
                    Statement::Expr {
                        expression: expression(ExprKind::For {
                            charge: Some(core::ChargeEvent::LoopIteration),
                            iterable: Box::new(expression(ExprKind::Array(vec![
                                integer(1),
                                integer(2),
                            ]))),
                            pattern: Pattern::Name("item".into()),
                            body: core::Block {
                                statements: vec![Statement::Assign {
                                    target: name("sum"),
                                    operator: "+=".into(),
                                    value: name("item"),
                                }],
                            },
                        }),
                        terminated: true,
                    },
                    Statement::Expr {
                        expression: call("assert", vec![binary("==", name("sum"), integer(3))]),
                        terminated: true,
                    },
                ],
            },
        };
        let program = core::Program {
            functions: vec![function],
            globals: core::Block::default(),
            ..Default::default()
        };
        let module = ril_codegen::lower::lower_native(&program).unwrap();
        for triple in ril_codegen::target::NATIVE_TARGETS {
            let artifact = CraneliftBackend
                .emit(&module, &TargetSpec::native(triple).unwrap())
                .unwrap();
            let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok("main") && symbol.is_definition())
            );
            assert!(object.symbols().any(|symbol|symbol.name()==Ok("ril_rt_cell_set")&&!symbol.is_definition()));
        }
    }

    #[test]
    fn emits_post_resume_core_continuations_for_both_targets() {
        // This checks the backend's Core contract. Source post-resume checking
        // remains gated until its answer and per-exit authority proofs exist.
        use ril_compiler_core::{
            ids::DefinitionId,
            source::{FileId, Span},
        };
        use ril_ir::core::{self, Expr, ExprKind, Pattern, Statement};
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let expression = |kind| Expr { kind, span };
        let integer = |value| {
            expression(ExprKind::Literal(core::Literal::Integer {
                value,
                bits: 64,
                signed: true,
            }))
        };
        let arm = expression(ExprKind::Block(core::Block {
            statements: vec![
                Statement::Bind {
                    pattern: Pattern::Name("answer".into()),
                    value: expression(ExprKind::Control {
                        operation: core::ControlOperation::Resume,
                        value: Some(Box::new(integer(1))),
                    }),
                    scoped: false,
                },
                Statement::Expr {
                    expression: expression(ExprKind::Binary {
                        operator: "+".into(),
                        left: Box::new(expression(ExprKind::Name("answer".into()))),
                        right: Box::new(integer(2)),
                    }),
                    terminated: false,
                },
            ],
        }));
        let program = core::Program {
            functions: vec![core::Function {
                role: core::FunctionRole::Ordinary,
                definition: DefinitionId(0),
                name: "main".into(),
                generic_parameters: vec![],
                parameters: vec![],
                span,
                body: core::Block {
                    statements: vec![
                        Statement::Handle {
                            definition: 0,
                            arms: vec![core::HandlerArm {
                                operation: 1,
                                parameters: vec![],
                                body: arm,
                            }],
                        },
                        Statement::Expr {
                            expression: expression(ExprKind::Perform {
                                operation: 1,
                                arguments: vec![],
                            }),
                            terminated: false,
                        },
                    ],
                },
            }],
            operations: vec![core::Operation {
                identity: 1,
                name: "Read::get".into(),
                span,
            }],
            ..Default::default()
        };
        let module = ril_codegen::lower::lower_native(&program).unwrap();
        for triple in ril_codegen::target::NATIVE_TARGETS {
            let artifact = CraneliftBackend
                .emit(&module, &TargetSpec::native(triple).unwrap())
                .unwrap();
            let object = object::File::parse(artifact.bytes.as_slice()).unwrap();
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok("ril_rt_cps_resume_then")
                        && !symbol.is_definition())
            );
        }
    }
}
