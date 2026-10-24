//! External declarations become explicit native CPS adapters, with bound host
//! descriptors installed before constant reads and ordinary global initializers.
use super::*;
use ril_ir::foreign as ir;
use ril_runtime_api::foreign as api;

pub(crate) struct Prepared {
    pub module: native::Module,
    pub descriptors: Option<String>,
    pub constants: Vec<(String, u32)>,
}

pub(crate) fn prepare(input: &native::Module) -> Result<Prepared, BackendError> {
    let mut bindings = HashMap::new();
    for binding in &input.foreign_bindings {
        if bindings
            .insert(binding.declaration.as_str(), binding)
            .is_some()
        {
            return Err(BackendError::InvalidIr(
                "duplicate external provider binding".into(),
            ));
        }
    }
    let mut descriptors = Vec::new();
    let mut indices = HashMap::new();
    for function in &input.external_functions {
        let index = descriptors.len();
        if indices
            .insert(function.internal_name.as_str(), index)
            .is_some()
        {
            return Err(BackendError::InvalidIr(
                "duplicate external declaration".into(),
            ));
        }
        descriptors.push(descriptor(
            &bindings,
            &function.declaration,
            &function.signature,
            &function.static_arguments,
            api::EntryKind::Function,
        )?);
    }
    let mut constants = Vec::new();
    for constant in &input.external_constants {
        let index = u32::try_from(descriptors.len())
            .map_err(|_| BackendError::InvalidIr("too many external bindings".into()))?;
        if indices
            .insert(constant.internal_name.as_str(), index as usize)
            .is_some()
        {
            return Err(BackendError::InvalidIr(
                "duplicate external declaration".into(),
            ));
        }
        if !constant.signature.parameters.is_empty() || !constant.signature.callbacks.is_empty() {
            return Err(BackendError::InvalidIr(
                "external constant has call parameters".into(),
            ));
        }
        descriptors.push(descriptor(
            &bindings,
            &constant.declaration,
            &constant.signature,
            &constant.static_arguments,
            api::EntryKind::Constant,
        )?);
        constants.push((constant.internal_name.clone(), index));
    }
    let mut module = input.clone();
    let metering = !input.budget_entries.is_empty();
    let mut metered_adapters = Vec::new();
    for function in &mut module.functions {
        if let Body::Foreign(external) = &function.body {
            let index = *indices
                .get(external.internal_name.as_str())
                .ok_or_else(|| {
                    BackendError::InvalidIr("foreign adapter has no descriptor".into())
                })?;
            let adapter = adapter(external, index)?;
            function.body = Body::Cps(std::sync::Arc::new(
                ril_codegen::cps::lower(&adapter).map_err(BackendError::NotImplemented)?,
            ));
            if metering {
                // Defaults are ordinary Ril computation and may establish a
                // local budget or retain an arm used by protected code. The
                // synthetic adapter adds no language FunctionEntry event;
                // foreign.invoke itself still rejects an active allowance.
                let mut graph = ril_codegen::cps::lower_metered(&adapter)
                    .map_err(BackendError::NotImplemented)?;
                let name = native::budget_entry_name(&adapter.name);
                graph.name = name.clone();
                module.budget_entries.insert(adapter.name.clone(), name);
                metered_adapters.push(native::Function {
                    symbol: format!("{}__budget", function.symbol),
                    body: Body::Cps(std::sync::Arc::new(graph)),
                });
            }
        }
    }
    module.functions.extend(metered_adapters);
    let descriptors = if descriptors.is_empty() {
        None
    } else {
        Some(serde_json::to_string(&descriptors).map_err(codegen)?)
    };
    Ok(Prepared {
        module,
        descriptors,
        constants,
    })
}

fn descriptor(
    bindings: &HashMap<&str, &ir::Binding>,
    declaration: &str,
    signature: &ir::Signature,
    static_arguments: &[ir::StaticArgument],
    kind: api::EntryKind,
) -> Result<api::BoundCall, BackendError> {
    let binding = bindings.get(declaration).ok_or_else(|| {
        BackendError::InvalidIr(format!(
            "external declaration has no explicit provider binding: {declaration}"
        ))
    })?;
    for callback in &signature.callbacks {
        if !callback.path.is_empty() {
            return Err(unsupported(
                "nested external callback paths require a provider protocol extension",
            ));
        }
        if callback.argument as usize >= signature.parameters.len() {
            return Err(BackendError::InvalidIr(
                "external callback parameter index is out of range".into(),
            ));
        }
    }
    if signature
        .arena
        .iter()
        .any(|ty| matches!(ty, ir::TypeNode::Resource { .. }))
    {
        return Err(unsupported(
            "external resource contracts require a persistent provider realm",
        ));
    }
    Ok(api::BoundCall {
        declaration: declaration.into(),
        export: binding.export.clone(),
        kind,
        static_arguments: static_arguments.iter().map(static_argument).collect(),
        provider: api::ProviderConfig {
            id: binding.provider.id.clone(),
            program: binding.provider.program.clone(),
            args: binding.provider.args.clone(),
            max_frame_bytes: binding.provider.max_frame_bytes,
        },
        signature: api::Signature {
            arena: signature.arena.iter().map(type_node).collect(),
            parameters: signature.parameters.clone(),
            result: signature.result,
            callbacks: signature
                .callbacks
                .iter()
                .map(|callback| api::CallbackSlot {
                    argument: callback.argument,
                    path: vec![],
                    mutable: callback.mutable,
                    parameters: callback.parameters.clone(),
                    result: callback.result,
                })
                .collect(),
        },
    })
}

fn static_argument(argument: &ir::StaticArgument) -> api::StaticArgument {
    api::StaticArgument {
        name: argument.name.clone(),
        value: match &argument.value {
            ir::StaticArgumentValue::Type { identity, schema } => api::StaticArgumentValue::Type {
                identity: identity.clone(),
                schema: *schema,
            },
            ir::StaticArgumentValue::Value { identity, value } => api::StaticArgumentValue::Value {
                identity: identity.clone(),
                value: match value {
                    ir::StaticValue::Unit => api::StaticValue::Unit,
                    ir::StaticValue::Bool(value) => api::StaticValue::Bool(*value),
                    ir::StaticValue::Integer {
                        decimal,
                        bits,
                        signed,
                    } => api::StaticValue::Integer {
                        decimal: decimal.clone(),
                        bits: *bits,
                        signed: *signed,
                    },
                    ir::StaticValue::BigInteger(value) => {
                        api::StaticValue::BigInteger(value.clone())
                    }
                    ir::StaticValue::Float { bits, raw } => api::StaticValue::Float {
                        bits: *bits,
                        raw: *raw,
                    },
                    ir::StaticValue::String(value) => api::StaticValue::String(value.clone()),
                    ir::StaticValue::Bytes(value) => api::StaticValue::Bytes(value.clone()),
                },
            },
            ir::StaticArgumentValue::Effects { identities } => api::StaticArgumentValue::Effects {
                identities: identities.clone(),
            },
            ir::StaticArgumentValue::Capabilities { identities } => {
                api::StaticArgumentValue::Capabilities {
                    identities: identities.clone(),
                }
            }
        },
    }
}

fn type_node(node: &ir::TypeNode) -> api::TypeNode {
    match node {
        ir::TypeNode::Unit => api::TypeNode::Unit,
        ir::TypeNode::Bool => api::TypeNode::Bool,
        ir::TypeNode::Integer { bits, signed } => api::TypeNode::Integer {
            bits: *bits,
            signed: *signed,
        },
        ir::TypeNode::BigInteger => api::TypeNode::BigInteger,
        ir::TypeNode::Float { bits } => api::TypeNode::Float { bits: *bits },
        ir::TypeNode::String => api::TypeNode::String,
        ir::TypeNode::Bytes => api::TypeNode::Bytes,
        ir::TypeNode::Array { element, length } => api::TypeNode::Array {
            element: *element,
            length: *length,
        },
        ir::TypeNode::Map { key, value } => api::TypeNode::Map {
            key: *key,
            value: *value,
        },
        ir::TypeNode::Set(ty) => api::TypeNode::Set(*ty),
        ir::TypeNode::Range(ty) => api::TypeNode::Range(*ty),
        ir::TypeNode::Immutable(ty) => api::TypeNode::Immutable(*ty),
        ir::TypeNode::Tuple(types) => api::TypeNode::Tuple(types.clone()),
        ir::TypeNode::Record(fields) => api::TypeNode::Record(fields.clone()),
        ir::TypeNode::Variant(cases) => api::TypeNode::Variant(
            cases
                .iter()
                .map(|case| api::VariantShape {
                    wire_tag: case.wire_tag.clone(),
                    runtime_tag: case.runtime_tag.clone(),
                    fields: case.fields.clone(),
                })
                .collect(),
        ),
        ir::TypeNode::Nominal {
            wire_tag,
            runtime_tag,
            payload,
        } => api::TypeNode::Nominal {
            wire_tag: wire_tag.clone(),
            runtime_tag: runtime_tag.clone(),
            payload: *payload,
        },
        ir::TypeNode::Opaque {
            wire_tag,
            runtime_tag,
        } => api::TypeNode::Opaque {
            wire_tag: wire_tag.clone(),
            runtime_tag: runtime_tag.clone(),
        },
        ir::TypeNode::OpaqueData {
            wire_tag,
            runtime_tag,
            representation,
        } => api::TypeNode::OpaqueData {
            wire_tag: wire_tag.clone(),
            runtime_tag: runtime_tag.clone(),
            representation: *representation,
        },
        ir::TypeNode::Callback => api::TypeNode::Callback,
        ir::TypeNode::Resource { contract } => api::TypeNode::Resource {
            contract: contract.clone(),
        },
    }
}

fn adapter(
    external: &ir::ExternalFunction,
    binding: usize,
) -> Result<core::Function, BackendError> {
    if external.parameters.len() != external.signature.parameters.len() {
        return Err(BackendError::InvalidIr(
            "external declaration parameter/schema arity mismatch".into(),
        ));
    }
    let span = external.span;
    let mut values = Vec::new();
    for parameter in &external.parameters {
        let Pattern::Name(name) = &parameter.pattern else {
            return Err(unsupported(
                "external destructuring parameters require a whole-argument identity binding",
            ));
        };
        values.push(Expr {
            span,
            kind: ExprKind::Name(name.clone()),
        });
    }
    Ok(core::Function {
        role: core::FunctionRole::Synthetic,
        definition: external.definition,
        name: external.internal_name.clone(),
        generic_parameters: vec![],
        parameters: external.parameters.clone(),
        span,
        body: core::Block {
            statements: vec![Statement::Expr {
                terminated: false,
                expression: Expr {
                    span,
                    kind: ExprKind::Call {
                        callback_entry: false,
                        callee: Box::new(Expr {
                            span,
                            kind: ExprKind::Name("\0ril.foreign.invoke".into()),
                        }),
                        arguments: vec![
                            core::Argument {
                                label: None,
                                value: Expr {
                                    span,
                                    kind: ExprKind::Literal(Literal::Integer {
                                        value: binding as i128,
                                        bits: 64,
                                        signed: true,
                                    }),
                                },
                            },
                            core::Argument {
                                label: None,
                                value: Expr {
                                    span,
                                    kind: ExprKind::Tuple(values),
                                },
                            },
                        ],
                    },
                },
            }],
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CraneliftBackend;
    use object::{Object, ObjectSymbol};
    use ril_codegen::{
        NativeBackend,
        target::{NATIVE_TARGETS, TargetSpec},
    };
    use ril_compiler_core::{
        ids::DefinitionId,
        source::{FileId, Span},
    };

    fn module() -> native::Module {
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let integer = |value| Expr {
            span,
            kind: ExprKind::Literal(Literal::Integer {
                value,
                bits: 64,
                signed: true,
            }),
        };
        let signature = ir::Signature {
            arena: vec![ir::TypeNode::Integer {
                bits: 64,
                signed: true,
            }],
            parameters: vec![0],
            result: 0,
            callbacks: vec![],
        };
        let external = ir::ExternalFunction {
            definition: DefinitionId(1),
            internal_name: "imported_value".into(),
            declaration: "foreign::value".into(),
            span,
            parameters: vec![core::Parameter {
                pattern: Pattern::Name("number".into()),
                default: Some(integer(5)),
            }],
            signature: signature.clone(),
            static_arguments: vec![],
        };
        let constant = ir::ExternalConstant {
            internal_name: "IMPORTED_CONSTANT".into(),
            declaration: "foreign::CONSTANT".into(),
            span,
            static_arguments: vec![],
            signature: ir::Signature {
                parameters: vec![],
                ..signature
            },
        };
        let main = core::Function {
            role: core::FunctionRole::Ordinary,
            definition: DefinitionId(0),
            name: "main".into(),
            generic_parameters: vec![],
            parameters: vec![],
            span,
            body: core::Block {
                statements: vec![Statement::Expr {
                    terminated: false,
                    expression: Expr {
                        span,
                        kind: ExprKind::Call {
                            callback_entry: false,
                            callee: Box::new(Expr {
                                span,
                                kind: ExprKind::Name("imported_value".into()),
                            }),
                            arguments: vec![],
                        },
                    },
                }],
            },
        };
        let program = core::Program {
            functions: vec![main],
            external_functions: vec![external],
            external_constants: vec![constant],
            ..core::Program::default()
        };
        let mut module = ril_codegen::lower::lower_native(&program).unwrap();
        let provider = ir::ProviderConfig {
            id: "test".into(),
            program: std::env::current_exe().unwrap(),
            args: vec![],
            max_frame_bytes: api::DEFAULT_MAX_FRAME_BYTES,
        };
        module.foreign_bindings = ["foreign::value", "foreign::CONSTANT"]
            .into_iter()
            .map(|declaration| ir::Binding {
                declaration: declaration.into(),
                export: declaration.into(),
                provider: provider.clone(),
            })
            .collect();
        module
    }

    #[test]
    fn foreign_declarations_emit_real_native_adapters_and_install_before_constant_reads() {
        let module = module();
        let prepared = prepare(&module).unwrap();
        let descriptors: Vec<api::BoundCall> =
            serde_json::from_str(prepared.descriptors.as_ref().unwrap()).unwrap();
        assert_eq!(descriptors.len(), 2);
        assert_eq!(descriptors[0].kind, api::EntryKind::Function);
        assert_eq!(descriptors[1].kind, api::EntryKind::Constant);
        assert_eq!(prepared.constants, vec![("IMPORTED_CONSTANT".into(), 1)]);
        for triple in NATIVE_TARGETS {
            let object = CraneliftBackend
                .emit(&module, &TargetSpec::native(triple).unwrap())
                .unwrap();
            let object = object::File::parse(object.bytes.as_slice()).unwrap();
            for import in [
                "ril_rt_foreign_install",
                "ril_rt_cps_call",
                "ril_rt_cps_run",
                "ril_rt_global_set",
            ] {
                assert!(
                    object
                        .symbols()
                        .any(|symbol| symbol.name() == Ok(import) && !symbol.is_definition()),
                    "{triple}: {import}"
                );
            }
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok("__ril_foreign_1") && symbol.is_definition()),
                "{triple}"
            );
        }
    }

    #[test]
    fn missing_provider_bindings_fail_before_object_emission() {
        let mut module = module();
        module.foreign_bindings.clear();
        assert!(
            matches!(prepare(&module), Err(BackendError::InvalidIr(message)) if message.contains("explicit provider binding"))
        );
    }

    #[test]
    fn phantom_static_arguments_keep_distinct_instances_of_one_export() {
        let mut module = module();
        let argument = |identity: &str| ir::StaticArgument {
            name: "T".into(),
            value: ir::StaticArgumentValue::Type {
                identity: identity.into(),
                schema: None,
            },
        };
        module.external_functions[0].static_arguments = vec![argument("int")];
        let mut second = module.external_functions[0].clone();
        second.definition = DefinitionId(2);
        second.internal_name = "imported_other_instance".into();
        second.static_arguments = vec![argument("str")];
        module.external_functions.push(second.clone());
        module.functions.push(native::Function {
            symbol: "__ril_foreign_2".into(),
            body: Body::Foreign(second),
        });
        let prepared = prepare(&module).unwrap();
        let descriptors: Vec<api::BoundCall> =
            serde_json::from_str(prepared.descriptors.as_ref().unwrap()).unwrap();
        assert_eq!(descriptors.len(), 3);
        assert_eq!(descriptors[0].declaration, descriptors[1].declaration);
        assert_eq!(descriptors[0].export, descriptors[1].export);
        assert_ne!(
            descriptors[0].static_arguments,
            descriptors[1].static_arguments
        );
        for triple in NATIVE_TARGETS {
            let object = CraneliftBackend
                .emit(&module, &TargetSpec::native(triple).unwrap())
                .unwrap();
            let object = object::File::parse(object.bytes.as_slice()).unwrap();
            assert!(
                object
                    .symbols()
                    .any(|symbol| symbol.name() == Ok("__ril_foreign_2") && symbol.is_definition())
            );
        }
    }

    #[test]
    fn retained_default_sites_cannot_borrow_another_owners_or_incomplete_proof() {
        use ril_compiler_core::ids::{CallableOwner, ClosureSiteId, HandlerSiteId};
        let mut module = module();
        let external = &mut module.external_functions[0];
        let span = external.span;
        external.signature.arena.push(ir::TypeNode::Callback);
        external.signature.parameters = vec![1];
        external.signature.callbacks = vec![ir::CallbackSlot {
            argument: 0,
            path: vec![],
            mutable: false,
            parameters: vec![],
            result: 0,
        }];
        external.parameters[0].default = Some(Expr {
            span,
            kind: ExprKind::Block(core::Block {
                statements: vec![
                    Statement::Handle {
                        definition: 100,
                        arms: vec![core::HandlerArm {
                            operation: 1,
                            parameters: vec![],
                            body: Expr {
                                span,
                                kind: ExprKind::Control {
                                    operation: core::ControlOperation::Resume,
                                    value: Some(Box::new(Expr {
                                        span,
                                        kind: ExprKind::Literal(Literal::Integer {
                                            value: 7,
                                            bits: 64,
                                            signed: true,
                                        }),
                                    })),
                                },
                            },
                        }],
                    },
                    Statement::Expr {
                        terminated: false,
                        expression: Expr {
                            span,
                            kind: ExprKind::Lambda {
                                parameters: vec![],
                                body: Box::new(Expr {
                                    span,
                                    kind: ExprKind::Perform {
                                        operation: 1,
                                        arguments: vec![],
                                    },
                                }),
                            },
                        },
                    },
                ],
            }),
        });
        for function in &mut module.functions {
            if matches!(function.body, Body::Foreign(_)) {
                function.body = Body::Foreign(external.clone());
            }
        }
        module.closure_sites.push(ril_ir::metadata::ClosureSite {
            id: ClosureSiteId(1),
            owner: CallableOwner::Function(external.definition),
            source: ril_compiler_core::ids::ExprId(0),
            span,
        });
        module
            .retained_handlers
            .push(ril_ir::metadata::RetainedHandler {
                callable: Some(CallableOwner::Lambda(ClosureSiteId(1))),
                span,
                definitions: Some(vec![HandlerSiteId(100)]),
            });
        let module = prepare(&module).unwrap().module;
        crate::managed::prepare(&module).unwrap();
        for missing in 0..4 {
            let mut incomplete = module.clone();
            let proof = &mut incomplete.retained_handlers[0];
            match missing {
                0 => proof.callable = None,
                1 => proof.callable = Some(CallableOwner::Lambda(ClosureSiteId(2))),
                2 => proof.definitions = None,
                _ => {
                    let mut partial = proof.clone();
                    partial.definitions = None;
                    incomplete.retained_handlers.push(partial);
                }
            }
            assert!(matches!(
                crate::managed::prepare(&incomplete),
                Err(BackendError::NotImplemented(_))
            ));
        }
    }
}
