//! Machine-code entry and continuation blocks for the selective CPS graph.
use super::*;
use ril_ir::cps::{self, BlockId, Input, Terminator};

pub(super) fn block_symbol(function: &cps::Function, block: BlockId) -> String {
    let mut identity = 0xcbf29ce484222325u64;
    for byte in function.name.bytes() {
        identity ^= u64::from(byte);
        identity = identity.wrapping_mul(0x100000001b3);
    }
    format!(
        "__ril_cps_{}_{identity:016x}_{}",
        function.definition.0, block.0
    )
}

pub(crate) fn emit_cps(
    module: &mut ObjectModule,
    builder: &mut FunctionBuilder<'_>,
    function: &cps::Function,
    block: BlockId,
    program: &mut ProgramInfo,
) -> Result<(), BackendError> {
    let start = builder.create_block();
    builder.append_block_params_for_function_params(start);
    builder.switch_to_block(start);
    let supplied_environment = builder.block_params(start)[0];
    let arguments = builder.block_params(start)[1];
    let failure = builder.create_block();
    let mut emitter = Emitter {
        module,
        builder,
        program,
        owner: function.name.clone(),
        locals: HashMap::new(),
        pending: HashMap::new(),
        slot: 0,
        failure,
        reachable: true,
        loops: vec![],
        scopes: vec![],
        global_init: function.name == native::GLOBAL_INITIALIZER
            || function.name == native::budget_entry_name(native::GLOBAL_INITIALIZER),
    };
    emitter.raw("ril_rt_enter", &[])?;
    emitter.root(supplied_environment)?;
    emitter.root(arguments)?;
    let node = &function.blocks[block.0 as usize];
    let environment = match node.input {
        Input::Function => emitter.handle("ril_rt_record", &[])?,
        Input::HandlerBody | Input::HandlerArm(_) => {
            emitter.handle("ril_rt_record_copy", &[supplied_environment])?
        }
        Input::Continue(_) => supplied_environment,
    };
    emitter.root(environment)?;
    let activation = if matches!(node.input, Input::Continue(_)) {
        get_environment(&mut emitter, environment, cps::ACTIVATION)?
    } else {
        let activation = emitter.handle("ril_rt_cps_activation_new", &[])?;
        set_environment(&mut emitter, environment, cps::ACTIVATION, activation)?;
        activation
    };
    emitter.raw("ril_rt_cps_activation_attach", &[activation])?;
    match &node.input {
        Input::Function => {
            let captures = emitter
                .program
                .functions
                .get(&function.name)
                .map(|info| info.captures.clone())
                .unwrap_or_default();
            for capture in captures {
                let cell = get_environment(&mut emitter, supplied_environment, &capture)?;
                set_environment(&mut emitter, environment, &capture, cell)?;
                emitter.locals.insert(capture, cell);
            }
            let supplied = Pattern::Name(cps::ARGUMENTS.into());
            emitter.bind(&supplied, arguments)?;
            persist_bindings(&mut emitter, environment, &supplied)?;
            // Missing defaults and named holes change the supplied arity. The
            // hidden continuation always follows the actual argument tuple.
            let length = emitter
                .raw("ril_rt_len", &[arguments])?
                .expect("argument count");
            let last = emitter.builder.ins().iadd_imm_s(length, -1);
            let high = emitter.i64(0);
            let bits = emitter.i32(64);
            let signed = emitter.i32(1);
            let last = emitter.handle("ril_rt_int", &[last, high, bits, signed])?;
            let safe = emitter.i32(0);
            let continuation = emitter.handle("ril_rt_index", &[arguments, last, safe])?;
            set_environment(&mut emitter, environment, cps::CONTINUATION, continuation)?;
            set_environment(
                &mut emitter,
                environment,
                cps::FUNCTION_RETURN,
                continuation,
            )?;
        }
        Input::HandlerBody => {
            let continuation = emitter.index_constant(arguments, 0)?;
            set_environment(&mut emitter, environment, cps::CONTINUATION, continuation)?;
        }
        Input::HandlerArm(parameters) => {
            for (index, parameter) in parameters.iter().enumerate() {
                let value = emitter.index_constant(arguments, index)?;
                emitter.bind(&parameter.pattern, value)?;
                persist_bindings(&mut emitter, environment, &parameter.pattern)?;
            }
            let resumption = emitter.index_constant(arguments, parameters.len())?;
            set_environment(&mut emitter, environment, cps::RESUMPTION, resumption)?;
            let continuation = emitter.index_constant(arguments, parameters.len() + 1)?;
            set_environment(&mut emitter, environment, cps::CONTINUATION, continuation)?;
        }
        Input::Continue(Some(pattern)) => {
            let value = emitter.index_constant(arguments, 0)?;
            emitter.bind(pattern, value)?;
            persist_bindings(&mut emitter, environment, pattern)?;
        }
        Input::Continue(None) => {}
    }
    let mut used = BTreeSet::new();
    free_block(
        &core::Block {
            statements: node.instructions.iter().flat_map(cps_statements).collect(),
        },
        &BTreeSet::new(),
        &mut used,
    );
    for instruction in &node.instructions {
        if let cps::Instruction::Hoist {
            declarations,
            functions,
        } = instruction
        {
            // These cells are created by this instruction. Captures of a
            // later initializer must not be loaded from the previous scope.
            used.retain(|name| !declarations.contains(name));
            for function in functions {
                let key = callable_key(&emitter.owner, function.span);
                let name = emitter.program.named.get(&key).ok_or_else(|| {
                    BackendError::InvalidIr("hoisted named callable was not declared".into())
                })?;
                used.extend(
                    emitter.program.functions[name]
                        .captures
                        .iter()
                        .filter(|name| !declarations.contains(*name))
                        .cloned(),
                );
            }
        }
    }
    match &node.terminator {
        Terminator::ScopeLeave { marker, value, .. } => {
            used.insert(marker.clone());
            free_names(value, &BTreeSet::new(), &mut used);
        }
        Terminator::Budget { limit, action, .. } => {
            free_names(limit, &BTreeSet::new(), &mut used);
            free_names(action, &BTreeSet::new(), &mut used);
        }
        Terminator::Return { value, .. } | Terminator::Resume { value, .. } => {
            free_names(value, &BTreeSet::new(), &mut used)
        }
        Terminator::Branch { condition, .. } => free_names(condition, &BTreeSet::new(), &mut used),
        Terminator::Call {
            callee, arguments, ..
        } => {
            free_names(callee, &BTreeSet::new(), &mut used);
            for argument in arguments {
                free_names(&argument.value, &BTreeSet::new(), &mut used)
            }
        }
        Terminator::Perform { arguments, .. } => {
            for argument in arguments {
                free_names(&argument.value, &BTreeSet::new(), &mut used)
            }
        }
        _ => {}
    }
    for local in used.intersection(&function.locals) {
        if !emitter.locals.contains_key(local) {
            let cell = get_environment(&mut emitter, environment, local)?;
            emitter.locals.insert(local.clone(), cell);
        }
    }
    for instruction in &node.instructions {
        match instruction {
            cps::Instruction::Hoist {
                declarations,
                functions,
            } => {
                emitter.hoist_declarations(declarations, functions)?;
                for name in declarations {
                    let cell = emitter.cell(name)?;
                    set_environment(&mut emitter, environment, name, cell)?;
                }
            }
            cps::Instruction::ReuseBindings { names } => {
                for name in names {
                    let cell = get_environment(&mut emitter, environment, name)?;
                    emitter.pending.insert(name.clone(), cell);
                }
            }
            cps::Instruction::Statement(statement) => match statement.as_ref() {
                Statement::Bind {
                    pattern,
                    value,
                    scoped,
                } => {
                    let mut value = emitter.expr(value)?;
                    if *scoped {
                        value =
                            emitter.handle("ril_rt_cps_scope_register", &[activation, value])?;
                    }
                    emitter.bind(pattern, value)?;
                    persist_bindings(&mut emitter, environment, pattern)?;
                }
                Statement::Assign {
                    target,
                    operator,
                    value,
                } => {
                    emitter.assignment(target, operator, value)?;
                }
                Statement::Expr { expression, .. } => {
                    emitter.expr(expression)?;
                }
                _ => return Err(unsupported("unconverted statement in native CPS block")),
            },
            cps::Instruction::ScopeEnter { marker } => {
                let value = emitter.handle("ril_rt_cps_scope_enter", &[activation])?;
                let pattern = Pattern::Name(marker.clone());
                emitter.bind(&pattern, value)?;
                persist_bindings(&mut emitter, environment, &pattern)?;
            }
        }
    }
    terminate(&mut emitter, function, environment, &node.terminator)?;
    emitter.switch(failure);
    let zero = emitter.i64(0);
    let returned = emitter.raw("ril_rt_leave", &[zero])?.expect("leave result");
    emitter.builder.ins().return_(&[returned]);
    emitter.builder.seal_all_blocks();
    Ok(())
}

fn set_environment(
    emitter: &mut Emitter<'_, '_>,
    environment: Value,
    name: &str,
    value: Value,
) -> Result<(), BackendError> {
    let key = emitter.string(name)?;
    emitter.handle("ril_rt_set_field", &[environment, key, value])?;
    Ok(())
}
fn get_environment(
    emitter: &mut Emitter<'_, '_>,
    environment: Value,
    name: &str,
) -> Result<Value, BackendError> {
    let key = emitter.string(name)?;
    emitter.handle("ril_rt_get_field", &[environment, key])
}
fn persist_bindings(
    emitter: &mut Emitter<'_, '_>,
    environment: Value,
    pattern: &Pattern,
) -> Result<(), BackendError> {
    let mut bindings = BTreeSet::new();
    names(pattern, &mut bindings);
    for name in bindings {
        let cell = emitter.cell(&name)?;
        set_environment(emitter, environment, &name, cell)?;
    }
    Ok(())
}
fn native_address(
    emitter: &mut Emitter<'_, '_>,
    function: &cps::Function,
    block: BlockId,
) -> Result<Value, BackendError> {
    let symbol = block_symbol(function, block);
    let target = emitter
        .program
        .symbols
        .get(&symbol)
        .ok_or_else(|| BackendError::InvalidIr(format!("missing CPS block {symbol}")))?
        .id;
    let reference = emitter
        .module
        .declare_func_in_func(target, emitter.builder.func);
    Ok(emitter.builder.ins().func_addr(types::I64, reference))
}
fn continuation(
    emitter: &mut Emitter<'_, '_>,
    function: &cps::Function,
    block: BlockId,
    environment: Value,
) -> Result<Value, BackendError> {
    let address = native_address(emitter, function, block)?;
    emitter.handle("ril_rt_cps_continuation", &[address, environment])
}
fn callable(
    emitter: &mut Emitter<'_, '_>,
    function: &cps::Function,
    block: BlockId,
    environment: Value,
) -> Result<Value, BackendError> {
    let address = native_address(emitter, function, block)?;
    if function.metered {
        // Handler body/arm entries already belong to this metered graph. They
        // have no independent ordinary function entry, but remain executable
        // during active budgets without entering a legacy unmetered callable.
        let entry_event = matches!(
            function.blocks[block.0 as usize].input,
            Input::HandlerArm(_)
        );
        let flags = ril_runtime_api::abi::CALLABLE_NORMAL_IS_CPS
            | (u32::from(entry_event) * ril_runtime_api::abi::CALLABLE_METERED_ENTRY_EVENT);
        let cps = emitter.i32(i64::from(flags));
        return emitter.handle(
            "ril_rt_callable_with_budget",
            &[address, address, environment, cps],
        );
    }
    emitter.handle("ril_rt_cps_callable", &[address, environment])
}
fn return_step(emitter: &mut Emitter<'_, '_>, step: Value) -> Result<(), BackendError> {
    let result = emitter.raw("ril_rt_leave", &[step])?.expect("leave result");
    emitter.builder.ins().return_(&[result]);
    emitter.reachable = false;
    Ok(())
}
fn jump(
    emitter: &mut Emitter<'_, '_>,
    function: &cps::Function,
    block: BlockId,
    environment: Value,
) -> Result<(), BackendError> {
    let target = continuation(emitter, function, block, environment)?;
    let value = emitter.handle("ril_rt_unit", &[])?;
    let step = emitter.handle("ril_rt_cps_return", &[target, value])?;
    return_step(emitter, step)
}
fn terminate(
    emitter: &mut Emitter<'_, '_>,
    function: &cps::Function,
    environment: Value,
    terminator: &Terminator,
) -> Result<(), BackendError> {
    match terminator {
        Terminator::ScopeLeave {
            marker,
            value,
            next,
        } => {
            let marker = emitter.name(marker)?;
            let value = emitter.expr(value)?;
            let next = continuation(emitter, function, *next, environment)?;
            let activation = get_environment(emitter, environment, cps::ACTIVATION)?;
            let step = emitter.handle(
                "ril_rt_cps_scope_leave_then",
                &[activation, marker, value, next],
            )?;
            return_step(emitter, step)
        }
        Terminator::Charge { event, span, next } => {
            emitter.locate(*span)?;
            let event = emitter.i32(*event as i64);
            let next = continuation(emitter, function, *next, environment)?;
            let step = emitter.handle("ril_rt_cps_charge", &[event, next])?;
            return_step(emitter, step)
        }
        Terminator::Budget {
            limit,
            action,
            exhaustion_operation,
            span,
            next,
            ..
        } => {
            let limit = emitter.expr(limit)?;
            let action = emitter.expr(action)?;
            let next = continuation(emitter, function, *next, environment)?;
            let operation = emitter.i64(*exhaustion_operation as i64);
            emitter.locate(*span)?;
            let step = emitter.handle("ril_rt_cps_budget", &[limit, action, next, operation])?;
            return_step(emitter, step)
        }
        Terminator::Jump(block) => jump(emitter, function, *block, environment),
        Terminator::Return {
            value,
            function: return_from_function,
        } => {
            let value = emitter.expr(value)?;
            let key = if *return_from_function {
                cps::FUNCTION_RETURN
            } else {
                cps::CONTINUATION
            };
            let target = get_environment(emitter, environment, key)?;
            let activation = get_environment(emitter, environment, cps::ACTIVATION)?;
            let step =
                emitter.handle("ril_rt_cps_activation_return", &[activation, target, value])?;
            return_step(emitter, step)
        }
        Terminator::Resume { value, next } => {
            let value = emitter.expr(value)?;
            let resumption = get_environment(emitter, environment, cps::RESUMPTION)?;
            let step = if let Some(next) = next {
                let next = continuation(emitter, function, *next, environment)?;
                emitter.handle("ril_rt_cps_resume_then", &[resumption, value, next])?
            } else {
                emitter.handle("ril_rt_cps_resume", &[resumption, value])?
            };
            return_step(emitter, step)
        }
        Terminator::Branch {
            condition,
            then_block,
            else_block,
        } => {
            let value = emitter.expr(condition)?;
            let truth = emitter.boolean_raw(value)?;
            let yes = emitter.builder.create_block();
            let no = emitter.builder.create_block();
            emitter.builder.ins().brif(truth, yes, &[], no, &[]);
            emitter.switch(yes);
            jump(emitter, function, *then_block, environment)?;
            emitter.switch(no);
            jump(emitter, function, *else_block, environment)
        }
        Terminator::Call {
            callback_entry,
            callee,
            arguments,
            next,
            span,
        } => {
            let callee = emitter.expr(callee)?;
            let mut args = vec![];
            for argument in arguments {
                args.push((argument.label.clone(), emitter.expr(&argument.value)?));
            }
            let args = emitter.ordered_arguments(args, *span, None)?;
            let args = emitter.sequence(1, &args)?;
            let next = continuation(emitter, function, *next, environment)?;
            emitter.locate(*span)?;
            let entry = if *callback_entry {
                "ril_rt_cps_callback_call"
            } else {
                "ril_rt_cps_call"
            };
            let step = emitter.handle(entry, &[callee, args, next])?;
            return_step(emitter, step)
        }
        Terminator::Perform {
            operation,
            arguments,
            next,
            span,
        } => {
            let mut args = vec![];
            for argument in arguments {
                args.push(emitter.expr(&argument.value)?);
            }
            let args = emitter.sequence(1, &args)?;
            let next = continuation(emitter, function, *next, environment)?;
            let operation = emitter.i64(*operation as i64);
            emitter.locate(*span)?;
            let step = emitter.handle("ril_rt_cps_perform", &[operation, args, next])?;
            return_step(emitter, step)
        }
        Terminator::Handle {
            definition,
            body,
            arms,
            next,
        } => {
            let body = callable(emitter, function, *body, environment)?;
            let table = emitter.handle("ril_rt_cps_handlers", &[])?;
            for arm in arms {
                // A persistent arm captures lexical cells only. Old scope
                // markers, argument tuples and continuation temporaries are
                // never part of its reusable definition environment.
                let mut bound = BTreeSet::new();
                for parameter in &arm.source.parameters {
                    names(&parameter.pattern, &mut bound);
                }
                let mut used = BTreeSet::new();
                free_names(&arm.source.body, &bound, &mut used);
                let captures = emitter.handle("ril_rt_record", &[])?;
                let source_captures = emitter
                    .program
                    .functions
                    .get(&function.name)
                    .map(|info| info.captures.clone())
                    .unwrap_or_default();
                for name in used.iter().filter(|name| {
                    function.locals.contains(*name) || source_captures.contains(*name)
                }) {
                    let key = emitter.string(name)?;
                    let cell = emitter.handle("ril_rt_get_field", &[environment, key])?;
                    emitter.handle("ril_rt_set_field", &[captures, key, cell])?;
                }
                let callable = if !function.metered
                    && let Some(symbol) = emitter
                        .program
                        .handler_budget_entries
                        .get(&(function.name.clone(), *definition, arm.operation))
                        .cloned()
                {
                    let address = native_address(emitter, function, arm.entry)?;
                    let metered = emitter
                        .program
                        .symbols
                        .get(&symbol)
                        .ok_or_else(|| {
                            BackendError::InvalidIr("metered handler entry is missing".into())
                        })?
                        .id;
                    let reference = emitter
                        .module
                        .declare_func_in_func(metered, emitter.builder.func);
                    let metered = emitter.builder.ins().func_addr(types::I64, reference);
                    let flags = emitter.i32(i64::from(
                        ril_runtime_api::abi::CALLABLE_NORMAL_IS_CPS
                            | ril_runtime_api::abi::CALLABLE_METERED_ENTRY_EVENT,
                    ));
                    emitter.handle(
                        "ril_rt_callable_with_budget",
                        &[address, metered, captures, flags],
                    )?
                } else {
                    if !function.metered
                        && emitter
                            .program
                            .functions
                            .get(&function.name)
                            .is_some_and(|info| info.budget.is_some())
                    {
                        return Err(unsupported(
                            "ordinary handler has no matching certified metered entry",
                        ));
                    }
                    callable(emitter, function, arm.entry, captures)?
                };
                let operation = emitter.i64(arm.operation as i64);
                emitter.handle("ril_rt_cps_handler_add", &[table, operation, callable])?;
            }
            let next = continuation(emitter, function, *next, environment)?;
            let definition = emitter.i64(*definition as i64);
            let step = emitter.handle("ril_rt_cps_handle", &[body, table, next, definition])?;
            return_step(emitter, step)
        }
    }
}
