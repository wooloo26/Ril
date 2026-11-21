use std::collections::{BTreeMap, BTreeSet};

use cranelift_codegen::{
    ir::{self, AbiParam, BlockArg, InstBuilder as _, Value, condcodes::IntCC, types},
    isa,
    settings::{self, Configurable as _},
    verify_function,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use ril_base::diag::Diagnostic;

use crate::mir::{self, BlockId, FunctionId, Instruction, Register, Target, Terminator};

type Result<T> = std::result::Result<T, Diagnostic>;

fn diagnostic(error: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::unsupported(format!("native code generation: {error}"))
}

fn target(pic: bool) -> Result<isa::OwnedTargetIsa> {
    let mut flags = settings::builder();
    flags
        .set("is_pic", if pic { "true" } else { "false" })
        .map_err(diagnostic)?;
    flags
        .set(
            "enable_verifier",
            if cfg!(debug_assertions) {
                "true"
            } else {
                "false"
            },
        )
        .map_err(diagnostic)?;
    let isa = cranelift_native::builder()
        .map_err(diagnostic)?
        .finish(settings::Flags::new(flags))
        .map_err(diagnostic)?;
    if isa.pointer_type() != types::I64 {
        return Err(diagnostic(
            "the Ril native ABI requires a 64-bit host target",
        ));
    }
    Ok(isa)
}

pub fn object(program: &mir::Program) -> Result<Vec<u8>> {
    let object = ObjectBuilder::new(target(true)?, "ril.program", default_libcall_names())
        .map_err(diagnostic)?;
    let mut module = ObjectModule::new(object);
    MirToClifTranslator::compile(&mut module, program)?;
    module.finish().emit().map_err(diagnostic)
}

pub fn emit_clif(program: &mir::Program) -> Result<String> {
    let object = ObjectBuilder::new(target(true)?, "ril.program", default_libcall_names())
        .map_err(diagnostic)?;
    let mut module = ObjectModule::new(object);
    let (_, text) = MirToClifTranslator::compile(&mut module, program)?;
    Ok(text)
}

#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "execute the verified native entry while its JIT module owns the code"
)]
pub fn jit(program: &mir::Program) -> Result<i32> {
    use cranelift_jit::{JITBuilder, JITModule};

    // JITModule also searches the process's dynamic symbols for imports. A
    // Ril foreign declaration alone cannot establish the C ABI of those symbols.
    for function in &program.functions {
        for block in &function.blocks {
            if let Some(Terminator::Invoke {
                target: Target::Foreign(symbol),
                ..
            }) = &block.terminator
            {
                return Err(diagnostic(format!(
                    "unregistered foreign JIT function {symbol}"
                )));
            }
        }
    }
    let mut builder = JITBuilder::with_isa(target(false)?, default_libcall_names());
    builder.symbols(ril_rt_core::symbols());
    let mut module = JITModule::new(builder);
    let (entry, _) = MirToClifTranslator::compile(&mut module, program)?;
    module.finalize_definitions().map_err(diagnostic)?;
    let address = module.get_finalized_function(entry);
    // SAFETY: the translator defines entry with the platform C signature () -> i32.
    // Runtime imports are bound to the linked Ril ABI, and the JIT module
    // remains alive and immutable for the duration of execution.
    let execute = unsafe { std::mem::transmute::<*const u8, extern "C" fn() -> i32>(address) };
    Ok(execute())
}

struct MirToClifTranslator<'a, M> {
    module: &'a mut M,
    functions: Vec<FuncId>,
    imports: BTreeMap<String, FuncId>,
}

impl<M: Module> MirToClifTranslator<'_, M> {
    fn compile(module: &mut M, program: &mir::Program) -> Result<(FuncId, String)> {
        let mut compiler = MirToClifTranslator {
            module,
            functions: Vec::new(),
            imports: BTreeMap::new(),
        };
        for (index, function) in program.functions.iter().enumerate() {
            let signature = compiler.signature(function.arity + 3, Some(types::I64));
            let id = compiler
                .module
                .declare_function(&format!("ril_fn_{index}"), Linkage::Local, &signature)
                .map_err(diagnostic)?;
            compiler.functions.push(id);
        }
        let mut ir = String::new();
        for (index, function) in program.functions.iter().enumerate() {
            let id = compiler.function_id(FunctionId(index))?;
            let code = compiler.translate(id, function)?;
            use std::fmt::Write as _;
            writeln!(ir, "\n; {}\n{code}", function.name).map_err(diagnostic)?;
        }
        let entry = compiler.wrapper(program.entry)?;
        Ok((entry, ir))
    }

    fn function_id(&self, id: FunctionId) -> Result<FuncId> {
        self.functions
            .get(id.0)
            .copied()
            .ok_or_else(|| diagnostic("invalid MIR function ID"))
    }

    fn signature(&self, count: usize, output: Option<ir::Type>) -> ir::Signature {
        let mut signature = self.module.make_signature();
        signature
            .params
            .extend((0..count).map(|_| AbiParam::new(types::I64)));
        signature.returns.extend(output.map(AbiParam::new));
        signature
    }

    fn import(&mut self, name: &str, count: usize, output: Option<ir::Type>) -> Result<FuncId> {
        if let Some(&id) = self.imports.get(name) {
            return Ok(id);
        }
        let signature = self.signature(count, output);
        let id = self
            .module
            .declare_function(name, Linkage::Import, &signature)
            .map_err(diagnostic)?;
        self.imports.insert(name.to_owned(), id);
        Ok(id)
    }

    fn call(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        id: FuncId,
        args: &[Value],
    ) -> Option<Value> {
        let reference = self.module.declare_func_in_func(id, builder.func);
        let call = builder.ins().call(reference, args);
        builder.inst_results(call).first().copied()
    }

    fn native(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        name: &str,
        params: &[Value],
        result: Option<ir::Type>,
    ) -> Result<Option<Value>> {
        let function = self.import(name, params.len(), result)?;
        Ok(self.call(builder, function, params))
    }

    fn handle(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        name: &str,
        args: &[Value],
    ) -> Result<Value> {
        self.native(builder, name, args, Some(types::I64))?
            .ok_or_else(|| diagnostic("runtime function has no return value"))
    }

    fn translate(&mut self, id: FuncId, function: &mir::Function) -> Result<String> {
        let mut context = self.module.make_context();
        context.func.signature = self.signature(function.arity + 3, Some(types::I64));
        let mut scratch = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut scratch);
        let order = reachable(function)?;
        let mut blocks = BTreeMap::new();
        for &source in &order {
            blocks.insert(source, builder.create_block());
        }
        let labels = |id| {
            blocks
                .get(&id)
                .copied()
                .ok_or_else(|| diagnostic("missing MIR successor"))
        };
        let entry = labels(BlockId(0))?;
        builder.append_block_params_for_function_params(entry);
        let abi = builder.block_params(entry).to_vec();
        let [rt, evidence, environment, rest @ ..] = abi.as_slice() else {
            return Err(diagnostic("missing Ril closure ABI parameters"));
        };
        let (rt, incoming_evidence, incoming_environment) = (*rt, *evidence, *environment);
        let mut registers = BTreeMap::new();
        for &id in &order {
            let block = function
                .blocks
                .get(id.0)
                .ok_or_else(|| diagnostic("invalid MIR block"))?;
            for (index, &register) in block.params.iter().enumerate() {
                let value = if id == BlockId(0) {
                    rest.get(index)
                        .copied()
                        .ok_or_else(|| diagnostic("entry argument count"))?
                } else {
                    builder.append_block_param(labels(id)?, types::I64)
                };
                registers.insert(register, value);
            }
        }
        for id in order {
            let source = function
                .blocks
                .get(id.0)
                .ok_or_else(|| diagnostic("invalid MIR block"))?;
            builder.switch_to_block(labels(id)?);
            if id == BlockId(0) {
                let size = number(&mut builder, function.registers)?;
                self.native(&mut builder, "ril_rt_roots_push", &[rt, size], None)?;
            }
            for &parameter in &source.params {
                self.root(&mut builder, rt, parameter, reg(&registers, parameter)?)?;
            }
            for (result, instruction) in &source.instructions {
                let value = match instruction {
                    Instruction::Evidence => incoming_evidence,
                    Instruction::Environment => incoming_environment,
                    _ => self.instruction(&mut builder, rt, instruction)?,
                };
                registers.insert(*result, value);
                self.root(&mut builder, rt, *result, value)?;
            }
            match source
                .terminator
                .as_ref()
                .ok_or_else(|| diagnostic("unterminated reachable MIR block"))?
            {
                Terminator::Jump(target, args) => {
                    let args = args
                        .iter()
                        .map(|r| reg(&registers, *r).map(BlockArg::Value))
                        .collect::<Result<Vec<_>>>()?;
                    builder.ins().jump(labels(*target)?, &args);
                }
                Terminator::Branch { condition, yes, no } => {
                    let value = reg(&registers, *condition)?;
                    let test = builder.ins().icmp_imm_s(IntCC::Equal, value, 2);
                    builder
                        .ins()
                        .brif(test, labels(*yes)?, &[], labels(*no)?, &[]);
                }
                Terminator::Invoke {
                    target,
                    evidence,
                    arguments,
                    normal,
                    unwind,
                    cleanup,
                    keep_result,
                } => {
                    let args = arguments
                        .iter()
                        .map(|arg| reg(&registers, *arg))
                        .collect::<Result<Vec<_>>>()?;
                    if *cleanup {
                        self.native(&mut builder, "ril_rt_cleanup_enter", &[rt], None)?;
                    }
                    let output = match target {
                        Target::Function(id) | Target::FunctionWithEnv { function: id, .. } => {
                            let environment =
                                if let Target::FunctionWithEnv { environment, .. } = target {
                                    reg(&registers, *environment)?
                                } else {
                                    builder.ins().iconst(types::I64, 0)
                                };
                            let args = [rt, reg(&registers, *evidence)?, environment]
                                .into_iter()
                                .chain(args)
                                .collect::<Vec<_>>();
                            self.call(&mut builder, self.function_id(*id)?, &args)
                                .ok_or_else(|| diagnostic("Ril callee has no return handle"))?
                        }
                        Target::Runtime(name) => {
                            let args = std::iter::once(rt).chain(args).collect::<Vec<_>>();
                            self.handle(&mut builder, name, &args)?
                        }
                        Target::Draft(operation) => {
                            let args = std::iter::once(rt).chain(args).collect::<Vec<_>>();
                            self.handle(&mut builder, operation.symbol(), &args)?
                        }
                        Target::Indirect {
                            address,
                            evidence,
                            environment,
                        } => {
                            let address = reg(&registers, *address)?;
                            let args = [
                                rt,
                                reg(&registers, *evidence)?,
                                reg(&registers, *environment)?,
                            ]
                            .into_iter()
                            .chain(args)
                            .collect::<Vec<_>>();
                            let sig = builder
                                .import_signature(self.signature(args.len(), Some(types::I64)));
                            let inst = builder.ins().call_indirect(sig, address, &args);
                            builder.inst_results(inst).first().copied().ok_or_else(|| {
                                diagnostic("indirect call did not produce an output")
                            })?
                        }
                        Target::Foreign(name) => self.handle(&mut builder, name, &args)?,
                    };
                    if *cleanup {
                        self.native(&mut builder, "ril_rt_cleanup_leave", &[rt], None)?;
                    }
                    let flag = builder
                        .ins()
                        .load(types::I8, ir::MemFlagsData::trusted(), rt, 0);
                    let args = if *keep_result {
                        vec![BlockArg::Value(output)]
                    } else {
                        Vec::new()
                    };
                    builder
                        .ins()
                        .brif(flag, labels(*unwind)?, &[], labels(*normal)?, &args);
                }
                Terminator::Return(value) => {
                    let value = reg(&registers, *value)?;
                    self.native(&mut builder, "ril_rt_roots_pop", &[rt], None)?;
                    builder.ins().return_(&[value]);
                }
            }
        }
        builder.seal_all_blocks();
        builder.finalize(self.module.target_config());
        if cfg!(debug_assertions) {
            verify_function(&context.func, self.module.isa()).map_err(diagnostic)?;
        }
        let text = context.func.display().to_string();
        self.module
            .define_function(id, &mut context)
            .map_err(|err| diagnostic(format!("{}: {err}\n{text}", function.name)))?;
        Ok(text)
    }

    fn root(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        rt: Value,
        register: Register,
        value: Value,
    ) -> Result<()> {
        let slot = number(builder, register.0)?;
        self.native(builder, "ril_rt_roots_set", &[rt, slot, value], None)?;
        Ok(())
    }

    fn instruction(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        rt: Value,
        instruction: &Instruction,
    ) -> Result<Value> {
        match instruction {
            Instruction::Evidence | Instruction::Environment => {
                Err(diagnostic("missing native incoming parameter"))
            }
            Instruction::FunctionAddress(id) => {
                let fun = self
                    .module
                    .declare_func_in_func(self.function_id(*id)?, builder.func);
                Ok(builder.ins().func_addr(types::I64, fun))
            }
            Instruction::Handle(value) => Ok(builder
                .ins()
                .iconst(types::I64, i64::from_ne_bytes(value.to_ne_bytes()))),
            Instruction::Float(bits) => {
                let bits = builder
                    .ins()
                    .iconst(types::I64, i64::from_ne_bytes(bits.to_ne_bytes()));
                self.handle(builder, "ril_rt_f64_literal", &[rt, bits])
            }
            Instruction::Integer(data) | Instruction::Text(data) | Instruction::Bytes(data) => {
                let name = match instruction {
                    Instruction::Integer(_) => "ril_rt_int_literal",
                    Instruction::Text(_) => "ril_rt_string",
                    _ => "ril_rt_bytes",
                };
                let id = self
                    .module
                    .declare_anonymous_data(false, false)
                    .map_err(diagnostic)?;
                let mut description = DataDescription::new();
                description.define(if data.is_empty() {
                    Box::new([0])
                } else {
                    data.clone()
                });
                self.module
                    .define_data(id, &description)
                    .map_err(diagnostic)?;
                let global = self.module.declare_data_in_func(id, builder.func);
                let addr = builder.ins().symbol_value(types::I64, global);
                let len = number(builder, data.len())?;
                self.handle(builder, name, &[rt, addr, len])
            }
        }
    }

    fn wrapper(&mut self, entry: FunctionId) -> Result<FuncId> {
        let mut context = self.module.make_context();
        context.func.signature = self.signature(0, Some(types::I32));
        let id = self
            .module
            .declare_function("main", Linkage::Export, &context.func.signature)
            .map_err(diagnostic)?;
        let mut scratch = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut scratch);
        let block = builder.create_block();
        builder.switch_to_block(block);
        let rt = self.handle(&mut builder, "ril_rt_create", &[])?;
        let null = builder.ins().iconst(types::I64, 0);
        let function = self.function_id(entry)?;
        let value = self
            .call(&mut builder, function, &[rt, null, null])
            .ok_or_else(|| diagnostic("entry has no return value"))?;
        let exit = self
            .native(
                &mut builder,
                "ril_rt_finish",
                &[rt, value],
                Some(types::I32),
            )?
            .ok_or_else(|| diagnostic("runtime finish must return status"))?;
        builder.ins().return_(&[exit]);
        builder.seal_block(block);
        builder.finalize(self.module.target_config());
        if cfg!(debug_assertions) {
            verify_function(&context.func, self.module.isa()).map_err(diagnostic)?;
        }
        self.module
            .define_function(id, &mut context)
            .map_err(diagnostic)?;
        Ok(id)
    }
}

fn reg(registers: &BTreeMap<Register, Value>, register: Register) -> Result<Value> {
    registers
        .get(&register)
        .copied()
        .ok_or_else(|| diagnostic(format!("undefined MIR register {}", register.0)))
}

fn number(builder: &mut FunctionBuilder<'_>, value: usize) -> Result<Value> {
    let value = i64::try_from(value).map_err(diagnostic)?;
    Ok(builder.ins().iconst(types::I64, value))
}

fn reachable(function: &mir::Function) -> Result<Vec<BlockId>> {
    let mut order = Vec::new();
    let mut visited = BTreeSet::new();
    let mut todo = vec![(BlockId(0), false)];
    while let Some((id, finished)) = todo.pop() {
        if finished {
            order.push(id);
        } else if visited.insert(id) {
            let block = function
                .blocks
                .get(id.0)
                .ok_or_else(|| diagnostic("MIR jump target is invalid"))?;
            let terminator = block
                .terminator
                .as_ref()
                .ok_or_else(|| diagnostic("MIR block is unterminated"))?;
            todo.push((id, true));
            match terminator {
                Terminator::Return(_) => {}
                Terminator::Jump(target, _) => todo.push((*target, false)),
                Terminator::Branch { yes, no, .. } => todo.extend([(*yes, false), (*no, false)]),
                Terminator::Invoke { normal, unwind, .. } => {
                    todo.extend([(*normal, false), (*unwind, false)]);
                }
            }
        }
    }
    order.reverse();
    Ok(order)
}
