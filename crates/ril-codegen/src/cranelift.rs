use std::collections::{BTreeMap, BTreeSet, HashMap};

use cranelift_codegen::{
    ir::{self, AbiParam, BlockArg, InstBuilder as _, Value, condcodes::IntCC, types},
    isa,
    settings::{self, Configurable as _},
    verify_function,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use ril_source::diag::Diagnostic;

use ril_mir::{
    self, BlockId, ForeignAbi, ForeignImport, FunctionId, Instruction, IntBinOp, IntUnaryOp,
    Register, Target, Terminator,
};

type Result<T> = std::result::Result<T, Diagnostic>;

const RIL_UNIT: i64 = 0;
const RIL_FALSE: i64 = 0b010;
const RIL_TRUE: i64 = 0b110;

/// Cranelift backend optimization level exposed to `ril build` / `ril run`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum OptLevel {
    #[default]
    None,
    Speed,
    SpeedAndSize,
}

impl OptLevel {
    const fn as_cranelift(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Speed => "speed",
            Self::SpeedAndSize => "speed_and_size",
        }
    }
}

fn diagnostic(error: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::unsupported(format!("native code generation: {error}"))
}

fn target(pic: bool, opt_level: OptLevel) -> Result<isa::OwnedTargetIsa> {
    let mut flags = settings::builder();
    flags
        .set("is_pic", if pic { "true" } else { "false" })
        .map_err(diagnostic)?;
    flags
        .set("opt_level", opt_level.as_cranelift())
        .map_err(diagnostic)?;
    flags.set("unwind_info", "true").map_err(diagnostic)?;
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

pub fn object(program: &ril_mir::Program) -> Result<Vec<u8>> {
    object_with_opt(program, OptLevel::None)
}

pub fn object_with_opt(program: &ril_mir::Program, opt_level: OptLevel) -> Result<Vec<u8>> {
    let mut object = ObjectBuilder::new(
        target(true, opt_level)?,
        "ril.program",
        default_libcall_names(),
    )
    .map_err(diagnostic)?;
    object.unwind_info(!cfg!(target_os = "macos"));
    let mut module = ObjectModule::new(object);
    MirToClifTranslator::compile(&mut module, program, None, false)?;
    module.finish().emit().map_err(diagnostic)
}

/// Compile a MIR program into `cgu_count` single-owner object files using deterministic
/// canonical symbol partitioning (`Linkage::Export` in the owning CGU, `Linkage::Import`
/// in all other CGUs). The executable `main` wrapper is emitted in CGU 0.
pub fn objects_with_opt(
    program: &ril_mir::Program,
    cgu_count: usize,
    opt_level: OptLevel,
) -> Result<Vec<Vec<u8>>> {
    let count = cgu_count.max(1).min(program.functions.len().max(1));
    if count <= 1 {
        return Ok(vec![object_with_opt(program, opt_level)?]);
    }
    let owners: Vec<usize> = program
        .functions
        .iter()
        .enumerate()
        .map(|(idx, function)| {
            if FunctionId(idx) == program.entry {
                0
            } else {
                let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
                for &b in function.symbol.as_bytes() {
                    hash ^= u64::from(b);
                    hash = hash.wrapping_mul(0x0100_0000_01b3);
                }
                usize::try_from(hash % (count as u64)).unwrap_or(0)
            }
        })
        .collect();
    let mut objects = Vec::with_capacity(count);
    for cgu in 0..count {
        let name = format!("ril.cgu.{cgu}");
        let mut object =
            ObjectBuilder::new(target(true, opt_level)?, name, default_libcall_names())
                .map_err(diagnostic)?;
        object.unwind_info(!cfg!(target_os = "macos"));
        let mut module = ObjectModule::new(object);
        MirToClifTranslator::compile_cgu(&mut module, program, &owners, cgu)?;
        objects.push(module.finish().emit().map_err(diagnostic)?);
    }
    Ok(objects)
}

pub fn emit_clif(program: &ril_mir::Program) -> Result<String> {
    emit_clif_with_opt(program, OptLevel::None)
}

pub fn emit_clif_with_opt(program: &ril_mir::Program, opt_level: OptLevel) -> Result<String> {
    let object = ObjectBuilder::new(
        target(true, opt_level)?,
        "ril.program",
        default_libcall_names(),
    )
    .map_err(diagnostic)?;
    let mut module = ObjectModule::new(object);
    let (_, text) = MirToClifTranslator::compile(&mut module, program, None, true)?;
    Ok(text)
}

#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "execute the verified native entry while its JIT module owns the code"
)]
pub fn jit(program: &ril_mir::Program) -> Result<i32> {
    // SAFETY: the resolver supplies no host functions. Every reachable import
    // outside the runtime must resolve explicitly before generated code is run.
    unsafe { jit_with_imports_and_opt(program, OptLevel::None, |_| None) }
}

#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "execute the verified native entry while its JIT module owns the code"
)]
pub fn jit_with_opt(program: &ril_mir::Program, opt_level: OptLevel) -> Result<i32> {
    // SAFETY: the resolver supplies no host functions. Every reachable import
    // outside the runtime must resolve explicitly before generated code is run.
    unsafe { jit_with_imports_and_opt(program, opt_level, |_| None) }
}

/// Execute native code with an embedding application's host bindings.
///
/// # Safety
/// Each resolved address must remain executable throughout the call and point
/// to a C-ABI function that takes the runtime context pointer followed by the
/// declared number of Ril value words (`u64`), and returns one Ril value word.
/// A constant uses an accessor that takes only the context pointer. Each
/// binding must honor the value, resource, and effect contracts of its
/// declaration and must never unwind across the C ABI.
#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "verify imports before entering generated native code"
)]
pub unsafe fn jit_with_imports(
    program: &ril_mir::Program,
    resolve: impl FnMut(&ForeignImport) -> Option<*const u8>,
) -> Result<i32> {
    // SAFETY: caller upholds the foreign import ABI contract.
    unsafe { jit_with_imports_and_opt(program, OptLevel::None, resolve) }
}

/// Execute native code at a chosen Cranelift optimization level with host bindings.
///
/// # Safety
/// Same requirements as [`jit_with_imports`].
#[cfg(feature = "native-runtime")]
#[allow(
    unsafe_code,
    reason = "verify imports before entering generated native code"
)]
pub unsafe fn jit_with_imports_and_opt(
    program: &ril_mir::Program,
    opt_level: OptLevel,
    mut resolve: impl FnMut(&ForeignImport) -> Option<*const u8>,
) -> Result<i32> {
    use cranelift_jit::{JITBuilder, JITModule};

    let mut builder = JITBuilder::with_isa(target(false, opt_level)?, default_libcall_names());
    builder.symbols(ril_rt::symbols());
    let mut imports = BTreeSet::new();
    for function in &program.functions {
        for id in reachable(function)? {
            let block = function
                .blocks
                .get(id.0)
                .ok_or_else(|| diagnostic("invalid foreign import block"))?;
            if let Some(Terminator::Invoke {
                target: Target::Foreign(import),
                ..
            }) = &block.terminator
            {
                imports.insert(import.as_ref());
            }
        }
    }
    let mut foreign_names = BTreeMap::new();
    for (ordinal, import) in imports.into_iter().enumerate() {
        let address = resolve(import)
            .filter(|address| !address.is_null())
            .ok_or_else(|| {
                diagnostic(format!(
                    "unregistered foreign JIT import {}",
                    import.declaration
                ))
            })?;
        // Use a private alias outside the runtime's symbol namespace.
        let alias = format!("ril_host_{ordinal}");
        builder.symbol(&alias, address);
        foreign_names.insert(import.clone(), alias);
    }
    let mut module = JITModule::new(builder);
    let (entry, _) =
        MirToClifTranslator::compile(&mut module, program, Some(&foreign_names), false)?;
    module.finalize_definitions().map_err(diagnostic)?;
    let address = module.get_finalized_function(entry);
    // SAFETY: the translator defines entry with the platform C signature () -> i32.
    // Runtime imports are bound to the linked Ril ABI, the caller vouches for
    // each host import, and the JIT module stays alive during execution.
    let execute = unsafe { std::mem::transmute::<*const u8, extern "C" fn() -> i32>(address) };
    Ok(execute())
}

struct MirToClifTranslator<'a, M> {
    module: &'a mut M,
    functions: Vec<FuncId>,
    foreign_names: Option<&'a BTreeMap<ForeignImport, String>>,
    data_pool: HashMap<Box<[u8]>, DataId>,
    emit_text: bool,
}

fn foreign_symbol<'a>(
    names: Option<&'a BTreeMap<ForeignImport, String>>,
    import: &'a ForeignImport,
) -> Result<&'a str> {
    match names {
        Some(names) => names
            .get(import)
            .map(String::as_str)
            .ok_or_else(|| diagnostic("missing checked foreign JIT binding")),
        None => Ok(&import.symbol),
    }
}

/// Maps each GC-managed MIR register and stack slot to its compact offset inside the
/// function's intrusive stack-allocated `RootFrame` (`[prev: 8B | count: 8B | slots: N*8B]`).
struct RootLayout {
    reg_slot: Vec<Option<i32>>,
    stack_slot_base: usize,
    total_slots: usize,
}

impl RootLayout {
    fn build(function: &ril_mir::Function, order: &[BlockId]) -> Self {
        let live_at_safepoint = compute_safepoint_liveness(function, order);
        let mut reg_slot = vec![None; function.registers];
        let mut next = 0usize;
        for (idx, ty) in function.reg_types.iter().enumerate() {
            if ty.is_gc_managed()
                && live_at_safepoint.contains(&Register(idx))
                && let Some(entry) = reg_slot.get_mut(idx)
                && let Ok(offset) = i32::try_from(16 + next * 8)
            {
                *entry = Some(offset);
                next += 1;
            }
        }
        let stack_slot_base = next;
        let total_slots = next + function.stack_slots;
        Self {
            reg_slot,
            stack_slot_base,
            total_slots,
        }
    }

    fn reg_offset(&self, reg: Register) -> Option<i32> {
        self.reg_slot.get(reg.0).copied().flatten()
    }

    fn stack_offset(&self, slot: usize) -> Result<i32> {
        i32::try_from(16 + (self.stack_slot_base + slot) * 8).map_err(diagnostic)
    }
}

fn inst_is_safepoint(inst: &Instruction) -> bool {
    matches!(
        inst,
        Instruction::Float(_)
            | Instruction::Integer(_)
            | Instruction::Text(_)
            | Instruction::Bytes(_)
            | Instruction::IntBinOp { .. }
            | Instruction::IntUnaryOp { .. }
    )
}

/// Backward dataflow liveness analysis finding every register live at or across any safepoint.
fn compute_safepoint_liveness(
    function: &ril_mir::Function,
    order: &[BlockId],
) -> BTreeSet<Register> {
    let mut live_in: HashMap<BlockId, BTreeSet<Register>> = HashMap::new();
    let mut at_safepoint = BTreeSet::new();

    for _ in 0..=order.len().saturating_add(4) {
        let mut changed = false;
        for &bid in order.iter().rev() {
            let Some(block) = function.blocks.get(bid.0) else {
                continue;
            };
            let mut live = BTreeSet::new();
            let mut add_succ = |succ: BlockId| {
                if let Some(succ_live) = live_in.get(&succ) {
                    live.extend(succ_live.iter().copied());
                }
                if let Some(succ_block) = function.blocks.get(succ.0) {
                    for p in &succ_block.params {
                        live.remove(p);
                    }
                }
            };
            match &block.terminator {
                Some(Terminator::Jump(target, args)) => {
                    add_succ(*target);
                    live.extend(args.iter().copied());
                }
                Some(Terminator::Branch { condition, yes, no }) => {
                    add_succ(*yes);
                    add_succ(*no);
                    live.insert(*condition);
                }
                Some(Terminator::Invoke {
                    target,
                    evidence,
                    arguments,
                    normal,
                    unwind,
                    ..
                }) => {
                    add_succ(*normal);
                    add_succ(*unwind);
                    live.insert(*evidence);
                    live.extend(arguments.iter().copied());
                    match target {
                        Target::FunctionWithEnv { environment, .. } => {
                            live.insert(*environment);
                        }
                        Target::Indirect {
                            address,
                            evidence,
                            environment,
                        } => {
                            live.insert(*address);
                            live.insert(*evidence);
                            live.insert(*environment);
                        }
                        Target::Function(_)
                        | Target::Runtime(_)
                        | Target::Draft(_)
                        | Target::Foreign(_) => {}
                    }
                    at_safepoint.extend(live.iter().copied());
                }
                Some(Terminator::Return(reg)) => {
                    live.insert(*reg);
                }
                Some(Terminator::Unreachable) | None => {}
            }

            for (dst, inst) in block.instructions.iter().rev() {
                live.remove(dst);
                inst.visit_reads(|r| {
                    live.insert(r);
                });
                if inst_is_safepoint(inst) {
                    at_safepoint.extend(live.iter().copied());
                }
            }

            let prev = live_in.entry(bid).or_default();
            if *prev != live {
                *prev = live;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    at_safepoint
}

impl<'a, M: Module> MirToClifTranslator<'a, M> {
    fn compile(
        module: &'a mut M,
        program: &ril_mir::Program,
        foreign_names: Option<&'a BTreeMap<ForeignImport, String>>,
        emit_text: bool,
    ) -> Result<(FuncId, String)> {
        let mut compiler = MirToClifTranslator {
            module,
            functions: Vec::new(),
            foreign_names,
            data_pool: HashMap::new(),
            emit_text,
        };
        for function in &program.functions {
            let signature = compiler.signature(function.arity + 3, Some(types::I64));
            let id = compiler
                .module
                .declare_function(&function.symbol, Linkage::Local, &signature)
                .map_err(diagnostic)?;
            compiler.functions.push(id);
        }
        let mut ir = String::new();
        for (index, function) in program.functions.iter().enumerate() {
            let id = compiler.function_id(FunctionId(index))?;
            let code = compiler.translate(id, function)?;
            if emit_text {
                use std::fmt::Write as _;
                writeln!(
                    ir,
                    "\n; {}\n; symbol: {}\n{code}",
                    function.name, function.symbol
                )
                .map_err(diagnostic)?;
            }
        }
        let (entry, wrapper) = compiler.wrapper(program.entry, program.suspend_at_entry)?;
        if emit_text {
            use std::fmt::Write as _;
            writeln!(ir, "\n; executable entry\n{wrapper}").map_err(diagnostic)?;
        }
        Ok((entry, ir))
    }

    fn compile_cgu(
        module: &'a mut M,
        program: &ril_mir::Program,
        owners: &[usize],
        cgu: usize,
    ) -> Result<()> {
        let mut compiler = MirToClifTranslator {
            module,
            functions: Vec::new(),
            foreign_names: None,
            data_pool: HashMap::new(),
            emit_text: false,
        };
        for (index, function) in program.functions.iter().enumerate() {
            let signature = compiler.signature(function.arity + 3, Some(types::I64));
            let linkage = if owners.get(index).copied() == Some(cgu) {
                Linkage::Export
            } else {
                Linkage::Import
            };
            let id = compiler
                .module
                .declare_function(&function.symbol, linkage, &signature)
                .map_err(diagnostic)?;
            compiler.functions.push(id);
        }
        for (index, function) in program.functions.iter().enumerate() {
            if owners.get(index).copied() != Some(cgu) {
                continue;
            }
            let id = compiler.function_id(FunctionId(index))?;
            let _ = compiler.translate(id, function)?;
        }
        if cgu == 0 {
            let _ = compiler.wrapper(program.entry, program.suspend_at_entry)?;
        }
        Ok(())
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
        let signature = self.signature(count, output);
        self.module
            .declare_function(name, Linkage::Import, &signature)
            .map_err(diagnostic)
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

    fn translate(&mut self, id: FuncId, function: &ril_mir::Function) -> Result<String> {
        let mut context = self.module.make_context();
        context.func.signature = self.signature(function.arity + 3, Some(types::I64));
        let mut scratch = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut scratch);
        if let Some(loc_id) = function.source_loc {
            builder.set_srcloc(ir::SourceLoc::new(loc_id));
        }
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
        let stack_slots: Vec<_> = (0..function.stack_slots)
            .map(|_| {
                builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    8,
                    3,
                ))
            })
            .collect();
        let root_layout = RootLayout::build(function, &order);
        let root_frame = if root_layout.total_slots > 0 {
            let bytes = u32::try_from(16 + root_layout.total_slots * 8).map_err(diagnostic)?;
            Some(builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                bytes,
                3,
            )))
        } else {
            None
        };
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
                let zero = builder.ins().iconst(types::I64, RIL_UNIT);
                if let Some(frame) = root_frame {
                    // Prologue invariant: zero-initialize all root slots BEFORE linking
                    // the frame into `rt.gc.top_frame` (offset 8 of Runtime).
                    for idx in 0..root_layout.total_slots {
                        let offset = i32::try_from(16 + idx * 8).map_err(diagnostic)?;
                        builder.ins().stack_store(types::I64, zero, frame, offset);
                    }
                    let prev = builder
                        .ins()
                        .load(types::I64, ir::MemFlagsData::trusted(), rt, 8);
                    builder.ins().stack_store(types::I64, prev, frame, 0);
                    let count = number(&mut builder, root_layout.total_slots)?;
                    builder.ins().stack_store(types::I64, count, frame, 8);
                    let frame_addr = builder.ins().stack_addr(types::I64, frame, 0);
                    builder
                        .ins()
                        .store(ir::MemFlagsData::trusted(), frame_addr, rt, 8);
                }
                for &slot in &stack_slots {
                    builder.ins().stack_store(types::I64, zero, slot, 0);
                }
            }
            for &parameter in &source.params {
                if let (Some(frame), Some(offset)) = (root_frame, root_layout.reg_offset(parameter))
                {
                    let val = reg(&registers, parameter)?;
                    builder.ins().stack_store(types::I64, val, frame, offset);
                }
            }
            for (result, instruction) in &source.instructions {
                match instruction {
                    Instruction::StackLoad(slot) => {
                        let clif_slot = *stack_slots
                            .get(*slot)
                            .ok_or_else(|| diagnostic("invalid MIR stack slot"))?;
                        let value = builder
                            .ins()
                            .stack_load(types::I64, types::I64, clif_slot, 0);
                        registers.insert(*result, value);
                        if let (Some(frame), Some(offset)) =
                            (root_frame, root_layout.reg_offset(*result))
                        {
                            builder.ins().stack_store(types::I64, value, frame, offset);
                        }
                    }
                    Instruction::StackStore { slot, value } => {
                        let clif_slot = *stack_slots
                            .get(*slot)
                            .ok_or_else(|| diagnostic("invalid MIR stack slot"))?;
                        let value = reg(&registers, *value)?;
                        builder.ins().stack_store(types::I64, value, clif_slot, 0);
                        if let Some(frame) = root_frame {
                            let offset = root_layout.stack_offset(*slot)?;
                            builder.ins().stack_store(types::I64, value, frame, offset);
                        }
                        let unit = builder.ins().iconst(types::I64, RIL_UNIT);
                        registers.insert(*result, unit);
                    }
                    Instruction::Evidence => {
                        registers.insert(*result, incoming_evidence);
                        if let (Some(frame), Some(offset)) =
                            (root_frame, root_layout.reg_offset(*result))
                        {
                            builder
                                .ins()
                                .stack_store(types::I64, incoming_evidence, frame, offset);
                        }
                    }
                    Instruction::Environment => {
                        registers.insert(*result, incoming_environment);
                        if let (Some(frame), Some(offset)) =
                            (root_frame, root_layout.reg_offset(*result))
                        {
                            builder.ins().stack_store(
                                types::I64,
                                incoming_environment,
                                frame,
                                offset,
                            );
                        }
                    }
                    Instruction::IntBinOp { op, left, right } => {
                        let a = reg(&registers, *left)?;
                        let b = reg(&registers, *right)?;
                        let value = self.emit_int_binop(&mut builder, rt, *op, a, b)?;
                        registers.insert(*result, value);
                        if let (Some(frame), Some(offset)) =
                            (root_frame, root_layout.reg_offset(*result))
                        {
                            builder.ins().stack_store(types::I64, value, frame, offset);
                        }
                    }
                    Instruction::IntUnaryOp { op, value } => {
                        let a = reg(&registers, *value)?;
                        let out = self.emit_int_unaryop(&mut builder, rt, *op, a)?;
                        registers.insert(*result, out);
                        if let (Some(frame), Some(offset)) =
                            (root_frame, root_layout.reg_offset(*result))
                        {
                            builder.ins().stack_store(types::I64, out, frame, offset);
                        }
                    }
                    Instruction::BoolNot(value) => {
                        let a = reg(&registers, *value)?;
                        // RIL_FALSE = 0b010 (2), RIL_TRUE = 0b110 (6); XOR 4 flips cleanly.
                        let mask = builder.ins().iconst(types::I64, 4);
                        let out = builder.ins().bxor(a, mask);
                        registers.insert(*result, out);
                    }
                    _ => {
                        let value = self.instruction(&mut builder, rt, instruction)?;
                        registers.insert(*result, value);
                        if let (Some(frame), Some(offset)) =
                            (root_frame, root_layout.reg_offset(*result))
                        {
                            builder.ins().stack_store(types::I64, value, frame, offset);
                        }
                    }
                }
            }
            match source
                .terminator
                .as_ref()
                .ok_or_else(|| diagnostic("unterminated reachable MIR block"))?
            {
                Terminator::Unreachable => {
                    builder
                        .ins()
                        .trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                }
                Terminator::Jump(target, args) => {
                    let args = args
                        .iter()
                        .map(|r| reg(&registers, *r).map(BlockArg::Value))
                        .collect::<Result<Vec<_>>>()?;
                    builder.ins().jump(labels(*target)?, &args);
                }
                Terminator::Branch { condition, yes, no } => {
                    let value = reg(&registers, *condition)?;
                    let test = builder.ins().icmp_imm_s(IntCC::Equal, value, RIL_TRUE);
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
                                    builder.ins().iconst(types::I64, RIL_UNIT)
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
                        Target::Foreign(import) => {
                            let arity = match import.abi {
                                ForeignAbi::Function { arity } => arity,
                                ForeignAbi::Constant => 0,
                            };
                            if arity != args.len() {
                                return Err(diagnostic(
                                    "foreign call arity differs from its declaration",
                                ));
                            }
                            let symbol = foreign_symbol(self.foreign_names, import)?;
                            let args = std::iter::once(rt).chain(args).collect::<Vec<_>>();
                            self.handle(&mut builder, symbol, &args)?
                        }
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
                    if let Some(frame) = root_frame {
                        let prev = builder.ins().stack_load(types::I64, types::I64, frame, 0);
                        builder
                            .ins()
                            .store(ir::MemFlagsData::trusted(), prev, rt, 8);
                    }
                    builder.ins().return_(&[value]);
                }
            }
        }
        builder.seal_all_blocks();
        builder.finalize(self.module.target_config());
        if cfg!(debug_assertions) {
            verify_function(&context.func, self.module.isa()).map_err(diagnostic)?;
        }
        let text = if self.emit_text {
            context.func.display().to_string()
        } else {
            String::new()
        };
        self.module
            .define_function(id, &mut context)
            .map_err(|err| {
                let dump = if text.is_empty() {
                    context.func.display().to_string()
                } else {
                    text.clone()
                };
                diagnostic(format!("{}: {err}\n{dump}", function.name))
            })?;
        Ok(text)
    }

    fn emit_int_binop(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        rt: Value,
        op: IntBinOp,
        a: Value,
        b: Value,
    ) -> Result<Value> {
        let one = builder.ins().iconst(types::I64, 1);
        let both_bits = builder.ins().band(a, b);
        let both_small = builder.ins().band(both_bits, one);

        let fast_block = builder.create_block();
        let slow_block = builder.create_block();
        let merge_block = builder.create_block();
        builder.append_block_param(merge_block, types::I64);
        builder.set_cold_block(slow_block);

        builder
            .ins()
            .brif(both_small, fast_block, &[], slow_block, &[]);

        builder.switch_to_block(fast_block);
        match op {
            IntBinOp::BitAnd => {
                let res = builder.ins().band(a, b);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
            IntBinOp::BitOr => {
                let res = builder.ins().bor(a, b);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
            IntBinOp::BitXor => {
                let x = builder.ins().bxor(a, b);
                let res = builder.ins().bor(x, one);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
            IntBinOp::Eq
            | IntBinOp::Ne
            | IntBinOp::Lt
            | IntBinOp::Le
            | IntBinOp::Gt
            | IntBinOp::Ge => {
                let cc = match op {
                    IntBinOp::Eq => IntCC::Equal,
                    IntBinOp::Ne => IntCC::NotEqual,
                    IntBinOp::Lt => IntCC::SignedLessThan,
                    IntBinOp::Le => IntCC::SignedLessThanOrEqual,
                    IntBinOp::Gt => IntCC::SignedGreaterThan,
                    IntBinOp::Ge => IntCC::SignedGreaterThanOrEqual,
                    _ => unreachable!(),
                };
                // Tagged SmallInt `(n << 1) | 1` preserves signed two's-complement ordering.
                let cmp = builder.ins().icmp(cc, a, b);
                let t = builder.ins().iconst(types::I64, RIL_TRUE);
                let f = builder.ins().iconst(types::I64, RIL_FALSE);
                let res = builder.ins().select(cmp, t, f);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
            IntBinOp::Add => {
                let a_even = builder.ins().bxor(a, one);
                let (sum, overflow) = builder.ins().sadd_overflow(a_even, b);
                builder.ins().brif(
                    overflow,
                    slow_block,
                    &[],
                    merge_block,
                    &[BlockArg::Value(sum)],
                );
            }
            IntBinOp::Sub => {
                let b_even = builder.ins().bxor(b, one);
                let (diff, overflow) = builder.ins().ssub_overflow(a, b_even);
                builder.ins().brif(
                    overflow,
                    slow_block,
                    &[],
                    merge_block,
                    &[BlockArg::Value(diff)],
                );
            }
            IntBinOp::Mul => {
                let a_raw = builder.ins().sshr(a, one);
                let b_even = builder.ins().bxor(b, one);
                let (prod_even, overflow) = builder.ins().smul_overflow(a_raw, b_even);
                let ok_block = builder.create_block();
                builder.ins().brif(overflow, slow_block, &[], ok_block, &[]);
                builder.switch_to_block(ok_block);
                let res = builder.ins().bor(prod_even, one);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
        }

        builder.switch_to_block(slow_block);
        let fallback = self.handle(builder, op.slow_symbol(), &[rt, a, b])?;
        builder
            .ins()
            .jump(merge_block, &[BlockArg::Value(fallback)]);

        builder.switch_to_block(merge_block);
        builder
            .block_params(merge_block)
            .first()
            .copied()
            .ok_or_else(|| diagnostic("missing merge param for IntBinOp"))
    }

    fn emit_int_unaryop(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        rt: Value,
        op: IntUnaryOp,
        a: Value,
    ) -> Result<Value> {
        let one = builder.ins().iconst(types::I64, 1);
        let is_small = builder.ins().band(a, one);

        let fast_block = builder.create_block();
        let slow_block = builder.create_block();
        let merge_block = builder.create_block();
        builder.append_block_param(merge_block, types::I64);
        builder.set_cold_block(slow_block);

        builder
            .ins()
            .brif(is_small, fast_block, &[], slow_block, &[]);

        builder.switch_to_block(fast_block);
        match op {
            IntUnaryOp::BitNot => {
                let mask = builder.ins().iconst(types::I64, -2);
                let res = builder.ins().bxor(a, mask);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
            IntUnaryOp::Neg => {
                let zero = builder.ins().iconst(types::I64, 0);
                let a_even = builder.ins().bxor(a, one);
                let (neg_even, overflow) = builder.ins().ssub_overflow(zero, a_even);
                let ok_block = builder.create_block();
                builder.ins().brif(overflow, slow_block, &[], ok_block, &[]);
                builder.switch_to_block(ok_block);
                let res = builder.ins().bor(neg_even, one);
                builder.ins().jump(merge_block, &[BlockArg::Value(res)]);
            }
        }

        builder.switch_to_block(slow_block);
        let fallback = self.handle(builder, op.slow_symbol(), &[rt, a])?;
        builder
            .ins()
            .jump(merge_block, &[BlockArg::Value(fallback)]);

        builder.switch_to_block(merge_block);
        builder
            .block_params(merge_block)
            .first()
            .copied()
            .ok_or_else(|| diagnostic("missing merge param for IntUnaryOp"))
    }

    fn instruction(
        &mut self,
        builder: &mut FunctionBuilder<'_>,
        rt: Value,
        instruction: &Instruction,
    ) -> Result<Value> {
        match instruction {
            Instruction::Evidence
            | Instruction::Environment
            | Instruction::StackLoad(_)
            | Instruction::StackStore { .. }
            | Instruction::IntBinOp { .. }
            | Instruction::IntUnaryOp { .. }
            | Instruction::BoolNot(_) => Err(diagnostic("missing native incoming parameter")),
            Instruction::ConstSmallInt(number) => {
                let tagged = (u64::from_ne_bytes(number.to_ne_bytes()) << 1) | 1;
                Ok(builder
                    .ins()
                    .iconst(types::I64, i64::from_ne_bytes(tagged.to_ne_bytes())))
            }
            Instruction::FunctionAddress(id) => {
                let fun = self
                    .module
                    .declare_func_in_func(self.function_id(*id)?, builder.func);
                Ok(builder.ins().func_addr(types::I64, fun))
            }
            Instruction::Handle(value) | Instruction::RawU64(value) => Ok(builder
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
                let id = if let Some(&cached) = self.data_pool.get(data) {
                    cached
                } else {
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
                    self.data_pool.insert(data.clone(), id);
                    id
                };
                let global = self.module.declare_data_in_func(id, builder.func);
                let addr = builder.ins().symbol_value(types::I64, global);
                let len = number(builder, data.len())?;
                self.handle(builder, name, &[rt, addr, len])
            }
        }
    }

    fn wrapper(&mut self, entry: FunctionId, suspend_at_entry: bool) -> Result<(FuncId, String)> {
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
        let null = builder.ins().iconst(types::I64, RIL_UNIT);
        let function = self.function_id(entry)?;
        let value = if suspend_at_entry {
            let entry = self.module.declare_func_in_func(function, builder.func);
            let address = builder.ins().func_addr(types::I64, entry);
            let closure = self.handle(
                &mut builder,
                "ril_rt_closure",
                &[rt, address, null, null, null],
            )?;
            self.handle(&mut builder, "ril_fiber_run", &[rt, closure])?
        } else {
            self.call(&mut builder, function, &[rt, null, null])
                .ok_or_else(|| diagnostic("entry has no return value"))?
        };
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
        let text = if self.emit_text {
            context.func.display().to_string()
        } else {
            String::new()
        };
        self.module
            .define_function(id, &mut context)
            .map_err(diagnostic)?;
        Ok((id, text))
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

fn reachable(function: &ril_mir::Function) -> Result<Vec<BlockId>> {
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
                Terminator::Return(_) | Terminator::Unreachable => {}
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

#[cfg(all(test, feature = "native-runtime"))]
mod tests {
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };

    use super::*;

    #[test]
    #[allow(unsafe_code, reason = "exercise a host function with a known C ABI")]
    fn explicitly_bound_host_import_executes_without_process_symbol_lookup() {
        static OBSERVED: AtomicU64 = AtomicU64::new(0);
        extern "C" fn enabled(_context: *mut std::ffi::c_void) -> u64 {
            6
        }
        extern "C" fn host(_context: *mut std::ffi::c_void, value: u64) -> u64 {
            OBSERVED.store(value, Ordering::Relaxed);
            0
        }
        let import = Arc::new(ForeignImport {
            declaration: "pkg/host.d.ril::record".into(),
            symbol: "record".into(),
            signature: "fn(value: bool) @io -> ()".into(),
            abi: ForeignAbi::Function { arity: 1 },
        });
        let constant = Arc::new(ForeignImport {
            declaration: "pkg/host.d.ril::enabled".into(),
            symbol: "enabled".into(),
            signature: "bool".into(),
            abi: ForeignAbi::Constant,
        });
        let program = ril_mir::Program {
            entry: FunctionId(0),
            suspend_at_entry: false,
            source_locs: Vec::new(),
            functions: vec![ril_mir::Function {
                name: "main".into(),
                symbol: "_Ril_main_test".into(),
                source_loc: None,
                arity: 0,
                registers: 4,
                reg_types: vec![
                    ril_mir::MirTy::Evidence,
                    ril_mir::MirTy::Bool,
                    ril_mir::MirTy::Unit,
                    ril_mir::MirTy::Unit,
                ],
                stack_slots: 0,
                blocks: vec![
                    ril_mir::Block {
                        params: Vec::new(),
                        instructions: vec![
                            (Register(0), Instruction::Evidence),
                            (Register(2), Instruction::Handle(0)),
                        ],
                        terminator: Some(Terminator::Invoke {
                            target: Target::Foreign(Arc::clone(&constant)),
                            evidence: Register(0),
                            arguments: Vec::new(),
                            normal: BlockId(1),
                            unwind: BlockId(3),
                            cleanup: false,
                            keep_result: true,
                        }),
                    },
                    ril_mir::Block {
                        params: vec![Register(1)],
                        terminator: Some(Terminator::Invoke {
                            target: Target::Foreign(Arc::clone(&import)),
                            evidence: Register(0),
                            arguments: vec![Register(1)],
                            normal: BlockId(2),
                            unwind: BlockId(3),
                            cleanup: false,
                            keep_result: true,
                        }),
                        ..ril_mir::Block::default()
                    },
                    ril_mir::Block {
                        params: vec![Register(3)],
                        terminator: Some(Terminator::Return(Register(3))),
                        ..ril_mir::Block::default()
                    },
                    ril_mir::Block {
                        terminator: Some(Terminator::Return(Register(2))),
                        ..ril_mir::Block::default()
                    },
                ],
            }],
        };
        assert!(jit(&program).is_err());
        // SAFETY: host has the declared null-unwind C ABI, accepts a packed bool,
        // and returns the unit word. enabled always returns the Ril true word.
        let exit = unsafe {
            jit_with_imports(&program, |request| {
                if request == import.as_ref() {
                    Some(host as *const u8)
                } else {
                    (request == constant.as_ref()).then_some(enabled as *const u8)
                }
            })
        }
        .unwrap();
        assert_eq!(exit, 0);
        assert_eq!(OBSERVED.load(Ordering::Relaxed), 6);
    }
}
