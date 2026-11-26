use std::collections::BTreeMap;

use cranelift_codegen::{
    ir::{self, BlockArg, InstBuilder as _, Value, condcodes::IntCC, types},
    verify_function,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId, Module};
use ril_mir::{BlockId, ForeignAbi, Instruction, IntBinOp, IntUnaryOp, Target, Terminator};

use super::{
    MirToClifTranslator, RIL_FALSE, RIL_TRUE, RIL_UNIT, Result,
    abi::{number, reg},
    diagnostic, foreign_symbol,
    liveness::{RootLayout, reachable, store_root},
};

impl<M: Module> MirToClifTranslator<'_, M> {
    pub(super) fn translate(&mut self, id: FuncId, function: &ril_mir::Function) -> Result<String> {
        let mut context = self.module.make_context();
        context.func.signature = self.signature(function.arity + 2, Some(types::I64));
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
        let [rt, environment, rest @ ..] = abi.as_slice() else {
            return Err(diagnostic("missing Ril closure ABI parameters"));
        };
        let (rt, incoming_environment) = (*rt, *environment);
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
                let val = reg(&registers, parameter)?;
                store_root(&mut builder, root_frame, &root_layout, parameter, val);
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
                        store_root(&mut builder, root_frame, &root_layout, *result, value);
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
                    Instruction::Environment => {
                        registers.insert(*result, incoming_environment);
                        store_root(
                            &mut builder,
                            root_frame,
                            &root_layout,
                            *result,
                            incoming_environment,
                        );
                    }
                    Instruction::IntBinOp { op, left, right } => {
                        let a = reg(&registers, *left)?;
                        let b = reg(&registers, *right)?;
                        let value = self.emit_int_binop(&mut builder, rt, *op, a, b)?;
                        registers.insert(*result, value);
                        store_root(&mut builder, root_frame, &root_layout, *result, value);
                    }
                    Instruction::IntUnaryOp { op, value } => {
                        let a = reg(&registers, *value)?;
                        let out = self.emit_int_unaryop(&mut builder, rt, *op, a)?;
                        registers.insert(*result, out);
                        store_root(&mut builder, root_frame, &root_layout, *result, out);
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
                        store_root(&mut builder, root_frame, &root_layout, *result, value);
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
                            let args = [rt, environment]
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
                            environment,
                        } => {
                            let address = reg(&registers, *address)?;
                            let args = [rt, reg(&registers, *environment)?]
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
            Instruction::Environment
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
}
