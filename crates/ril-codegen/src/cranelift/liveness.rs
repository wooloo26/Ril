use std::collections::{BTreeSet, HashMap};

use cranelift_codegen::ir::{self, InstBuilder as _, Value, types};
use cranelift_frontend::FunctionBuilder;
use ril_mir::{BlockId, Instruction, Register, Target, Terminator};

use super::{Result, diagnostic};

/// Maps each GC-managed MIR register and stack slot to its compact offset inside the
/// function's intrusive stack-allocated `RootFrame` (`[prev: 8B | count: 8B | slots: N*8B]`).
pub(super) struct RootLayout {
    reg_slot: Vec<Option<i32>>,
    stack_slot_base: usize,
    pub(super) total_slots: usize,
}

impl RootLayout {
    pub(super) fn build(function: &ril_mir::Function, order: &[BlockId]) -> Self {
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

    pub(super) fn reg_offset(&self, reg: Register) -> Option<i32> {
        self.reg_slot.get(reg.0).copied().flatten()
    }

    pub(super) fn stack_offset(&self, slot: usize) -> Result<i32> {
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
                    arguments,
                    normal,
                    unwind,
                    ..
                }) => {
                    add_succ(*normal);
                    add_succ(*unwind);
                    live.extend(arguments.iter().copied());
                    match target {
                        Target::FunctionWithEnv { environment, .. } => {
                            live.insert(*environment);
                        }
                        Target::Indirect {
                            address,
                            environment,
                        } => {
                            live.insert(*address);
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

pub(super) fn store_root(
    builder: &mut FunctionBuilder<'_>,
    root_frame: Option<ir::StackSlot>,
    root_layout: &RootLayout,
    register: Register,
    value: Value,
) {
    if let (Some(frame), Some(offset)) = (root_frame, root_layout.reg_offset(register)) {
        builder.ins().stack_store(types::I64, value, frame, offset);
    }
}

pub(super) fn reachable(function: &ril_mir::Function) -> Result<Vec<BlockId>> {
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
            for succ in terminator.successors() {
                todo.push((succ, false));
            }
        }
    }
    order.reverse();
    Ok(order)
}
