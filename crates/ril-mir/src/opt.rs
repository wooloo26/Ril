use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::{
    BlockId, Function, Instruction, IntBinOp, IntUnaryOp, Program, Register, Target, Terminator,
};

const SMALL_MIN: i64 = i64::MIN >> 1;
const SMALL_MAX: i64 = i64::MAX >> 1;
const RIL_FALSE: u64 = 0b010;
const RIL_TRUE: u64 = 0b110;

/// Runs intra-procedural SSA optimizations on every function in `program`:
/// 1. Redundant block-parameter elimination (prunes immutable `let` locals threaded across CFGs)
/// 2. Constant folding & branch simplification (`ConstSmallInt`, `BoolNot`, constant `Branch`)
/// 3. Dead pure instruction elimination (including unused `Instruction::Evidence`)
pub(crate) fn optimize(program: &mut Program) {
    for function in &mut program.functions {
        optimize_function(function);
    }
}

fn optimize_function(function: &mut Function) {
    for _ in 0..6 {
        let mut changed = false;
        changed |= eliminate_redundant_block_params(function);
        changed |= fold_constants(function);
        changed |= eliminate_dead_instructions(function);
        if !changed {
            break;
        }
    }
}

fn reachable(function: &Function) -> Vec<BlockId> {
    let mut order = Vec::new();
    let mut visited = BTreeSet::new();
    let mut stack = vec![(BlockId(0), false)];
    while let Some((id, done)) = stack.pop() {
        if done {
            order.push(id);
            continue;
        }
        if !visited.insert(id) {
            continue;
        }
        let Some(block) = function.blocks.get(id.0) else {
            continue;
        };
        stack.push((id, true));
        match &block.terminator {
            Some(Terminator::Return(_) | Terminator::Unreachable) | None => {}
            Some(Terminator::Jump(target, _)) => stack.push((*target, false)),
            Some(Terminator::Branch { yes, no, .. }) => stack.extend([(*yes, false), (*no, false)]),
            Some(Terminator::Invoke { normal, unwind, .. }) => {
                stack.extend([(*normal, false), (*unwind, false)]);
            }
        }
    }
    order.reverse();
    order
}

/// Removes any block parameter `p` of a Jump-targeted block `B` where every incoming edge
/// passes either the same register `r` or `p` itself (e.g. immutable `let` bindings carried
/// across `if`/`match`/`while`/`for` merge blocks).
fn eliminate_redundant_block_params(function: &mut Function) -> bool {
    let order = reachable(function);
    let mut invoke_targets = BTreeSet::new();
    let mut incoming: BTreeMap<BlockId, Vec<Vec<Register>>> = BTreeMap::new();

    for &bid in &order {
        let Some(block) = function.blocks.get(bid.0) else {
            continue;
        };
        match &block.terminator {
            Some(Terminator::Jump(target, args)) => {
                incoming.entry(*target).or_default().push(args.clone());
            }
            Some(Terminator::Invoke { normal, unwind, .. }) => {
                invoke_targets.insert(*normal);
                invoke_targets.insert(*unwind);
            }
            _ => {}
        }
    }

    let mut replacements: HashMap<Register, Register> = HashMap::new();
    let mut remove_indices: BTreeMap<BlockId, Vec<usize>> = BTreeMap::new();

    for &bid in &order {
        if bid == BlockId(0) || invoke_targets.contains(&bid) {
            continue;
        }
        let Some(block) = function.blocks.get(bid.0) else {
            continue;
        };
        if block.params.is_empty() {
            continue;
        }
        let Some(edges) = incoming.get(&bid) else {
            continue;
        };
        if edges.is_empty() {
            continue;
        }
        let mut to_remove = Vec::new();
        for (idx, &param) in block.params.iter().enumerate() {
            let mut candidate: Option<Register> = None;
            let mut uniform = true;
            for edge in edges {
                let Some(&arg) = edge.get(idx) else {
                    uniform = false;
                    break;
                };
                if arg == param {
                    continue;
                }
                match candidate {
                    None => candidate = Some(arg),
                    Some(prev) if prev == arg => {}
                    Some(_) => {
                        uniform = false;
                        break;
                    }
                }
            }
            if uniform && let Some(replacement) = candidate {
                replacements.insert(param, replacement);
                to_remove.push(idx);
            }
        }
        if !to_remove.is_empty() {
            remove_indices.insert(bid, to_remove);
        }
    }

    if replacements.is_empty() {
        return false;
    }

    for (&bid, indices) in &remove_indices {
        if let Some(block) = function.blocks.get_mut(bid.0) {
            let remove_set: BTreeSet<usize> = indices.iter().copied().collect();
            let mut idx = 0usize;
            block.params.retain(|_| {
                let keep = !remove_set.contains(&idx);
                idx += 1;
                keep
            });
        }
    }

    for block in &mut function.blocks {
        if let Some(Terminator::Jump(target, args)) = &mut block.terminator
            && let Some(indices) = remove_indices.get(target)
        {
            let remove_set: BTreeSet<usize> = indices.iter().copied().collect();
            let mut idx = 0usize;
            args.retain(|_| {
                let keep = !remove_set.contains(&idx);
                idx += 1;
                keep
            });
        }
    }

    substitute_registers(function, &replacements);
    true
}

#[derive(Clone, Copy)]
enum ConstVal {
    SmallInt(i64),
    Bool(bool),
}

fn fold_constants(function: &mut Function) -> bool {
    let order = reachable(function);
    let mut constants: HashMap<Register, ConstVal> = HashMap::new();
    let mut changed = false;

    for &bid in &order {
        let Some(block) = function.blocks.get_mut(bid.0) else {
            continue;
        };
        for (dst, inst) in &mut block.instructions {
            match inst {
                Instruction::ConstSmallInt(n) => {
                    constants.insert(*dst, ConstVal::SmallInt(*n));
                }
                Instruction::Handle(RIL_TRUE) => {
                    constants.insert(*dst, ConstVal::Bool(true));
                }
                Instruction::Handle(RIL_FALSE) => {
                    constants.insert(*dst, ConstVal::Bool(false));
                }
                Instruction::BoolNot(src) => {
                    if let Some(ConstVal::Bool(b)) = constants.get(src).copied() {
                        let flipped = !b;
                        *inst = Instruction::Handle(if flipped { RIL_TRUE } else { RIL_FALSE });
                        constants.insert(*dst, ConstVal::Bool(flipped));
                        changed = true;
                    }
                }
                Instruction::IntUnaryOp { op, value } => {
                    if let Some(ConstVal::SmallInt(n)) = constants.get(value).copied() {
                        let folded = match op {
                            IntUnaryOp::BitNot => Some(!n),
                            IntUnaryOp::Neg => n
                                .checked_neg()
                                .filter(|&v| (SMALL_MIN..=SMALL_MAX).contains(&v)),
                        };
                        if let Some(res) = folded {
                            *inst = Instruction::ConstSmallInt(res);
                            if let Some(ty) = function.reg_types.get_mut(dst.0) {
                                *ty = super::MirTy::SmallInt;
                            }
                            constants.insert(*dst, ConstVal::SmallInt(res));
                            changed = true;
                        }
                    }
                }
                Instruction::IntBinOp { op, left, right } => {
                    if let (Some(ConstVal::SmallInt(a)), Some(ConstVal::SmallInt(b))) =
                        (constants.get(left).copied(), constants.get(right).copied())
                    {
                        match op {
                            IntBinOp::Eq
                            | IntBinOp::Ne
                            | IntBinOp::Lt
                            | IntBinOp::Le
                            | IntBinOp::Gt
                            | IntBinOp::Ge => {
                                let res = match op {
                                    IntBinOp::Eq => a == b,
                                    IntBinOp::Ne => a != b,
                                    IntBinOp::Lt => a < b,
                                    IntBinOp::Le => a <= b,
                                    IntBinOp::Gt => a > b,
                                    IntBinOp::Ge => a >= b,
                                    _ => false,
                                };
                                *inst = Instruction::Handle(if res { RIL_TRUE } else { RIL_FALSE });
                                constants.insert(*dst, ConstVal::Bool(res));
                                changed = true;
                            }
                            IntBinOp::Add
                            | IntBinOp::Sub
                            | IntBinOp::Mul
                            | IntBinOp::BitAnd
                            | IntBinOp::BitOr
                            | IntBinOp::BitXor => {
                                let res = match op {
                                    IntBinOp::Add => a.checked_add(b),
                                    IntBinOp::Sub => a.checked_sub(b),
                                    IntBinOp::Mul => a.checked_mul(b),
                                    IntBinOp::BitAnd => Some(a & b),
                                    IntBinOp::BitOr => Some(a | b),
                                    IntBinOp::BitXor => Some(a ^ b),
                                    _ => None,
                                };
                                if let Some(val) =
                                    res.filter(|&v| (SMALL_MIN..=SMALL_MAX).contains(&v))
                                {
                                    *inst = Instruction::ConstSmallInt(val);
                                    if let Some(ty) = function.reg_types.get_mut(dst.0) {
                                        *ty = super::MirTy::SmallInt;
                                    }
                                    constants.insert(*dst, ConstVal::SmallInt(val));
                                    changed = true;
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        if let Some(Terminator::Branch { condition, yes, no }) = &block.terminator
            && let Some(ConstVal::Bool(b)) = constants.get(condition).copied()
        {
            let target = if b { *yes } else { *no };
            block.terminator = Some(Terminator::Jump(target, Vec::new()));
            changed = true;
        }
    }

    changed
}

fn eliminate_dead_instructions(function: &mut Function) -> bool {
    let order = reachable(function);
    let mut used = BTreeSet::new();
    for &bid in &order {
        let Some(block) = function.blocks.get(bid.0) else {
            continue;
        };
        for (_, inst) in &block.instructions {
            inst.visit_reads(|reg| {
                used.insert(reg);
            });
        }
        if let Some(term) = &block.terminator {
            visit_terminator_reads(term, |reg| {
                used.insert(reg);
            });
        }
    }
    let mut removed = false;
    for &bid in &order {
        let Some(block) = function.blocks.get_mut(bid.0) else {
            continue;
        };
        let before = block.instructions.len();
        block.instructions.retain(|(reg, inst)| {
            matches!(inst, Instruction::StackStore { .. }) || used.contains(reg)
        });
        if block.instructions.len() != before {
            removed = true;
        }
    }
    removed
}

fn visit_terminator_reads(term: &Terminator, mut visit: impl FnMut(Register)) {
    match term {
        Terminator::Unreachable => {}
        Terminator::Return(reg) => visit(*reg),
        Terminator::Jump(_, args) => {
            for &arg in args {
                visit(arg);
            }
        }
        Terminator::Branch { condition, .. } => visit(*condition),
        Terminator::Invoke {
            target,
            evidence,
            arguments,
            ..
        } => {
            visit(*evidence);
            match target {
                Target::FunctionWithEnv { environment, .. } => visit(*environment),
                Target::Indirect {
                    address,
                    evidence,
                    environment,
                } => {
                    visit(*address);
                    visit(*evidence);
                    visit(*environment);
                }
                Target::Function(_)
                | Target::Runtime(_)
                | Target::Draft(_)
                | Target::Foreign(_) => {}
            }
            for &arg in arguments {
                visit(arg);
            }
        }
    }
}

fn resolve_reg(map: &HashMap<Register, Register>, mut reg: Register) -> Register {
    let mut steps = 0;
    while let Some(&next) = map.get(&reg) {
        if next == reg || steps > 64 {
            break;
        }
        reg = next;
        steps += 1;
    }
    reg
}

fn substitute_registers(function: &mut Function, map: &HashMap<Register, Register>) {
    for block in &mut function.blocks {
        for (_, inst) in &mut block.instructions {
            inst.remap_reads(|reg| *reg = resolve_reg(map, *reg));
        }
        if let Some(term) = &mut block.terminator {
            match term {
                Terminator::Unreachable => {}
                Terminator::Return(reg) => *reg = resolve_reg(map, *reg),
                Terminator::Jump(_, args) => {
                    for arg in args {
                        *arg = resolve_reg(map, *arg);
                    }
                }
                Terminator::Branch { condition, .. } => *condition = resolve_reg(map, *condition),
                Terminator::Invoke {
                    target,
                    evidence,
                    arguments,
                    ..
                } => {
                    *evidence = resolve_reg(map, *evidence);
                    match target {
                        Target::FunctionWithEnv { environment, .. } => {
                            *environment = resolve_reg(map, *environment);
                        }
                        Target::Indirect {
                            address,
                            evidence,
                            environment,
                        } => {
                            *address = resolve_reg(map, *address);
                            *evidence = resolve_reg(map, *evidence);
                            *environment = resolve_reg(map, *environment);
                        }
                        Target::Function(_)
                        | Target::Runtime(_)
                        | Target::Draft(_)
                        | Target::Foreign(_) => {}
                    }
                    for arg in arguments {
                        *arg = resolve_reg(map, *arg);
                    }
                }
            }
        }
    }
}
