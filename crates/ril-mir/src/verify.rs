use std::collections::BTreeSet;

use ril_source::diag::Diagnostic;

use super::{BlockId, Function, Instruction, MirTy, Program, Register, Target, Terminator};

fn err(function: &Function, detail: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::unsupported(format!("MIR verifier error in {}: {detail}", function.name))
}

/// Verifies structural, CFG, SSA, stack-slot, and GC-type invariants on a MIR program.
pub(crate) fn verify(program: &Program) -> Result<(), Diagnostic> {
    if program.entry.0 >= program.functions.len() {
        return Err(Diagnostic::unsupported(format!(
            "MIR verifier error: entry function {:?} out of bounds ({})",
            program.entry,
            program.functions.len()
        )));
    }
    for function in &program.functions {
        verify_function(function, program.functions.len())?;
    }
    Ok(())
}

fn verify_function(function: &Function, function_count: usize) -> Result<(), Diagnostic> {
    if function.blocks.is_empty() {
        return Err(err(function, "function has no basic blocks"));
    }
    if function.reg_types.len() != function.registers {
        return Err(err(
            function,
            format!(
                "reg_types length {} does not match registers {}",
                function.reg_types.len(),
                function.registers
            ),
        ));
    }
    let Some(entry) = function.blocks.first() else {
        return Err(err(function, "function has no basic blocks"));
    };
    if entry.params.len() != function.arity {
        return Err(err(
            function,
            format!(
                "entry block param count {} does not match arity {}",
                entry.params.len(),
                function.arity
            ),
        ));
    }

    // Collect reachable blocks in reverse post-order.
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
        let block = function
            .blocks
            .get(id.0)
            .ok_or_else(|| err(function, format!("invalid block {:?}", id)))?;
        let Some(term) = &block.terminator else {
            return Err(err(
                function,
                format!("reachable block {:?} is unterminated", id),
            ));
        };
        stack.push((id, true));
        match term {
            Terminator::Return(_) | Terminator::Unreachable => {}
            Terminator::Jump(target, _) => stack.push((*target, false)),
            Terminator::Branch { yes, no, .. } => stack.extend([(*yes, false), (*no, false)]),
            Terminator::Invoke { normal, unwind, .. } => {
                stack.extend([(*normal, false), (*unwind, false)]);
            }
        }
    }
    order.reverse();

    let mut defined = BTreeSet::new();
    let check_reg = |r: Register| -> Result<(), Diagnostic> {
        if r.0 >= function.registers {
            return Err(err(
                function,
                format!("register {:?} out of range (max {})", r, function.registers),
            ));
        }
        Ok(())
    };
    let define = |defined: &mut BTreeSet<Register>, r: Register| -> Result<(), Diagnostic> {
        check_reg(r)?;
        if !defined.insert(r) {
            return Err(err(
                function,
                format!("SSA violation: register {:?} defined more than once", r),
            ));
        }
        Ok(())
    };

    for &id in &order {
        let block = function
            .blocks
            .get(id.0)
            .ok_or_else(|| err(function, format!("invalid block {:?}", id)))?;
        for &param in &block.params {
            define(&mut defined, param)?;
        }
        for (dst, inst) in &block.instructions {
            match inst {
                Instruction::FunctionAddress(fid) => {
                    if fid.0 >= function_count {
                        return Err(err(
                            function,
                            format!("FunctionAddress {:?} out of bounds", fid),
                        ));
                    }
                    if function
                        .reg_types
                        .get(dst.0)
                        .is_some_and(|ty| ty.is_gc_managed())
                    {
                        return Err(err(
                            function,
                            format!("FunctionAddress register {:?} must not be GC-managed", dst),
                        ));
                    }
                }
                Instruction::RawU64(_) => {
                    if function
                        .reg_types
                        .get(dst.0)
                        .is_some_and(|ty| ty.is_gc_managed())
                    {
                        return Err(err(
                            function,
                            format!("RawU64 register {:?} must not be GC-managed", dst),
                        ));
                    }
                }
                Instruction::StackLoad(slot) | Instruction::StackStore { slot, .. }
                    if *slot >= function.stack_slots =>
                {
                    return Err(err(
                        function,
                        format!(
                            "stack slot {slot} out of range (max {})",
                            function.stack_slots
                        ),
                    ));
                }
                _ => {}
            }
            let mut read_err = None;
            inst.visit_reads(|r| {
                if read_err.is_none()
                    && let Err(e) = check_reg(r)
                {
                    read_err = Some(e);
                }
            });
            if let Some(e) = read_err {
                return Err(e);
            }
            define(&mut defined, *dst)?;
        }
        if let Some(term) = &block.terminator {
            match term {
                Terminator::Unreachable => {}
                Terminator::Return(r) => check_reg(*r)?,
                Terminator::Branch { condition, yes, no } => {
                    check_reg(*condition)?;
                    for &target in &[yes, no] {
                        let target_block = function.blocks.get(target.0).ok_or_else(|| {
                            err(function, format!("invalid branch target {:?}", target))
                        })?;
                        if !target_block.params.is_empty() {
                            return Err(err(
                                function,
                                format!("branch target {:?} expects block params", target),
                            ));
                        }
                    }
                }
                Terminator::Jump(target, args) => {
                    let target_block = function.blocks.get(target.0).ok_or_else(|| {
                        err(function, format!("invalid jump target {:?}", target))
                    })?;
                    if target_block.params.len() != args.len() {
                        return Err(err(
                            function,
                            format!(
                                "jump to {:?} passes {} args, target expects {}",
                                target,
                                args.len(),
                                target_block.params.len()
                            ),
                        ));
                    }
                    for &arg in args {
                        check_reg(arg)?;
                    }
                }
                Terminator::Invoke {
                    target,
                    evidence,
                    arguments,
                    normal,
                    unwind,
                    keep_result,
                    ..
                } => {
                    check_reg(*evidence)?;
                    for &arg in arguments {
                        check_reg(arg)?;
                    }
                    match target {
                        Target::Function(fid) => {
                            if fid.0 >= function_count {
                                return Err(err(
                                    function,
                                    format!("invoke target {:?} out of bounds", fid),
                                ));
                            }
                        }
                        Target::FunctionWithEnv {
                            function: fid,
                            environment,
                        } => {
                            if fid.0 >= function_count {
                                return Err(err(
                                    function,
                                    format!("invoke target {:?} out of bounds", fid),
                                ));
                            }
                            check_reg(*environment)?;
                        }
                        Target::Indirect {
                            address,
                            evidence,
                            environment,
                        } => {
                            check_reg(*address)?;
                            check_reg(*evidence)?;
                            check_reg(*environment)?;
                        }
                        Target::Runtime(_) | Target::Draft(_) | Target::Foreign(_) => {}
                    }
                    let normal_block = function.blocks.get(normal.0).ok_or_else(|| {
                        err(function, format!("invalid normal block {:?}", normal))
                    })?;
                    let expected_params = usize::from(*keep_result);
                    if normal_block.params.len() != expected_params {
                        return Err(err(
                            function,
                            format!(
                                "invoke normal target {:?} has {} params, expected {}",
                                normal,
                                normal_block.params.len(),
                                expected_params
                            ),
                        ));
                    }
                    let unwind_block = function.blocks.get(unwind.0).ok_or_else(|| {
                        err(function, format!("invalid unwind block {:?}", unwind))
                    })?;
                    if !unwind_block.params.is_empty() {
                        return Err(err(
                            function,
                            format!("invoke unwind target {:?} must take 0 params", unwind),
                        ));
                    }
                }
            }
        }
    }

    // Verify no non-GC-managed raw registers are marked managed.
    for (idx, ty) in function.reg_types.iter().enumerate() {
        if matches!(ty, MirTy::RawFnPtr | MirTy::RawU64 | MirTy::Foreign) && ty.is_gc_managed() {
            return Err(err(
                function,
                format!("raw register r{idx} must never be GC-managed"),
            ));
        }
    }

    Ok(())
}
