use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::{BlockId, Function, Instruction, Program, Register, Target, Terminator};

const MAX_PASSES: usize = 8;

pub(super) fn promote_program(program: &mut Program) {
    for function in &mut program.functions {
        promote_function(function);
    }
}

fn promote_function(function: &mut Function) {
    for _ in 0..MAX_PASSES {
        let promoted = promote_pass(function);
        let simplified = simplify_stack_slots(function);
        let coalesced = coalesce_blocks(function);
        let cleaned = super::opt::eliminate_dead_instructions(function);
        if !promoted && !simplified && !coalesced && !cleaned {
            break;
        }
    }
    compact_stack_slots(function);
}

#[derive(Clone, Debug)]
enum AllocKind {
    Record,
    Tuple,
    Array,
    Tag(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Origin {
    None,
    Single(usize),
    Many,
}

impl Origin {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, value) | (value, Self::None) => value,
            (Self::Single(a), Self::Single(b)) if a == b => Self::Single(a),
            _ => Self::Many,
        }
    }
}

struct Candidate {
    alloc_block: BlockId,
    def_block: BlockId,
    alloc_reg: Register,
    kind: AllocKind,
    valid: bool,
    uses: Vec<CandidateUse>,
}

enum CandidateUse {
    RecordStore {
        block: BlockId,
        key: String,
        value: Register,
        normal: BlockId,
        keep_result: bool,
    },
    RecordLoad {
        block: BlockId,
        key: String,
        normal: BlockId,
        keep_result: bool,
    },
    Append {
        block: BlockId,
        value: Register,
        normal: BlockId,
        keep_result: bool,
    },
    IndexLoad {
        block: BlockId,
        index: usize,
        normal: BlockId,
        keep_result: bool,
    },
    IndexStore {
        block: BlockId,
        index: usize,
        value: Register,
        normal: BlockId,
        keep_result: bool,
    },
    Len {
        block: BlockId,
        normal: BlockId,
        keep_result: bool,
    },
    IsTag {
        block: BlockId,
        matches: bool,
        normal: BlockId,
        keep_result: bool,
    },
}

struct Cfg {
    order: Vec<BlockId>,
    pos: HashMap<BlockId, usize>,
    preds: Vec<Vec<usize>>,
    succs: Vec<Vec<usize>>,
    dom: Vec<Vec<u64>>,
    reach: Vec<Vec<u64>>,
}

impl Cfg {
    fn build(function: &Function) -> Self {
        let order = function.rpo();
        let n = order.len();
        let pos: HashMap<_, _> = order.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        let mut preds = vec![Vec::new(); n];
        let mut succs = vec![Vec::new(); n];
        for (i, &block_id) in order.iter().enumerate() {
            if let Some(block) = function.blocks.get(block_id.0)
                && let Some(term) = &block.terminator
            {
                for succ in term.successors() {
                    if let Some(&j) = pos.get(&succ)
                        && !succs.get(i).is_some_and(|list| list.contains(&j))
                    {
                        if let Some(list) = succs.get_mut(i) {
                            list.push(j);
                        }
                        if let Some(list) = preds.get_mut(j) {
                            list.push(i);
                        }
                    }
                }
            }
        }
        let words = n.div_ceil(64).max(1);
        let mut dom = vec![vec![u64::MAX; words]; n];
        if let Some(entry_dom) = dom.first_mut() {
            entry_dom.fill(0);
            set_bit(entry_dom, 0);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for i in 1..n {
                let Some(pred_list) = preds.get(i) else {
                    continue;
                };
                if pred_list.is_empty() {
                    continue;
                }
                let mut next = vec![u64::MAX; words];
                for &p in pred_list {
                    if let Some(p_dom) = dom.get(p) {
                        for (dst, &src) in next.iter_mut().zip(p_dom) {
                            *dst &= src;
                        }
                    }
                }
                set_bit(&mut next, i);
                if dom.get(i) != Some(&next) {
                    if let Some(slot) = dom.get_mut(i) {
                        *slot = next;
                    }
                    changed = true;
                }
            }
        }
        let mut reach = vec![vec![0_u64; words]; n];
        for start in 0..n {
            let mut work = vec![start];
            let mut seen = vec![0_u64; words];
            set_bit(&mut seen, start);
            while let Some(node) = work.pop() {
                if let Some(list) = succs.get(node) {
                    for &next in list {
                        if !has_bit(&seen, next) {
                            set_bit(&mut seen, next);
                            work.push(next);
                        }
                    }
                }
            }
            if let Some(slot) = reach.get_mut(start) {
                *slot = seen;
            }
        }
        Self {
            order,
            pos,
            preds,
            succs,
            dom,
            reach,
        }
    }

    fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        let (Some(&pa), Some(&pb)) = (self.pos.get(&a), self.pos.get(&b)) else {
            return false;
        };
        self.dom.get(pb).is_some_and(|bits| has_bit(bits, pa))
    }

    fn can_reach(&self, from: BlockId, to: BlockId) -> bool {
        let (Some(&pf), Some(&pt)) = (self.pos.get(&from), self.pos.get(&to)) else {
            return false;
        };
        self.reach.get(pf).is_some_and(|bits| has_bit(bits, pt))
    }

    fn single_pred(&self, block: BlockId, expected: BlockId) -> bool {
        let (Some(&pb), Some(&pe)) = (self.pos.get(&block), self.pos.get(&expected)) else {
            return false;
        };
        self.preds
            .get(pb)
            .is_some_and(|list| list.as_slice() == [pe])
    }

    fn can_reach_avoiding(&self, start: BlockId, target: BlockId, forbidden: BlockId) -> bool {
        let (Some(&ps), Some(&pt), Some(&pf)) = (
            self.pos.get(&start),
            self.pos.get(&target),
            self.pos.get(&forbidden),
        ) else {
            return false;
        };
        if ps == pf {
            return false;
        }
        let words = self.order.len().div_ceil(64).max(1);
        let mut seen = vec![0_u64; words];
        let mut work = vec![ps];
        set_bit(&mut seen, ps);
        while let Some(node) = work.pop() {
            if node == pt {
                return true;
            }
            if let Some(list) = self.succs.get(node) {
                for &next in list {
                    if next != pf && !has_bit(&seen, next) {
                        set_bit(&mut seen, next);
                        work.push(next);
                    }
                }
            }
        }
        false
    }
}

fn set_bit(words: &mut [u64], index: usize) {
    if let Some(word) = words.get_mut(index / 64) {
        *word |= 1_u64 << (index % 64);
    }
}

fn has_bit(words: &[u64], index: usize) -> bool {
    words
        .get(index / 64)
        .is_some_and(|word| (*word & (1_u64 << (index % 64))) != 0)
}

fn promote_pass(function: &mut Function) -> bool {
    let cfg = Cfg::build(function);
    let mut const_text = HashMap::new();
    let mut const_int = HashMap::new();
    for &block_id in &cfg.order {
        let Some(block) = function.blocks.get(block_id.0) else {
            continue;
        };
        for (reg, inst) in &block.instructions {
            match inst {
                Instruction::Text(bytes) => {
                    if let Ok(text) = std::str::from_utf8(bytes) {
                        const_text.insert(*reg, text.to_owned());
                    }
                }
                Instruction::Integer(bytes) => {
                    if let Ok(text) = std::str::from_utf8(bytes)
                        && let Ok(value) = text.parse::<usize>()
                    {
                        const_int.insert(*reg, value);
                    }
                }
                Instruction::ConstSmallInt(n) => {
                    if let Ok(value) = usize::try_from(*n) {
                        const_int.insert(*reg, value);
                    }
                }
                _ => {}
            }
        }
    }

    let mut candidates = Vec::new();
    let mut alloc_block_to_candidate = HashMap::new();
    for &block_id in &cfg.order {
        let Some(block) = function.blocks.get(block_id.0) else {
            continue;
        };
        let Some(Terminator::Invoke {
            target: Target::Runtime(symbol),
            arguments,
            normal,
            cleanup: false,
            keep_result: true,
            ..
        }) = &block.terminator
        else {
            continue;
        };
        if !cfg.single_pred(*normal, block_id) {
            continue;
        }
        let Some(normal_block) = function.blocks.get(normal.0) else {
            continue;
        };
        let [alloc_reg] = normal_block.params.as_slice() else {
            continue;
        };
        let kind = match (*symbol, arguments.as_slice()) {
            ("ril_rt_record", []) => AllocKind::Record,
            ("ril_rt_tuple", []) => AllocKind::Tuple,
            ("ril_rt_array", []) => AllocKind::Array,
            ("ril_rt_tag", [name_reg]) => {
                let Some(tag) = const_text.get(name_reg) else {
                    continue;
                };
                AllocKind::Tag(tag.clone())
            }
            _ => continue,
        };
        let id = candidates.len();
        alloc_block_to_candidate.insert(block_id, id);
        candidates.push(Candidate {
            alloc_block: block_id,
            def_block: *normal,
            alloc_reg: *alloc_reg,
            kind,
            valid: true,
            uses: Vec::new(),
        });
    }
    if candidates.is_empty() {
        return false;
    }

    let mut origins = vec![Origin::None; function.registers];
    if let Some(entry) = function.blocks.first() {
        for &param in &entry.params {
            if let Some(slot) = origins.get_mut(param.0) {
                *slot = Origin::Many;
            }
        }
    }
    for &block_id in &cfg.order {
        let Some(block) = function.blocks.get(block_id.0) else {
            continue;
        };
        for &(reg, _) in &block.instructions {
            if let Some(slot) = origins.get_mut(reg.0) {
                *slot = Origin::Many;
            }
        }
        if let Some(Terminator::Invoke {
            normal,
            keep_result: true,
            ..
        }) = &block.terminator
            && let Some(normal_block) = function.blocks.get(normal.0)
            && let Some(&res) = normal_block.params.first()
            && let Some(slot) = origins.get_mut(res.0)
        {
            *slot = match alloc_block_to_candidate.get(&block_id) {
                Some(&id) => Origin::Single(id),
                None => Origin::Many,
            };
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &block_id in &cfg.order {
            let Some(block) = function.blocks.get(block_id.0) else {
                continue;
            };
            if let Some(Terminator::Jump(target, args)) = &block.terminator
                && let Some(target_block) = function.blocks.get(target.0)
            {
                for (&arg, &param) in args.iter().zip(&target_block.params) {
                    let arg_origin = origins.get(arg.0).copied().unwrap_or(Origin::Many);
                    let current = origins.get(param.0).copied().unwrap_or(Origin::None);
                    let joined = current.join(arg_origin);
                    if joined != current {
                        if let Some(slot) = origins.get_mut(param.0) {
                            *slot = joined;
                        }
                        changed = true;
                    }
                }
            }
        }
    }

    let origin_of = |reg: Register| origins.get(reg.0).copied().unwrap_or(Origin::Many);
    let invalidate = |candidates: &mut [Candidate], reg: Register| {
        if let Origin::Single(id) = origin_of(reg)
            && let Some(cand) = candidates.get_mut(id)
        {
            cand.valid = false;
        }
    };

    for &block_id in &cfg.order {
        let Some(block) = function.blocks.get(block_id.0) else {
            continue;
        };
        for (_, inst) in &block.instructions {
            inst.visit_reads(|reg| invalidate(&mut candidates, reg));
        }
        match &block.terminator {
            Some(Terminator::Return(reg)) => invalidate(&mut candidates, *reg),
            Some(Terminator::Branch { condition, .. }) => invalidate(&mut candidates, *condition),
            Some(Terminator::Jump(target, args)) => {
                if let Some(target_block) = function.blocks.get(target.0) {
                    for (&arg, &param) in args.iter().zip(&target_block.params) {
                        if let Origin::Single(id) = origin_of(arg) {
                            let ok = origin_of(param) == Origin::Single(id)
                                && candidates.get(id).is_some_and(|cand| {
                                    cand.def_block != *target
                                        && (cfg.dominates(cand.def_block, *target)
                                            || !cfg.can_reach(*target, cand.def_block))
                                });
                            if !ok && let Some(cand) = candidates.get_mut(id) {
                                cand.valid = false;
                            }
                        }
                    }
                }
            }
            Some(Terminator::Invoke {
                target,
                evidence,
                arguments,
                normal,
                cleanup,
                keep_result,
                ..
            }) => {
                invalidate(&mut candidates, *evidence);
                match target {
                    Target::FunctionWithEnv { environment, .. } => {
                        invalidate(&mut candidates, *environment);
                    }
                    Target::Indirect {
                        address,
                        evidence,
                        environment,
                    } => {
                        invalidate(&mut candidates, *address);
                        invalidate(&mut candidates, *evidence);
                        invalidate(&mut candidates, *environment);
                    }
                    _ => {}
                }
                for &arg in arguments.iter().skip(1) {
                    invalidate(&mut candidates, arg);
                }
                if let Some(&arg0) = arguments.first()
                    && let Origin::Single(id) = origin_of(arg0)
                    && let Some(cand) = candidates.get_mut(id)
                {
                    if *cleanup
                        || !cfg.dominates(cand.def_block, block_id)
                        || !cfg.single_pred(*normal, block_id)
                    {
                        cand.valid = false;
                        continue;
                    }
                    let Target::Runtime(symbol) = target else {
                        cand.valid = false;
                        continue;
                    };
                    let parsed = match (&cand.kind, *symbol, arguments.as_slice()) {
                        (AllocKind::Record, "ril_rt_store", [_, key_reg, val_reg]) => const_text
                            .get(key_reg)
                            .map(|key| CandidateUse::RecordStore {
                                block: block_id,
                                key: key.clone(),
                                value: *val_reg,
                                normal: *normal,
                                keep_result: *keep_result,
                            }),
                        (AllocKind::Record, "ril_rt_load", [_, key_reg]) => {
                            const_text.get(key_reg).map(|key| CandidateUse::RecordLoad {
                                block: block_id,
                                key: key.clone(),
                                normal: *normal,
                                keep_result: *keep_result,
                            })
                        }
                        (
                            AllocKind::Tuple | AllocKind::Array | AllocKind::Tag(_),
                            "ril_rt_append",
                            [_, val_reg],
                        ) => Some(CandidateUse::Append {
                            block: block_id,
                            value: *val_reg,
                            normal: *normal,
                            keep_result: *keep_result,
                        }),
                        (
                            AllocKind::Tuple | AllocKind::Array | AllocKind::Tag(_),
                            "ril_rt_load",
                            [_, idx_reg],
                        ) => const_int
                            .get(idx_reg)
                            .map(|&index| CandidateUse::IndexLoad {
                                block: block_id,
                                index,
                                normal: *normal,
                                keep_result: *keep_result,
                            }),
                        (
                            AllocKind::Tuple | AllocKind::Array | AllocKind::Tag(_),
                            "ril_rt_store",
                            [_, idx_reg, val_reg],
                        ) => const_int
                            .get(idx_reg)
                            .map(|&index| CandidateUse::IndexStore {
                                block: block_id,
                                index,
                                value: *val_reg,
                                normal: *normal,
                                keep_result: *keep_result,
                            }),
                        (AllocKind::Tuple | AllocKind::Array, "ril_rt_len", [_]) => {
                            Some(CandidateUse::Len {
                                block: block_id,
                                normal: *normal,
                                keep_result: *keep_result,
                            })
                        }
                        (AllocKind::Tag(tag), "ril_rt_is_tag", [_, expected_reg]) => const_text
                            .get(expected_reg)
                            .map(|expected| CandidateUse::IsTag {
                                block: block_id,
                                matches: expected == tag,
                                normal: *normal,
                                keep_result: *keep_result,
                            }),
                        _ => None,
                    };
                    if let Some(item) = parsed {
                        cand.uses.push(item);
                    } else {
                        cand.valid = false;
                    }
                }
            }
            Some(Terminator::Unreachable) | None => {}
        }
    }

    let mut promoted_any = false;
    for cand in candidates {
        if !cand.valid {
            continue;
        }
        match &cand.kind {
            AllocKind::Record => {
                if !validate_record(&cfg, &cand) {
                    continue;
                }
                let mut keys = BTreeSet::new();
                for item in &cand.uses {
                    match item {
                        CandidateUse::RecordStore { key, .. }
                        | CandidateUse::RecordLoad { key, .. } => {
                            keys.insert(key.clone());
                        }
                        _ => {}
                    }
                }
                let base = function.stack_slots;
                let slots: BTreeMap<_, _> = keys
                    .into_iter()
                    .enumerate()
                    .map(|(offset, key)| (key, base + offset))
                    .collect();
                function.stack_slots += slots.len();
                rewrite_allocation(function, cand.alloc_block, cand.def_block);
                for item in cand.uses {
                    match item {
                        CandidateUse::RecordStore {
                            block,
                            key,
                            value,
                            normal,
                            keep_result,
                        } => {
                            if let Some(&slot) = slots.get(&key) {
                                rewrite_store(function, block, slot, value, normal, keep_result);
                            }
                        }
                        CandidateUse::RecordLoad {
                            block,
                            key,
                            normal,
                            keep_result,
                        } => {
                            if let Some(&slot) = slots.get(&key) {
                                rewrite_load(function, block, slot, normal, keep_result);
                            }
                        }
                        _ => {}
                    }
                }
                let _ = cand.alloc_reg;
                promoted_any = true;
            }
            AllocKind::Tuple | AllocKind::Array | AllocKind::Tag(_) => {
                let Some(appends) = validate_sequence(&cfg, &cand) else {
                    continue;
                };
                let count = appends.len();
                let base = function.stack_slots;
                function.stack_slots += count;
                rewrite_allocation(function, cand.alloc_block, cand.def_block);
                for (index, &(block, value, normal, keep_result)) in appends.iter().enumerate() {
                    rewrite_store(function, block, base + index, value, normal, keep_result);
                }
                for item in cand.uses {
                    match item {
                        CandidateUse::Append { .. } => {}
                        CandidateUse::IndexLoad {
                            block,
                            index,
                            normal,
                            keep_result,
                        } => {
                            rewrite_load(function, block, base + index, normal, keep_result);
                        }
                        CandidateUse::IndexStore {
                            block,
                            index,
                            value,
                            normal,
                            keep_result,
                        } => {
                            rewrite_store(
                                function,
                                block,
                                base + index,
                                value,
                                normal,
                                keep_result,
                            );
                        }
                        CandidateUse::Len {
                            block,
                            normal,
                            keep_result,
                        } => {
                            rewrite_const(
                                function,
                                block,
                                Instruction::Integer(count.to_string().into_bytes().into()),
                                normal,
                                keep_result,
                            );
                        }
                        CandidateUse::IsTag {
                            block,
                            matches,
                            normal,
                            keep_result,
                        } => {
                            rewrite_const(
                                function,
                                block,
                                Instruction::Handle(if matches { 6 } else { 2 }),
                                normal,
                                keep_result,
                            );
                        }
                        _ => {}
                    }
                }
                promoted_any = true;
            }
        }
    }
    promoted_any
}

fn validate_record(cfg: &Cfg, cand: &Candidate) -> bool {
    let mut stores: BTreeMap<&str, Vec<BlockId>> = BTreeMap::new();
    for item in &cand.uses {
        if let CandidateUse::RecordStore { key, normal, .. } = item {
            stores.entry(key.as_str()).or_default().push(*normal);
        }
    }
    for item in &cand.uses {
        if let CandidateUse::RecordLoad { block, key, .. } = item {
            let initialized = stores
                .get(key.as_str())
                .is_some_and(|normals| normals.iter().any(|&normal| cfg.dominates(normal, *block)));
            if !initialized {
                return false;
            }
        }
    }
    true
}

fn validate_sequence(
    cfg: &Cfg,
    cand: &Candidate,
) -> Option<Vec<(BlockId, Register, BlockId, bool)>> {
    let mut appends = Vec::new();
    for item in &cand.uses {
        if let CandidateUse::Append {
            block,
            value,
            normal,
            keep_result,
        } = item
        {
            appends.push((*block, *value, *normal, *keep_result));
        }
    }
    // Order appends by dominance: earlier appends must dominate later ones.
    let mut ordered = Vec::with_capacity(appends.len());
    let mut remaining = appends;
    let mut frontier = cand.def_block;
    while !remaining.is_empty() {
        let next_pos = remaining.iter().position(|&(block, _, normal, _)| {
            cfg.dominates(frontier, block)
                && remaining
                    .iter()
                    .all(|&(other, _, _, _)| other == block || cfg.dominates(normal, other))
        })?;
        let item = remaining.swap_remove(next_pos);
        if cfg.can_reach_avoiding(item.2, item.0, cand.def_block) {
            return None;
        }
        frontier = item.2;
        ordered.push(item);
    }
    let init_end = frontier;
    let count = ordered.len();
    for item in &cand.uses {
        match item {
            CandidateUse::Append { .. } => {}
            CandidateUse::IndexLoad { block, index, .. }
            | CandidateUse::IndexStore { block, index, .. } => {
                if *index >= count || !cfg.dominates(init_end, *block) {
                    return None;
                }
            }
            CandidateUse::Len { block, .. } | CandidateUse::IsTag { block, .. } => {
                if !cfg.dominates(init_end, *block) {
                    return None;
                }
            }
            _ => return None,
        }
    }
    Some(ordered)
}

fn alloc_reg(function: &mut Function) -> Register {
    let id = Register(function.registers);
    function.registers += 1;
    function.reg_types.push(super::MirTy::Any);
    id
}

fn rewrite_allocation(function: &mut Function, alloc_block: BlockId, normal: BlockId) {
    let dummy = alloc_reg(function);
    if let Some(block) = function.blocks.get_mut(alloc_block.0) {
        block.instructions.push((dummy, Instruction::Handle(0)));
        block.terminator = Some(Terminator::Jump(normal, vec![dummy]));
    }
}

fn rewrite_store(
    function: &mut Function,
    block_id: BlockId,
    slot: usize,
    value: Register,
    normal: BlockId,
    keep_result: bool,
) {
    let result = alloc_reg(function);
    if let Some(block) = function.blocks.get_mut(block_id.0) {
        block
            .instructions
            .push((result, Instruction::StackStore { slot, value }));
        let args = if keep_result {
            vec![result]
        } else {
            Vec::new()
        };
        block.terminator = Some(Terminator::Jump(normal, args));
    }
}

fn rewrite_load(
    function: &mut Function,
    block_id: BlockId,
    slot: usize,
    normal: BlockId,
    keep_result: bool,
) {
    let result = alloc_reg(function);
    if let Some(block) = function.blocks.get_mut(block_id.0) {
        block
            .instructions
            .push((result, Instruction::StackLoad(slot)));
        let args = if keep_result {
            vec![result]
        } else {
            Vec::new()
        };
        block.terminator = Some(Terminator::Jump(normal, args));
    }
}

fn rewrite_const(
    function: &mut Function,
    block_id: BlockId,
    instruction: Instruction,
    normal: BlockId,
    keep_result: bool,
) {
    let result = alloc_reg(function);
    if let Some(block) = function.blocks.get_mut(block_id.0) {
        block.instructions.push((result, instruction));
        let args = if keep_result {
            vec![result]
        } else {
            Vec::new()
        };
        block.terminator = Some(Terminator::Jump(normal, args));
    }
}

fn simplify_stack_slots(function: &mut Function) -> bool {
    if function.stack_slots == 0 {
        return false;
    }
    let cfg = Cfg::build(function);
    let mut stores: Vec<Vec<(BlockId, usize, Register)>> = vec![Vec::new(); function.stack_slots];
    let mut loads: Vec<Vec<(BlockId, usize, Register)>> = vec![Vec::new(); function.stack_slots];
    for &block_id in &cfg.order {
        let Some(block) = function.blocks.get(block_id.0) else {
            continue;
        };
        for (index, &(reg, ref inst)) in block.instructions.iter().enumerate() {
            match inst {
                Instruction::StackStore { slot, value } => {
                    if let Some(list) = stores.get_mut(*slot) {
                        list.push((block_id, index, *value));
                    }
                }
                Instruction::StackLoad(slot) => {
                    if let Some(list) = loads.get_mut(*slot) {
                        list.push((block_id, index, reg));
                    }
                }
                _ => {}
            }
        }
    }

    let mut replacements = HashMap::new();
    let mut dead_slots = BTreeSet::new();
    for slot in 0..function.stack_slots {
        let slot_loads = loads.get(slot).map_or(&[][..], Vec::as_slice);
        let slot_stores = stores.get(slot).map_or(&[][..], Vec::as_slice);
        if slot_loads.is_empty() {
            if !slot_stores.is_empty() {
                dead_slots.insert(slot);
            }
            continue;
        }
        if let &[(store_block, store_idx, value)] = slot_stores {
            let all_dominated = slot_loads.iter().all(|&(load_block, load_idx, _)| {
                (store_block == load_block && store_idx < load_idx)
                    || (store_block != load_block && cfg.dominates(store_block, load_block))
            });
            if all_dominated {
                for &(_, _, reg) in slot_loads {
                    replacements.insert(reg, value);
                }
                dead_slots.insert(slot);
            }
        }
    }
    if replacements.is_empty() && dead_slots.is_empty() {
        return false;
    }
    if !replacements.is_empty() {
        substitute_registers(function, &replacements);
    }
    for block in &mut function.blocks {
        block.instructions.retain(|(reg, inst)| {
            if replacements.contains_key(reg) {
                return false;
            }
            match inst {
                Instruction::StackStore { slot, .. } | Instruction::StackLoad(slot) => {
                    !dead_slots.contains(slot)
                }
                _ => true,
            }
        });
    }
    true
}

fn coalesce_blocks(function: &mut Function) -> bool {
    let n = function.blocks.len();
    if n <= 1 {
        return false;
    }
    // Compute reachability and predecessor counts once in O(B + E).
    let mut reachable = vec![false; n];
    let mut pred_count = vec![0usize; n];
    let mut stack = vec![BlockId(0)];
    if let Some(slot) = reachable.first_mut() {
        *slot = true;
    }
    while let Some(id) = stack.pop() {
        let Some(block) = function.blocks.get(id.0) else {
            continue;
        };
        let Some(term) = &block.terminator else {
            continue;
        };
        let succs: Vec<BlockId> = match term {
            Terminator::Unreachable | Terminator::Return(_) => Vec::new(),
            Terminator::Jump(target, _) => vec![*target],
            Terminator::Branch { yes, no, .. } => vec![*yes, *no],
            Terminator::Invoke { normal, unwind, .. } => {
                if normal == unwind {
                    vec![*normal]
                } else {
                    vec![*normal, *unwind]
                }
            }
        };
        for succ in succs {
            if let Some(count) = pred_count.get_mut(succ.0) {
                *count += 1;
            }
            if let Some(seen) = reachable.get_mut(succ.0)
                && !*seen
            {
                *seen = true;
                stack.push(succ);
            }
        }
    }

    let mut merged = vec![false; n];
    let mut subst: HashMap<Register, Register> = HashMap::new();
    let mut changed_any = false;

    for idx in 0..n {
        if !reachable.get(idx).copied().unwrap_or(false)
            || merged.get(idx).copied().unwrap_or(false)
        {
            continue;
        }
        while let Some(Terminator::Jump(target, args)) = function
            .blocks
            .get(idx)
            .and_then(|block| block.terminator.as_ref())
        {
            let (target, args) = (*target, args.clone());
            if target.0 == 0
                || target.0 == idx
                || target.0 >= n
                || merged.get(target.0).copied().unwrap_or(false)
                || pred_count.get(target.0).copied().unwrap_or(0) != 1
            {
                break;
            }
            let same_arity = function
                .blocks
                .get(target.0)
                .is_some_and(|tb| tb.params.len() == args.len());
            if !same_arity {
                break;
            }
            let (params, mut instructions, terminator) = {
                let Some(target_block) = function.blocks.get_mut(target.0) else {
                    break;
                };
                (
                    std::mem::take(&mut target_block.params),
                    std::mem::take(&mut target_block.instructions),
                    target_block.terminator.take(),
                )
            };
            if let Some(from_block) = function.blocks.get_mut(idx) {
                from_block.instructions.append(&mut instructions);
                from_block.terminator = terminator;
            }
            for (param, arg) in params.into_iter().zip(args) {
                let resolved = resolve_reg(&subst, arg);
                subst.insert(param, resolved);
            }
            if let Some(slot) = merged.get_mut(target.0) {
                *slot = true;
            }
            changed_any = true;
        }
    }

    if !subst.is_empty() {
        substitute_registers(function, &subst);
    }
    changed_any
}

fn compact_stack_slots(function: &mut Function) {
    if function.stack_slots == 0 {
        return;
    }
    let order = function.rpo();
    let mut remap = BTreeMap::new();
    for &block_id in &order {
        let Some(block) = function.blocks.get_mut(block_id.0) else {
            continue;
        };
        for (_, inst) in &mut block.instructions {
            match inst {
                Instruction::StackLoad(slot) | Instruction::StackStore { slot, .. } => {
                    let next = remap.len();
                    *slot = *remap.entry(*slot).or_insert(next);
                }
                _ => {}
            }
        }
    }
    function.stack_slots = remap.len();
}

fn resolve_reg(map: &HashMap<Register, Register>, mut reg: Register) -> Register {
    while let Some(&next) = map.get(&reg) {
        if next == reg {
            break;
        }
        reg = next;
    }
    reg
}

fn substitute_registers(function: &mut Function, map: &HashMap<Register, Register>) {
    for block in &mut function.blocks {
        for (_, inst) in &mut block.instructions {
            inst.remap_reads(|reg| *reg = resolve_reg(map, *reg));
        }
        if let Some(term) = &mut block.terminator {
            term.remap_reads(|reg| *reg = resolve_reg(map, *reg));
        }
    }
}
