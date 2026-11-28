mod builtins;
mod calls;
mod closures;
mod control;
mod slice;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use ril_sema::{
    access::Analysis,
    hir::{DefinitionId, DefinitionKind, Resolution},
    syntax::{
        Argument, Ast, Expr, ExprId, Function as SyntaxFunction, Handler, Member, Name, Pattern,
        PatternId, StmtId, StmtKind, StringPart, Transfer,
    },
    ty::{self, Ty, TypedProgram, Value},
};
use ril_source::{
    diag::Diagnostic,
    span::{FileId, Span},
};

use super::{
    Block, BlockId, DraftOp, Function, FunctionId, Instruction, IntBinOp, IntLowering, IntUnaryOp,
    ManagedInt, MirTy, Program, Register, SourceLocEntry, Target, Terminator,
};

type Result<T> = std::result::Result<T, Diagnostic>;
type Locals = BTreeMap<DefinitionId, Register>;

enum NativeBody<'a> {
    Expression(ExprId),
    Statements(Vec<StmtId>),
    CtlArmAdapter {
        op_arity: usize,
        abort_k_first: bool,
        omit_k: bool,
    },
    Accessor(&'a [(bool, Member)]),
    Constructor(&'a str, usize),
    Primitive(&'static str, usize),
}

pub(super) fn lower(typed: &TypedProgram, _analysis: &Analysis) -> Result<Program> {
    let file = typed.hir.entry;
    let entry = typed
        .hir
        .definitions()
        .find(|(_, def)| {
            def.name.value == "main"
                && def.name.span.file == file
                && def.kind == DefinitionKind::Function
        })
        .map(|(id, _)| id)
        .ok_or_else(|| Diagnostic::unsupported("native lowering requires an executable entry"))?;
    let mut lowering = Lowering {
        typed,
        queued: Vec::new(),
        named_index: HashMap::new(),
        ctor_index: HashMap::new(),
        prim_index: HashMap::new(),
        closure_index: HashMap::new(),
        defer_index: HashMap::new(),
        stmt_thunk_index: HashMap::new(),
        adapter_index: HashMap::new(),
        used_symbols: HashSet::new(),
        source_locs: Vec::new(),
        effect_ops: HashMap::new(),
        top_level_fns: collect_top_level_functions(typed),
        boxed: captured_slots(typed),
    };
    let entry = lowering.queue(Work::Named(
        entry,
        BTreeMap::new(),
        Vec::new(),
        BTreeMap::new(),
    ));
    let mut functions = Vec::new();
    while let Some(work) = lowering.queued.get(functions.len()).cloned() {
        functions.push(lowering.function(work)?);
    }
    Ok(Program {
        entry,
        functions,
        source_locs: lowering.source_locs,
    })
}

fn collect_top_level_functions(typed: &TypedProgram) -> HashSet<DefinitionId> {
    fn walk_items(
        typed: &TypedProgram,
        ast: &Ast,
        items: &[StmtId],
        out: &mut HashSet<DefinitionId>,
    ) {
        for &stmt_id in items {
            match &ast.stmt(stmt_id).value.kind {
                StmtKind::Function(fun) => {
                    if let Some(Resolution::Definition(id)) = typed.hir.resolve(fun.name.span) {
                        out.insert(id);
                    }
                }
                StmtKind::Sub { items, .. } => walk_items(typed, ast, items, out),
                _ => {}
            }
        }
    }

    let mut out = HashSet::new();
    for file in typed.hir.files() {
        walk_items(typed, &file.ast, &file.ast.items, &mut out);
    }
    out
}

fn captured_slots(typed: &TypedProgram) -> BTreeSet<DefinitionId> {
    typed.boxed_var_captures.clone()
}

struct Lowering<'a> {
    typed: &'a TypedProgram,
    queued: Vec<Work>,
    named_index: HashMap<DefinitionId, Vec<FunctionId>>,
    ctor_index: HashMap<(DefinitionId, usize), FunctionId>,
    prim_index: HashMap<DefinitionId, FunctionId>,
    closure_index: HashMap<(FileId, ExprId), Vec<FunctionId>>,
    defer_index: HashMap<(FileId, ExprId), Vec<FunctionId>>,
    stmt_thunk_index: HashMap<(FileId, Span), Vec<FunctionId>>,
    adapter_index: HashMap<(usize, bool, bool), FunctionId>,
    used_symbols: HashSet<String>,
    source_locs: Vec<SourceLocEntry>,
    effect_ops: HashMap<String, u64>,
    top_level_fns: HashSet<DefinitionId>,
    boxed: BTreeSet<DefinitionId>,
}

#[derive(Clone, PartialEq)]
enum Work {
    Constructor(DefinitionId, usize),
    Primitive(DefinitionId, &'static str, usize),
    Named(
        DefinitionId,
        BTreeMap<DefinitionId, Ty>,
        Vec<DefinitionId>,
        BTreeMap<DefinitionId, Value>,
    ),
    Closure {
        file: FileId,
        syntax: ExprId,
        captures: Vec<DefinitionId>,
        types: BTreeMap<DefinitionId, Ty>,
        statics: BTreeMap<DefinitionId, Value>,
        tail_resume_k: Option<DefinitionId>,
    },
    DeferThunk {
        file: FileId,
        syntax: ExprId,
        captures: Vec<DefinitionId>,
        types: BTreeMap<DefinitionId, Ty>,
        statics: BTreeMap<DefinitionId, Value>,
    },
    StmtThunk {
        file: FileId,
        statements: Vec<StmtId>,
        span: Span,
        captures: Vec<DefinitionId>,
        types: BTreeMap<DefinitionId, Ty>,
        statics: BTreeMap<DefinitionId, Value>,
    },
    CtlArmAdapter {
        op_arity: usize,
        abort_k_first: bool,
        omit_k: bool,
    },
}

impl<'a> Lowering<'a> {
    fn effect_op_id(&mut self, label: &str) -> u64 {
        if let Some(&id) = self.effect_ops.get(label) {
            return id;
        }
        let id = (self.effect_ops.len() as u64) + 1;
        self.effect_ops.insert(label.to_owned(), id);
        id
    }

    fn queue(&mut self, work: Work) -> FunctionId {
        match &work {
            Work::Constructor(id, arity) => {
                if let Some(&func) = self.ctor_index.get(&(*id, *arity)) {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.ctor_index.insert((*id, *arity), function);
                self.queued.push(work);
                function
            }
            Work::Primitive(id, _, _) => {
                if let Some(&func) = self.prim_index.get(id) {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.prim_index.insert(*id, function);
                self.queued.push(work);
                function
            }
            Work::Named(id, _, _, _) => {
                let id = *id;
                if let Some(bucket) = self.named_index.get(&id)
                    && let Some(&func) = bucket
                        .iter()
                        .find(|&&f| self.queued.get(f.0) == Some(&work))
                {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.queued.push(work);
                self.named_index.entry(id).or_default().push(function);
                function
            }
            Work::Closure { file, syntax, .. } => {
                let key = (*file, *syntax);
                if let Some(bucket) = self.closure_index.get(&key)
                    && let Some(&func) = bucket
                        .iter()
                        .find(|&&f| self.queued.get(f.0) == Some(&work))
                {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.queued.push(work);
                self.closure_index.entry(key).or_default().push(function);
                function
            }
            Work::DeferThunk { file, syntax, .. } => {
                let key = (*file, *syntax);
                if let Some(bucket) = self.defer_index.get(&key)
                    && let Some(&func) = bucket
                        .iter()
                        .find(|&&f| self.queued.get(f.0) == Some(&work))
                {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.queued.push(work);
                self.defer_index.entry(key).or_default().push(function);
                function
            }
            Work::StmtThunk { file, span, .. } => {
                let key = (*file, *span);
                if let Some(bucket) = self.stmt_thunk_index.get(&key)
                    && let Some(&func) = bucket
                        .iter()
                        .find(|&&f| self.queued.get(f.0) == Some(&work))
                {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.queued.push(work);
                self.stmt_thunk_index.entry(key).or_default().push(function);
                function
            }
            Work::CtlArmAdapter {
                op_arity,
                abort_k_first,
                omit_k,
            } => {
                let key = (*op_arity, *abort_k_first, *omit_k);
                if let Some(&func) = self.adapter_index.get(&key) {
                    return func;
                }
                let function = FunctionId(self.queued.len());
                self.queued.push(work);
                self.adapter_index.insert(key, function);
                function
            }
        }
    }

    fn resolve(&self, span: Span) -> Option<DefinitionId> {
        self.typed
            .hir
            .resolve(span)
            .and_then(Resolution::definition)
    }

    fn declaration(&self, id: DefinitionId) -> Option<&'a SyntaxFunction> {
        let def = self.typed.hir.definition(id);
        let stmt = def.stmt?;
        let ast = &self.typed.hir.file(def.name.span.file).ast;
        match &ast.stmt(stmt).value.kind {
            StmtKind::Function(func) => Some(func),
            _ => None,
        }
    }

    fn mangle_symbol(
        &mut self,
        kind: &str,
        name: &str,
        arity: usize,
        types: &BTreeMap<DefinitionId, Ty>,
        statics: &BTreeMap<DefinitionId, Value>,
        captures: &[DefinitionId],
    ) -> String {
        use std::fmt::Write as _;
        let mut canonical = String::new();
        let _ = write!(canonical, "{kind}\0{name}\0arity={arity}");
        for (def, ty) in types {
            let _ = write!(
                canonical,
                "\0T:{}={}",
                self.typed.hir.definition(*def).name.value,
                ty.qualified_display(&self.typed.hir)
            );
        }
        for (def, val) in statics {
            let _ = write!(
                canonical,
                "\0S:{}={val:?}",
                self.typed.hir.definition(*def).name.value
            );
        }
        for cap in captures {
            let def = self.typed.hir.definition(*cap);
            let _ = write!(canonical, "\0C:{}@{}", def.name.value, def.name.span.start);
        }
        let mut h1: u64 = 0xcbf2_9ce4_8422_2325;
        let mut h2: u64 = 0x8422_2325_cbf2_9ce4;
        for &byte in canonical.as_bytes() {
            h1 ^= u64::from(byte);
            h1 = h1.wrapping_mul(0x0100_0000_01b3);
            h2 = h2.wrapping_mul(0x0100_0000_01b3);
            h2 ^= u64::from(byte).wrapping_add(0x9e37_79b9);
        }
        let mut sanitized = String::new();
        let mut prev_underscore = false;
        for ch in name.chars() {
            if ch.is_ascii_alphanumeric() {
                sanitized.push(ch);
                prev_underscore = false;
            } else if !prev_underscore && !sanitized.is_empty() {
                sanitized.push('_');
                prev_underscore = true;
            }
            if sanitized.len() >= 48 {
                break;
            }
        }
        let trimmed = sanitized.trim_matches('_');
        let stem = if trimmed.is_empty() { "fn" } else { trimmed };
        let base = format!("_Ril_{stem}_{h1:08x}{h2:08x}");
        if self.used_symbols.insert(base.clone()) {
            return base;
        }
        let mut suffix = 2usize;
        loop {
            let candidate = format!("{base}__{suffix}");
            if self.used_symbols.insert(candidate.clone()) {
                return candidate;
            }
            suffix += 1;
        }
    }

    fn record_source_loc(&mut self, span: Span) -> Option<u32> {
        if span.file == FileId::BUILTIN {
            return None;
        }
        let file = self.typed.hir.file(span.file);
        let loc = file.source().location(span.start)?;
        let id = u32::try_from(self.source_locs.len() + 1).ok()?;
        self.source_locs.push(SourceLocEntry {
            id,
            file: file.path.display().to_string(),
            line: u32::try_from(loc.line).unwrap_or(u32::MAX),
            column: u32::try_from(loc.column).unwrap_or(u32::MAX),
        });
        Some(id)
    }

    fn function(&mut self, work: Work) -> Result<Function> {
        let mut tail_resume_k = None;
        let (kind_tag, fn_span, file, name, body, params, guards, captures, types, statics) =
            match work {
                Work::Constructor(id, arity) => {
                    let def = self.typed.hir.definition(id);
                    (
                        "ctor",
                        def.name.span,
                        def.name.span.file,
                        self.typed.hir.export_name(id),
                        NativeBody::Constructor(&def.name.value, arity),
                        &[][..],
                        Vec::new(),
                        Vec::new(),
                        BTreeMap::new(),
                        BTreeMap::new(),
                    )
                }
                Work::Primitive(id, symbol, arity) => {
                    let def = self.typed.hir.definition(id);
                    (
                        "prim",
                        def.name.span,
                        def.name.span.file,
                        self.typed.hir.export_name(id),
                        NativeBody::Primitive(symbol, arity),
                        &[][..],
                        Vec::new(),
                        Vec::new(),
                        BTreeMap::new(),
                        BTreeMap::new(),
                    )
                }
                Work::Named(id, types, captures, statics) => {
                    let f = self.declaration(id).ok_or_else(|| {
                        Diagnostic::unsupported("missing native function definition")
                    })?;
                    let body = if let Some(body) = f.body {
                        NativeBody::Expression(body)
                    } else {
                        return Err(Diagnostic::unsupported(format!(
                            "native code for {} is required",
                            self.typed.hir.export_name(id)
                        )));
                    };
                    (
                        "fn",
                        f.name.span,
                        f.name.span.file,
                        self.typed.hir.export_name(id),
                        body,
                        f.signature.params.as_slice(),
                        f.signature
                            .guards
                            .iter()
                            .copied()
                            .filter(|&g| !self.typed.hir.is_static_proof_guard(f.name.span.file, g))
                            .collect(),
                        captures,
                        types,
                        statics,
                    )
                }
                Work::Closure {
                    file,
                    syntax,
                    captures,
                    types,
                    statics,
                    tail_resume_k: tr_k,
                } => {
                    tail_resume_k = tr_k;
                    let ast = &self.typed.hir.file(file).ast;
                    let node = ast.expr(syntax);
                    let (body, params) = match &node.value {
                        Expr::Closure { params, body, .. } => {
                            (NativeBody::Expression(*body), params.as_slice())
                        }
                        Expr::Accessor(path) => (NativeBody::Accessor(path), &[][..]),
                        _ => return Err(Diagnostic::unsupported("invalid closure body")),
                    };
                    let tag = if tr_k.is_some() {
                        "tail_ctl_closure"
                    } else {
                        "closure"
                    };
                    (
                        tag,
                        node.span,
                        file,
                        format!(
                            "{}:{tag}@{}",
                            self.typed.hir.file(file).path.display(),
                            node.span.start
                        ),
                        body,
                        params,
                        Vec::new(),
                        captures,
                        types,
                        statics,
                    )
                }
                Work::DeferThunk {
                    file,
                    syntax,
                    captures,
                    types,
                    statics,
                } => {
                    let span = self.typed.hir.file(file).ast.expr(syntax).span;
                    (
                        "defer",
                        span,
                        file,
                        format!(
                            "{}:defer@{}",
                            self.typed.hir.file(file).path.display(),
                            span.start
                        ),
                        NativeBody::Expression(syntax),
                        &[][..],
                        Vec::new(),
                        captures,
                        types,
                        statics,
                    )
                }
                Work::StmtThunk {
                    file,
                    statements,
                    span,
                    captures,
                    types,
                    statics,
                } => (
                    "ctl_body",
                    span,
                    file,
                    format!(
                        "{}:ctl_body@{}",
                        self.typed.hir.file(file).path.display(),
                        span.start
                    ),
                    NativeBody::Statements(statements),
                    &[][..],
                    Vec::new(),
                    captures,
                    types,
                    statics,
                ),
                Work::CtlArmAdapter {
                    op_arity,
                    abort_k_first,
                    omit_k,
                } => (
                    "ctl_arm",
                    Span::new(FileId::BUILTIN, 0, 0),
                    self.typed.hir.entry,
                    format!("ctl_arm_adapter_{op_arity}_{abort_k_first}_{omit_k}"),
                    NativeBody::CtlArmAdapter {
                        op_arity,
                        abort_k_first,
                        omit_k,
                    },
                    &[][..],
                    Vec::new(),
                    Vec::new(),
                    BTreeMap::new(),
                    BTreeMap::new(),
                ),
            };
        let params: Vec<_> = params.iter().filter(|param| !param.is_meta).collect();
        let arity = match body {
            NativeBody::Accessor(_) => 1,
            NativeBody::CtlArmAdapter { .. } => 2,
            NativeBody::Constructor(_, arity) | NativeBody::Primitive(_, arity) => arity,
            _ => params.len(),
        };
        let symbol = self.mangle_symbol(kind_tag, &name, arity, &types, &statics, &captures);
        let source_loc = self.record_source_loc(fn_span);
        let mut builder = Builder {
            global: self,
            file,
            function: Function {
                name,
                symbol,
                source_loc,
                arity,
                registers: 0,
                reg_types: Vec::new(),
                stack_slots: 0,
                blocks: Vec::new(),
            },
            current: None,
            locals: BTreeMap::new(),
            scopes: Vec::new(),
            pads: HashMap::new(),
            traps: Vec::new(),
            loops: Vec::new(),
            types,
            statics,
            guards,
            running_guard: false,
            tail_resume_k,
        };
        let entry = builder.block(arity);
        builder.current = Some(entry);
        let fail = builder.block(0);
        let fail_value = builder.instruction_at(fail, Instruction::Handle(0));
        builder.term_at(fail, Terminator::Return(fail_value));
        builder.traps.push((0, fail));
        if !captures.is_empty() {
            let environment = builder.instruction(Instruction::Environment);
            for (index, id) in captures.into_iter().enumerate() {
                let index = builder.integer(&index.to_string());
                let value = builder.runtime("ril_rt_load", vec![environment, index]);
                builder.locals.insert(id, value);
            }
        }
        for (param, value) in params.iter().zip(builder.params(entry)) {
            if let Some(pattern) = param.pattern {
                builder.bind(pattern, value)?;
            } else if let Some(name) = &param.name {
                builder.bind_name(name, value);
            }
        }
        for (param, value) in params.iter().zip(builder.params(entry)) {
            for &guard in &param.guards {
                if !builder.global.typed.hir.is_static_proof_guard(file, guard) {
                    builder.run_guard(guard, value)?;
                }
            }
        }
        let result = match body {
            NativeBody::Expression(body) => builder.expr(body)?,
            NativeBody::Statements(statements) => builder.lower_statements(&statements)?,
            NativeBody::CtlArmAdapter {
                op_arity,
                abort_k_first,
                omit_k,
            } => {
                let entry_params = builder.params(entry);
                let args_tuple = entry_params
                    .first()
                    .copied()
                    .unwrap_or_else(|| builder.unit());
                let k = entry_params
                    .get(1)
                    .copied()
                    .unwrap_or_else(|| builder.unit());
                let env = builder.instruction(Instruction::Environment);
                let zero = builder.integer("0");
                let handler = builder.runtime("ril_rt_load", vec![env, zero]);
                let mut call_args = Vec::with_capacity(op_arity + usize::from(!omit_k));
                for index in 0..op_arity {
                    let idx = builder.integer(&index.to_string());
                    call_args.push(builder.runtime("ril_rt_load", vec![args_tuple, idx]));
                }
                if !omit_k {
                    call_args.push(if abort_k_first { builder.unit() } else { k });
                }
                builder.invoke_closure(handler, call_args)
            }
            NativeBody::Accessor(path) => {
                let value = builder.result_param(entry);
                builder.project_path(path, value)?
            }
            NativeBody::Constructor(tag, _) => builder.tag(tag, builder.params(entry)),
            NativeBody::Primitive(symbol, _) => builder.runtime(symbol, builder.params(entry)),
        };
        if builder.current.is_some() {
            builder.return_value(result)?;
        }
        Ok(builder.function)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum ScopeAction {
    PopHandler,
    LeaveFnHandler,
    Defer {
        function: FunctionId,
        environment: Register,
    },
}

#[derive(Clone)]
struct Loop {
    header: BlockId,
    exit: BlockId,
    names: Vec<DefinitionId>,
    scopes: usize,
    counter: Option<Register>,
}

struct Builder<'b, 'a> {
    global: &'b mut Lowering<'a>,
    file: FileId,
    function: Function,
    current: Option<BlockId>,
    locals: Locals,
    scopes: Vec<ScopeAction>,
    pads: HashMap<(BlockId, Vec<ScopeAction>), BlockId>,
    traps: Vec<(usize, BlockId)>,
    loops: Vec<Loop>,
    types: BTreeMap<DefinitionId, Ty>,
    statics: BTreeMap<DefinitionId, Value>,
    guards: Vec<ExprId>,
    running_guard: bool,
    tail_resume_k: Option<DefinitionId>,
}

impl<'a> Builder<'_, 'a> {
    fn ast(&self) -> &'a Ast {
        &self.global.typed.hir.file(self.file).ast
    }

    fn register(&mut self) -> Register {
        self.register_typed(MirTy::Any)
    }

    fn register_typed(&mut self, ty: MirTy) -> Register {
        let id = self.function.registers;
        self.function.registers += 1;
        self.function.reg_types.push(ty);
        Register(id)
    }

    fn block(&mut self, count: usize) -> BlockId {
        let id = BlockId(self.function.blocks.len());
        let params = (0..count).map(|_| self.register()).collect();
        self.function.blocks.push(Block {
            params,
            ..Block::default()
        });
        id
    }

    fn params(&self, block: BlockId) -> Vec<Register> {
        self.function
            .blocks
            .get(block.0)
            .unwrap_or_else(|| ril_source::ice!("invalid MIR block"))
            .params
            .clone()
    }

    fn instruction_ty(instruction: &Instruction) -> MirTy {
        match instruction {
            Instruction::Handle(0) | Instruction::StackStore { .. } => MirTy::Unit,
            Instruction::Handle(2 | 6) | Instruction::BoolNot(_) => MirTy::Bool,
            Instruction::Handle(_) => MirTy::Any,
            Instruction::ConstSmallInt(_) => MirTy::SmallInt,
            Instruction::RawU64(_) => MirTy::RawU64,
            Instruction::FunctionAddress(_) => MirTy::RawFnPtr,
            Instruction::Environment => MirTy::Obj,
            Instruction::Integer(_) => MirTy::Int,
            Instruction::Float(_) => MirTy::F64,
            Instruction::Text(_) => MirTy::Str,
            Instruction::Bytes(_) => MirTy::Bytes,
            Instruction::IntBinOp { op, .. } => op.result_ty(),
            Instruction::IntUnaryOp { .. } | Instruction::StackLoad(_) => MirTy::Any,
        }
    }

    fn instruction_at(&mut self, block: BlockId, instruction: Instruction) -> Register {
        let value = self.register_typed(Self::instruction_ty(&instruction));
        self.function
            .blocks
            .get_mut(block.0)
            .unwrap_or_else(|| ril_source::ice!("invalid MIR block"))
            .instructions
            .push((value, instruction));
        value
    }

    fn instruction(&mut self, instruction: Instruction) -> Register {
        if let Some(block) = self.current {
            self.instruction_at(block, instruction)
        } else {
            self.register_typed(Self::instruction_ty(&instruction))
        }
    }

    fn term_at(&mut self, block: BlockId, term: Terminator) {
        self.function
            .blocks
            .get_mut(block.0)
            .unwrap_or_else(|| ril_source::ice!("invalid MIR block"))
            .terminator = Some(term);
    }

    fn terminate(&mut self, term: Terminator) {
        if let Some(block) = self.current.take() {
            self.term_at(block, term);
        }
    }

    fn unit(&mut self) -> Register {
        self.instruction(Instruction::Handle(0))
    }

    fn boolean(&mut self, value: bool) -> Register {
        self.instruction(Instruction::Handle(if value { 6 } else { 2 }))
    }

    fn string(&mut self, value: &str) -> Register {
        self.instruction(Instruction::Text(value.as_bytes().into()))
    }

    fn integer(&mut self, value: &str) -> Register {
        if let Ok(number) = value.parse::<i64>()
            && ((i64::MIN >> 1)..=(i64::MAX >> 1)).contains(&number)
        {
            return self.instruction(Instruction::ConstSmallInt(number));
        }
        self.instruction(Instruction::Integer(value.as_bytes().into()))
    }

    fn unsupported(&self, span: Span, feature: &str) -> Diagnostic {
        Diagnostic::unsupported_at(span, format!("native lowering does not support {feature}"))
    }

    fn invoke(&mut self, target: Target, arguments: Vec<Register>, cleanup: bool) -> Register {
        let Some(block) = self.current else {
            return self.register();
        };
        let normal = self.block(1);
        let unwind = self.unwind_pad();
        self.term_at(
            block,
            Terminator::Invoke {
                target,
                arguments,
                normal,
                unwind,
                cleanup,
                keep_result: true,
            },
        );
        self.current = Some(normal);
        self.params(normal)
            .first()
            .copied()
            .unwrap_or_else(|| ril_source::ice!("invoke normal block has no result param"))
    }

    fn runtime(&mut self, symbol: &'static str, arguments: Vec<Register>) -> Register {
        let result = self.invoke(Target::Runtime(symbol), arguments, false);
        if symbol == "ril_rt_closure_address"
            && let Some(ty) = self.function.reg_types.get_mut(result.0)
        {
            *ty = MirTy::RawFnPtr;
        }
        result
    }

    fn draft(&mut self, operation: DraftOp, arguments: Vec<Register>) -> Register {
        self.invoke(Target::Draft(operation), arguments, false)
    }

    fn is_draft(&self, expression: ExprId) -> bool {
        matches!(
            self.global
                .typed
                .types
                .get(&self.ast().expr(expression).span),
            Some(Ty::Draft(_))
        )
    }

    fn collection(&mut self, expression: ExprId) -> Result<Register> {
        let handle = self.expr(expression)?;
        if self.is_draft(expression) {
            Ok(self.draft(DraftOp::Read, vec![handle]))
        } else {
            Ok(handle)
        }
    }

    fn unwind_pad(&mut self) -> BlockId {
        let &(depth, end) = self
            .traps
            .last()
            .unwrap_or_else(|| ril_source::ice!("native function has no panic target"));
        let scopes = self.scopes.get(depth..).unwrap_or_default().to_vec();
        if let Some(&block) = self.pads.get(&(end, scopes.clone())) {
            return block;
        }
        let mut next = end;
        for action in &scopes {
            let block = self.block(0);
            let (target, cleanup) = match *action {
                ScopeAction::PopHandler => (Target::Runtime("ril_rt_handler_pop"), false),
                ScopeAction::LeaveFnHandler => (Target::Runtime("ril_rt_handler_leave_fn"), false),
                ScopeAction::Defer {
                    function,
                    environment,
                } => (
                    Target::FunctionWithEnv {
                        function,
                        environment,
                    },
                    true,
                ),
            };
            self.term_at(
                block,
                Terminator::Invoke {
                    target,
                    arguments: Vec::new(),
                    normal: next,
                    unwind: next,
                    cleanup,
                    keep_result: false,
                },
            );
            next = block;
        }
        self.pads.insert((end, scopes), next);
        next
    }

    fn unwind_scopes_to(&mut self, depth: usize) {
        while self.scopes.len() > depth {
            if let Some(action) = self.scopes.pop() {
                match action {
                    ScopeAction::PopHandler => {
                        self.runtime("ril_rt_handler_pop", Vec::new());
                    }
                    ScopeAction::LeaveFnHandler => {
                        self.runtime("ril_rt_handler_leave_fn", Vec::new());
                    }
                    ScopeAction::Defer {
                        function,
                        environment,
                    } => {
                        self.invoke(
                            Target::FunctionWithEnv {
                                function,
                                environment,
                            },
                            Vec::new(),
                            false,
                        );
                    }
                }
            }
        }
    }

    fn expr(&mut self, id: ExprId) -> Result<Register> {
        let span = self.ast().expr(id).span;
        let depth = self
            .global
            .typed
            .narrowings
            .get(&span)
            .copied()
            .unwrap_or_default();
        let mut value = self.expr_impl(id)?;
        if self
            .global
            .typed
            .types
            .get(&span)
            .is_some_and(|ty| self.concrete(ty) == Ty::Never)
        {
            self.terminate(Terminator::Unreachable);
            return Ok(value);
        }
        for _ in 0..depth {
            let zero = self.integer("0");
            value = self.runtime("ril_rt_load", vec![value, zero]);
        }
        Ok(value)
    }

    fn expr_impl(&mut self, id: ExprId) -> Result<Register> {
        if self.current.is_none() {
            return Ok(self.register());
        }
        let node = self.ast().expr(id);
        let span = node.span;
        if let Some(constant) = self
            .global
            .typed
            .static_value(span, &self.statics, &self.types)?
            && !matches!(constant, Value::Type(_))
        {
            return self.constant(&constant, span);
        }
        if let Some((base, steps)) = self.ast().navigation_chain(id) {
            return self.navigation(base, &steps, span);
        }
        match &node.value {
            Expr::Unit => Ok(self.unit()),
            Expr::Closure { .. } | Expr::Accessor(_) => self.lift(id, None),
            Expr::Literal(literal) => self.constant(
                &ty::literal(literal).map_err(|_| self.unsupported(span, "malformed literal"))?,
                span,
            ),
            Expr::Path(path) => {
                let def = self
                    .global
                    .resolve(path.span)
                    .ok_or_else(|| self.unsupported(span, "namespace as a value"))?;
                self.read(def, span)
            }
            Expr::Block { statements, .. } => self.lower_statements(statements),
            Expr::With {
                handlers,
                statements,
                ..
            } => {
                if handlers.iter().any(|h| h.is_ctl) {
                    self.lower_with_ctl(handlers, statements, span)
                } else {
                    let entries = self.encode_fn_frame(handlers, span)?;
                    let scope_depth = self.scopes.len();
                    let names: Vec<_> = self.locals.keys().copied().collect();
                    self.runtime("ril_rt_handler_push_fn_frame", vec![entries]);
                    self.scopes.push(ScopeAction::PopHandler);
                    let result = self.lower_statements(statements)?;
                    self.unwind_scopes_to(scope_depth);
                    self.locals
                        .retain(|&name, _| names.binary_search(&name).is_ok());
                    Ok(result)
                }
            }
            Expr::Unary { op, value } => {
                let value = self.expr(*value)?;
                match op.value.as_str() {
                    "new" | "ref" | "^mut" => Ok(value),
                    "?" => self.propagate(value),
                    "!" => Ok(self.instruction(Instruction::BoolNot(value))),
                    "-" => Ok(self.instruction(Instruction::IntUnaryOp {
                        op: IntUnaryOp::Neg,
                        value,
                    })),
                    "~" => Ok(self.instruction(Instruction::IntUnaryOp {
                        op: IntUnaryOp::BitNot,
                        value,
                    })),
                    op => ManagedInt
                        .unary(op)
                        .map(|symbol| self.runtime(symbol, vec![value]))
                        .ok_or_else(|| self.unsupported(span, "unary operator")),
                }
            }
            Expr::Binary { op, left, right } => self.binary(op, *left, *right),
            Expr::Call { callee, args } => self.call(*callee, args, span),
            Expr::Wrap { path, args } => self.wrap(path, args, span),
            Expr::Pipeline {
                value,
                pipe_span,
                mode,
                mode_span,
                target,
                propagate,
            } => {
                let mut arguments = vec![Argument {
                    value: *value,
                    mode: *mode,
                    mode_span: *mode_span,
                    pipe_span: Some(*pipe_span),
                    name: None,
                }];
                let callee = if let Expr::Call { callee, args } = &self.ast().expr(*target).value {
                    arguments.extend(args.iter().cloned());
                    *callee
                } else {
                    *target
                };
                let value = self.call(callee, &arguments, span)?;
                if *propagate {
                    self.propagate(value)
                } else {
                    Ok(value)
                }
            }
            Expr::Cast { value, .. } => self.expr(*value),
            Expr::If {
                is_meta,
                condition,
                yes,
                no,
            } => self.conditional(*is_meta, condition, *yes, *no, span),
            Expr::While { condition, body } => self.while_loop(condition, *body),
            Expr::For {
                iterable,
                pattern,
                body,
                ..
            } => self.for_loop(*iterable, *pattern, *body),
            Expr::Match {
                is_meta,
                value,
                arms,
                ..
            } => self.match_expr(*is_meta, *value, arms, span),
            Expr::Transfer { kind, value } => {
                match kind {
                    Transfer::Return => {
                        let value = if let Some(value) = value {
                            self.expr(*value)?
                        } else {
                            self.unit()
                        };
                        self.return_value(value)?;
                    }
                    Transfer::Continue | Transfer::Break => self.loop_transfer(*kind, span)?,
                }
                Ok(self.register())
            }
            Expr::Record { name, fields } => {
                let record = self.runtime("ril_rt_record", Vec::new());
                let mut provided = BTreeMap::new();
                for field in fields {
                    let key = self.string(&field.name.value);
                    let value = if let Some(value) = field.value {
                        self.expr(value)?
                    } else {
                        let def = self
                            .global
                            .resolve(field.name.span)
                            .ok_or_else(|| self.unsupported(field.name.span, "record shorthand"))?;
                        self.read(def, field.name.span)?
                    };
                    self.runtime("ril_rt_store", vec![record, key, value]);
                    provided.insert(field.name.value.clone(), value);
                }
                if let Some(name) = name {
                    self.defaults(name, record, &provided)?;
                }
                Ok(record)
            }
            Expr::Array(items) | Expr::Tuple(items) => {
                let symbol = if matches!(node.value, Expr::Array(_)) {
                    "ril_rt_array"
                } else {
                    "ril_rt_tuple"
                };
                let list = self.runtime(symbol, Vec::new());
                for &item in items {
                    let value = self.expr(item)?;
                    self.runtime("ril_rt_append", vec![list, value]);
                }
                Ok(list)
            }
            Expr::Map(entries) => {
                let map = self.runtime("ril_rt_map", Vec::new());
                for &(key, value) in entries {
                    let key = self.expr(key)?;
                    let value = self.expr(value)?;
                    self.runtime("ril_rt_store", vec![map, key, value]);
                }
                Ok(map)
            }
            Expr::Member { base, member, .. } => {
                let base = self.collection(*base)?;
                let key = self.member_key(member)?;
                Ok(self.runtime("ril_rt_load", vec![base, key]))
            }
            Expr::Index { base, index, .. } => {
                let base = self.collection(*base)?;
                self.index(base, *index, false)
            }
            Expr::Interpolated(parts) => {
                if parts.is_empty() {
                    return Ok(self.string(""));
                }
                let mut rendered = Vec::with_capacity(parts.len());
                for part in parts {
                    let value = match part {
                        StringPart::Text(text) => self.constant(
                            &ty::literal(&ril_sema::syntax::Literal {
                                kind: ril_sema::syntax::LiteralKind::String,
                                text: text.clone(),
                            })
                            .map_err(|_| self.unsupported(span, "string escape"))?,
                            span,
                        )?,
                        StringPart::Interpolation(expr) => {
                            let value = self.expr(*expr)?;
                            self.runtime("ril_rt_text", vec![value])
                        }
                    };
                    rendered.push(value);
                }
                match rendered.as_slice() {
                    [only] => Ok(*only),
                    [a, b] => Ok(self.runtime("ril_rt_concat", vec![*a, *b])),
                    _ => {
                        let array = self.runtime("ril_rt_array", Vec::new());
                        for part in rendered {
                            self.runtime("ril_rt_append", vec![array, part]);
                        }
                        Ok(self.runtime("ril_rt_concat_many", vec![array]))
                    }
                }
            }
            Expr::Meta(_) => Err(self.unsupported(span, "unresolved meta expression")),
            _ => Err(self.unsupported(span, "this expression form")),
        }
    }

    fn lower_statements(&mut self, statements: &[StmtId]) -> Result<Register> {
        let scope_depth = self.scopes.len();
        let names: Vec<_> = self.locals.keys().copied().collect();
        let mut result = self.unit();
        for (index, &stmt_id) in statements.iter().enumerate() {
            if self.current.is_none() {
                break;
            }
            let stmt_node = self.ast().stmt(stmt_id);
            if let StmtKind::With(handler) = &stmt_node.value.kind
                && handler.is_ctl
            {
                let rest = statements.get(index + 1..).unwrap_or_default();
                result =
                    self.lower_with_ctl(std::slice::from_ref(handler), rest, stmt_node.span)?;
                break;
            }
            result = self.statement(stmt_id)?;
        }
        self.unwind_scopes_to(scope_depth);
        self.locals
            .retain(|&name, _| names.binary_search(&name).is_ok());
        Ok(result)
    }

    fn encode_fn_frame(&mut self, handlers: &[Handler], span: Span) -> Result<Register> {
        let entries = self.runtime("ril_rt_array", Vec::new());
        for handler in handlers {
            let operation = self
                .global
                .resolve(handler.operation.span)
                .ok_or_else(|| self.unsupported(span, "unresolved handler"))?;
            let label = self
                .global
                .typed
                .operation_evidence(operation, handler.operation.span, &self.types)
                .ok_or_else(|| self.unsupported(span, "invalid handler operation"))?;
            let op_id = self.global.effect_op_id(&label);
            let op_key = self.integer(&op_id.to_string());
            let is_ctl = self.boolean(false);
            let value = self.expr(handler.value)?;
            self.runtime("ril_rt_append", vec![entries, op_key]);
            self.runtime("ril_rt_append", vec![entries, is_ctl]);
            self.runtime("ril_rt_append", vec![entries, value]);
        }
        Ok(entries)
    }

    fn is_tail_resumptive_ctl_arm(&self, expr_id: ExprId) -> Option<DefinitionId> {
        let ast = self.ast();
        let Expr::Closure { params, body, .. } = &ast.expr(expr_id).value else {
            return None;
        };
        let last_param = params.last()?;
        let k_span = if let Some(pat) = last_param.pattern {
            match &ast.pattern(pat).value {
                Pattern::Binding(_, name) if name.value != "_" => name.span,
                _ => return None,
            }
        } else if let Some(name) = &last_param.name
            && name.value != "_"
        {
            name.span
        } else {
            return None;
        };
        let k_id = self.global.resolve(k_span)?;
        self.expr_is_strictly_tail_resumptive(*body, k_id)
            .then_some(k_id)
    }

    fn span_free_of(&self, span: Span, target: DefinitionId) -> bool {
        self.global
            .typed
            .hir
            .references_within(span)
            .all(|(_, def)| def != target)
    }

    fn expr_is_strictly_tail_resumptive(&self, expr_id: ExprId, k_id: DefinitionId) -> bool {
        let ast = self.ast();
        let node = ast.expr(expr_id);
        match &node.value {
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && self.global.resolve(path.span) == Some(k_id)
                {
                    return args
                        .iter()
                        .all(|a| self.span_free_of(ast.expr(a.value).span, k_id));
                }
                false
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                if !helpers.is_empty() {
                    return false;
                }
                let Some((&last, init)) = statements.split_last() else {
                    return false;
                };
                for &stmt_id in init {
                    let stmt = ast.stmt(stmt_id);
                    if matches!(
                        stmt.value.kind,
                        StmtKind::Defer(_)
                            | StmtKind::With(_)
                            | StmtKind::Binding {
                                fallback: Some(_),
                                ..
                            }
                    ) {
                        return false;
                    }
                    if !self.span_free_of(stmt.span, k_id) {
                        return false;
                    }
                }
                let StmtKind::Expr(tail) = ast.stmt(last).value.kind else {
                    return false;
                };
                self.expr_is_strictly_tail_resumptive(tail, k_id)
            }
            Expr::If {
                is_meta: false,
                condition,
                yes,
                no: Some(no),
            } => {
                let cond_ok = match condition {
                    ril_sema::syntax::Condition::Expr(e) => {
                        self.span_free_of(ast.expr(*e).span, k_id)
                    }
                    ril_sema::syntax::Condition::Binding { value, .. } => {
                        self.span_free_of(ast.expr(*value).span, k_id)
                    }
                };
                cond_ok
                    && self.expr_is_strictly_tail_resumptive(*yes, k_id)
                    && self.expr_is_strictly_tail_resumptive(*no, k_id)
            }
            Expr::Match {
                is_meta: false,
                value,
                arms,
                ..
            } => {
                if !self.span_free_of(ast.expr(*value).span, k_id) || arms.is_empty() {
                    return false;
                }
                arms.iter().all(|arm| {
                    arm.guard
                        .is_none_or(|g| self.span_free_of(ast.expr(g).span, k_id))
                        && self.expr_is_strictly_tail_resumptive(arm.body, k_id)
                })
            }
            _ => false,
        }
    }

    fn lower_with_ctl(
        &mut self,
        handlers: &[Handler],
        statements: &[StmtId],
        span: Span,
    ) -> Result<Register> {
        let entries = self.runtime("ril_rt_array", Vec::new());
        let mut needs_coro_stack = false;
        for handler in handlers {
            let operation = self
                .global
                .resolve(handler.operation.span)
                .ok_or_else(|| self.unsupported(span, "unresolved handler"))?;
            let label = self
                .global
                .typed
                .operation_evidence(operation, handler.operation.span, &self.types)
                .ok_or_else(|| self.unsupported(span, "invalid handler operation"))?;
            let op_id = self.global.effect_op_id(&label);
            let op_key = self.integer(&op_id.to_string());
            let (arm_kind_tag, stored) = if handler.is_ctl {
                let op_arity = self.global.declaration(operation).map_or(0, |decl| {
                    decl.signature.params.iter().filter(|p| !p.is_meta).count()
                });
                let omit_k = self.global.typed.hir.is_abort_only_ctl_operation(operation);
                let abort_k_first = omit_k
                    || matches!(
                        &self.ast().expr(handler.value).value,
                        Expr::Closure { params, .. }
                            if params.last().is_some_and(|p| {
                                p.name.as_ref().is_some_and(|n| n.value == "_")
                                    || p.pattern.is_some_and(|pat| {
                                        matches!(self.ast().pattern(pat).value, Pattern::Wildcard)
                                    })
                            })
                    );
                let tail_k = if !abort_k_first {
                    self.is_tail_resumptive_ctl_arm(handler.value)
                } else {
                    None
                };
                let value = if let Some(k_id) = tail_k {
                    self.lift_with_tail_resume(handler.value, None, Some(k_id))?
                } else {
                    self.expr(handler.value)?
                };
                let kind_tag = if tail_k.is_some() {
                    self.integer("2")
                } else if abort_k_first {
                    self.integer("3")
                } else {
                    needs_coro_stack = true;
                    self.integer("1")
                };
                let env = self.runtime("ril_rt_tuple", Vec::new());
                self.runtime("ril_rt_append", vec![env, value]);
                let adapter_fn = self.global.queue(Work::CtlArmAdapter {
                    op_arity,
                    abort_k_first,
                    omit_k,
                });
                (kind_tag, self.box_closure(adapter_fn, 2, env))
            } else {
                let value = self.expr(handler.value)?;
                (self.integer("0"), value)
            };
            self.runtime("ril_rt_append", vec![entries, op_key]);
            self.runtime("ril_rt_append", vec![entries, arm_kind_tag]);
            self.runtime("ril_rt_append", vec![entries, stored]);
        }
        let body_spans: Vec<Span> = statements
            .iter()
            .map(|&stmt| self.ast().stmt(stmt).span)
            .collect();
        let captures = self.collect_captures_in_spans(body_spans);
        let body_env = self.environment(&captures);
        let body_fn = self.global.queue(Work::StmtThunk {
            file: self.file,
            statements: statements.to_vec(),
            span,
            captures,
            types: self.types.clone(),
            statics: self.statics.clone(),
        });
        let body_thunk = self.box_closure(body_fn, 0, body_env);
        let runtime_fn = if needs_coro_stack {
            "ril_rt_with_ctl"
        } else {
            "ril_rt_with_ctl_fast"
        };
        Ok(self.runtime(runtime_fn, vec![entries, body_thunk]))
    }

    fn statement(&mut self, id: StmtId) -> Result<Register> {
        let node = self.ast().stmt(id);
        match &node.value.kind {
            StmtKind::Expr(id) => self.expr(*id),
            StmtKind::Binding {
                pattern,
                value: Some(expr),
                fallback,
                is_meta,
                ..
            } => {
                if *is_meta {
                    return Ok(self.unit());
                }
                let value = self.expr(*expr)?;
                if let Some(fallback) = fallback {
                    let good = self.block(0);
                    let bad = self.block(0);
                    self.test_pattern(*pattern, value, good, bad)?;
                    let prior = self.locals.clone();
                    let scopes = self.scopes.clone();
                    self.current = Some(bad);
                    self.expr(*fallback)?;
                    self.terminate(Terminator::Unreachable);
                    self.locals = prior;
                    self.scopes = scopes;
                    self.current = Some(good);
                }
                self.bind(*pattern, value)?;
                Ok(self.unit())
            }
            StmtKind::Defer(defer_expr) => {
                let defer_span = self.ast().expr(*defer_expr).span;
                let captures = self.collect_captures_in_spans(std::iter::once(defer_span));
                let environment = self.environment(&captures);
                let function = self.global.queue(Work::DeferThunk {
                    file: self.file,
                    syntax: *defer_expr,
                    captures,
                    types: self.types.clone(),
                    statics: self.statics.clone(),
                });
                self.scopes.push(ScopeAction::Defer {
                    function,
                    environment,
                });
                Ok(self.unit())
            }
            StmtKind::With(handler) => {
                let operation = self
                    .global
                    .resolve(handler.operation.span)
                    .ok_or_else(|| self.unsupported(node.span, "unresolved handler"))?;
                let label = self
                    .global
                    .typed
                    .operation_evidence(operation, handler.operation.span, &self.types)
                    .ok_or_else(|| self.unsupported(node.span, "invalid handler operation"))?;
                let op_id = self.global.effect_op_id(&label);
                let key = self.instruction(Instruction::RawU64(op_id));
                let value = self.expr(handler.value)?;
                self.runtime("ril_rt_handler_push_fn", vec![key, value]);
                self.scopes.push(ScopeAction::PopHandler);
                Ok(self.unit())
            }
            _ => Ok(self.unit()),
        }
    }

    fn defaults(
        &mut self,
        name: &ril_sema::syntax::Path,
        record: Register,
        fields: &BTreeMap<String, Register>,
    ) -> Result<()> {
        use ril_sema::syntax::{Type, TypeDefinition};
        let Some(id) = self.global.resolve(name.span) else {
            return Ok(());
        };
        let definition = self.global.typed.hir.definition(id);
        let Some(stmt) = definition.stmt else {
            return Ok(());
        };
        let ast = &self.global.typed.hir.file(definition.name.span.file).ast;
        let StmtKind::Type(declaration) = &ast.stmt(stmt).value.kind else {
            return Ok(());
        };
        let TypeDefinition::Data(repr) = declaration.definition else {
            return Ok(());
        };
        let Type::Record {
            fields: declared, ..
        } = &ast.ty(repr).value
        else {
            return Ok(());
        };
        let old = self.locals.clone();
        let file = std::mem::replace(&mut self.file, definition.name.span.file);
        let result = (|| {
            for field in declared {
                if let Some(&value) = fields.get(&field.name.value) {
                    self.bind_name(&field.name, value);
                } else if let Some(default) = field.default {
                    let value = self.expr(default)?;
                    self.bind_name(&field.name, value);
                    let key = self.string(&field.name.value);
                    self.runtime("ril_rt_store", vec![record, key, value]);
                }
            }
            Ok(())
        })();
        self.file = file;
        self.locals = old;
        result
    }

    fn constant(&mut self, value: &Value, span: Span) -> Result<Register> {
        Ok(match value {
            Value::Unit => self.unit(),
            Value::Bool(value) => self.boolean(*value),
            Value::Int(value) => self.integer(&value.to_string()),
            Value::F64(bits) => self.instruction(Instruction::Float(*bits)),
            Value::Str(text) => self.string(text),
            Value::Bytes(bytes) => {
                self.instruction(Instruction::Bytes(bytes.clone().into_boxed_slice()))
            }
            Value::Array(items) | Value::Tuple(items) => {
                let symbol = if matches!(value, Value::Array(_)) {
                    "ril_rt_array"
                } else {
                    "ril_rt_tuple"
                };
                let array = self.runtime(symbol, Vec::new());
                for item in items {
                    let item = self.constant(item, span)?;
                    self.runtime("ril_rt_append", vec![array, item]);
                }
                array
            }
            Value::Record(fields) => {
                let record = self.runtime("ril_rt_record", Vec::new());
                for (key, item) in fields {
                    let key = self.string(key);
                    let item = self.constant(item, span)?;
                    self.runtime("ril_rt_store", vec![record, key, item]);
                }
                record
            }
            Value::Map(fields) => {
                let map = self.runtime("ril_rt_map", Vec::new());
                for (key, item) in fields {
                    let key = self.constant(key, span)?;
                    let item = self.constant(item, span)?;
                    self.runtime("ril_rt_store", vec![map, key, item]);
                }
                map
            }
            Value::Tag(tag, items) => {
                let items = items
                    .iter()
                    .map(|item| self.constant(item, span))
                    .collect::<Result<Vec<_>>>()?;
                self.tag(tag, items)
            }
            Value::Mode(mode) => {
                use ril_sema::syntax::Mode;
                let tag = match (mode.variable, mode.mode) {
                    (false, Mode::Plain) => "Let",
                    (true, Mode::Plain) => "Var",
                    (false, Mode::Mut) => "Mut",
                    (false, Mode::Shared) => "SharedMut",
                    (false, Mode::Ref) => "Ref",
                    (true, Mode::Mut) => "VarMut",
                    (true, Mode::Shared) => "VarSharedMut",
                    (true, Mode::Ref) => "VarRef",
                    _ => "Let",
                };
                self.tag(tag, Vec::new())
            }
            Value::Type(_) => {
                return Err(self.unsupported(span, "static-only value in runtime code"));
            }
        })
    }

    fn read(&mut self, source: DefinitionId, span: Span) -> Result<Register> {
        if let Some(value) = self.statics.get(&source).cloned() {
            return self.constant(&value, span);
        }
        if let Some(&value) = self.locals.get(&source) {
            if self.global.boxed.contains(&source) {
                let key = self.integer("0");
                return Ok(self.runtime("ril_rt_load", vec![value, key]));
            }
            return Ok(value);
        }
        let def = self.global.typed.hir.definition(source);
        if matches!(def.kind, DefinitionKind::Variant(_) | DefinitionKind::Type)
            && let Some(Ty::Callable(signature)) = self.global.typed.types.get(&span)
        {
            let arity = signature.parameters.len();
            let function = self.global.queue(Work::Constructor(source, arity));
            let environment = self.unit();
            return Ok(self.box_closure(function, arity, environment));
        }
        match def.kind {
            DefinitionKind::Constant => {
                let prev_file = self.file;
                self.file = def.name.span.file;
                let result = match def.stmt.map(|stmt| &self.ast().stmt(stmt).value.kind) {
                    Some(StmtKind::Binding {
                        value: Some(expr), ..
                    }) => self.expr(*expr),
                    _ => Err(self.unsupported(span, "uninitialized constant")),
                };
                self.file = prev_file;
                result
            }
            DefinitionKind::Variant(_) => Ok(self.tag(&def.name.value, Vec::new())),
            DefinitionKind::Type if self.global.typed.hir.unit_constructor(source) => {
                Ok(self.unit())
            }
            DefinitionKind::Function if self.global.declaration(source).is_some() => {
                let captures = self.named_captures(source);
                let environment = self.environment(&captures);
                let (types, statics) = self.project_callee_env(source, span, BTreeMap::new());
                let id = self
                    .global
                    .queue(Work::Named(source, types, captures, statics));
                let arity = self
                    .global
                    .declaration(source)
                    .map_or(0, |f| f.signature.params.len());
                Ok(self.box_closure(id, arity, environment))
            }
            DefinitionKind::Primitive(_)
                if self.global.typed.hir.runtime_symbol(source).is_some() =>
            {
                let symbol = self
                    .global
                    .typed
                    .hir
                    .runtime_symbol(source)
                    .unwrap_or_else(|| ril_source::ice!("checked runtime symbol"));
                let arity = self.global.declaration(source).map_or(0, |f| {
                    f.signature.params.iter().filter(|p| !p.is_meta).count()
                });
                let id = self.global.queue(Work::Primitive(source, symbol, arity));
                let environment = self.unit();
                Ok(self.box_closure(id, arity, environment))
            }
            _ => Err(self.unsupported(span, "first-class callable or uninitialized local")),
        }
    }

    fn member_key(&mut self, member: &Member) -> Result<Register> {
        Ok(match member {
            Member::Name(name) => self.string(&name.value),
            Member::Index(index) => self.integer(&index.value),
            Member::Computed(value) => self.expr(*value)?,
        })
    }

    fn project_path(&mut self, path: &[(bool, Member)], mut value: Register) -> Result<Register> {
        let mut optional = false;
        for (safe, member) in path {
            optional |= *safe;
            let key = self.member_key(member)?;
            value = self.runtime(
                if optional {
                    "ril_rt_safe_member"
                } else {
                    "ril_rt_load"
                },
                vec![value, key],
            );
        }
        Ok(value)
    }

    fn tag(&mut self, name: &str, args: Vec<Register>) -> Register {
        let name = self.string(name);
        let tag = self.runtime("ril_rt_tag", vec![name]);
        for arg in args {
            self.runtime("ril_rt_append", vec![tag, arg]);
        }
        tag
    }

    fn bind_name(&mut self, name: &Name, value: Register) {
        if let Some(id) = self.global.resolve(name.span) {
            let value = if self.global.boxed.contains(&id) {
                let cell = self.runtime("ril_rt_tuple", Vec::new());
                self.runtime("ril_rt_append", vec![cell, value]);
                cell
            } else {
                value
            };
            self.locals.insert(id, value);
        }
    }

    fn bind(&mut self, id: PatternId, value: Register) -> Result<()> {
        let node = self.ast().pattern(id);
        match &node.value {
            Pattern::Binding(_, name) => self.bind_name(name, value),
            Pattern::Rest(Some(name)) => self.bind_name(name, value),
            Pattern::Slice { text, elements } => self.bind_slice(*text, elements, value)?,
            Pattern::Or(items) => self.bind_alternatives(node.span, items, value)?,
            Pattern::Tuple(items) => {
                for (index, &item) in items.iter().enumerate() {
                    let key = self.integer(&index.to_string());
                    let next = self.runtime("ril_rt_load", vec![value, key]);
                    self.bind(item, next)?;
                }
            }
            Pattern::Wrap(_, items) => match items.as_slice() {
                [] => {}
                [inner] => self.bind(*inner, value)?,
                many => {
                    for (index, &item) in many.iter().enumerate() {
                        let key = self.integer(&index.to_string());
                        let next = self.runtime("ril_rt_load", vec![value, key]);
                        self.bind(item, next)?;
                    }
                }
            },
            Pattern::Constructor(_, Some(items)) => {
                for (index, &item) in items.iter().enumerate() {
                    let key = self.integer(&index.to_string());
                    let next = self.runtime("ril_rt_load", vec![value, key]);
                    self.bind(item, next)?;
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    let key = self.string(&field.name.value);
                    let next = self.runtime("ril_rt_load", vec![value, key]);
                    if let Some(item) = field.pattern {
                        self.bind(item, next)?;
                    } else {
                        self.bind_name(&field.name, next);
                    }
                }
            }
            Pattern::Subset { binding, .. } => {
                self.bind(*binding, value)?;
            }
            Pattern::Wildcard
            | Pattern::Rest(None)
            | Pattern::Unit
            | Pattern::Literal(_)
            | Pattern::Constructor(_, None)
            | Pattern::Range { .. } => {}
            _ => return Err(self.unsupported(node.span, "this binding pattern")),
        }
        Ok(())
    }
}
