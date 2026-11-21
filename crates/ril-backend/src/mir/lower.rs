mod control;

use std::collections::{BTreeMap, HashMap};

use ril_base::{
    diag::Diagnostic,
    span::{FileId, Span},
};
use ril_sema::{
    access::Analysis,
    hir::{DefinitionId, DefinitionKind, Resolution},
    syntax::{
        Argument, Ast, Expr, ExprId, Function as SyntaxFunction, Member, Name, Pattern, PatternId,
        StmtId, StmtKind, StringPart, Transfer,
    },
    ty::{self, TypedProgram, Value},
};

use super::{
    Block, BlockId, DraftOp, Function, FunctionId, Instruction, IntLowering, ManagedInt, Program,
    Register, Target, Terminator,
};

type Result<T> = std::result::Result<T, Diagnostic>;
type Locals = BTreeMap<DefinitionId, Register>;

pub(super) fn lower(typed: &TypedProgram, analysis: &Analysis) -> Result<Program> {
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
        analysis,
        queued: Vec::new(),
        ids: BTreeMap::new(),
    };
    let entry = lowering.queue(entry);
    let mut functions = Vec::new();
    while let Some(&id) = lowering.queued.get(functions.len()) {
        functions.push(lowering.function(id)?);
    }
    Ok(Program { entry, functions })
}

struct Lowering<'a> {
    typed: &'a TypedProgram,
    analysis: &'a Analysis,
    queued: Vec<DefinitionId>,
    ids: BTreeMap<DefinitionId, FunctionId>,
}

impl<'a> Lowering<'a> {
    fn queue(&mut self, id: DefinitionId) -> FunctionId {
        if let Some(&function) = self.ids.get(&id) {
            return function;
        }
        let function = FunctionId(self.queued.len());
        self.ids.insert(id, function);
        self.queued.push(id);
        function
    }

    fn resolve(&self, span: Span) -> Option<DefinitionId> {
        match self.typed.hir.resolve(span) {
            Some(Resolution::Definition(id)) => Some(id),
            _ => None,
        }
    }

    fn declaration(&self, id: DefinitionId) -> Option<&'a SyntaxFunction> {
        let def = self.typed.hir.definition(id);
        let ast = &self.typed.hir.file(def.name.span.file).ast;
        match &ast.stmt(def.stmt?).value.kind {
            StmtKind::Function(func) => Some(func),
            _ => None,
        }
    }

    fn function(&mut self, id: DefinitionId) -> Result<Function> {
        let func = self
            .declaration(id)
            .ok_or_else(|| Diagnostic::unsupported("missing native function definition"))?;
        let name = self.typed.hir.export_name(id);
        let body = func
            .body
            .ok_or_else(|| Diagnostic::unsupported("missing native function body"))?;
        let arity = func.signature.params.len();
        let mut builder = Builder {
            global: self,
            file: func.name.span.file,
            function: Function {
                name,
                arity,
                registers: 0,
                blocks: Vec::new(),
            },
            current: None,
            locals: BTreeMap::new(),
            cleanups: Vec::new(),
            pads: HashMap::new(),
            traps: Vec::new(),
            loops: Vec::new(),
            handlers: BTreeMap::new(),
            capture_return: None,
        };
        let entry = builder.block(arity);
        builder.current = Some(entry);
        for (param, value) in func.signature.params.iter().zip(builder.params(entry)) {
            if let Some(id) = param
                .name
                .as_ref()
                .and_then(|name| builder.global.resolve(name.span))
            {
                builder.locals.insert(id, value);
            }
        }
        let fail = builder.block(0);
        let fail_value = builder.instruction_at(fail, Instruction::Handle(0));
        builder.term_at(fail, Terminator::Return(fail_value));
        builder.traps.push((0, fail));
        let result = builder.expr(body)?;
        if builder.current.is_some() {
            builder.cleanup_to(0);
            builder.terminate(Terminator::Return(result));
        }
        Ok(builder.function)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Cleanup {
    function: FunctionId,
    value: Register,
}

#[derive(Clone)]
struct Loop {
    header: BlockId,
    exit: BlockId,
    names: Vec<DefinitionId>,
    cleanups: usize,
}

#[derive(Clone)]
struct BoundHandler {
    closure: ExprId,
    locals: Locals,
    outer: BTreeMap<DefinitionId, BoundHandler>,
}

struct Builder<'b, 'a> {
    global: &'b mut Lowering<'a>,
    file: FileId,
    function: Function,
    current: Option<BlockId>,
    locals: Locals,
    cleanups: Vec<Cleanup>,
    pads: HashMap<(BlockId, Vec<Cleanup>), BlockId>,
    traps: Vec<(usize, BlockId)>,
    loops: Vec<Loop>,
    handlers: BTreeMap<DefinitionId, BoundHandler>,
    capture_return: Option<(BlockId, usize)>,
}

impl<'a> Builder<'_, 'a> {
    fn ast(&self) -> &'a Ast {
        &self.global.typed.hir.file(self.file).ast
    }

    fn register(&mut self) -> Register {
        let id = self.function.registers;
        self.function.registers += 1;
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
            .unwrap_or_else(|| ril_base::ice!("invalid MIR block"))
            .params
            .clone()
    }

    fn instruction_at(&mut self, block: BlockId, instruction: Instruction) -> Register {
        let value = self.register();
        self.function
            .blocks
            .get_mut(block.0)
            .unwrap_or_else(|| ril_base::ice!("invalid MIR block"))
            .instructions
            .push((value, instruction));
        value
    }

    fn instruction(&mut self, instruction: Instruction) -> Register {
        if let Some(block) = self.current {
            self.instruction_at(block, instruction)
        } else {
            self.register()
        }
    }

    fn term_at(&mut self, block: BlockId, term: Terminator) {
        self.function
            .blocks
            .get_mut(block.0)
            .unwrap_or_else(|| ril_base::ice!("invalid MIR block"))
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
        self.instruction(Instruction::Handle(if value { 2 } else { 1 }))
    }

    fn string(&mut self, value: &str) -> Register {
        self.instruction(Instruction::Text(value.as_bytes().into()))
    }

    fn integer(&mut self, value: &str) -> Register {
        self.instruction(Instruction::Integer(value.as_bytes().into()))
    }

    fn unsupported(&self, span: Span, feature: &str) -> Diagnostic {
        Diagnostic {
            primary: Some(span),
            ..Diagnostic::unsupported(format!("native lowering does not support {feature}"))
        }
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
            .unwrap_or_else(|| ril_base::ice!("invoke normal block has no result param"))
    }

    fn runtime(&mut self, symbol: &'static str, arguments: Vec<Register>) -> Register {
        self.invoke(Target::Runtime(symbol), arguments, false)
    }

    fn unwind_pad(&mut self) -> BlockId {
        let &(depth, end) = self
            .traps
            .last()
            .unwrap_or_else(|| ril_base::ice!("native function has no panic target"));
        let cleanups = self.cleanups.get(depth..).unwrap_or_default().to_vec();
        if let Some(&block) = self.pads.get(&(end, cleanups.clone())) {
            return block;
        }
        let mut next = end;
        for cleanup in &cleanups {
            let block = self.block(0);
            self.term_at(
                block,
                Terminator::Invoke {
                    target: Target::Function(cleanup.function),
                    arguments: vec![cleanup.value],
                    normal: next,
                    unwind: next,
                    cleanup: true,
                    keep_result: false,
                },
            );
            next = block;
        }
        self.pads.insert((end, cleanups), next);
        next
    }

    fn cleanup_to(&mut self, depth: usize) {
        while self.cleanups.len() > depth {
            if let Some(cleanup) = self.cleanups.pop() {
                self.invoke(
                    Target::Function(cleanup.function),
                    vec![cleanup.value],
                    true,
                );
            }
        }
    }

    fn expr(&mut self, id: ExprId) -> Result<Register> {
        if self.current.is_none() {
            return Ok(self.register());
        }
        let node = self.ast().expr(id);
        let span = node.span;
        if let Some(constant) = self.global.typed.static_values.get(&span)
            && !matches!(constant, Value::Type(_) | Value::Mode(_))
        {
            return self.constant(constant, span);
        }
        match &node.value {
            Expr::Unit => Ok(self.unit()),
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
            Expr::Block { statements, .. } => {
                let cleanup_depth = self.cleanups.len();
                let names: Vec<_> = self.locals.keys().copied().collect();
                let saved_handlers = self.handlers.clone();
                let mut result = self.unit();
                for &statement in statements {
                    if self.current.is_none() {
                        break;
                    }
                    result = self.statement(statement)?;
                }
                self.cleanup_to(cleanup_depth);
                self.locals
                    .retain(|&name, _| names.binary_search(&name).is_ok());
                self.handlers = saved_handlers;
                Ok(result)
            }
            Expr::Unary { op, value } => {
                let value = self.expr(*value)?;
                match op.value.as_str() {
                    "new" | "ref" | "^mut" => Ok(value),
                    "?" => self.propagate(value),
                    op => ManagedInt
                        .unary(op)
                        .map(|symbol| self.runtime(symbol, vec![value]))
                        .ok_or_else(|| self.unsupported(span, "unary operator")),
                }
            }
            Expr::Binary { op, left, right } => self.binary(op, *left, *right),
            Expr::Call { callee, args } => self.call(*callee, args, span),
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let mut arguments = vec![Argument {
                    value: *value,
                    mode: *mode,
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
            Expr::If { condition, yes, no } => self.conditional(condition, *yes, *no),
            Expr::While { condition, body } => self.while_loop(condition, *body),
            Expr::Match { value, arms, .. } => self.match_expr(*value, arms, span),
            Expr::Transfer { kind, value } => {
                match kind {
                    Transfer::Return => {
                        let value = if let Some(value) = value {
                            self.expr(*value)?
                        } else {
                            self.unit()
                        };
                        self.return_value(value);
                    }
                    Transfer::Continue | Transfer::Break => self.loop_transfer(*kind, span)?,
                }
                Ok(self.register())
            }
            Expr::Record { fields, .. } => {
                let record = self.runtime("ril_rt_record", Vec::new());
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
            Expr::Member { base, member, safe } => {
                let base = self.expr(*base)?;
                let key = self.member_key(member)?;
                if *safe {
                    Err(self.unsupported(span, "safe field projection"))
                } else {
                    Ok(self.runtime("ril_rt_load", vec![base, key]))
                }
            }
            Expr::Index { base, index, safe } => {
                let base = self.expr(*base)?;
                let key = self.expr(*index)?;
                Ok(self.runtime(
                    if *safe {
                        "ril_rt_safe_load"
                    } else {
                        "ril_rt_load"
                    },
                    vec![base, key],
                ))
            }
            Expr::Interpolated(parts) => {
                let mut accumulated = self.string("");
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
                    accumulated = self.runtime("ril_rt_concat", vec![accumulated, value]);
                }
                Ok(accumulated)
            }
            _ => Err(self.unsupported(span, "this expression form")),
        }
    }

    fn statement(&mut self, id: StmtId) -> Result<Register> {
        let node = self.ast().stmt(id);
        match &node.value.kind {
            StmtKind::Expr(id) => self.expr(*id),
            StmtKind::Binding {
                pattern,
                value: Some(expr),
                resource,
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
                    let cleanups = self.cleanups.clone();
                    self.current = Some(bad);
                    self.expr(*fallback)?;
                    self.locals = prior;
                    self.cleanups = cleanups;
                    self.current = Some(good);
                }
                self.bind(*pattern, value)?;
                if *resource {
                    let function = self
                        .global
                        .analysis
                        .cleanups
                        .get(&node.span)
                        .copied()
                        .ok_or_else(|| self.unsupported(node.span, "unresolved cleanup"))?;
                    self.cleanups.push(Cleanup {
                        function: self.global.queue(function),
                        value,
                    });
                }
                Ok(self.unit())
            }
            StmtKind::With(handlers) => {
                let prior = self.handlers.clone();
                for handler in handlers {
                    let operation = self
                        .global
                        .resolve(handler.operation.span)
                        .ok_or_else(|| self.unsupported(node.span, "unresolved handler"))?;
                    self.handlers.insert(
                        operation,
                        BoundHandler {
                            closure: handler.value,
                            locals: self.locals.clone(),
                            outer: prior.clone(),
                        },
                    );
                }
                Ok(self.unit())
            }
            _ => Ok(self.unit()),
        }
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
            Value::Type(_) | Value::Mode(_) => {
                return Err(self.unsupported(span, "static-only value in runtime code"));
            }
        })
    }

    fn read(&mut self, source: DefinitionId, span: Span) -> Result<Register> {
        if let Some(&value) = self.locals.get(&source) {
            return Ok(value);
        }
        let def = self.global.typed.hir.definition(source);
        match def.kind {
            DefinitionKind::Constant => {
                let prev_file = self.file;
                self.file = def.name.span.file;
                let result = match def.stmt.map(|stmt| &self.ast().stmt(stmt).value.kind) {
                    Some(StmtKind::Binding {
                        value: Some(expr), ..
                    }) => self.expr(*expr),
                    _ => Err(self.unsupported(span, "foreign constant")),
                };
                self.file = prev_file;
                result
            }
            DefinitionKind::Primitive(_) if def.name.value == "None" => {
                Ok(self.tag("None", Vec::new()))
            }
            DefinitionKind::Primitive(_) if def.name.value == "OS" => {
                Ok(self.string(std::env::consts::OS))
            }
            DefinitionKind::Primitive(_) if def.name.value == "ARCH" => {
                Ok(self.string(std::env::consts::ARCH))
            }
            DefinitionKind::Primitive(_) if def.name.value == "HAS_OPENAT" => {
                Ok(self.boolean(cfg!(unix)))
            }
            DefinitionKind::Variant(_) => Ok(self.tag(&def.name.value, Vec::new())),
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

    fn tag(&mut self, name: &str, args: Vec<Register>) -> Register {
        let name = self.string(name);
        let tag = self.runtime("ril_rt_tag", vec![name]);
        for arg in args {
            self.runtime("ril_rt_append", vec![tag, arg]);
        }
        tag
    }

    fn call(&mut self, callee: ExprId, args: &[Argument], span: Span) -> Result<Register> {
        let Expr::Path(path) = &self.ast().expr(callee).value else {
            let args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            return self.inline_closure(callee, &args, span);
        };
        let id = self
            .global
            .resolve(path.span)
            .ok_or_else(|| self.unsupported(span, "unresolved call"))?;
        let def = self.global.typed.hir.definition(id);
        let name = def.name.value.as_str();
        if matches!(def.kind, DefinitionKind::Primitive(_)) {
            return self.primitive(name, args, span);
        }
        if let Some(handler) = self.handlers.get(&id).cloned() {
            let args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            let locals = std::mem::replace(&mut self.locals, handler.locals);
            let handlers = std::mem::replace(&mut self.handlers, handler.outer);
            let result = self.inline_closure(handler.closure, &args, span);
            self.handlers = handlers;
            self.locals = locals;
            return result;
        }
        if matches!(def.kind, DefinitionKind::Variant(_) | DefinitionKind::Type) {
            let args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            return Ok(self.tag(name, args));
        }
        let Some(function) = self.global.declaration(id) else {
            return Err(self.unsupported(span, "callable value"));
        };
        let values = self.arguments(function, args, span)?;
        if function.body.is_some() {
            let function = self.global.queue(id);
            Ok(self.invoke(Target::Function(function), values, false))
        } else if self.global.typed.hir.effect_of(id).is_some() {
            Err(self.unsupported(span, "effect operation requiring dynamic evidence"))
        } else {
            Ok(self.invoke(Target::Foreign(name.to_owned()), values, false))
        }
    }

    fn arguments(
        &mut self,
        function: &SyntaxFunction,
        args: &[Argument],
        span: Span,
    ) -> Result<Vec<Register>> {
        let mut values = vec![None; function.signature.params.len()];
        for arg in args {
            let index = if let Some(name) = &arg.name {
                function.signature.params.iter().position(|p| {
                    p.name
                        .as_ref()
                        .is_some_and(|param| param.value == name.value)
                })
            } else {
                values.iter().position(Option::is_none)
            }
            .ok_or_else(|| self.unsupported(span, "argument binding"))?;
            let value = self.expr(arg.value)?;
            if let Some(slot) = values.get_mut(index) {
                *slot = Some(value);
            }
        }
        let file = self.file;
        let locals = self.locals.clone();
        self.file = function.name.span.file;
        let mut ordered = Vec::new();
        let result = (|| {
            for (param, value) in function.signature.params.iter().zip(values) {
                let value = if let Some(value) = value {
                    value
                } else if let Some(default) = param.default {
                    self.expr(default)?
                } else {
                    return Err(self.unsupported(span, "missing argument"));
                };
                if let Some(id) = param
                    .name
                    .as_ref()
                    .and_then(|name| self.global.resolve(name.span))
                {
                    self.locals.insert(id, value);
                }
                ordered.push(value);
            }
            Ok(ordered)
        })();
        self.file = file;
        self.locals = locals;
        result
    }

    fn primitive(&mut self, name: &str, args: &[Argument], span: Span) -> Result<Register> {
        if name == "absorb_panic"
            && let [action] = args
        {
            return self.absorb(action.value, span);
        }
        if name == "derive"
            && let [base, update] = args
        {
            let base = self.expr(base.value)?;
            let draft = self.runtime(DraftOp::Begin.symbol(), vec![base]);
            self.inline_closure(update.value, &[draft], span)?;
            return Ok(self.runtime(DraftOp::Commit.symbol(), vec![draft]));
        }
        let mut args = args
            .iter()
            .map(|arg| self.expr(arg.value))
            .collect::<Result<Vec<_>>>()?;
        if matches!(name, "Ok" | "Err" | "Some") {
            return Ok(self.tag(name, args));
        }
        let symbol = match name {
            "print" => "ril_rt_print",
            "println" => "ril_rt_println",
            "panic" => "ril_rt_panic",
            "assert" => {
                if args.len() == 1 {
                    args.push(self.string("assertion failed"));
                }
                "ril_rt_assert"
            }
            "len" => "ril_rt_len",
            "clone" => "ril_rt_clone",
            "inspect" => "ril_rt_inspect",
            "push" => "ril_rt_append",
            "inner" => {
                args.push(self.integer("0"));
                "ril_rt_load"
            }
            "panic_message" if args.len() == 1 => {
                return args
                    .pop()
                    .ok_or_else(|| self.unsupported(span, "missing panic info"));
            }
            _ => return Err(self.unsupported(span, &format!("primitive {name}"))),
        };
        Ok(self.runtime(symbol, args))
    }

    fn inline_closure(&mut self, id: ExprId, args: &[Register], span: Span) -> Result<Register> {
        let Expr::Closure { params, body, .. } = &self.ast().expr(id).value else {
            return Err(self.unsupported(span, "nonliteral closure"));
        };
        if params.len() != args.len() {
            return Err(self.unsupported(span, "closure arity"));
        }
        let old = self.locals.clone();
        for (parameter, &value) in params.iter().zip(args) {
            if let Some(pattern) = parameter.pattern {
                self.bind(pattern, value)?;
            } else if let Some(name) = &parameter.name {
                self.bind_name(name, value);
            }
        }
        let exit = self.block(1);
        let depth = self.cleanups.len();
        let target = self.capture_return.replace((exit, depth));
        let result = self.expr(*body)?;
        self.terminate(Terminator::Jump(exit, vec![result]));
        self.capture_return = target;
        self.locals = old;
        self.cleanups.truncate(depth);
        self.current = Some(exit);
        self.params(exit)
            .first()
            .copied()
            .ok_or_else(|| self.unsupported(span, "closure result"))
    }

    fn absorb(&mut self, action: ExprId, span: Span) -> Result<Register> {
        let caught = self.block(0);
        let join = self.block(1);
        self.traps.push((self.cleanups.len(), caught));
        let result = self.inline_closure(action, &[], span)?;
        self.traps.pop();
        let ok = self.tag("Ok", vec![result]);
        self.terminate(Terminator::Jump(join, vec![ok]));
        self.current = Some(caught);
        let message = self.runtime("ril_rt_panic_take", Vec::new());
        let info = self.tag("Panicked", vec![message]);
        let error = self.tag("Err", vec![info]);
        self.terminate(Terminator::Jump(join, vec![error]));
        self.current = Some(join);
        self.params(join)
            .first()
            .copied()
            .ok_or_else(|| self.unsupported(span, "panic boundary result"))
    }

    fn bind_name(&mut self, name: &Name, value: Register) {
        if let Some(id) = self.global.resolve(name.span) {
            self.locals.insert(id, value);
        }
    }

    fn bind(&mut self, id: PatternId, value: Register) -> Result<()> {
        let node = self.ast().pattern(id);
        match &node.value {
            Pattern::Binding(_, name) => self.bind_name(name, value),
            Pattern::Tuple(items) => {
                for (index, &item) in items.iter().enumerate() {
                    let key = self.integer(&index.to_string());
                    let next = self.runtime("ril_rt_load", vec![value, key]);
                    self.bind(item, next)?;
                }
            }
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
            Pattern::Wildcard
            | Pattern::Unit
            | Pattern::Literal(_)
            | Pattern::Constructor(_, None)
            | Pattern::Range { .. } => {}
            _ => return Err(self.unsupported(node.span, "this binding pattern")),
        }
        Ok(())
    }
}
