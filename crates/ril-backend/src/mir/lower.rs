mod control;
mod slice;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::Arc,
};

use ril_base::{
    diag::Diagnostic,
    span::{FileId, Span},
};
use ril_sema::{
    access::{Analysis, CleanupAction},
    hir::{DefinitionId, DefinitionKind, Resolution, TextBuiltin},
    syntax::{
        Argument, Ast, Expr, ExprId, Function as SyntaxFunction, Member, Name, Parameter, Pattern,
        PatternId, StmtId, StmtKind, StringPart, Transfer,
    },
    ty::{self, Ty, TypedProgram, Value},
};

use super::{
    Block, BlockId, DraftOp, ForeignAbi, ForeignImport, Function, FunctionId, Instruction,
    IntLowering, ManagedInt, Program, Register, Target, Terminator,
};

type Result<T> = std::result::Result<T, Diagnostic>;
type Locals = BTreeMap<DefinitionId, Register>;

enum NativeBody<'a> {
    Expression(ExprId),
    Accessor(&'a [(bool, Member)]),
    Foreign(Arc<ForeignImport>),
    Constructor(&'a str, usize),
}

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
        boxed: captured_slots(typed),
    };
    let suspend_at_entry = typed
        .callables
        .get(&entry)
        .is_some_and(|callable| callable.effects.iter().any(|effect| effect == "fiber"));
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
        suspend_at_entry,
    })
}

fn captured_slots(typed: &TypedProgram) -> BTreeSet<DefinitionId> {
    typed.thir.boxed_var_captures.clone()
}

struct Lowering<'a> {
    typed: &'a TypedProgram,
    analysis: &'a Analysis,
    queued: Vec<Work>,
    boxed: BTreeSet<DefinitionId>,
}

#[derive(Clone, PartialEq)]
enum Work {
    Constructor(DefinitionId, usize),
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
    },
}

impl<'a> Lowering<'a> {
    fn queue(&mut self, work: Work) -> FunctionId {
        if let Some(id) = self.queued.iter().position(|known| known == &work) {
            return FunctionId(id);
        }
        let function = FunctionId(self.queued.len());
        self.queued.push(work);
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
        let stmt = def.stmt?;
        let ast = &self.typed.hir.file(def.name.span.file).ast;
        match &ast.stmt(stmt).value.kind {
            StmtKind::Function(func) => Some(func),
            _ => None,
        }
    }

    fn foreign(&self, id: DefinitionId) -> Result<Arc<ForeignImport>> {
        let definition = self.typed.hir.definition(id);
        if self
            .typed
            .hir
            .file(definition.name.span.file)
            .is_interface()
        {
            return Err(Diagnostic::unsupported(format!(
                "native code for {} is required",
                self.typed.hir.export_name(id)
            )));
        }
        let callable =
            self.typed.callables.get(&id).unwrap_or_else(|| {
                ril_base::ice!("foreign declaration requires a checked signature")
            });
        Ok(self.foreign_import(
            id,
            &Ty::Callable(callable.clone()),
            ForeignAbi::Function {
                arity: callable.parameters.len(),
            },
        ))
    }

    fn foreign_import(&self, id: DefinitionId, ty: &Ty, abi: ForeignAbi) -> Arc<ForeignImport> {
        Arc::new(ForeignImport {
            declaration: self.typed.hir.export_name(id),
            signature: ty.qualified_display(&self.typed.hir).to_string(),
            symbol: self.typed.hir.definition(id).name.value.clone(),
            abi,
        })
    }

    fn function(&mut self, work: Work) -> Result<Function> {
        let (file, name, body, params, guards, captures, types, statics) = match work {
            Work::Constructor(id, arity) => {
                let def = self.typed.hir.definition(id);
                (
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
            Work::Named(id, types, captures, statics) => {
                let f = self
                    .declaration(id)
                    .ok_or_else(|| Diagnostic::unsupported("missing native function definition"))?;
                let body = if let Some(body) = f.body {
                    NativeBody::Expression(body)
                } else {
                    NativeBody::Foreign(self.foreign(id)?)
                };
                (
                    f.name.span.file,
                    self.typed.hir.export_name(id),
                    body,
                    f.signature.params.as_slice(),
                    f.signature.guards.clone(),
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
            } => {
                let ast = &self.typed.hir.file(file).ast;
                let node = ast.expr(syntax);
                let (body, params) = match &node.value {
                    Expr::Closure { params, body, .. } => {
                        (NativeBody::Expression(*body), params.as_slice())
                    }
                    Expr::Accessor(path) => (NativeBody::Accessor(path), &[][..]),
                    _ => return Err(Diagnostic::unsupported("invalid closure body")),
                };
                (
                    file,
                    format!(
                        "{}:closure@{}",
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
        };
        let params: Vec<_> = params.iter().filter(|param| !param.is_meta).collect();
        let arity = match body {
            NativeBody::Accessor(_) => 1,
            NativeBody::Constructor(_, arity) => arity,
            _ => params.len(),
        };
        let mut builder = Builder {
            global: self,
            file,
            function: Function {
                name,
                arity,
                registers: 0,
                stack_slots: 0,
                blocks: Vec::new(),
            },
            current: None,
            locals: BTreeMap::new(),
            cleanups: Vec::new(),
            pads: HashMap::new(),
            traps: Vec::new(),
            loops: Vec::new(),
            evidence: Register(0),
            types,
            statics,
            guards,
            running_guard: false,
        };
        let entry = builder.block(arity);
        builder.current = Some(entry);
        builder.evidence = builder.instruction(Instruction::Evidence);
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
                builder.run_guard(guard, value)?;
            }
        }
        let result = match body {
            NativeBody::Expression(body) => builder.expr(body)?,
            NativeBody::Foreign(import) => {
                builder.invoke(Target::Foreign(import), builder.params(entry), false)
            }
            NativeBody::Accessor(path) => {
                let value = builder.result_param(entry);
                builder.project_path(path, value)?
            }
            NativeBody::Constructor(tag, _) => builder.tag(tag, builder.params(entry)),
        };
        if builder.current.is_some() {
            builder.return_value(result)?;
        }
        Ok(builder.function)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Cleanup {
    action: Clean,
    evidence: Register,
    value: Register,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Clean {
    Function(FunctionId),
    Sender,
}

impl Clean {
    fn target(self) -> Target {
        match self {
            Self::Function(id) => Target::Function(id),
            Self::Sender => Target::Runtime("ril_channel_close"),
        }
    }
}

#[derive(Clone)]
struct Loop {
    header: BlockId,
    exit: BlockId,
    names: Vec<DefinitionId>,
    cleanups: usize,
    counter: Option<Register>,
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
    evidence: Register,
    types: BTreeMap<DefinitionId, Ty>,
    statics: BTreeMap<DefinitionId, Value>,
    guards: Vec<ExprId>,
    running_guard: bool,
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
        Diagnostic::unsupported_at(span, format!("native lowering does not support {feature}"))
    }

    fn invoke(&mut self, target: Target, arguments: Vec<Register>, cleanup: bool) -> Register {
        self.invoke_with(target, arguments, cleanup, self.evidence)
    }

    fn invoke_with(
        &mut self,
        target: Target,
        arguments: Vec<Register>,
        cleanup: bool,
        evidence: Register,
    ) -> Register {
        let Some(block) = self.current else {
            return self.register();
        };
        let normal = self.block(1);
        let unwind = self.unwind_pad();
        self.term_at(
            block,
            Terminator::Invoke {
                target,
                evidence,
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
                    target: cleanup.action.target(),
                    evidence: cleanup.evidence,
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
                self.invoke_with(
                    cleanup.action.target(),
                    vec![cleanup.value],
                    false,
                    cleanup.evidence,
                );
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
            && !matches!(constant, Value::Type(_) | Value::Mode(_))
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
            Expr::Block { statements, .. } => {
                let cleanup_depth = self.cleanups.len();
                let names: Vec<_> = self.locals.keys().copied().collect();
                let saved_evidence = self.evidence;
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
                self.evidence = saved_evidence;
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
            Expr::For {
                iterable,
                pattern,
                body,
                ..
            } => self.for_loop(*iterable, *pattern, *body),
            Expr::Match { value, arms, .. } => self.match_expr(*value, arms, span),
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
                    self.terminate(Terminator::Unreachable);
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
                        action: match function {
                            CleanupAction::Function(function) => {
                                Clean::Function(self.global.queue(Work::Named(
                                    function,
                                    BTreeMap::new(),
                                    Vec::new(),
                                    self.statics.clone(),
                                )))
                            }
                            CleanupAction::CloseSender => Clean::Sender,
                        },
                        evidence: self.evidence,
                        value,
                    });
                }
                Ok(self.unit())
            }
            StmtKind::With(handlers) => {
                let mut installed = Vec::new();
                for handler in handlers {
                    let operation = self
                        .global
                        .resolve(handler.operation.span)
                        .ok_or_else(|| self.unsupported(node.span, "unresolved handler"))?;
                    let label = self
                        .global
                        .typed
                        .operation_evidence(operation, handler.operation.span, &self.types)
                        .ok_or_else(|| self.unsupported(node.span, "invalid handler operation"))?;
                    let key = self.string(&label);
                    installed.push((key, self.expr(handler.value)?));
                }
                for (name, handler) in installed {
                    self.evidence =
                        self.runtime("ril_rt_evidence_push", vec![self.evidence, name, handler]);
                }
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
            Value::Type(_) | Value::Mode(_) => {
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
        if (matches!(def.kind, DefinitionKind::Variant(_))
            || matches!(def.kind, DefinitionKind::Primitive(_))
                && matches!(def.name.value.as_str(), "Some" | "Ok" | "Err"))
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
                    Some(StmtKind::Binding { value: None, .. }) => {
                        let ty =
                            self.global.typed.bindings.get(&source).ok_or_else(|| {
                                self.unsupported(span, "unchecked foreign constant")
                            })?;
                        let import = self.global.foreign_import(source, ty, ForeignAbi::Constant);
                        Ok(self.invoke(Target::Foreign(import), Vec::new(), false))
                    }
                    _ => Err(self.unsupported(span, "uninitialized constant")),
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
            DefinitionKind::Type if self.global.typed.hir.unit_constructor(source) => {
                Ok(self.tag(&def.name.value, Vec::new()))
            }
            DefinitionKind::Function if self.global.declaration(source).is_some() => {
                let captures = self.named_captures(source);
                let environment = self.environment(&captures);
                let id = self.global.queue(Work::Named(
                    source,
                    BTreeMap::new(),
                    captures,
                    self.statics.clone(),
                ));
                let arity = self
                    .global
                    .declaration(source)
                    .map_or(0, |f| f.signature.params.len());
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

    fn call(&mut self, callee: ExprId, args: &[Argument], span: Span) -> Result<Register> {
        let callee_expression = &self.ast().expr(callee).value;
        let Expr::Path(path) = callee_expression else {
            if let Expr::Closure { params, .. } = callee_expression
                && params.iter().any(|param| param.is_meta)
            {
                let metadata =
                    self.global
                        .typed
                        .static_arguments(span, &self.statics, &self.types)?;
                let value = self.lift(callee, Some(&metadata))?;
                let args = self.arguments(params, self.file, args, &metadata, span)?;
                return Ok(self.invoke_closure(value, args));
            }
            let value = self.expr(callee)?;
            let args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            return Ok(self.invoke_closure(value, args));
        };
        let id = self
            .global
            .resolve(path.span)
            .ok_or_else(|| self.unsupported(span, "unresolved call"))?;
        let def = self.global.typed.hir.definition(id);
        let name = def.name.value.as_str();
        if matches!(def.kind, DefinitionKind::Primitive(_)) {
            if let Some(builtin) = self.global.typed.hir.text_builtin(id) {
                return self.text_builtin(builtin, args);
            }
            if let Some(module @ ("Fiber" | "Channel")) = self.global.typed.hir.primitive_module(id)
            {
                return self.concurrent(module, name, args, span);
            }
            return self.primitive(name, args, span);
        }
        if let Some(label) = self
            .global
            .typed
            .operation_evidence(id, path.span, &self.types)
        {
            let operation = self
                .global
                .declaration(id)
                .ok_or_else(|| self.unsupported(span, "missing effect operation"))?;
            let args = self.arguments(
                &operation.signature.params,
                operation.name.span.file,
                args,
                &BTreeMap::new(),
                span,
            )?;
            let key = self.string(&label);
            let handler = self.runtime("ril_rt_evidence_find", vec![self.evidence, key]);
            return Ok(self.invoke_closure(handler, args));
        }
        if def.kind == DefinitionKind::Local {
            let closure = self.read(id, span)?;
            let args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            return Ok(self.invoke_closure(closure, args));
        }
        if matches!(def.kind, DefinitionKind::Variant(_) | DefinitionKind::Type) {
            let unit_payload = args.is_empty()
                && matches!(self.global.typed.types.get(&self.ast().expr(callee).span),
                    Some(Ty::Callable(call)) if matches!(call.parameters.as_slice(), [parameter] if self.concrete(&parameter.ty) == Ty::Unit));
            let mut args = args
                .iter()
                .map(|arg| self.expr(arg.value))
                .collect::<Result<Vec<_>>>()?;
            if unit_payload {
                args.push(self.unit());
            }
            if let Some(&arity) = self.global.typed.tuple_payloads.get(&span)
                && let [tuple] = args.as_slice()
            {
                let tuple = *tuple;
                args = (0..arity)
                    .map(|index| {
                        let index = self.integer(&index.to_string());
                        self.runtime("ril_rt_load", vec![tuple, index])
                    })
                    .collect();
            }
            return Ok(self.tag(name, args));
        }
        let Some(function) = self.global.declaration(id) else {
            return Err(self.unsupported(span, "callable value"));
        };
        let metadata = self
            .global
            .typed
            .static_arguments(span, &self.statics, &self.types)?;
        let values = self.arguments(
            &function.signature.params,
            function.name.span.file,
            args,
            &metadata,
            span,
        )?;
        if function.body.is_some() {
            let mut types = self.types.clone();
            if let Some(arguments) = self.global.typed.type_arguments.get(&span) {
                types.extend(arguments.iter().map(|(&id, ty)| (id, self.concrete(ty))));
            }
            let captures = self.named_captures(id);
            let environment = (!captures.is_empty()).then(|| self.environment(&captures));
            let mut statics = self.statics.clone();
            statics.extend(metadata);
            let function = self.global.queue(Work::Named(id, types, captures, statics));
            let target = environment.map_or(Target::Function(function), |environment| {
                Target::FunctionWithEnv {
                    function,
                    environment,
                }
            });
            Ok(self.invoke(target, values, false))
        } else {
            Ok(self.invoke(Target::Foreign(self.global.foreign(id)?), values, false))
        }
    }

    fn named_captures(&self, id: DefinitionId) -> Vec<DefinitionId> {
        self.global
            .declaration(id)
            .into_iter()
            .flat_map(|fun| {
                fun.signature
                    .obligations
                    .state
                    .iter()
                    .filter(|clause| clause.kind == ril_sema::syntax::StateKind::Environment)
                    .flat_map(|clause| &clause.bindings)
            })
            .filter_map(|(_, path)| self.global.resolve(path.span))
            .collect()
    }

    fn environment(&mut self, captures: &[DefinitionId]) -> Register {
        if captures.is_empty() {
            return self.unit();
        }
        let environment = self.runtime("ril_rt_tuple", Vec::new());
        for id in captures {
            if let Some(&value) = self.locals.get(id) {
                self.runtime("ril_rt_append", vec![environment, value]);
            }
        }
        environment
    }

    fn box_closure(&mut self, id: FunctionId, arity: usize, environment: Register) -> Register {
        let address = self.instruction(Instruction::FunctionAddress(id));
        let arity = self.instruction(Instruction::RawU64(
            u64::try_from(arity).unwrap_or(u64::MAX),
        ));
        self.runtime(
            "ril_rt_closure",
            vec![address, arity, self.evidence, environment],
        )
    }

    fn invoke_closure(&mut self, closure: Register, args: Vec<Register>) -> Register {
        let arity = self.instruction(Instruction::RawU64(
            u64::try_from(args.len()).unwrap_or(u64::MAX),
        ));
        let address = self.runtime("ril_rt_closure_address", vec![closure, arity]);
        let evidence = self.runtime("ril_rt_closure_evidence", vec![closure]);
        let environment = self.runtime("ril_rt_closure_environment", vec![closure]);
        self.invoke(
            Target::Indirect {
                address,
                evidence,
                environment,
            },
            args,
            false,
        )
    }

    fn lift(
        &mut self,
        id: ExprId,
        arguments: Option<&BTreeMap<DefinitionId, Value>>,
    ) -> Result<Register> {
        let span = self.ast().expr(id).span;
        let mut referenced = Vec::new();
        for node in self
            .ast()
            .expressions()
            .filter(|node| node.span.start > span.start && node.span.end <= span.end)
        {
            match &node.value {
                Expr::Path(path) => {
                    if let Some(def) = self.global.resolve(path.span) {
                        referenced.push(def);
                    }
                }
                Expr::Record { fields, .. } => {
                    for field in fields {
                        if field.value.is_none()
                            && let Some(def) = self.global.resolve(field.name.span)
                        {
                            referenced.push(def);
                        }
                    }
                }
                _ => {}
            }
        }
        let mut capture = std::collections::BTreeSet::new();
        let mut visited_fns = std::collections::BTreeSet::new();
        while let Some(def) = referenced.pop() {
            if self.locals.contains_key(&def) {
                capture.insert(def);
            } else if visited_fns.insert(def) {
                let info = self.global.typed.hir.definition(def);
                if let Some(stmt_id) = info.stmt {
                    let ast = &self.global.typed.hir.file(info.name.span.file).ast;
                    if let StmtKind::Function(fun) = &ast.stmt(stmt_id).value.kind {
                        for (_, up_path) in fun
                            .signature
                            .obligations
                            .state
                            .iter()
                            .flat_map(|clause| &clause.bindings)
                        {
                            if let Some(up_def) = self.global.resolve(up_path.span) {
                                referenced.push(up_def);
                            }
                        }
                    }
                }
            }
        }
        let capture: Vec<_> = capture.into_iter().collect();
        let environment = self.environment(&capture);
        let mut statics = self.statics.clone();
        if let Some(arguments) = arguments {
            statics.extend(arguments.clone());
        }
        let work = Work::Closure {
            file: self.file,
            syntax: id,
            captures: capture,
            types: self.types.clone(),
            statics,
        };
        let function = self.global.queue(work);
        let arity = match &self.ast().expr(id).value {
            Expr::Closure { params, .. } => params.iter().filter(|param| !param.is_meta).count(),
            Expr::Accessor(_) => 1,
            _ => 0,
        };
        Ok(self.box_closure(function, arity, environment))
    }

    fn concrete(&self, ty: &Ty) -> Ty {
        ty.specialize(&self.types)
    }

    fn arguments(
        &mut self,
        parameters: &[Parameter],
        callee_file: FileId,
        args: &[Argument],
        metadata: &BTreeMap<DefinitionId, Value>,
        span: Span,
    ) -> Result<Vec<Register>> {
        let mut values = vec![None; parameters.len()];
        let mut provided = vec![false; values.len()];
        for arg in args {
            let index = if let Some(name) = &arg.name {
                parameters.iter().position(|p| {
                    p.name
                        .as_ref()
                        .is_some_and(|param| param.value == name.value)
                })
            } else {
                provided.iter().position(|present| !present)
            }
            .ok_or_else(|| self.unsupported(span, "argument binding"))?;
            if let Some(provided) = provided.get_mut(index) {
                *provided = true;
            }
            if parameters.get(index).is_some_and(|param| !param.is_meta) {
                let value = self.expr(arg.value)?;
                if let Some(slot) = values.get_mut(index) {
                    *slot = Some(value);
                }
            }
        }
        let file = self.file;
        let locals = self.locals.clone();
        let statics = self.statics.clone();
        self.statics.extend(metadata.clone());
        self.file = callee_file;
        let mut ordered = Vec::new();
        let result = (|| {
            for (param, value) in parameters.iter().zip(values) {
                if param.is_meta {
                    continue;
                }
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
        self.statics = statics;
        result
    }

    fn concurrent(
        &mut self,
        module: &str,
        name: &str,
        args: &[Argument],
        span: Span,
    ) -> Result<Register> {
        let symbol = match (module, name) {
            ("Fiber", "run") => "ril_fiber_run",
            ("Fiber", "scope") => "ril_fiber_scope",
            ("Fiber", "try_scope") => "ril_fiber_try_scope",
            ("Fiber", "spawn") => "ril_fiber_spawn",
            ("Fiber", "join")
                if args
                    .get(1)
                    .is_some_and(|arg| arg.mode == ril_sema::syntax::Mode::New) =>
            {
                "ril_fiber_join_owned"
            }
            ("Fiber", "join") => "ril_fiber_join",
            ("Fiber", "cancel") => "ril_fiber_cancel",
            ("Fiber", "cancel_scope") => "ril_fiber_cancel_scope",
            ("Fiber", "yield" | "yield_now") => "ril_fiber_yield",
            ("Fiber", "sleep" | "sleep_ms") => "ril_fiber_sleep",
            ("Fiber", "is_cancelled") => "ril_fiber_cancelled",
            ("Fiber", "uncancellable") => "ril_fiber_uncancellable",
            ("Fiber", "supervise") => "ril_fiber_supervise",
            ("Fiber", "timeout_ms") => "ril_fiber_timeout",
            ("Fiber", "zip") => "ril_fiber_zip",
            ("Fiber", "try_zip") => "ril_fiber_try_zip",
            ("Fiber", "race") => "ril_fiber_race",
            ("Fiber", "map") => "ril_fiber_map",
            ("Fiber", "try_map") => "ril_fiber_try_map",
            ("Channel", "bounded") | ("Channel", "mpsc") if !args.is_empty() => {
                "ril_channel_bounded"
            }
            ("Channel", "unbounded" | "mpsc") => "ril_channel_unbounded",
            ("Channel", "send") => "ril_channel_send",
            ("Channel", "recv") => "ril_channel_recv",
            ("Channel", "try_send") => "ril_channel_try_send",
            ("Channel", "try_recv") => "ril_channel_try_recv",
            ("Channel", "clone") => "ril_channel_clone",
            ("Channel", "close") => "ril_channel_close",
            ("Channel", "close_recv") => "ril_channel_close_recv",
            ("Channel", "drain") => "ril_channel_drain",
            _ => return Err(self.unsupported(span, &format!("{module}::{name}"))),
        };
        let args = args
            .iter()
            .map(|arg| self.expr(arg.value))
            .collect::<Result<Vec<_>>>()?;
        Ok(self.runtime(symbol, args))
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
            let draft = self.draft(DraftOp::Begin, vec![base]);
            let abort = self.block(0);
            let done = self.block(1);
            self.traps.push((self.cleanups.len(), abort));
            let callback = self.expr(update.value)?;
            self.invoke_closure(callback, vec![draft]);
            self.traps.pop();
            let result = self.draft(DraftOp::Commit, vec![draft]);
            self.terminate(Terminator::Jump(done, vec![result]));
            self.current = Some(abort);
            let outer_unwind = self.unwind_pad();
            self.term_at(
                abort,
                Terminator::Invoke {
                    target: Target::Draft(DraftOp::Abort),
                    evidence: self.evidence,
                    arguments: vec![draft],
                    normal: outer_unwind,
                    unwind: outer_unwind,
                    cleanup: true,
                    keep_result: false,
                },
            );
            self.current = Some(done);
            return Ok(self.result_param(done));
        }
        if name == "inner"
            && let [arg] = args
        {
            let wrapper = self.collection(arg.value)?;
            return Ok(
                match self
                    .global
                    .typed
                    .types
                    .get(&span)
                    .map(|ty| self.concrete(ty))
                {
                    Some(Ty::Unit) => self.unit(),
                    Some(Ty::Record(..)) => wrapper,
                    Some(Ty::Tuple(_)) if arg.mode == ril_sema::syntax::Mode::Mut => wrapper,
                    Some(Ty::Tuple(parts)) => {
                        let tuple = self.runtime("ril_rt_tuple", Vec::new());
                        for index in 0..parts.len() {
                            let key = self.integer(&index.to_string());
                            let value = self.runtime("ril_rt_load", vec![wrapper, key]);
                            self.runtime("ril_rt_append", vec![tuple, value]);
                        }
                        tuple
                    }
                    _ => {
                        let key = self.integer("0");
                        self.runtime("ril_rt_load", vec![wrapper, key])
                    }
                },
            );
        }
        if name == "inspect"
            && let [argument] = args
        {
            let argument_span = self.ast().expr(argument.value).span;
            let value = self.expr(argument.value)?;
            if let Some(plan) = self
                .global
                .typed
                .inspection_plan(span, argument_span, &self.types)
            {
                let plan = self.constant(&plan, span)?;
                return Ok(self.runtime("ril_rt_inspect_typed", vec![value, plan]));
            }
            return Ok(self.runtime("ril_rt_inspect", vec![value]));
        }
        let mut args = args
            .iter()
            .map(|arg| self.expr(arg.value))
            .collect::<Result<Vec<_>>>()?;
        if matches!(name, "Ok" | "Err" | "Some" | "Panicked") {
            if args.is_empty() && matches!(name, "Some" | "Ok" | "Err") {
                args.push(self.unit());
            }
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
            "read" => "ril_rt_file_read",
            "write" => "ril_rt_file_write",
            "to_f64" => "ril_rt_to_f64",
            "to_int" | "convert" => "ril_rt_to_int",
            "trunc" => "ril_rt_trunc",
            "checked_div" => "ril_rt_checked_div",
            "checked_rem" => "ril_rt_checked_rem",
            "clone" => "ril_rt_clone",
            "push" => "ril_rt_append",
            "panic_message" => "ril_rt_panic_message",
            _ => return Err(self.unsupported(span, &format!("primitive {name}"))),
        };
        Ok(self.runtime(symbol, args))
    }

    fn text_builtin(&mut self, builtin: TextBuiltin, args: &[Argument]) -> Result<Register> {
        use TextBuiltin::*;
        let symbol = match builtin {
            Join => "ril_rt_str_join",
            StartsWith => "ril_rt_str_starts_with",
            EndsWith => "ril_rt_str_ends_with",
            ScalarAt => "ril_rt_str_at",
            Scalars => "ril_rt_str_scalars",
            FromScalars => "ril_rt_str_from_scalars",
            EncodeUtf8 => "ril_rt_encode_utf8",
            DecodeUtf8 => "ril_rt_decode_utf8",
            ByteAt => "ril_rt_bytes_at",
            ToArray => "ril_rt_bytes_to_array",
            FromArray => "ril_rt_bytes_from_array",
        };
        let order = builtin
            .argument_order(
                args.iter()
                    .map(|arg| arg.name.as_ref().map(|label| label.value.as_str())),
            )
            .unwrap_or_else(|| ril_base::ice!("text primitive arguments passed type checking"));
        let written = args
            .iter()
            .map(|arg| self.expr(arg.value))
            .collect::<Result<Vec<_>>>()?;
        let args = order
            .into_iter()
            .map(|index| {
                written
                    .get(index)
                    .copied()
                    .unwrap_or_else(|| ril_base::ice!("missing checked text argument"))
            })
            .collect();
        Ok(self.runtime(symbol, args))
    }

    fn absorb(&mut self, action: ExprId, span: Span) -> Result<Register> {
        let action = self.expr(action)?;
        let caught = self.block(0);
        let join = self.block(1);
        self.traps.push((self.cleanups.len(), caught));
        let result = self.invoke_closure(action, Vec::new());
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
                if let Some(binding) = binding {
                    self.bind(*binding, value)?;
                }
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
