//! Selective native CPS conversion. Calls and operations become explicit native
//! continuation edges; ordinary value operations stay in the shared Core IR.
use ril_compiler_core::{
    phase::{NotImplemented, Stage},
    source::Span,
};
use ril_ir::{
    core::{self, Expr, ExprKind, Pattern, Statement},
    cps::{self, BlockId, Input, Terminator},
};
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
mod concurrent_tests;
mod iteration;
mod metering;
mod parameters;
mod rename;

/// Control and host operations retain the native return continuation even when
/// the source has no explicit perform/handler. This chooses a calling convention,
/// not a finite-computation proof or a claim that every host adapter already parks.
/// Keep this table aligned with runtime-api's managed-entry guard; the backend
/// tests both contracts without adding a runtime dependency to codegen.
pub fn native_step_builtin(name: &str) -> bool {
    let name = name.strip_prefix("Prelude::").unwrap_or(name);
    matches!(
        name,
        "\0ril.foreign.invoke"
            | "Concurrent::scope"
            | "Concurrent::fork"
            | "Concurrent::join"
            | "Channel::bounded"
            | "Channel::send"
            | "Channel::recv"
            | "Channel::detach"
            | "Channel::attach"
            | "Channel::close"
            | "Parallel::map"
            | "Parallel::map_bounded"
            | "Parallel::find"
            | "Parallel::first"
            | "Parallel::any"
            | "Parallel::fold"
            | "Parallel::join"
            | "Parallel::join3"
            | "Parallel::for_each"
            | "Io::read_buffered"
            | "Io::read_buffered_at"
            | "Io::write_buffered"
            | "Io::flush"
            | "Time::sleep"
            | "Random::entropy"
            | "Io::stdin_read"
            | "Io::stdout_write"
            | "Io::stderr_write"
            | "Io::write_stdout"
            | "Io::write_stderr"
            | "print"
            | "println"
            | "File::open"
            | "File::open_path"
            | "File::read"
            | "File::read_chunk"
            | "File::write"
            | "File::seek"
            | "File::sync"
            | "File::close"
            | "File::read_bytes"
            | "File::read_text"
            | "File::write_bytes"
            | "File::write_text"
            | "File::metadata"
            | "File::read_dir"
            | "File::create_dir"
            | "File::create_dir_all"
            | "File::remove_file"
            | "File::remove_dir"
            | "File::rename"
            | "File::canonicalize"
            | "File::temp_file"
            | "Process::run"
            | "Process::spawn"
            | "Process::wait"
            | "Process::terminate"
    ) || name
        .strip_prefix("Channel::__bounded_")
        .is_some_and(|location| {
            let parts: Vec<_> = location.split('_').collect();
            parts.len() == 3
                && parts.iter().all(|part| {
                    !part.is_empty()
                        && part.bytes().all(|byte| byte.is_ascii_digit())
                        && part.parse::<u32>().is_ok()
                })
        })
}

fn unsupported(detail: impl Into<String>) -> NotImplemented {
    NotImplemented::new(Stage::Lowering, detail)
}
fn expression(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}
fn name(value: &str, span: Span) -> Expr {
    expression(ExprKind::Name(value.into()), span)
}
fn unit(span: Span) -> Expr {
    expression(ExprKind::Literal(core::Literal::Unit), span)
}
pub fn normalize(function: &core::Function) -> Result<core::Function, NotImplemented> {
    rename::function(function)
}
pub fn contains_budget(program: &core::Program) -> bool {
    let mut found = false;
    for function in &program.functions {
        walk_function(function, &mut |expr| {
            found |= matches!(expr.kind, ExprKind::Budget { .. })
        });
    }
    for function in &program.external_functions {
        for parameter in &function.parameters {
            if let Some(default) = &parameter.default {
                walk_expr(default, &mut |expr| {
                    found |= matches!(expr.kind, ExprKind::Budget { .. })
                });
            }
        }
    }
    walk_block(&program.globals, &mut |expr| {
        found |= matches!(expr.kind, ExprKind::Budget { .. })
    });
    found
}

/// Local or computed callees can carry a residual operation row. They therefore
/// enter the CPS domain even when no direct operation appears in the caller.
pub fn suspending_functions(program: &core::Program) -> BTreeSet<String> {
    let operations: BTreeSet<_> = program
        .operations
        .iter()
        .map(|operation| operation.name.clone())
        .collect();
    let known: BTreeSet<_> = program
        .functions
        .iter()
        .map(|function| function.name.clone())
        .chain(
            program
                .external_functions
                .iter()
                .map(|function| function.internal_name.clone()),
        )
        .collect();
    let mut marked: BTreeSet<_> = program
        .external_functions
        .iter()
        .map(|function| function.internal_name.clone())
        .collect();
    for function in &program.functions {
        let mut seed = has_handler(&function.body) || has_scoped(&function.body);
        seed |= nested_suspends(&function.body, &operations);
        walk_function(function, &mut |expr| {
            seed |= matches!(
                expr.kind,
                ExprKind::Budget { .. }
                    | ExprKind::Perform { .. }
                    | ExprKind::Control {
                        operation: core::ControlOperation::Resume,
                        ..
                    }
            );
            if let ExprKind::Name(name) = &expr.kind {
                seed |= operations.contains(name) || native_step_builtin(name);
            }
            seed |= direct_handler(expr);
            seed |= direct_scoped(expr);
            if let ExprKind::Block(block)
            | ExprKind::Loop { body: block, .. }
            | ExprKind::While { body: block, .. }
            | ExprKind::For { body: block, .. } = &expr.kind
            {
                seed |= nested_suspends(block, &operations);
            }
        });
        if seed {
            marked.insert(function.name.clone());
        }
    }
    // A callable parameter, local alias, or computed callee can receive a CPS
    // value from a caller. Absence of a direct operation elsewhere in this
    // module is not evidence that its dynamic target uses the managed ABI.
    let mut globals = BTreeSet::new();
    collect_bindings(&program.globals, &mut globals);
    loop {
        let before = marked.len();
        for function in &program.functions {
            let mut locals = BTreeSet::new();
            locals.extend(globals.iter().cloned());
            for parameter in &function.parameters {
                pattern_names(&parameter.pattern, &mut locals);
            }
            collect_bindings(&function.body, &mut locals);
            walk_function(function, &mut |expr| {
                if let ExprKind::Lambda { parameters, .. } = &expr.kind {
                    for parameter in parameters {
                        pattern_names(&parameter.pattern, &mut locals);
                    }
                }
                if let ExprKind::Block(block)
                | ExprKind::Loop { body: block, .. }
                | ExprKind::While { body: block, .. }
                | ExprKind::For { body: block, .. } = &expr.kind
                {
                    collect_bindings(block, &mut locals);
                }
            });
            let mut suspends = false;
            walk_function(function, &mut |expr| match &expr.kind {
                ExprKind::Budget { .. }
                | ExprKind::Perform { .. }
                | ExprKind::Control {
                    operation: core::ControlOperation::Resume,
                    ..
                } => suspends = true,
                ExprKind::Call {
                    callee, arguments, ..
                } => {
                    suspends |= match &callee.kind {
                        ExprKind::Name(target) => {
                            locals.contains(target) || marked.contains(target)
                        }
                        _ => true,
                    };
                    // A standard higher-order operation may invoke a supplied
                    // user callable. Never classify its actual row as empty.
                    if matches!(&callee.kind,ExprKind::Name(target)if !known.contains(target)&&!locals.contains(target))
                    {
                        for argument in arguments {
                            walk_expr(&argument.value, &mut |value| {
                                if let ExprKind::Name(target) = &value.kind {
                                    suspends |= marked.contains(target)
                                }
                            });
                        }
                    }
                }
                ExprKind::Derive { recipe, .. } => {
                    suspends |= match &recipe.kind {
                        ExprKind::Name(target) => {
                            locals.contains(target) || marked.contains(target)
                        }
                        _ => true,
                    };
                }
                _ => suspends |= direct_handler(expr),
            });
            suspends |= has_handler(&function.body);
            if suspends {
                marked.insert(function.name.clone());
            }
        }
        if marked.len() == before {
            return marked;
        }
    }
}

pub fn lower(function: &core::Function) -> Result<cps::Function, NotImplemented> {
    lower_with_captures(function, &BTreeSet::new())
}
pub fn lower_with_captures(
    function: &core::Function,
    captures: &BTreeSet<String>,
) -> Result<cps::Function, NotImplemented> {
    lower_options(function, captures, false)
}
pub fn lower_metered_with_captures(
    function: &core::Function,
    captures: &BTreeSet<String>,
) -> Result<cps::Function, NotImplemented> {
    lower_options(function, captures, true)
}
pub fn lower_metered(function: &core::Function) -> Result<cps::Function, NotImplemented> {
    lower_metered_with_captures(function, &BTreeSet::new())
}
fn lower_options(
    function: &core::Function,
    captures: &BTreeSet<String>,
    metered: bool,
) -> Result<cps::Function, NotImplemented> {
    let renamed = rename::function(function)?;
    let function = &renamed;
    let mut locals = BTreeSet::new();
    locals.extend(captures.iter().cloned());
    let mut counts = BTreeMap::<String, u32>::new();
    for parameter in &function.parameters {
        let mut names = BTreeSet::new();
        pattern_names(&parameter.pattern, &mut names);
        for name in names {
            *counts.entry(name.clone()).or_default() += 1;
            locals.insert(name);
        }
    }
    let defaults = core::Block {
        statements: function
            .parameters
            .iter()
            .filter_map(|parameter| parameter.default.clone())
            .map(|expression| Statement::Expr {
                expression,
                terminated: false,
            })
            .collect(),
    };
    collect_binding_counts(&defaults, &mut counts);
    collect_binding_counts(&function.body, &mut counts);
    if counts.values().any(|count| *count > 1) {
        return Err(unsupported(
            "CPS lexical shadowing requires distinct environment slots",
        ));
    }
    collect_bindings(&function.body, &mut locals);
    collect_bindings(&defaults, &mut locals);
    let mut builder = Builder {
        metered,
        blocks: vec![],
        locals,
        next_temporary: 0,
        span: function.span,
        loops: vec![],
        handler_depth: 0,
        scopes: vec![],
        retained_lambdas: BTreeSet::new(),
        hoisted_bindings: BTreeSet::new(),
    };
    let result = builder.temporary();
    let done = builder.block(
        Input::Continue(None),
        vec![],
        Terminator::Return {
            value: name(&result, function.span),
            function: false,
        },
    );
    let body = builder.scoped_block(&function.body, &result, done)?;
    let event = match function.role {
        core::FunctionRole::Ordinary => Some(core::ChargeEvent::FunctionEntry),
        core::FunctionRole::Handler => Some(core::ChargeEvent::HandlerEntry),
        core::FunctionRole::Synthetic => None,
    };
    let body = builder.charge(event, function.span, body);
    // Omitted defaults are argument evaluation, before logical body entry.
    // A default may panic or invoke another metered callable without ever
    // reaching this function's own entry event.
    let body = builder.parameters(&function.parameters, body)?;
    let entry = builder.block(Input::Function, vec![], Terminator::Jump(body));
    Ok(cps::Function {
        role: function.role,
        metered,
        name: function.name.clone(),
        definition: function.definition,
        generic_parameters: function.generic_parameters.clone(),
        span: function.span,
        parameters: function.parameters.clone(),
        entry,
        locals: builder.locals,
        retained_lambdas: builder.retained_lambdas,
        blocks: builder.blocks,
    })
}

pub fn lambda_suspends(
    body: &Expr,
    dynamic: &BTreeSet<String>,
    known_cps: &BTreeSet<String>,
    operations: &BTreeSet<String>,
) -> bool {
    let mut seed = false;
    walk_expr(body, &mut |expr| {
        if let ExprKind::Block(block)
        | ExprKind::Loop { body: block, .. }
        | ExprKind::While { body: block, .. }
        | ExprKind::For { body: block, .. } = &expr.kind
        {
            seed |= nested_suspends(block, operations);
            seed |= has_scoped(block);
        }
        seed |= matches!(
            expr.kind,
            ExprKind::Budget { .. }
                | ExprKind::Perform { .. }
                | ExprKind::Control {
                    operation: core::ControlOperation::Resume,
                    ..
                }
        );
        if let ExprKind::Block(block) = &expr.kind {
            seed |= has_handler(block);
        }
        if let ExprKind::Name(name) = &expr.kind {
            seed |= operations.contains(name) || native_step_builtin(name);
        }
    });
    let mut dynamic = dynamic.clone();
    walk_expr(body, &mut |expr| {
        if let ExprKind::Block(block) = &expr.kind {
            collect_bindings(block, &mut dynamic);
        }
    });
    let mut suspends = seed;
    walk_expr(body, &mut |expr| match &expr.kind {
        ExprKind::Call { callee, .. } => {
            suspends |= match &callee.kind {
                ExprKind::Name(target) => dynamic.contains(target) || known_cps.contains(target),
                _ => true,
            }
        }
        ExprKind::Derive { recipe, .. } => {
            suspends |= match &recipe.kind {
                ExprKind::Name(target) => dynamic.contains(target) || known_cps.contains(target),
                _ => true,
            }
        }
        ExprKind::Name(target) => suspends |= known_cps.contains(target),
        _ => {}
    });
    suspends
}

pub fn callable_suspends(
    parameters: &[core::Parameter],
    body: &Expr,
    dynamic: &BTreeSet<String>,
    known_cps: &BTreeSet<String>,
    operations: &BTreeSet<String>,
) -> bool {
    lambda_suspends(body, dynamic, known_cps, operations)
        || parameters
            .iter()
            .filter_map(|parameter| parameter.default.as_ref())
            .any(|default| lambda_suspends(default, dynamic, known_cps, operations))
}

struct Builder {
    metered: bool,
    blocks: Vec<cps::Block>,
    locals: BTreeSet<String>,
    next_temporary: u32,
    span: Span,
    loops: Vec<(BlockId, BlockId, Option<String>, usize)>,
    handler_depth: u32,
    scopes: Vec<String>,
    retained_lambdas: BTreeSet<(u32, u32, u32)>,
    hoisted_bindings: BTreeSet<String>,
}
impl Builder {
    fn temporary(&mut self) -> String {
        let name = format!("\0ril.cps.value.{}", self.next_temporary);
        self.next_temporary += 1;
        self.locals.insert(name.clone());
        name
    }
    fn block(
        &mut self,
        input: Input,
        instructions: Vec<Statement>,
        terminator: Terminator,
    ) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(cps::Block {
            input,
            instructions: instructions
                .into_iter()
                .map(|statement| cps::Instruction::Statement(Box::new(statement)))
                .collect(),
            terminator,
        });
        id
    }
    fn scope_instruction(&mut self, instruction: cps::Instruction, next: BlockId) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(cps::Block {
            input: Input::Continue(None),
            instructions: vec![instruction],
            terminator: Terminator::Jump(next),
        });
        id
    }
    fn scoped_block(
        &mut self,
        block: &core::Block,
        destination: &str,
        next: BlockId,
    ) -> Result<BlockId, NotImplemented> {
        let marker = self.temporary();
        let leave = self.block(
            Input::Continue(None),
            vec![],
            Terminator::ScopeLeave {
                marker: marker.clone(),
                value: name(destination, self.span),
                next,
            },
        );
        self.scopes.push(marker.clone());
        let saved_hoisted = self.hoisted_bindings.clone();
        let functions: Vec<_> = block
            .statements
            .iter()
            .filter_map(|statement| match statement {
                Statement::Function(function) => Some(function.clone()),
                _ => None,
            })
            .collect();
        let mut declarations = BTreeSet::new();
        if !functions.is_empty() {
            for statement in &block.statements {
                match statement {
                    Statement::Bind { pattern, .. } => pattern_names(pattern, &mut declarations),
                    Statement::Function(function) => {
                        declarations.insert(function.name.clone());
                        if self.handler_depth > 0 {
                            self.retained_lambdas.insert((
                                function.span.file.0,
                                function.span.start,
                                function.span.end,
                            ));
                        }
                    }
                    _ => {}
                }
            }
            self.hoisted_bindings.extend(declarations.iter().cloned());
        }
        let mut body = self.statements(&block.statements, destination, leave)?;
        if !functions.is_empty() {
            body = self.scope_instruction(
                cps::Instruction::Hoist {
                    declarations,
                    functions,
                },
                body,
            );
        }
        self.hoisted_bindings = saved_hoisted;
        self.scopes.pop();
        Ok(self.scope_instruction(cps::Instruction::ScopeEnter { marker }, body))
    }
    fn unwind_scopes(&mut self, depth: usize, value: &str, mut next: BlockId) -> BlockId {
        // Build backwards so execution leaves the innermost scope first.
        let markers = self.scopes[depth..].to_vec();
        for marker in markers {
            next = self.block(
                Input::Continue(None),
                vec![],
                Terminator::ScopeLeave {
                    marker,
                    value: name(value, self.span),
                    next,
                },
            );
        }
        next
    }
    fn assign_result(&mut self, destination: &str, value: Expr, next: BlockId) -> BlockId {
        self.block(
            Input::Continue(None),
            vec![Statement::Bind {
                pattern: Pattern::Name(destination.into()),
                value,
                scoped: false,
            }],
            Terminator::Jump(next),
        )
    }
    fn continuation(&mut self, destination: &str, next: BlockId) -> BlockId {
        self.block(
            Input::Continue(Some(Pattern::Name(destination.into()))),
            vec![],
            Terminator::Jump(next),
        )
    }
    fn tail_answer(&self, mut next: BlockId, destination: &str) -> bool {
        let mut visited = BTreeSet::new();
        while visited.insert(next) {
            let block = &self.blocks[next.0 as usize];
            if !matches!(block.input, Input::Continue(None)) {
                return false;
            }
            if !block.instructions.is_empty() {
                return false;
            }
            match &block.terminator {
                Terminator::ScopeLeave {
                    value,
                    next: target,
                    ..
                } if matches!(&value.kind, ExprKind::Name(name) if name == destination) => {
                    next = *target
                }
                Terminator::Jump(target) => next = *target,
                Terminator::Return {
                    value,
                    function: false,
                } => return matches!(&value.kind,ExprKind::Name(name)if name==destination),
                _ => return false,
            }
        }
        false
    }
    fn statements(
        &mut self,
        statements: &[Statement],
        destination: &str,
        next: BlockId,
    ) -> Result<BlockId, NotImplemented> {
        let Some((first, rest)) = statements.split_first() else {
            return Ok(self.assign_result(destination, unit(self.span), next));
        };
        match first {
            Statement::Handle { definition, arms } => {
                let body_result = self.temporary();
                let body_done = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Return {
                        value: name(&body_result, self.span),
                        function: false,
                    },
                );
                self.handler_depth += 1;
                let body = self.statements(rest, &body_result, body_done)?;
                self.handler_depth -= 1;
                let body = self.block(Input::HandlerBody, vec![], Terminator::Jump(body));
                let mut lowered_arms = vec![];
                for arm in arms {
                    let result = self.temporary();
                    let done = self.block(
                        Input::Continue(None),
                        vec![],
                        Terminator::Return {
                            value: name(&result, arm.body.span),
                            function: false,
                        },
                    );
                    let entry = self.expr(&arm.body, &result, done)?;
                    let entry =
                        self.charge(Some(core::ChargeEvent::HandlerEntry), arm.body.span, entry);
                    let entry = self.block(
                        Input::HandlerArm(arm.parameters.clone()),
                        vec![],
                        Terminator::Jump(entry),
                    );
                    lowered_arms.push(cps::Arm {
                        source: arm.clone(),
                        operation: arm.operation,
                        entry,
                    });
                }
                let next = self.continuation(destination, next);
                Ok(self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Handle {
                        definition: *definition,
                        body,
                        arms: lowered_arms,
                        next,
                    },
                ))
            }
            Statement::Bind {
                pattern,
                value,
                scoped,
            } => {
                let tail = self.statements(rest, destination, next)?;
                let temporary = self.temporary();
                let bind = self.block(
                    Input::Continue(None),
                    vec![Statement::Bind {
                        pattern: pattern.clone(),
                        value: name(&temporary, value.span),
                        scoped: *scoped,
                    }],
                    Terminator::Jump(tail),
                );
                let mut names = BTreeSet::new();
                pattern_names(pattern, &mut names);
                let reused = names
                    .intersection(&self.hoisted_bindings)
                    .cloned()
                    .collect::<BTreeSet<_>>();
                if !reused.is_empty() {
                    self.blocks[bind.0 as usize]
                        .instructions
                        .insert(0, cps::Instruction::ReuseBindings { names: reused });
                }
                self.expr(value, &temporary, bind)
            }
            Statement::Expr {
                expression,
                terminated,
            } => {
                if rest.is_empty() && !*terminated {
                    return self.expr(expression, destination, next);
                }
                let tail = self.statements(rest, destination, next)?;
                let discard = self.temporary();
                self.expr(expression, &discard, tail)
            }
            Statement::Assign {
                target,
                operator,
                value,
            } => {
                let mut address_values = vec![];
                let mut address_slots = vec![];
                let target = match &target.kind {
                    ExprKind::Name(_) => target.clone(),
                    ExprKind::Field {
                        base,
                        field,
                        safe: false,
                    } => {
                        let slot = self.temporary();
                        address_values.push(*base.clone());
                        address_slots.push(slot.clone());
                        expression(
                            ExprKind::Field {
                                base: Box::new(name(&slot, base.span)),
                                field: field.clone(),
                                safe: false,
                            },
                            target.span,
                        )
                    }
                    ExprKind::Index {
                        base,
                        index,
                        safe: false,
                    } => {
                        let a = self.temporary();
                        let b = self.temporary();
                        address_values.push(*base.clone());
                        address_values.push(*index.clone());
                        address_slots.push(a.clone());
                        address_slots.push(b.clone());
                        expression(
                            ExprKind::Index {
                                base: Box::new(name(&a, base.span)),
                                index: Box::new(name(&b, index.span)),
                                safe: false,
                            },
                            target.span,
                        )
                    }
                    _ => return Err(unsupported("CPS assignment address")),
                };
                let tail = self.statements(rest, destination, next)?;
                let rhs = self.temporary();
                let old = if operator != "=" {
                    Some(self.temporary())
                } else {
                    None
                };
                let final_value = if let Some(old) = &old {
                    expression(
                        ExprKind::Binary {
                            operator: operator.trim_end_matches('=').into(),
                            left: Box::new(name(old, target.span)),
                            right: Box::new(name(&rhs, value.span)),
                        },
                        value.span,
                    )
                } else {
                    name(&rhs, value.span)
                };
                let assign = self.block(
                    Input::Continue(None),
                    vec![Statement::Assign {
                        target: target.clone(),
                        operator: "=".into(),
                        value: final_value,
                    }],
                    Terminator::Jump(tail),
                );
                let entry = self.expr(value, &rhs, assign)?;
                let entry = if let Some(old) = old {
                    self.assign_result(&old, target, entry)
                } else {
                    entry
                };
                self.values(&address_values, &address_slots, entry)
            }
            Statement::Function(_) => self.statements(rest, destination, next),
        }
    }
    fn values(
        &mut self,
        values: &[Expr],
        destinations: &[String],
        mut next: BlockId,
    ) -> Result<BlockId, NotImplemented> {
        for (value, destination) in values.iter().zip(destinations).rev() {
            next = self.expr(value, destination, next)?;
        }
        Ok(next)
    }
    fn expr(
        &mut self,
        expr: &Expr,
        destination: &str,
        next: BlockId,
    ) -> Result<BlockId, NotImplemented> {
        let span = expr.span;
        match &expr.kind {
            ExprKind::ConstRef(_) | ExprKind::Literal(_) | ExprKind::Name(_) => {
                Ok(self.assign_result(destination, expr.clone(), next))
            }
            ExprKind::Lambda { .. } => {
                if self.handler_depth > 0 {
                    self.retained_lambdas
                        .insert((span.file.0, span.start, span.end));
                }
                Ok(self.assign_result(destination, expr.clone(), next))
            }
            ExprKind::Block(block) => self.scoped_block(block, destination, next),
            ExprKind::Call {
                callee,
                arguments,
                callback_entry,
            } => {
                let target = self.temporary();
                let args: Vec<_> = arguments.iter().map(|_| self.temporary()).collect();
                let continuation = self.continuation(destination, next);
                let call = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Call {
                        callback_entry: *callback_entry,
                        span,
                        callee: name(&target, span),
                        arguments: arguments
                            .iter()
                            .zip(&args)
                            .map(|(argument, key)| core::Argument {
                                label: argument.label.clone(),
                                value: name(key, argument.value.span),
                            })
                            .collect(),
                        next: continuation,
                    },
                );
                let values: Vec<_> = arguments
                    .iter()
                    .map(|argument| argument.value.clone())
                    .collect();
                // A literal body passed directly to the canonical scope entry
                // is invoked immediately in this task, while these handlers
                // are live. Avoid marking just this creation as retaining a
                // handler; do not remove a span marker shared by another IR
                // expression or touch lambdas created inside the body.
                let entry = if matches!(&callee.kind, ExprKind::Name(name) if name == "Concurrent::scope")
                    && let [action] = values.as_slice()
                    && matches!(action.kind, ExprKind::Lambda { .. })
                {
                    self.assign_result(&args[0], action.clone(), call)
                } else {
                    self.values(&values, &args, call)?
                };
                self.expr(callee, &target, entry)
            }
            ExprKind::Perform {
                operation,
                arguments,
            } => {
                let args: Vec<_> = arguments.iter().map(|_| self.temporary()).collect();
                let continuation = self.continuation(destination, next);
                let perform = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Perform {
                        span,
                        operation: *operation,
                        arguments: arguments
                            .iter()
                            .zip(&args)
                            .map(|(argument, key)| core::Argument {
                                label: argument.label.clone(),
                                value: name(key, argument.value.span),
                            })
                            .collect(),
                        next: continuation,
                    },
                );
                let values: Vec<_> = arguments
                    .iter()
                    .map(|argument| argument.value.clone())
                    .collect();
                self.values(&values, &args, perform)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_block = self.expr(then_branch, destination, next)?;
                let fallback = else_branch
                    .as_deref()
                    .cloned()
                    .unwrap_or_else(|| unit(span));
                let else_block = self.expr(&fallback, destination, next)?;
                let value = self.temporary();
                let branch = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Branch {
                        condition: name(&value, condition.span),
                        then_block,
                        else_block,
                    },
                );
                self.expr(condition, &value, branch)
            }
            ExprKind::Unary { operator, operand } => {
                let value = self.temporary();
                let compute = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Unary {
                            operator: operator.clone(),
                            operand: Box::new(name(&value, operand.span)),
                        },
                        span,
                    ),
                    next,
                );
                self.expr(operand, &value, compute)
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "&&" | "||") => {
                let left_value = self.temporary();
                let right_block = self.expr(right, destination, next)?;
                let skipped = self.assign_result(destination, name(&left_value, left.span), next);
                let (then_block, else_block) = if operator == "&&" {
                    (right_block, skipped)
                } else {
                    (skipped, right_block)
                };
                let branch = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Branch {
                        condition: name(&left_value, left.span),
                        then_block,
                        else_block,
                    },
                );
                self.expr(left, &left_value, branch)
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => self.coalesce(left, right, destination, next, span),
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if matches!(operator.as_str(), "|>" | "!>") {
                    return Err(unsupported("CPS unlowered pipeline"));
                }
                let a = self.temporary();
                let b = self.temporary();
                let compute = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Binary {
                            operator: operator.clone(),
                            left: Box::new(name(&a, left.span)),
                            right: Box::new(name(&b, right.span)),
                        },
                        span,
                    ),
                    next,
                );
                let right = self.expr(right, &b, compute)?;
                self.expr(left, &a, right)
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let names: Vec<_> = items.iter().map(|_| self.temporary()).collect();
                let values: Vec<_> = items
                    .iter()
                    .zip(&names)
                    .map(|(value, key)| name(key, value.span))
                    .collect();
                let kind = if matches!(expr.kind, ExprKind::Tuple(_)) {
                    ExprKind::Tuple(values)
                } else {
                    ExprKind::Array(values)
                };
                let compute = self.assign_result(destination, expression(kind, span), next);
                self.values(items, &names, compute)
            }
            ExprKind::Record {
                members,
                fields,
                spread,
            } => {
                let source_members = if members.is_empty() {
                    spread
                        .iter()
                        .map(|value| core::RecordMember::Spread(*value.clone()))
                        .chain(fields.iter().map(|(key, value)| {
                            core::RecordMember::Field(key.clone(), value.clone())
                        }))
                        .collect::<Vec<_>>()
                } else {
                    members.clone()
                };
                let mut values = vec![];
                let mut keys = vec![];
                let mut lowered = vec![];
                for member in source_members {
                    let slot = self.temporary();
                    match member {
                        core::RecordMember::Field(key, value) => {
                            lowered.push(core::RecordMember::Field(key, name(&slot, value.span)));
                            values.push(value);
                        }
                        core::RecordMember::Spread(value) => {
                            lowered.push(core::RecordMember::Spread(name(&slot, value.span)));
                            values.push(value);
                        }
                    }
                    keys.push(slot);
                }
                let compute = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Record {
                            members: lowered,
                            fields: vec![],
                            spread: None,
                        },
                        span,
                    ),
                    next,
                );
                self.values(&values, &keys, compute)
            }
            ExprKind::Map(entries) => {
                let mut values = vec![];
                let mut keys = vec![];
                let mut lowered = vec![];
                for (key, value) in entries {
                    let a = self.temporary();
                    let b = self.temporary();
                    lowered.push((name(&a, key.span), name(&b, value.span)));
                    values.push(key.clone());
                    values.push(value.clone());
                    keys.push(a);
                    keys.push(b);
                }
                let compute =
                    self.assign_result(destination, expression(ExprKind::Map(lowered), span), next);
                self.values(&values, &keys, compute)
            }
            ExprKind::Derive { base, recipe } => {
                let draft = self.temporary();
                let action = self.temporary();
                let ignored = self.temporary();
                let publish = self.assign_result(destination, name(&draft, span), next);
                let returned = self.continuation(&ignored, publish);
                let invoke = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Call {
                        callback_entry: true,
                        span,
                        callee: name(&action, recipe.span),
                        arguments: vec![core::Argument {
                            label: None,
                            value: name(&draft, span),
                        }],
                        next: returned,
                    },
                );
                let action = self.expr(recipe, &action, invoke)?;
                // Derive snapshots first, then evaluates and invokes its recipe.
                // The draft stays in the continuation environment and is only
                // published after the recipe returns normally.
                let cloned = expression(
                    ExprKind::Call {
                        callback_entry: false,
                        callee: Box::new(name("Prelude::clone", span)),
                        arguments: vec![core::Argument {
                            label: None,
                            value: *base.clone(),
                        }],
                    },
                    span,
                );
                self.expr(&cloned, &draft, action)
            }
            ExprKind::Range {
                lower,
                upper,
                inclusive,
            } => {
                let mut values = vec![];
                let mut keys = vec![];
                let mut bound = |value: &Option<Box<Expr>>, builder: &mut Self| {
                    value.as_ref().map(|value| {
                        let slot = builder.temporary();
                        values.push(*value.clone());
                        keys.push(slot.clone());
                        Box::new(name(&slot, value.span))
                    })
                };
                let lower = bound(lower, self);
                let upper = bound(upper, self);
                let compute = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Range {
                            lower,
                            upper,
                            inclusive: *inclusive,
                        },
                        span,
                    ),
                    next,
                );
                self.values(&values, &keys, compute)
            }
            ExprKind::Field { base, field, safe } => {
                let value = self.temporary();
                let compute = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Field {
                            base: Box::new(name(&value, base.span)),
                            field: field.clone(),
                            safe: *safe,
                        },
                        span,
                    ),
                    next,
                );
                self.expr(base, &value, compute)
            }
            ExprKind::Index { base, index, safe } => {
                let a = self.temporary();
                let b = self.temporary();
                let compute = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Index {
                            base: Box::new(name(&a, base.span)),
                            index: Box::new(name(&b, index.span)),
                            safe: *safe,
                        },
                        span,
                    ),
                    next,
                );
                let right = self.expr(index, &b, compute)?;
                let lookup = if *safe {
                    let skipped = self.assign_result(destination, name(&a, base.span), next);
                    self.block(
                        Input::Continue(None),
                        vec![],
                        Terminator::Branch {
                            condition: expression(
                                ExprKind::Is {
                                    value: Box::new(name(&a, base.span)),
                                    pattern: Pattern::Constructor {
                                        tag: "Prelude::None".into(),
                                        arguments: vec![],
                                    },
                                },
                                span,
                            ),
                            then_block: skipped,
                            else_block: right,
                        },
                    )
                } else {
                    right
                };
                self.expr(base, &a, lookup)
            }
            ExprKind::Is { value, pattern } => {
                let subject = self.temporary();
                let test = self.pattern_test(pattern, &subject, destination, next, span)?;
                self.expr(value, &subject, test)
            }
            ExprKind::Match { value, arms } => {
                let subject = self.temporary();
                let failure = expression(
                    ExprKind::Call {
                        callback_entry: false,
                        callee: Box::new(name("Prelude::panic", span)),
                        arguments: vec![core::Argument {
                            label: None,
                            value: expression(
                                ExprKind::Literal(core::Literal::String(
                                    "nonexhaustive native CPS match".into(),
                                )),
                                span,
                            ),
                        }],
                    },
                    span,
                );
                let mut tail = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Return {
                        value: failure,
                        function: false,
                    },
                );
                for arm in arms.iter().rev() {
                    let mut bound = BTreeSet::new();
                    pattern_names(&arm.pattern, &mut bound);
                    self.locals.extend(bound.iter().cloned());
                    let mut success = self.expr(&arm.body, destination, next)?;
                    if let Some(guard) = &arm.guard {
                        let matched = self.temporary();
                        let branch = self.block(
                            Input::Continue(None),
                            vec![],
                            Terminator::Branch {
                                condition: name(&matched, guard.span),
                                then_block: success,
                                else_block: tail,
                            },
                        );
                        success = self.expr(guard, &matched, branch)?;
                    }
                    if !bound.is_empty() {
                        success = self.block(
                            Input::Continue(None),
                            vec![Statement::Bind {
                                pattern: arm.pattern.clone(),
                                value: name(&subject, value.span),
                                scoped: false,
                            }],
                            Terminator::Jump(success),
                        );
                    }
                    let matched = self.temporary();
                    let branch = self.block(
                        Input::Continue(None),
                        vec![],
                        Terminator::Branch {
                            condition: name(&matched, span),
                            then_block: success,
                            else_block: tail,
                        },
                    );
                    tail = self.pattern_test(
                        &binding_test_pattern(&arm.pattern),
                        &subject,
                        &matched,
                        branch,
                        span,
                    )?;
                }
                self.expr(value, &subject, tail)
            }
            ExprKind::Control { operation, value } => {
                let temporary = self.temporary();
                let terminator = match operation {
                    core::ControlOperation::Return => Terminator::Return {
                        value: name(&temporary, span),
                        function: true,
                    },
                    core::ControlOperation::Resume => Terminator::Resume {
                        value: name(&temporary, span),
                        next: if self.tail_answer(next, destination) {
                            None
                        } else {
                            Some(self.continuation(destination, next))
                        },
                    },
                    core::ControlOperation::Last | core::ControlOperation::Next => {
                        let Some((header, exit, result, depth)) = self.loops.last().cloned() else {
                            return Err(unsupported("CPS loop exit outside a loop"));
                        };
                        let next = if *operation == core::ControlOperation::Next {
                            header
                        } else {
                            exit
                        };
                        let entry = if *operation == core::ControlOperation::Last {
                            if let Some(result) = result {
                                self.assign_result(&result, name(&temporary, span), next)
                            } else {
                                next
                            }
                        } else {
                            next
                        };
                        let entry = self.unwind_scopes(depth, &temporary, entry);
                        let value = value.as_deref().cloned().unwrap_or_else(|| unit(span));
                        return self.expr(&value, &temporary, entry);
                    }
                };
                let control = self.block(Input::Continue(None), vec![], terminator);
                let control = if *operation == core::ControlOperation::Resume {
                    self.charge(Some(core::ChargeEvent::Resume), span, control)
                } else {
                    control
                };
                let value = value.as_deref().cloned().unwrap_or_else(|| unit(span));
                self.expr(&value, &temporary, control)
            }
            ExprKind::While {
                condition,
                body,
                charge,
            } => {
                if has_handler(body) {
                    return Err(unsupported("CPS loop-local handler exit context"));
                }
                let exit = self.assign_result(destination, unit(span), next);
                let header = self.block(Input::Continue(None), vec![], Terminator::Jump(exit));
                self.loops.push((header, exit, None, self.scopes.len()));
                let discarded = self.temporary();
                let body = self.scoped_block(body, &discarded, header)?;
                self.loops.pop();
                let value = self.temporary();
                let branch = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Branch {
                        condition: name(&value, condition.span),
                        then_block: body,
                        else_block: exit,
                    },
                );
                let condition = self.expr(condition, &value, branch)?;
                let condition = self.charge(*charge, span, condition);
                self.blocks[header.0 as usize].terminator = Terminator::Jump(condition);
                Ok(header)
            }
            ExprKind::Loop { body, charge } => {
                if has_handler(body) {
                    return Err(unsupported("CPS loop-local handler exit context"));
                }
                let header = self.block(Input::Continue(None), vec![], Terminator::Jump(next));
                self.loops
                    .push((header, next, Some(destination.into()), self.scopes.len()));
                let discarded = self.temporary();
                let body = self.scoped_block(body, &discarded, header)?;
                let body = self.charge(*charge, span, body);
                self.loops.pop();
                self.blocks[header.0 as usize].terminator = Terminator::Jump(body);
                Ok(header)
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
                charge,
            } => self.for_loop(iterable, pattern, body, *charge, destination, next, span),
            ExprKind::Charge(event) => {
                let result = self.assign_result(destination, unit(span), next);
                Ok(self.charge(Some(*event), span, result))
            }
            ExprKind::Budget {
                limit,
                action,
                exhaustion_operation,
                coverage,
            } => self.budget(
                limit,
                action,
                *exhaustion_operation,
                *coverage,
                destination,
                next,
                span,
            ),
        }
    }
    fn coalesce(
        &mut self,
        left: &Expr,
        right: &Expr,
        destination: &str,
        next: BlockId,
        span: Span,
    ) -> Result<BlockId, NotImplemented> {
        let subject = self.temporary();
        let tag_test = |tag: &str| {
            expression(
                ExprKind::Is {
                    value: Box::new(name(&subject, span)),
                    pattern: Pattern::Constructor {
                        tag: format!("Prelude::{tag}"),
                        arguments: vec![],
                    },
                },
                span,
            )
        };
        let some = self.block(
            Input::Continue(None),
            vec![Statement::Bind {
                pattern: Pattern::Constructor {
                    tag: "Prelude::Some".into(),
                    arguments: vec![Pattern::Name(destination.into())],
                },
                value: name(&subject, span),
                scoped: false,
            }],
            Terminator::Jump(next),
        );
        let ok = self.block(
            Input::Continue(None),
            vec![Statement::Bind {
                pattern: Pattern::Constructor {
                    tag: "Prelude::Ok".into(),
                    arguments: vec![Pattern::Name(destination.into())],
                },
                value: name(&subject, span),
                scoped: false,
            }],
            Terminator::Jump(next),
        );
        let some_test = self.temporary();
        let success_branch = self.block(
            Input::Continue(None),
            vec![],
            Terminator::Branch {
                condition: name(&some_test, span),
                then_block: some,
                else_block: ok,
            },
        );
        let success = self.assign_result(&some_test, tag_test("Some"), success_branch);

        let error = self.temporary();
        let call = expression(
            ExprKind::Call {
                callback_entry: true,
                callee: Box::new(right.clone()),
                arguments: vec![core::Argument {
                    label: None,
                    value: name(&error, span),
                }],
            },
            span,
        );
        let fallback_call = self.expr(&call, destination, next)?;
        let error_fallback = self.block(
            Input::Continue(None),
            vec![Statement::Bind {
                pattern: Pattern::Constructor {
                    tag: "Prelude::Err".into(),
                    arguments: vec![Pattern::Name(error)],
                },
                value: name(&subject, span),
                scoped: false,
            }],
            Terminator::Jump(fallback_call),
        );
        let none_fallback = self.expr(right, destination, next)?;
        let error_test = self.temporary();
        let failure_branch = self.block(
            Input::Continue(None),
            vec![],
            Terminator::Branch {
                condition: name(&error_test, span),
                then_block: error_fallback,
                else_block: none_fallback,
            },
        );
        let failure = self.assign_result(&error_test, tag_test("Err"), failure_branch);

        let successful = self.temporary();
        let branch = self.block(
            Input::Continue(None),
            vec![],
            Terminator::Branch {
                condition: name(&successful, span),
                then_block: success,
                else_block: failure,
            },
        );
        let test = self.assign_result(
            &successful,
            expression(
                ExprKind::Is {
                    value: Box::new(name(&subject, span)),
                    pattern: Pattern::Alternative(vec![
                        Pattern::Constructor {
                            tag: "Prelude::Some".into(),
                            arguments: vec![],
                        },
                        Pattern::Constructor {
                            tag: "Prelude::Ok".into(),
                            arguments: vec![],
                        },
                    ]),
                },
                span,
            ),
            branch,
        );
        self.expr(left, &subject, test)
    }
    fn pattern_test(
        &mut self,
        pattern: &Pattern,
        subject: &str,
        destination: &str,
        next: BlockId,
        span: Span,
    ) -> Result<BlockId, NotImplemented> {
        let boolean = |value| expression(ExprKind::Literal(core::Literal::Bool(value)), span);
        match pattern {
            Pattern::Wildcard => Ok(self.assign_result(destination, boolean(true), next)),
            Pattern::Rest(_) => Err(unsupported("standalone native sequence remainder")),
            Pattern::Literal(_) => Ok(self.assign_result(
                destination,
                expression(
                    ExprKind::Is {
                        value: Box::new(name(subject, span)),
                        pattern: pattern.clone(),
                    },
                    span,
                ),
                next,
            )),
            Pattern::Name(expected) => {
                let temporary = self.temporary();
                let equal = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Binary {
                            operator: "==".into(),
                            left: Box::new(name(subject, span)),
                            right: Box::new(name(&temporary, span)),
                        },
                        span,
                    ),
                    next,
                );
                self.expr(&name(expected, span), &temporary, equal)
            }
            Pattern::Value(expected) => {
                if matches!(expected.kind, ExprKind::Range { .. }) {
                    return Ok(self.assign_result(
                        destination,
                        expression(
                            ExprKind::Is {
                                value: Box::new(name(subject, span)),
                                pattern: pattern.clone(),
                            },
                            span,
                        ),
                        next,
                    ));
                }
                let temporary = self.temporary();
                let equal = self.assign_result(
                    destination,
                    expression(
                        ExprKind::Binary {
                            operator: "==".into(),
                            left: Box::new(name(subject, span)),
                            right: Box::new(name(&temporary, expected.span)),
                        },
                        span,
                    ),
                    next,
                );
                self.expr(expected, &temporary, equal)
            }
            Pattern::Constructor { tag, arguments } => {
                let tag_test = expression(
                    ExprKind::Is {
                        value: Box::new(name(subject, span)),
                        pattern: Pattern::Constructor {
                            tag: tag.clone(),
                            arguments: vec![],
                        },
                    },
                    span,
                );
                if arguments.is_empty() {
                    return Ok(self.assign_result(destination, tag_test, next));
                }
                let false_result = self.assign_result(destination, boolean(false), next);
                let payload = self.temporary();
                let payload_pattern = if arguments.len() == 1 {
                    arguments[0].clone()
                } else {
                    Pattern::Tuple(arguments.clone())
                };
                let check =
                    self.pattern_test(&payload_pattern, &payload, destination, next, span)?;
                let extract = self.block(
                    Input::Continue(None),
                    vec![Statement::Bind {
                        pattern: Pattern::Constructor {
                            tag: tag.clone(),
                            arguments: vec![Pattern::Name(payload)],
                        },
                        value: name(subject, span),
                        scoped: false,
                    }],
                    Terminator::Jump(check),
                );
                let matched = self.temporary();
                let branch = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Branch {
                        condition: name(&matched, span),
                        then_block: extract,
                        else_block: false_result,
                    },
                );
                Ok(self.assign_result(&matched, tag_test, branch))
            }
            Pattern::Tuple(items) | Pattern::Array(items) => {
                let mut rest = None;
                for (index, pattern) in items.iter().enumerate() {
                    if matches!(pattern, Pattern::Rest(_)) && rest.replace(index).is_some() {
                        return Err(unsupported("native sequence pattern has multiple rests"));
                    }
                }
                let false_result = self.assign_result(destination, boolean(false), next);
                let mut tail = self.assign_result(destination, boolean(true), next);
                for (index, pattern) in items.iter().enumerate().rev() {
                    if matches!(pattern, Pattern::Rest(_)) {
                        continue;
                    }
                    let child = self.temporary();
                    let matched = self.temporary();
                    let branch = self.block(
                        Input::Continue(None),
                        vec![],
                        Terminator::Branch {
                            condition: name(&matched, span),
                            then_block: tail,
                            else_block: false_result,
                        },
                    );
                    let check = self.pattern_test(pattern, &child, &matched, branch, span)?;
                    let literal_index = expression(
                        ExprKind::Literal(core::Literal::Integer {
                            value: index as i128,
                            bits: 64,
                            signed: true,
                        }),
                        span,
                    );
                    let index = if rest.is_some_and(|rest| index > rest) {
                        expression(
                            ExprKind::Binary {
                                operator: "-".into(),
                                left: Box::new(expression(
                                    ExprKind::Call {
                                        callback_entry: false,
                                        callee: Box::new(name("Prelude::len", span)),
                                        arguments: vec![core::Argument {
                                            label: None,
                                            value: name(subject, span),
                                        }],
                                    },
                                    span,
                                )),
                                right: Box::new(expression(
                                    ExprKind::Literal(core::Literal::Integer {
                                        value: (items.len() - index) as i128,
                                        bits: 64,
                                        signed: true,
                                    }),
                                    span,
                                )),
                            },
                            span,
                        )
                    } else {
                        literal_index
                    };
                    let projection = expression(
                        ExprKind::Index {
                            base: Box::new(name(subject, span)),
                            index: Box::new(index),
                            safe: false,
                        },
                        span,
                    );
                    tail = self.assign_result(&child, projection, check);
                }
                // Native shape testing checks length before touching an item.
                // The nested tests below run only after that first guard.
                let shape_items = items
                    .iter()
                    .map(|item| {
                        if matches!(item, Pattern::Rest(_)) {
                            Pattern::Rest(None)
                        } else {
                            Pattern::Wildcard
                        }
                    })
                    .collect();
                let shape = if matches!(pattern, Pattern::Array(_)) {
                    Pattern::Array(shape_items)
                } else {
                    Pattern::Tuple(shape_items)
                };
                let matched = self.temporary();
                let branch = self.block(
                    Input::Continue(None),
                    vec![],
                    Terminator::Branch {
                        condition: name(&matched, span),
                        then_block: tail,
                        else_block: false_result,
                    },
                );
                Ok(self.assign_result(
                    &matched,
                    expression(
                        ExprKind::Is {
                            value: Box::new(name(subject, span)),
                            pattern: shape,
                        },
                        span,
                    ),
                    branch,
                ))
            }
            Pattern::Record(fields) | Pattern::RecordRest { fields, .. } => {
                let false_result = self.assign_result(destination, boolean(false), next);
                let mut tail = self.assign_result(destination, boolean(true), next);
                for (field, pattern) in fields.iter().rev() {
                    let child = self.temporary();
                    let matched = self.temporary();
                    let branch = self.block(
                        Input::Continue(None),
                        vec![],
                        Terminator::Branch {
                            condition: name(&matched, span),
                            then_block: tail,
                            else_block: false_result,
                        },
                    );
                    let check = self.pattern_test(pattern, &child, &matched, branch, span)?;
                    let projection = expression(
                        ExprKind::Field {
                            base: Box::new(name(subject, span)),
                            field: field.clone(),
                            safe: false,
                        },
                        span,
                    );
                    tail = self.assign_result(&child, projection, check);
                }
                Ok(tail)
            }
            Pattern::Alternative(items) => {
                let true_result = self.assign_result(destination, boolean(true), next);
                let mut tail = self.assign_result(destination, boolean(false), next);
                for pattern in items.iter().rev() {
                    let matched = self.temporary();
                    let branch = self.block(
                        Input::Continue(None),
                        vec![],
                        Terminator::Branch {
                            condition: name(&matched, span),
                            then_block: true_result,
                            else_block: tail,
                        },
                    );
                    tail = self.pattern_test(pattern, subject, &matched, branch, span)?;
                }
                Ok(tail)
            }
        }
    }
}

fn pattern_names(pattern: &Pattern, names: &mut BTreeSet<String>) {
    match pattern {
        Pattern::Name(name) | Pattern::Rest(Some(name)) => {
            names.insert(name.clone());
        }
        Pattern::Tuple(items)
        | Pattern::Array(items)
        | Pattern::Alternative(items)
        | Pattern::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                pattern_names(item, names)
            }
        }
        Pattern::Record(fields) => {
            for (_, pattern) in fields {
                pattern_names(pattern, names)
            }
        }
        Pattern::RecordRest { fields, rest } => {
            names.insert(rest.clone());
            for (_, pattern) in fields {
                pattern_names(pattern, names);
            }
        }
        _ => {}
    }
}
fn collect_bindings(block: &core::Block, names: &mut BTreeSet<String>) {
    let mut counts = BTreeMap::new();
    collect_binding_counts(block, &mut counts);
    names.extend(counts.into_keys());
}
fn collect_binding_counts(block: &core::Block, counts: &mut BTreeMap<String, u32>) {
    for statement in &block.statements {
        match statement {
            Statement::Bind { pattern, .. } => {
                let mut names = BTreeSet::new();
                pattern_names(pattern, &mut names);
                for name in names {
                    *counts.entry(name).or_default() += 1;
                }
            }
            Statement::Handle { arms, .. } => {
                for arm in arms {
                    for parameter in &arm.parameters {
                        let mut names = BTreeSet::new();
                        pattern_names(&parameter.pattern, &mut names);
                        for name in names {
                            *counts.entry(name).or_default() += 1;
                        }
                    }
                }
            }
            Statement::Function(function) => {
                *counts.entry(function.name.clone()).or_default() += 1;
            }
            _ => {}
        }
    }
    walk_block(block, &mut |expr| {
        if let ExprKind::For { pattern, .. } = &expr.kind {
            let mut names = BTreeSet::new();
            pattern_names(pattern, &mut names);
            for name in names {
                *counts.entry(name).or_default() += 1;
            }
        }
        if let ExprKind::Match { arms, .. } = &expr.kind {
            for arm in arms {
                let mut names = BTreeSet::new();
                pattern_names(&arm.pattern, &mut names);
                for name in names {
                    *counts.entry(name).or_default() += 1;
                }
            }
        }
        if let ExprKind::Block(block)
        | ExprKind::Loop { body: block, .. }
        | ExprKind::While { body: block, .. }
        | ExprKind::For { body: block, .. } = &expr.kind
        {
            for statement in &block.statements {
                if let Statement::Function(function) = statement {
                    *counts.entry(function.name.clone()).or_default() += 1;
                }
                if let Statement::Bind { pattern, .. } = statement {
                    let mut names = BTreeSet::new();
                    pattern_names(pattern, &mut names);
                    for name in names {
                        *counts.entry(name).or_default() += 1;
                    }
                }
                if let Statement::Handle { arms, .. } = statement {
                    for arm in arms {
                        for parameter in &arm.parameters {
                            let mut names = BTreeSet::new();
                            pattern_names(&parameter.pattern, &mut names);
                            for name in names {
                                *counts.entry(name).or_default() += 1;
                            }
                        }
                    }
                }
            }
        }
    });
}
fn binding_test_pattern(pattern: &Pattern) -> Pattern {
    match pattern {
        Pattern::Name(_) => Pattern::Wildcard,
        Pattern::Tuple(items) => Pattern::Tuple(items.iter().map(binding_test_pattern).collect()),
        Pattern::Array(items) => Pattern::Array(items.iter().map(binding_test_pattern).collect()),
        Pattern::Rest(_) => Pattern::Rest(None),
        Pattern::RecordRest { fields, .. } => Pattern::Record(
            fields
                .iter()
                .map(|(key, value)| (key.clone(), binding_test_pattern(value)))
                .collect(),
        ),
        Pattern::Record(fields) => Pattern::Record(
            fields
                .iter()
                .map(|(key, value)| (key.clone(), binding_test_pattern(value)))
                .collect(),
        ),
        Pattern::Constructor { tag, arguments } => Pattern::Constructor {
            tag: tag.clone(),
            arguments: arguments.iter().map(binding_test_pattern).collect(),
        },
        Pattern::Alternative(items) => {
            Pattern::Alternative(items.iter().map(binding_test_pattern).collect())
        }
        _ => pattern.clone(),
    }
}
fn has_handler(block: &core::Block) -> bool {
    if block
        .statements
        .iter()
        .any(|statement| matches!(statement, Statement::Handle { .. }))
    {
        return true;
    }
    let mut found = false;
    walk_block(block, &mut |expr| {
        if let ExprKind::Block(block)
        | ExprKind::Loop { body: block, .. }
        | ExprKind::While { body: block, .. }
        | ExprKind::For { body: block, .. } = &expr.kind
        {
            found |= block
                .statements
                .iter()
                .any(|statement| matches!(statement, Statement::Handle { .. }));
        }
    });
    found
}

fn has_scoped(block: &core::Block) -> bool {
    if block
        .statements
        .iter()
        .any(|statement| matches!(statement, Statement::Bind { scoped: true, .. }))
    {
        return true;
    }
    let mut found = false;
    walk_block(block, &mut |expr| {
        if let ExprKind::Block(block)
        | ExprKind::Loop { body: block, .. }
        | ExprKind::While { body: block, .. }
        | ExprKind::For { body: block, .. } = &expr.kind
        {
            found |= block
                .statements
                .iter()
                .any(|statement| matches!(statement, Statement::Bind { scoped: true, .. }));
        }
    });
    found
}

fn nested_suspends(block: &core::Block, operations: &BTreeSet<String>) -> bool {
    let mut suspends = false;
    for statement in &block.statements {
        if let Statement::Function(function) = statement {
            suspends |= has_handler(&function.body)
                || has_scoped(&function.body)
                || nested_suspends(&function.body, operations);
            walk_function(function, &mut |expr| {
                suspends |= matches!(
                    expr.kind,
                    ExprKind::Budget { .. }
                        | ExprKind::Perform { .. }
                        | ExprKind::Control {
                            operation: core::ControlOperation::Resume,
                            ..
                        }
                );
                if let ExprKind::Name(name) = &expr.kind {
                    suspends |= operations.contains(name) || native_step_builtin(name);
                }
                if let ExprKind::Block(block)
                | ExprKind::Loop { body: block, .. }
                | ExprKind::While { body: block, .. }
                | ExprKind::For { body: block, .. } = &expr.kind
                {
                    suspends |= nested_suspends(block, operations);
                }
            });
        }
    }
    suspends
}
fn direct_handler(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Block(block)
        | ExprKind::Loop { body: block, .. }
        | ExprKind::While { body: block, .. }
        | ExprKind::For { body: block, .. } => block
            .statements
            .iter()
            .any(|statement| matches!(statement, Statement::Handle { .. })),
        _ => false,
    }
}
fn direct_scoped(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Block(block)
        | ExprKind::Loop { body: block, .. }
        | ExprKind::While { body: block, .. }
        | ExprKind::For { body: block, .. } => block
            .statements
            .iter()
            .any(|statement| matches!(statement, Statement::Bind { scoped: true, .. })),
        _ => false,
    }
}
fn walk_function(function: &core::Function, visit: &mut impl FnMut(&Expr)) {
    for parameter in &function.parameters {
        if let Some(default) = &parameter.default {
            walk_expr(default, visit);
        }
    }
    walk_block(&function.body, visit);
}
fn walk_block(block: &core::Block, visit: &mut impl FnMut(&Expr)) {
    for statement in &block.statements {
        match statement {
            Statement::Bind { value, .. } => walk_expr(value, visit),
            Statement::Assign { target, value, .. } => {
                walk_expr(target, visit);
                walk_expr(value, visit)
            }
            Statement::Expr { expression, .. } => walk_expr(expression, visit),
            Statement::Handle { arms, .. } => {
                for arm in arms {
                    walk_expr(&arm.body, visit)
                }
            }
            Statement::Function(_) => {}
        }
    }
}
fn walk_expr(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    match &expr.kind {
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                walk_expr(item, visit)
            }
        }
        ExprKind::Map(items) => {
            for (a, b) in items {
                walk_expr(a, visit);
                walk_expr(b, visit)
            }
        }
        ExprKind::Range { lower, upper, .. } => {
            for value in [lower, upper].into_iter().flatten() {
                walk_expr(value, visit)
            }
        }
        ExprKind::Record {
            members,
            fields,
            spread,
        } => {
            if members.is_empty() {
                for (_, value) in fields {
                    walk_expr(value, visit)
                }
                if let Some(value) = spread {
                    walk_expr(value, visit)
                }
            } else {
                for member in members {
                    match member {
                        core::RecordMember::Field(_, value) | core::RecordMember::Spread(value) => {
                            walk_expr(value, visit)
                        }
                    }
                }
            }
        }
        ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
            walk_expr(operand, visit)
        }
        ExprKind::Binary { left, right, .. }
        | ExprKind::Budget {
            limit: left,
            action: right,
            ..
        }
        | ExprKind::Index {
            base: left,
            index: right,
            ..
        }
        | ExprKind::Derive {
            base: left,
            recipe: right,
        } => {
            walk_expr(left, visit);
            walk_expr(right, visit)
        }
        ExprKind::Call {
            callee, arguments, ..
        } => {
            walk_expr(callee, visit);
            for argument in arguments {
                walk_expr(&argument.value, visit)
            }
        }
        ExprKind::Perform { arguments, .. } => {
            for argument in arguments {
                walk_expr(&argument.value, visit)
            }
        }
        ExprKind::Lambda { body, parameters } => {
            for parameter in parameters {
                if let Some(default) = &parameter.default {
                    walk_expr(default, visit);
                }
            }
            walk_expr(body, visit);
        }
        ExprKind::Block(block) | ExprKind::Loop { body: block, .. } => walk_block(block, visit),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            walk_expr(condition, visit);
            walk_expr(then_branch, visit);
            if let Some(branch) = else_branch {
                walk_expr(branch, visit)
            }
        }
        ExprKind::Match { value, arms } => {
            walk_expr(value, visit);
            for arm in arms {
                walk_pattern(&arm.pattern, visit);
                if let Some(guard) = &arm.guard {
                    walk_expr(guard, visit)
                }
                walk_expr(&arm.body, visit)
            }
        }
        ExprKind::Is { value, pattern } => {
            walk_expr(value, visit);
            walk_pattern(pattern, visit)
        }
        ExprKind::While {
            condition, body, ..
        } => {
            walk_expr(condition, visit);
            walk_block(body, visit)
        }
        ExprKind::For { iterable, body, .. } => {
            walk_expr(iterable, visit);
            walk_block(body, visit)
        }
        ExprKind::Control {
            value: Some(value), ..
        } => walk_expr(value, visit),
        _ => {}
    }
}
fn walk_pattern(pattern: &Pattern, visit: &mut impl FnMut(&Expr)) {
    match pattern {
        Pattern::Value(value) => walk_expr(value, visit),
        Pattern::Tuple(items)
        | Pattern::Array(items)
        | Pattern::Alternative(items)
        | Pattern::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                walk_pattern(item, visit)
            }
        }
        Pattern::Record(fields) | Pattern::RecordRest { fields, .. } => {
            for (_, pattern) in fields {
                walk_pattern(pattern, visit)
            }
        }
        _ => {}
    }
}
