//! Expand certified standard operations into ordinary structured Core before
//! selective CPS. Callback calls keep their native return continuations.
use ril_compiler_core::{
    ids::DefinitionId,
    phase::{NotImplemented, Stage},
    source::Span,
};
use ril_ir::core::{self, Expr, ExprKind, Pattern, Statement};
use std::collections::{BTreeMap, BTreeSet};
mod file;
mod heap;
mod io;
mod iter;
mod order;
mod process;

pub(crate) fn lower(program: &core::Program) -> Result<core::Program, NotImplemented> {
    let mut program = program.clone();
    let mut lower = Lower {
        next: 0,
        functions: program
            .functions
            .iter()
            .map(|function| function.name.clone())
            .chain(
                program
                    .external_functions
                    .iter()
                    .map(|function| function.internal_name.clone()),
            )
            .collect(),
        wrappers: BTreeMap::new(),
        next_definition: 0,
        rewriting: false,
        constructors: BTreeMap::new(),
    };
    // Include nested declarations in the definition namespace before adding
    // wrappers, even if their source statements appear after a builtin value.
    for function in &mut program.functions {
        lower.function(function)?;
    }
    for function in &mut program.external_functions {
        lower.external(function)?;
    }
    lower.block(&mut program.globals)?;
    lower.rewriting = true;
    for function in &mut program.functions {
        lower.function(function)?;
    }
    for function in &mut program.external_functions {
        lower.external(function)?;
    }
    lower.block(&mut program.globals)?;
    program.functions.extend(lower.wrappers.into_values());
    program
        .constructors
        .extend(lower.constructors.into_values());
    Ok(program)
}
struct Lower {
    next: u32,
    functions: BTreeSet<String>,
    wrappers: BTreeMap<String, core::Function>,
    next_definition: u32,
    rewriting: bool,
    constructors: BTreeMap<String, core::Constructor>,
}
fn operation(name: &str) -> Option<&str> {
    let name = name.strip_prefix("Prelude::").unwrap_or(name);
    if let Some(location) = name.strip_prefix("Heap::__new_") {
        let parts: Vec<_> = location.split('_').collect();
        if parts.len() == 3
            && parts.iter().all(|part| {
                !part.is_empty()
                    && part.bytes().all(|byte| byte.is_ascii_digit())
                    && part.parse::<u32>().is_ok()
            })
        {
            return Some("Heap::new");
        }
    }
    matches!(
        name,
        "Array::map"
            | "Array::filter"
            | "Array::fold"
            | "Array::find"
            | "Array::any"
            | "Array::all"
            | "Array::for_each"
            | "Options::map"
            | "Options::and_then"
            | "Options::unwrap_or_else"
            | "Results::map"
            | "Results::map_err"
            | "Results::and_then"
            | "Results::recover"
            | "Order::sorted"
            | "Order::binary_search"
            | "Heap::new"
            | "Heap::push"
            | "Heap::pop"
            | "File::with_file"
            | "Process::with_child"
            | "Io::read_all"
            | "Io::write_all"
            | "Iter::cursor"
            | "Iter::pull"
            | "Iter::collect"
            | "Iter::fold"
            | "Iter::indexed"
            | "Iter::map"
            | "Iter::filter"
            | "Iter::take"
    )
    .then_some(name)
}
fn arity(operation: &str) -> usize {
    if matches!(
        operation,
        "Iter::cursor" | "Iter::indexed" | "Heap::new" | "Heap::pop"
    ) {
        return 1;
    }
    if operation == "Iter::fold" {
        return 4;
    }
    if matches!(
        operation,
        "Array::fold" | "Order::binary_search" | "File::with_file" | "Io::write_all"
    ) {
        3
    } else {
        2
    }
}
fn expr(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}
fn name(value: &str, span: Span) -> Expr {
    expr(ExprKind::Name(value.into()), span)
}
fn integer(value: i128, span: Span) -> Expr {
    expr(
        ExprKind::Literal(core::Literal::Integer {
            value,
            bits: 64,
            signed: true,
        }),
        span,
    )
}
fn unit(span: Span) -> Expr {
    expr(ExprKind::Literal(core::Literal::Unit), span)
}
fn call(callee: Expr, values: Vec<Expr>, span: Span) -> Expr {
    expr(
        ExprKind::Call {
            callback_entry: false,
            callee: Box::new(callee),
            arguments: values
                .into_iter()
                .map(|value| core::Argument { label: None, value })
                .collect(),
        },
        span,
    )
}
fn callback_call(callee: Expr, values: Vec<Expr>, span: Span) -> Expr {
    let mut invocation = call(callee, values, span);
    if let ExprKind::Call { callback_entry, .. } = &mut invocation.kind {
        *callback_entry = true;
    }
    invocation
}
fn bind(name: &str, value: Expr) -> Statement {
    Statement::Bind {
        pattern: Pattern::Name(name.into()),
        value,
        scoped: false,
    }
}
fn statement(expression: Expr) -> Statement {
    Statement::Expr {
        expression,
        terminated: true,
    }
}
fn block(mut statements: Vec<Statement>, tail: Expr, span: Span) -> Expr {
    statements.push(Statement::Expr {
        expression: tail,
        terminated: false,
    });
    expr(ExprKind::Block(core::Block { statements }), span)
}
fn boolean(value: bool, span: Span) -> Expr {
    expr(ExprKind::Literal(core::Literal::Bool(value)), span)
}
fn assign(target: &str, value: Expr, span: Span) -> Statement {
    Statement::Assign {
        target: name(target, span),
        operator: "=".into(),
        value,
    }
}
fn conditional(condition: Expr, yes: Expr, no: Expr, span: Span) -> Expr {
    expr(
        ExprKind::If {
            condition: Box::new(condition),
            then_branch: Box::new(yes),
            else_branch: Some(Box::new(no)),
        },
        span,
    )
}
impl Lower {
    fn external(
        &mut self,
        function: &mut ril_ir::foreign::ExternalFunction,
    ) -> Result<(), NotImplemented> {
        self.next_definition = self.next_definition.max(function.definition.0);
        for parameter in &mut function.parameters {
            if let Some(default) = &mut parameter.default {
                self.expression(default)?;
            }
        }
        Ok(())
    }
    fn temporary(&mut self, label: &str) -> String {
        let value = format!("\0ril.hof.{}.{label}", self.next);
        self.next += 1;
        value
    }
    fn wrapper(&mut self, operation: &str, span: Span) -> Result<String, NotImplemented> {
        if let Some(wrapper) = self.wrappers.get(operation) {
            return Ok(wrapper.name.clone());
        }
        let wrapper_name = format!("\0ril.hof.builtin.{operation}");
        self.next_definition = self
            .next_definition
            .checked_add(1)
            .filter(|id| *id != u32::MAX)
            .ok_or_else(|| {
                NotImplemented::new(
                    Stage::Lowering,
                    "native builtin wrapper definition domain is exhausted",
                )
            })?;
        let arguments: Vec<_> = (0..arity(operation))
            .map(|_| self.temporary("argument"))
            .collect();
        let parameters = arguments
            .iter()
            .map(|name| core::Parameter {
                pattern: Pattern::Name(name.clone()),
                default: None,
            })
            .collect();
        let arguments: Vec<_> = arguments
            .iter()
            .map(|argument| name(argument, span))
            .collect();
        let body = self.expand(operation, &arguments, span);
        self.wrappers.insert(
            operation.into(),
            core::Function {
                role: core::FunctionRole::Synthetic,
                definition: DefinitionId(self.next_definition),
                name: wrapper_name.clone(),
                generic_parameters: vec![],
                parameters,
                body: core::Block {
                    statements: vec![Statement::Expr {
                        expression: body,
                        terminated: false,
                    }],
                },
                span,
            },
        );
        Ok(wrapper_name)
    }
    fn expand(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        if operation.starts_with("Array::") {
            self.array(operation, arguments, span)
        } else if operation.starts_with("Order::") {
            self.order(operation, arguments, span)
        } else if operation.starts_with("Heap::") {
            self.heap(operation, arguments, span)
        } else if operation == "File::with_file" {
            self.file(arguments, span)
        } else if operation == "Process::with_child" {
            self.process(arguments, span)
        } else if operation.starts_with("Io::") {
            self.io(operation, arguments, span)
        } else if operation.starts_with("Iter::") {
            self.iter(operation, arguments, span)
        } else {
            self.variant(operation, arguments, span)
        }
    }
    fn function(&mut self, function: &mut core::Function) -> Result<(), NotImplemented> {
        self.next_definition = self.next_definition.max(function.definition.0);
        for parameter in &mut function.parameters {
            if let Some(value) = &mut parameter.default {
                self.expression(value)?;
            }
        }
        self.block(&mut function.body)
    }
    fn block(&mut self, block: &mut core::Block) -> Result<(), NotImplemented> {
        for statement in &mut block.statements {
            match statement {
                Statement::Bind { value, .. } => self.expression(value)?,
                Statement::Assign { target, value, .. } => {
                    self.expression(target)?;
                    self.expression(value)?;
                }
                Statement::Expr { expression, .. } => self.expression(expression)?,
                Statement::Function(function) => self.function(function)?,
                Statement::Handle { arms, .. } => {
                    for arm in arms {
                        self.expression(&mut arm.body)?;
                    }
                }
            }
        }
        Ok(())
    }
    fn pattern(&mut self, pattern: &mut Pattern) -> Result<(), NotImplemented> {
        match pattern {
            Pattern::Value(value) => self.expression(value)?,
            Pattern::Tuple(values)
            | Pattern::Array(values)
            | Pattern::Alternative(values)
            | Pattern::Constructor {
                arguments: values, ..
            } => {
                for value in values {
                    self.pattern(value)?;
                }
            }
            Pattern::Record(values) | Pattern::RecordRest { fields: values, .. } => {
                for (_, value) in values {
                    self.pattern(value)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn expression(&mut self, value: &mut Expr) -> Result<(), NotImplemented> {
        let span = value.span;
        match &mut value.kind {
            ExprKind::Budget { limit, action, .. } => {
                self.expression(limit)?;
                self.expression(action)?;
            }
            ExprKind::Call {
                callee, arguments, ..
            } => {
                // Direct operations expand in place. A value position instead
                // gets a top-level wrapper, which captures no handler context.
                if !matches!(&callee.kind,ExprKind::Name(name)if !self.functions.contains(name)&&operation(name).is_some())
                {
                    self.expression(callee)?;
                }
                for argument in arguments.iter_mut() {
                    self.expression(&mut argument.value)?;
                }
                if let ExprKind::Name(target) = &callee.kind
                    && self.rewriting
                    && !self.functions.contains(target)
                    && let Some(operation) = operation(target)
                {
                    if arguments.len() != arity(operation)
                        || arguments.iter().any(|argument| argument.label.is_some())
                    {
                        return Err(NotImplemented::new(
                            Stage::Lowering,
                            "higher-order expansion needs the certified positional arity",
                        ));
                    }
                    let arguments: Vec<_> = arguments
                        .iter()
                        .map(|argument| argument.value.clone())
                        .collect();
                    *value = self.expand(operation, &arguments, span);
                }
            }
            ExprKind::Tuple(values) | ExprKind::Array(values) => {
                for value in values {
                    self.expression(value)?;
                }
            }
            ExprKind::Map(values) => {
                for (key, value) in values {
                    self.expression(key)?;
                    self.expression(value)?;
                }
            }
            ExprKind::Range { lower, upper, .. } => {
                for value in [lower, upper].into_iter().flatten() {
                    self.expression(value)?;
                }
            }
            ExprKind::Record { members } => {
                for member in members {
                    match member {
                        core::RecordMember::Field(_, value) | core::RecordMember::Spread(value) => {
                            self.expression(value)?
                        }
                    }
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
                self.expression(operand)?
            }
            ExprKind::Binary { left, right, .. }
            | ExprKind::Index {
                base: left,
                index: right,
                ..
            }
            | ExprKind::Derive {
                base: left,
                recipe: right,
            } => {
                self.expression(left)?;
                self.expression(right)?;
            }
            ExprKind::Lambda { parameters, body } => {
                for parameter in parameters {
                    if let Some(value) = &mut parameter.default {
                        self.expression(value)?;
                    }
                }
                self.expression(body)?;
            }
            ExprKind::Block(block) | ExprKind::Loop { body: block, .. } => self.block(block)?,
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expression(condition)?;
                self.expression(then_branch)?;
                if let Some(value) = else_branch {
                    self.expression(value)?;
                }
            }
            ExprKind::Match { value, arms } => {
                self.expression(value)?;
                for arm in arms {
                    self.pattern(&mut arm.pattern)?;
                    if let Some(value) = &mut arm.guard {
                        self.expression(value)?;
                    }
                    self.expression(&mut arm.body)?;
                }
            }
            ExprKind::Is { value, pattern } => {
                self.expression(value)?;
                self.pattern(pattern)?;
            }
            ExprKind::While {
                condition, body, ..
            } => {
                self.expression(condition)?;
                self.block(body)?;
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
                ..
            } => {
                self.expression(iterable)?;
                self.pattern(pattern)?;
                self.block(body)?;
            }
            ExprKind::Control { value, .. } => {
                if let Some(value) = value {
                    self.expression(value)?;
                }
            }
            ExprKind::Perform { arguments, .. } => {
                for argument in arguments {
                    self.expression(&mut argument.value)?;
                }
            }
            ExprKind::Name(target) if self.rewriting && !self.functions.contains(target) => {
                if let Some(operation) = operation(target) {
                    *value = name(&self.wrapper(operation, span)?, span);
                }
            }
            ExprKind::ConstRef(_)
            | ExprKind::Literal(_)
            | ExprKind::Name(_)
            | ExprKind::Charge(_) => {}
        }
        Ok(())
    }
    fn array(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        let array = self.temporary("array");
        let action = self.temporary("callback");
        let count = self.temporary("count");
        let index = self.temporary("index");
        let item = self.temporary("item");
        let output = self.temporary("output");
        let value = self.temporary("value");
        let mut statements = vec![bind(&array, arguments[0].clone())];
        if operation == "Array::fold" {
            statements.push(bind(&output, arguments[1].clone()));
        }
        statements.push(bind(&action, arguments.last().unwrap().clone()));
        statements.push(bind(
            &count,
            call(name("Prelude::len", span), vec![name(&array, span)], span),
        ));
        statements.push(bind(&index, integer(0, span)));
        let initializer = match operation {
            "Array::map" | "Array::filter" => Some(expr(ExprKind::Array(vec![]), span)),
            "Array::find" => Some(name("Prelude::None", span)),
            "Array::any" => Some(boolean(false, span)),
            "Array::all" => Some(boolean(true, span)),
            _ => None,
        };
        if let Some(initializer) = initializer {
            statements.push(bind(&output, initializer));
        }
        let mut callback_arguments = vec![];
        if operation == "Array::fold" {
            callback_arguments.push(name(&output, span));
        }
        callback_arguments.push(name(&item, span));
        let mut body = vec![
            statement(expr(
                ExprKind::Charge(core::ChargeEvent::LoopIteration),
                span,
            )),
            bind(
                &item,
                expr(
                    ExprKind::Index {
                        base: Box::new(name(&array, span)),
                        index: Box::new(name(&index, span)),
                        safe: false,
                    },
                    span,
                ),
            ),
            bind(
                &value,
                callback_call(name(&action, span), callback_arguments, span),
            ),
        ];
        match operation {
            "Array::map" => body.push(statement(call(
                name("Array::push", span),
                vec![name(&output, span), name(&value, span)],
                span,
            ))),
            "Array::filter" => body.push(statement(conditional(
                name(&value, span),
                call(
                    name("Array::push", span),
                    vec![name(&output, span), name(&item, span)],
                    span,
                ),
                unit(span),
                span,
            ))),
            "Array::fold" => body.push(assign(&output, name(&value, span), span)),
            "Array::find" | "Array::any" | "Array::all" => {
                let condition = if operation == "Array::all" {
                    expr(
                        ExprKind::Unary {
                            operator: "!".into(),
                            operand: Box::new(name(&value, span)),
                        },
                        span,
                    )
                } else {
                    name(&value, span)
                };
                let result = if operation == "Array::find" {
                    call(name("Prelude::Some", span), vec![name(&item, span)], span)
                } else {
                    boolean(operation == "Array::any", span)
                };
                body.push(statement(conditional(
                    condition,
                    block(
                        vec![assign(&output, result, span)],
                        expr(
                            ExprKind::Control {
                                operation: core::ControlOperation::Last,
                                value: None,
                            },
                            span,
                        ),
                        span,
                    ),
                    unit(span),
                    span,
                )));
            }
            _ => {}
        }
        body.push(Statement::Assign {
            target: name(&index, span),
            operator: "+=".into(),
            value: integer(1, span),
        });
        statements.push(statement(expr(
            ExprKind::While {
                charge: None,
                condition: Box::new(expr(
                    ExprKind::Binary {
                        operator: "<".into(),
                        left: Box::new(name(&index, span)),
                        right: Box::new(name(&count, span)),
                    },
                    span,
                )),
                body: core::Block { statements: body },
            },
            span,
        )));
        let result = if operation == "Array::for_each" {
            unit(span)
        } else {
            name(&output, span)
        };
        block(statements, result, span)
    }
    fn variant(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        let input = self.temporary("variant");
        let callback = self.temporary("callback");
        let payload = self.temporary("payload");
        let option = operation.starts_with("Options::");
        let error = matches!(operation, "Results::map_err" | "Results::recover");
        let tag = if option {
            "Some"
        } else if error {
            "Err"
        } else {
            "Ok"
        };
        let condition = expr(
            ExprKind::Is {
                value: Box::new(name(&input, span)),
                pattern: Pattern::Constructor {
                    tag: format!("Prelude::{tag}"),
                    arguments: vec![],
                },
            },
            span,
        );
        let extract = Statement::Bind {
            pattern: Pattern::Constructor {
                tag: format!("Prelude::{tag}"),
                arguments: vec![Pattern::Name(payload.clone())],
            },
            value: name(&input, span),
            scoped: false,
        };
        let call_callback = callback_call(name(&callback, span), vec![name(&payload, span)], span);
        let yes = if operation == "Options::unwrap_or_else" {
            block(vec![extract], name(&payload, span), span)
        } else {
            let output = match operation {
                "Options::map" | "Results::map" | "Results::map_err" => call(
                    name(&format!("Prelude::{tag}"), span),
                    vec![call_callback],
                    span,
                ),
                _ => call_callback,
            };
            block(vec![extract], output, span)
        };
        let no = match operation {
            "Options::unwrap_or_else" => callback_call(name(&callback, span), vec![], span),
            "Results::recover" => block(
                vec![Statement::Bind {
                    pattern: Pattern::Constructor {
                        tag: "Prelude::Ok".into(),
                        arguments: vec![Pattern::Name(payload.clone())],
                    },
                    value: name(&input, span),
                    scoped: false,
                }],
                name(&payload, span),
                span,
            ),
            _ => name(&input, span),
        };
        block(
            vec![
                bind(&input, arguments[0].clone()),
                bind(&callback, arguments[1].clone()),
            ],
            conditional(condition, yes, no, span),
            span,
        )
    }
}
