//! Lower verified structured expressions into native control flow and runtime calls.
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, Block as ClifBlock, InstBuilder, Type, Value, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use ril_codegen::BackendError;
use ril_compiler_core::ids::{CallableOwner, ClosureSiteId};
use ril_ir::core::{self, ControlOperation, Expr, ExprKind, Literal, Pattern, Statement};
use ril_ir::native::{self, Body};
use ril_runtime_api::abi::BinaryOp;
use std::collections::{BTreeSet, HashMap, HashSet};
#[path = "managed/cleanup.rs"]
mod cleanup;
#[path = "managed/constants.rs"]
mod constants;
#[path = "cps.rs"]
mod cps;
#[cfg(test)]
#[path = "managed/default_tests.rs"]
mod default_tests;
#[path = "managed/discovery.rs"]
mod discovery;
#[path = "managed/foreign.rs"]
pub(crate) mod foreign;
#[path = "managed/hof.rs"]
mod hof;
#[path = "managed/named.rs"]
mod named;
#[path = "managed/patterns.rs"]
mod patterns;
#[path = "managed/retention.rs"]
mod retention;
pub(crate) use cps::emit_cps;

fn codegen(error: impl std::fmt::Display) -> BackendError {
    BackendError::Codegen(error.to_string())
}
fn unsupported(detail: impl Into<String>) -> BackendError {
    BackendError::NotImplemented(ril_compiler_core::phase::NotImplemented::new(
        ril_compiler_core::phase::Stage::Codegen,
        detail,
    ))
}

#[derive(Clone)]
pub(crate) struct FunctionInfo {
    pub metered_entry_event: bool,
    pub budget: Option<FuncId>,
    pub id: FuncId,
    pub parameters: Vec<core::Parameter>,
    pub captures: Vec<String>,
    pub cps: bool,
}

/// One lexical callable site within one concrete function instance. Normal and
/// metered entries share a language identity and therefore the same lifted site.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CallableKey {
    owner: String,
    span: (u32, u32, u32),
}
fn callable_key(owner: &str, span: ril_compiler_core::source::Span) -> CallableKey {
    CallableKey {
        owner: owner.strip_prefix("\0ril.budget.").unwrap_or(owner).into(),
        span: (span.file.0, span.start, span.end),
    }
}
fn canonical_owner(name: &str) -> &str {
    name.strip_prefix("\0ril.budget.").unwrap_or(name)
}

pub(crate) struct ProgramInfo {
    pub constants: constants::Pool,
    pub foreign_descriptors: Option<String>,
    pub foreign_constants: Vec<(String, u32)>,
    pub handler_budget_entries: HashMap<(String, u64, u64), String>,
    pub retained_handlers: HashMap<String, Vec<u64>>,
    pub operations: HashMap<String, u64>,
    pub constructors: HashMap<String, core::Constructor>,
    pub functions: HashMap<String, FunctionInfo>,
    pub symbols: HashMap<String, FunctionInfo>,
    pub globals: HashSet<String>,
    pub lambdas: HashMap<CallableKey, String>,
    pub named: HashMap<CallableKey, String>,
    pub call_signatures: HashMap<(u32, u32, u32), Vec<core::CallParameter>>,
    pub imports: HashMap<&'static str, FuncId>,
    pub next_data: usize,
}

pub(crate) fn signature(module: &ObjectModule, body: &Body) -> cranelift_codegen::ir::Signature {
    let mut signature = module.make_signature();
    if matches!(
        body,
        Body::Managed(_) | Body::Cps(_) | Body::CpsBlock { .. }
    ) {
        signature
            .params
            .extend([AbiParam::new(types::I64), AbiParam::new(types::I64)]);
    }
    signature
        .returns
        .push(AbiParam::new(if matches!(body, Body::Entry { .. }) {
            types::I32
        } else {
            types::I64
        }));
    signature
}

pub(crate) struct Prepared {
    pub constants: constants::Pool,
    pub handler_budget_entries: HashMap<(String, u64, u64), String>,
    pub retained_handlers: HashMap<String, Vec<u64>>,
    pub retained_proofs: HashMap<CallableOwner, Vec<u64>>,
    pub unproven_retained: HashSet<CallableOwner>,
    pub unowned_retained_sites: HashSet<(u32, u32, u32)>,
    pub callable_owners: HashMap<String, CallableOwner>,
    pub closure_sites: HashMap<(CallableOwner, (u32, u32, u32)), ClosureSiteId>,
    nonretaining_adapters: retention::Adapters,
    pub budget_entries: HashMap<String, String>,
    pub functions: Vec<native::Function>,
    pub captures: HashMap<String, Vec<String>>,
    pub lambdas: HashMap<CallableKey, String>,
    pub named: HashMap<CallableKey, String>,
    pub globals: HashSet<String>,
}

fn cps_statements(
    instruction: &ril_ir::cps::Instruction,
) -> impl Iterator<Item = core::Statement> + '_ {
    let statement = match instruction {
        ril_ir::cps::Instruction::Statement(statement) => Some(statement.as_ref().clone()),
        _ => None,
    };
    let functions = match instruction {
        ril_ir::cps::Instruction::Hoist { functions, .. } => functions.as_slice(),
        _ => &[],
    };
    statement
        .into_iter()
        .chain(functions.iter().cloned().map(Statement::Function))
}

fn names(pattern: &Pattern, result: &mut BTreeSet<String>) {
    match pattern {
        Pattern::Name(name) | Pattern::Rest(Some(name)) => {
            result.insert(name.clone());
        }
        Pattern::Tuple(patterns) | Pattern::Array(patterns) | Pattern::Alternative(patterns) => {
            for pattern in patterns {
                names(pattern, result)
            }
        }
        Pattern::Record(fields) => {
            for (_, pattern) in fields {
                names(pattern, result)
            }
        }
        Pattern::RecordRest { fields, rest } => {
            result.insert(rest.clone());
            for (_, pattern) in fields {
                names(pattern, result);
            }
        }
        Pattern::Constructor { arguments, .. } => {
            for pattern in arguments {
                names(pattern, result)
            }
        }
        _ => {}
    }
}

fn visit_expr<'a>(expr: &'a Expr, visit: &mut impl FnMut(&'a Expr) -> bool) {
    if !visit(expr) {
        return;
    }
    match &expr.kind {
        ExprKind::Budget { limit, action, .. } => {
            visit_expr(limit, visit);
            visit_expr(action, visit);
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                visit_expr(item, visit)
            }
        }
        ExprKind::Map(items) => {
            for (key, value) in items {
                visit_expr(key, visit);
                visit_expr(value, visit)
            }
        }
        ExprKind::Range { lower, upper, .. } => {
            for value in [lower, upper].into_iter().flatten() {
                visit_expr(value, visit)
            }
        }
        ExprKind::Record {
            fields,
            spread,
            members,
        } if members.is_empty() => {
            if let Some(spread) = spread {
                visit_expr(spread, visit)
            }
            for (_, value) in fields {
                visit_expr(value, visit)
            }
        }
        ExprKind::Record { members, .. } => {
            for member in members {
                match member {
                    core::RecordMember::Field(_, value) | core::RecordMember::Spread(value) => {
                        visit_expr(value, visit)
                    }
                }
            }
        }
        ExprKind::Unary { operand, .. } => visit_expr(operand, visit),
        ExprKind::Binary { left, right, .. } => {
            visit_expr(left, visit);
            visit_expr(right, visit)
        }
        ExprKind::Call {
            callee, arguments, ..
        } => {
            visit_expr(callee, visit);
            for arg in arguments {
                visit_expr(&arg.value, visit)
            }
        }
        ExprKind::Perform { arguments, .. } => {
            for argument in arguments {
                visit_expr(&argument.value, visit);
            }
        }
        ExprKind::Field { base, .. } => visit_expr(base, visit),
        ExprKind::Index { base, index, .. } => {
            visit_expr(base, visit);
            visit_expr(index, visit)
        }
        ExprKind::Lambda { body, parameters } => {
            for parameter in parameters {
                if let Some(value) = &parameter.default {
                    visit_expr(value, visit)
                }
            }
            visit_expr(body, visit)
        }
        ExprKind::Block(block) | ExprKind::Loop { body: block, .. } => visit_block(block, visit),
        ExprKind::While {
            condition, body, ..
        } => {
            visit_expr(condition, visit);
            visit_block(body, visit)
        }
        ExprKind::For { iterable, body, .. } => {
            visit_expr(iterable, visit);
            visit_block(body, visit)
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visit_expr(condition, visit);
            visit_expr(then_branch, visit);
            if let Some(branch) = else_branch {
                visit_expr(branch, visit)
            }
        }
        ExprKind::Match { value, arms } => {
            visit_expr(value, visit);
            for arm in arms {
                visit_pattern_values(&arm.pattern, visit);
                if let Some(guard) = &arm.guard {
                    visit_expr(guard, visit)
                }
                visit_expr(&arm.body, visit)
            }
        }
        ExprKind::Is { value, pattern } => {
            visit_expr(value, visit);
            visit_pattern_values(pattern, visit);
        }
        ExprKind::Control {
            value: Some(value), ..
        } => visit_expr(value, visit),
        ExprKind::Derive { base, recipe } => {
            visit_expr(base, visit);
            visit_expr(recipe, visit)
        }
        _ => {}
    }
}

fn visit_pattern_values<'a>(pattern: &'a Pattern, visit: &mut impl FnMut(&'a Expr) -> bool) {
    match pattern {
        Pattern::Value(value) => visit_expr(value, visit),
        Pattern::Tuple(patterns)
        | Pattern::Array(patterns)
        | Pattern::Alternative(patterns)
        | Pattern::Constructor {
            arguments: patterns,
            ..
        } => {
            for pattern in patterns {
                visit_pattern_values(pattern, visit)
            }
        }
        Pattern::Record(fields) | Pattern::RecordRest { fields, .. } => {
            for (_, pattern) in fields {
                visit_pattern_values(pattern, visit)
            }
        }
        _ => {}
    }
}

fn visit_block<'a>(block: &'a core::Block, visit: &mut impl FnMut(&'a Expr) -> bool) {
    for statement in &block.statements {
        match statement {
            Statement::Bind { value, .. } => visit_expr(value, visit),
            Statement::Assign { target, value, .. } => {
                visit_expr(target, visit);
                visit_expr(value, visit);
            }
            Statement::Expr { expression, .. } => visit_expr(expression, visit),
            // A named callable has its own capture scope and is visited after lifting.
            Statement::Function(_) => {}
            Statement::Handle { arms, .. } => {
                for arm in arms {
                    visit_expr(&arm.body, visit)
                }
            }
        }
    }
}

fn free_block(block: &core::Block, outer: &BTreeSet<String>, free: &mut BTreeSet<String>) {
    let mut bound = outer.clone();
    let mut lexical = BTreeSet::new();
    for statement in &block.statements {
        match statement {
            Statement::Function(function) => {
                bound.insert(function.name.clone());
            }
            Statement::Bind { pattern, .. } => names(pattern, &mut lexical),
            _ => {}
        }
    }
    for statement in &block.statements {
        match statement {
            Statement::Bind { pattern, value, .. } => {
                free_names(value, &bound, free);
                names(pattern, &mut bound);
            }
            Statement::Assign { target, value, .. } => {
                free_names(target, &bound, free);
                free_names(value, &bound, free);
            }
            Statement::Expr { expression, .. } => free_names(expression, &bound, free),
            Statement::Function(function) => {
                bound.insert(function.name.clone());
                let mut own = bound.clone();
                own.extend(lexical.iter().cloned());
                for parameter in &function.parameters {
                    if let Some(default) = &parameter.default {
                        free_names(default, &own, free)
                    }
                    names(&parameter.pattern, &mut own);
                }
                free_block(&function.body, &own, free);
            }
            Statement::Handle { arms, .. } => {
                for arm in arms {
                    let mut own = bound.clone();
                    for parameter in &arm.parameters {
                        names(&parameter.pattern, &mut own)
                    }
                    free_names(&arm.body, &own, free);
                }
            }
        }
    }
}

fn free_names(expr: &Expr, bound: &BTreeSet<String>, free: &mut BTreeSet<String>) {
    match &expr.kind {
        ExprKind::Budget { limit, action, .. } => {
            free_names(limit, bound, free);
            free_names(action, bound, free);
        }
        ExprKind::Charge(_) => {}
        ExprKind::Name(name) => {
            if !bound.contains(name) {
                free.insert(name.clone());
            }
        }
        ExprKind::ConstRef(_) | ExprKind::Literal(_) => {}
        ExprKind::Block(block) | ExprKind::Loop { body: block, .. } => {
            free_block(block, bound, free)
        }
        ExprKind::Tuple(values) | ExprKind::Array(values) => {
            for value in values {
                free_names(value, bound, free)
            }
        }
        ExprKind::Map(values) => {
            for (key, value) in values {
                free_names(key, bound, free);
                free_names(value, bound, free)
            }
        }
        ExprKind::Range { lower, upper, .. } => {
            for value in [lower, upper].into_iter().flatten() {
                free_names(value, bound, free)
            }
        }
        ExprKind::Record {
            fields,
            spread,
            members,
        } if members.is_empty() => {
            if let Some(value) = spread {
                free_names(value, bound, free)
            }
            for (_, value) in fields {
                free_names(value, bound, free)
            }
        }
        ExprKind::Record { members, .. } => {
            for member in members {
                match member {
                    core::RecordMember::Field(_, value) | core::RecordMember::Spread(value) => {
                        free_names(value, bound, free)
                    }
                }
            }
        }
        ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
            free_names(operand, bound, free)
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
            free_names(left, bound, free);
            free_names(right, bound, free)
        }
        ExprKind::Call {
            callee, arguments, ..
        } => {
            free_names(callee, bound, free);
            for argument in arguments {
                free_names(&argument.value, bound, free)
            }
        }
        ExprKind::Perform { arguments, .. } => {
            for argument in arguments {
                free_names(&argument.value, bound, free);
            }
        }
        ExprKind::Lambda { parameters, body } => {
            let mut own = bound.clone();
            for parameter in parameters {
                if let Some(default) = &parameter.default {
                    free_names(default, &own, free)
                }
                names(&parameter.pattern, &mut own)
            }
            free_names(body, &own, free)
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            free_names(condition, bound, free);
            free_names(then_branch, bound, free);
            if let Some(value) = else_branch {
                free_names(value, bound, free)
            }
        }
        ExprKind::While {
            condition, body, ..
        } => {
            free_names(condition, bound, free);
            free_block(body, bound, free)
        }
        ExprKind::For {
            iterable,
            pattern,
            body,
            ..
        } => {
            free_names(iterable, bound, free);
            let mut own = bound.clone();
            names(pattern, &mut own);
            free_block(body, &own, free)
        }
        ExprKind::Match { value, arms } => {
            free_names(value, bound, free);
            for arm in arms {
                visit_pattern_values(&arm.pattern, &mut |value| {
                    free_names(value, bound, free);
                    false
                });
                let mut own = bound.clone();
                names(&arm.pattern, &mut own);
                if let Some(guard) = &arm.guard {
                    free_names(guard, &own, free)
                }
                free_names(&arm.body, &own, free)
            }
        }
        ExprKind::Is { value, pattern } => {
            free_names(value, bound, free);
            let mut used = BTreeSet::new();
            names(pattern, &mut used);
            free.extend(used.difference(bound).cloned());
            visit_pattern_values(pattern, &mut |value| {
                free_names(value, bound, free);
                false
            });
        }
        ExprKind::Control { value, .. } => {
            if let Some(value) = value {
                free_names(value, bound, free)
            }
        }
    }
}

pub(crate) fn prepare(input: &native::Module) -> Result<Prepared, BackendError> {
    let constants = constants::prepare(input)?;
    let mut globals = BTreeSet::new();
    globals.extend(constants.names.values().cloned());
    globals.extend(input.global_bindings.iter().cloned());
    globals.extend(
        input
            .external_constants
            .iter()
            .map(|constant| constant.internal_name.clone()),
    );
    for function in &input.functions {
        if let Body::Managed(function) = &function.body
            && function.name == native::GLOBAL_INITIALIZER
        {
            for statement in &function.body.statements {
                if let Statement::Bind { pattern, .. } = statement {
                    names(pattern, &mut globals)
                }
            }
        }
    }
    let mut prepared = Prepared {
        constants,
        nonretaining_adapters: retention::adapters(input)?,
        handler_budget_entries: HashMap::new(),
        retained_handlers: HashMap::new(),
        retained_proofs: HashMap::new(),
        unproven_retained: HashSet::new(),
        unowned_retained_sites: HashSet::new(),
        callable_owners: input
            .functions
            .iter()
            .filter_map(|function| {
                let (name, definition) = match &function.body {
                    Body::Managed(function) => (&function.name, function.definition),
                    Body::Cps(function) => (&function.name, function.definition),
                    _ => return None,
                };
                let name = canonical_owner(name);
                Some((
                    name.into(),
                    if name == native::GLOBAL_INITIALIZER {
                        CallableOwner::Global
                    } else {
                        CallableOwner::Function(definition)
                    },
                ))
            })
            .collect(),
        closure_sites: {
            let mut sites = HashMap::new();
            for site in &input.closure_sites {
                let location = (
                    site.owner,
                    (site.span.file.0, site.span.start, site.span.end),
                );
                if sites.insert(location, site.id).is_some() {
                    return Err(unsupported(
                        "native closure cache cannot distinguish source sites at one owner/location; executable closure identities are required",
                    ));
                }
            }
            sites
        },
        budget_entries: input
            .budget_entries
            .iter()
            .map(|(name, entry)| (name.clone(), entry.clone()))
            .collect(),
        functions: input.functions.clone(),
        captures: HashMap::new(),
        lambdas: HashMap::new(),
        named: HashMap::new(),
        globals: globals.into_iter().collect(),
    };
    for proof in &input.retained_handlers {
        let Some(key) = proof.callable else {
            prepared.unowned_retained_sites.insert((
                proof.span.file.0,
                proof.span.start,
                proof.span.end,
            ));
            continue;
        };
        let Some(definitions) = &proof.definitions else {
            prepared.unproven_retained.insert(key);
            continue;
        };
        let definitions: Vec<_> = definitions
            .iter()
            .map(|definition| u64::from(definition.0))
            .collect();
        if let Some(previous) = prepared.retained_proofs.insert(key, definitions.clone())
            && previous != definitions
        {
            return Err(unsupported(
                "retained handler definitions differ within one lexical callable instance",
            ));
        }
    }
    let mut cursor = 0;
    let mut known_cps: BTreeSet<_> = input
        .functions
        .iter()
        .filter_map(|function| {
            // Bootstrap uses CPS even in an entirely pure module. Treating it
            // as a user-call seed would upgrade lifted callees after their
            // enclosing callers had already been selected as Managed.
            if let Body::Cps(graph) = &function.body
                && canonical_owner(&graph.name) != native::GLOBAL_INITIALIZER
            {
                Some(graph.name.clone())
            } else {
                None
            }
        })
        .collect();
    while cursor < prepared.functions.len() {
        let function = prepared.functions[cursor].clone();
        cursor += 1;
        if let Body::Cps(graph) = &function.body {
            if graph.metered
                && let Some(normal_name) = graph.name.strip_prefix("\0ril.budget.")
            {
                for block in &graph.blocks {
                    if let ril_ir::cps::Terminator::Handle {
                        definition, arms, ..
                    } = &block.terminator
                    {
                        for arm in arms {
                            prepared.handler_budget_entries.insert(
                                (normal_name.into(), *definition, arm.operation),
                                cps::block_symbol(graph, arm.entry),
                            );
                        }
                    }
                }
            }
            for index in 0..graph.blocks.len() {
                let block = ril_ir::cps::BlockId(index as u32);
                if block != graph.entry {
                    prepared.functions.push(native::Function {
                        symbol: cps::block_symbol(graph, block),
                        body: Body::CpsBlock {
                            function: graph.clone(),
                            block,
                        },
                    });
                }
            }
        }
        let (function, cps_locals, retained_lambdas) = match &function.body {
            Body::Managed(function) => (function.clone(), BTreeSet::new(), BTreeSet::new()),
            Body::Cps(graph) => (
                core::Function {
                    role: graph.role,
                    definition: graph.definition,
                    name: graph.name.clone(),
                    generic_parameters: graph.generic_parameters.clone(),
                    // Executable defaults already occur in CPS instructions.
                    // Do not discover their unnormalized metadata copies again.
                    parameters: graph
                        .parameters
                        .iter()
                        .map(|parameter| core::Parameter {
                            pattern: parameter.pattern.clone(),
                            default: None,
                        })
                        .collect(),
                    body: core::Block {
                        statements: graph
                            .blocks
                            .iter()
                            .flat_map(|block| block.instructions.iter().flat_map(cps_statements))
                            .collect(),
                    },
                    span: graph.span,
                },
                graph.locals.clone(),
                graph.retained_lambdas.clone(),
            ),
            _ => continue,
        };
        let mut bound = BTreeSet::new();
        bound.extend(cps_locals);
        if let Some(captures) = prepared.captures.get(&function.name) {
            bound.extend(captures.iter().cloned());
        }
        let found = discovery::function(&function, &bound);
        named::prepare(
            &function,
            &found,
            &mut prepared,
            &mut known_cps,
            &input.operations,
            &retained_lambdas,
        )?;
        for creation in found {
            let discovery::Callable::Lambda(expr) = creation.callable else {
                continue;
            };
            let ExprKind::Lambda { parameters, body } = &expr.kind else {
                unreachable!();
            };
            let (span, parameters, body) = (expr.span, parameters.clone(), body.as_ref().clone());
            let bound = creation.bound;
            let key = callable_key(&function.name, span);
            let site = key.span;
            let callable = prepared
                .callable_owners
                .get(canonical_owner(&function.name))
                .and_then(|owner| prepared.closure_sites.get(&(*owner, site)))
                .copied()
                .map(CallableOwner::Lambda);
            if prepared.lambdas.contains_key(&key) {
                continue;
            }
            let symbol = format!("__ril_lambda_{}", prepared.lambdas.len());
            let name = format!("\0ril.lambda.{}", prepared.lambdas.len());
            if let Some(owner) = callable {
                prepared.callable_owners.insert(name.clone(), owner);
            }
            let mut local = BTreeSet::new();
            let mut used = BTreeSet::new();
            for parameter in &parameters {
                if let Some(default) = &parameter.default {
                    free_names(default, &local, &mut used);
                }
                names(&parameter.pattern, &mut local)
            }
            free_names(&body, &local, &mut used);
            let captures: Vec<_> = used.intersection(&bound).cloned().collect();
            let nonretaining_adapter = prepared
                .callable_owners
                .get(canonical_owner(&function.name))
                .and_then(|owner| prepared.nonretaining_adapters.get(&(*owner, site)))
                .copied();
            if let Some(builtin) = nonretaining_adapter {
                retention::validate(builtin, callable, &parameters, &body, &captures, &prepared)?;
            }
            prepared.captures.insert(name.clone(), captures.clone());
            prepared.lambdas.insert(key, name.clone());
            let mut dynamic: BTreeSet<_> = captures.iter().cloned().collect();
            dynamic.extend(prepared.globals.iter().cloned());
            dynamic.extend(local);
            let operations = input
                .operations
                .iter()
                .map(|operation| operation.name.clone())
                .collect();
            let suspends = ril_codegen::cps::callable_suspends(
                &parameters,
                &body,
                &dynamic,
                &known_cps,
                &operations,
            );
            if nonretaining_adapter.is_none()
                && (callable.is_some_and(|owner| prepared.unproven_retained.contains(&owner))
                    || (((suspends && retained_lambdas.contains(&site))
                        || prepared.unowned_retained_sites.contains(&site))
                        && callable
                            .is_none_or(|owner| !prepared.retained_proofs.contains_key(&owner))))
            {
                return Err(unsupported(
                    "CPS callable creation under a retained handler context",
                ));
            }
            if let Some(definitions) =
                callable.and_then(|owner| prepared.retained_proofs.get(&owner))
            {
                prepared
                    .retained_handlers
                    .insert(name.clone(), definitions.clone());
            }
            let block = match body.kind {
                ExprKind::Block(block) => block,
                _ => core::Block {
                    statements: vec![Statement::Expr {
                        expression: body,
                        terminated: false,
                    }],
                },
            };
            let mut lambda = core::Function {
                role: core::FunctionRole::Ordinary,
                definition: function.definition,
                name: name.clone(),
                generic_parameters: vec![],
                parameters,
                body: block,
                span,
            };
            if !input.budget_entries.is_empty() {
                lambda =
                    ril_codegen::cps::normalize(&lambda).map_err(BackendError::NotImplemented)?;
                let capture_set = captures.iter().cloned().collect();
                let mut graph =
                    ril_codegen::cps::lower_metered_with_captures(&lambda, &capture_set)
                        .map_err(BackendError::NotImplemented)?;
                let budget_name = native::budget_entry_name(&name);
                graph.name = budget_name.clone();
                prepared
                    .budget_entries
                    .insert(name.clone(), budget_name.clone());
                prepared.captures.insert(budget_name, captures.clone());
                prepared.functions.push(native::Function {
                    symbol: format!("{symbol}__budget"),
                    body: Body::Cps(std::sync::Arc::new(graph)),
                });
            }
            let body = if suspends {
                let captures = captures.into_iter().collect();
                let graph = ril_codegen::cps::lower_with_captures(&lambda, &captures)
                    .map_err(BackendError::NotImplemented)?;
                known_cps.insert(name.clone());
                Body::Cps(std::sync::Arc::new(graph))
            } else {
                Body::Managed(lambda)
            };
            prepared.functions.push(native::Function { symbol, body });
        }
    }
    cleanup::validate(&prepared)?;
    hof::validate(&prepared)?;
    Ok(prepared)
}

pub(crate) fn emit_managed(
    module: &mut ObjectModule,
    builder: &mut FunctionBuilder<'_>,
    function: &core::Function,
    program: &mut ProgramInfo,
) -> Result<(), BackendError> {
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    let environment = builder.block_params(entry)[0];
    let arguments = builder.block_params(entry)[1];
    let failure = builder.create_block();
    let mut emitter = Emitter {
        module,
        builder,
        program,
        owner: function.name.clone(),
        locals: HashMap::new(),
        pending: HashMap::new(),
        slot: 0,
        failure,
        reachable: true,
        loops: vec![],
        scopes: vec![],
        global_init: function.name == native::GLOBAL_INITIALIZER,
    };
    emitter.raw("ril_rt_enter", &[])?;
    emitter.root(environment)?;
    emitter.root(arguments)?;
    let captures = emitter
        .program
        .functions
        .get(&function.name)
        .map(|info| info.captures.clone())
        .unwrap_or_default();
    for name in captures {
        let key = emitter.string(&name)?;
        let cell = emitter.handle("ril_rt_get_field", &[environment, key])?;
        emitter.root(cell)?;
        emitter.locals.insert(name, cell);
    }
    for (index, parameter) in function.parameters.iter().enumerate() {
        let value = if let Some(default) = &parameter.default {
            let length = emitter
                .raw("ril_rt_len", &[arguments])?
                .expect("length result");
            let present =
                emitter
                    .builder
                    .ins()
                    .icmp_imm_u(IntCC::UnsignedGreaterThan, length, index as i64);
            let supplied = emitter.builder.create_block();
            let fallback = emitter.builder.create_block();
            let joined = emitter.builder.create_block();
            emitter.builder.append_block_param(joined, types::I64);
            emitter
                .builder
                .ins()
                .brif(present, supplied, &[], fallback, &[]);
            emitter.switch(supplied);
            let value = emitter.index_constant(arguments, index)?;
            let tag = emitter.string(native::MISSING_ARGUMENT_TAG)?;
            let missing = emitter
                .raw("ril_rt_variant_is", &[value, tag])?
                .expect("missing argument test");
            let selected = emitter.builder.create_block();
            emitter
                .builder
                .ins()
                .brif(missing, fallback, &[], selected, &[]);
            emitter.switch(selected);
            emitter.builder.ins().jump(joined, &[value.into()]);
            emitter.switch(fallback);
            let value = emitter.expr(default)?;
            if emitter.reachable {
                emitter.builder.ins().jump(joined, &[value.into()]);
            }
            emitter.switch(joined);
            emitter.builder.block_params(joined)[0]
        } else {
            emitter.index_constant(arguments, index)?
        };
        emitter.bind(&parameter.pattern, value)?;
    }
    let result = emitter.block(&function.body, false)?;
    if emitter.reachable {
        let result = emitter
            .raw("ril_rt_leave", &[result])?
            .expect("leave result");
        emitter.builder.ins().return_(&[result]);
    }
    emitter.switch(failure);
    let zero = emitter.i64(0);
    let result = emitter.raw("ril_rt_leave", &[zero])?.expect("leave result");
    emitter.builder.ins().return_(&[result]);
    emitter.builder.seal_all_blocks();
    Ok(())
}

pub(crate) fn emit_entry(
    module: &mut ObjectModule,
    builder: &mut FunctionBuilder<'_>,
    initializer: &str,
    entry: &str,
    program: &mut ProgramInfo,
) -> Result<(), BackendError> {
    let block = builder.create_block();
    builder.switch_to_block(block);
    let failure = builder.create_block();

    let mut emitter = Emitter {
        module,
        builder,
        program,
        owner: String::new(),
        locals: HashMap::new(),
        pending: HashMap::new(),
        slot: 0,
        failure,
        reachable: true,
        loops: vec![],
        scopes: vec![],
        global_init: false,
    };
    emitter.raw("ril_rt_init", &[])?;
    let expected = emitter.i32(i64::from(ril_runtime_api::CONTRACT_VERSION));
    let compatible = emitter
        .raw("ril_rt_require_contract", &[expected])?
        .expect("runtime contract result");
    emitter.checked(compatible);
    emitter.initialize_constants()?;
    if let Some(descriptors) = emitter.program.foreign_descriptors.clone() {
        let encoded = emitter.string(&descriptors)?;
        emitter.handle("ril_rt_foreign_install", &[encoded])?;
        for (name, binding) in emitter.program.foreign_constants.clone() {
            let tag = emitter.string("\0ril.foreign.invoke")?;
            let callable = emitter.handle("ril_rt_builtin_value", &[tag])?;
            let binding = emitter.literal(&Literal::Integer {
                value: i128::from(binding),
                bits: 64,
                signed: true,
            })?;
            let empty = emitter.sequence(1, &[])?;
            let arguments = emitter.sequence(1, &[binding, empty])?;
            let continuation = emitter.handle("ril_rt_cps_end", &[])?;
            let step = emitter.handle("ril_rt_cps_call", &[callable, arguments, continuation])?;
            let value = emitter.handle("ril_rt_cps_run", &[step])?;
            let cell = emitter.handle("ril_rt_cell", &[value])?;
            let name = emitter.string(&name)?;
            emitter.handle("ril_rt_global_set", &[name, cell])?;
        }
    }
    let env = emitter.handle("ril_rt_unit", &[])?;
    let args = emitter.sequence(1, &[])?;
    let init = emitter
        .program
        .symbols
        .get(initializer)
        .ok_or_else(|| BackendError::InvalidIr("missing initializer".into()))?
        .clone();
    let target_info = emitter
        .program
        .symbols
        .get(entry)
        .ok_or_else(|| BackendError::InvalidIr("missing entry".into()))?
        .clone();
    if init.cps {
        let reference = emitter
            .module
            .declare_func_in_func(init.id, emitter.builder.func);
        let address = emitter.builder.ins().func_addr(types::I64, reference);
        let callable = emitter.handle("ril_rt_cps_callable", &[address, env])?;
        let continuation = emitter.handle("ril_rt_cps_end", &[])?;
        let step = emitter.handle("ril_rt_cps_call", &[callable, args, continuation])?;
        emitter.handle("ril_rt_cps_run", &[step])?;
    } else {
        emitter.direct(init.id, &[env, args])?;
    }
    emitter.raw("ril_rt_begin_entry", &[])?;
    let result = if target_info.cps {
        let reference = emitter
            .module
            .declare_func_in_func(target_info.id, emitter.builder.func);
        let address = emitter.builder.ins().func_addr(types::I64, reference);
        let callable = emitter.handle("ril_rt_cps_callable", &[address, env])?;
        let continuation = emitter.handle("ril_rt_cps_end", &[])?;
        let step = emitter.handle("ril_rt_cps_call", &[callable, args, continuation])?;
        emitter.handle("ril_rt_cps_run", &[step])?
    } else {
        emitter.direct(target_info.id, &[env, args])?
    };
    let status = emitter
        .raw("ril_rt_finish", &[result])?
        .expect("finish result");
    emitter.builder.ins().return_(&[status]);
    emitter.switch(failure);
    let zero = emitter.i64(0);
    let status = emitter
        .raw("ril_rt_finish", &[zero])?
        .expect("finish result");
    emitter.builder.ins().return_(&[status]);
    emitter.builder.seal_all_blocks();
    Ok(())
}

struct LoopBlocks {
    exit: ClifBlock,
    next: ClifBlock,
    scope_depth: usize,
}
struct Emitter<'a, 'b> {
    module: &'a mut ObjectModule,
    builder: &'a mut FunctionBuilder<'b>,
    program: &'a mut ProgramInfo,
    owner: String,
    locals: HashMap<String, Value>,
    pending: HashMap<String, Value>,
    slot: u32,
    failure: ClifBlock,
    reachable: bool,
    loops: Vec<LoopBlocks>,
    scopes: Vec<Value>,
    global_init: bool,
}

impl Emitter<'_, '_> {
    fn switch(&mut self, block: ClifBlock) {
        self.builder.switch_to_block(block);
        self.reachable = true;
    }
    fn i64(&mut self, value: i64) -> Value {
        self.builder.ins().iconst(types::I64, value)
    }
    fn i32(&mut self, value: i64) -> Value {
        self.builder.ins().iconst(types::I32, value)
    }
    fn raw(&mut self, name: &'static str, args: &[Value]) -> Result<Option<Value>, BackendError> {
        let id = if let Some(id) = self.program.imports.get(name) {
            *id
        } else {
            let (parameters, result) = runtime_signature(name)?;
            let mut signature = self.module.make_signature();
            signature
                .params
                .extend(parameters.into_iter().map(AbiParam::new));
            if let Some(result) = result {
                signature.returns.push(AbiParam::new(result));
            }
            let id = self
                .module
                .declare_function(name, Linkage::Import, &signature)
                .map_err(codegen)?;
            self.program.imports.insert(name, id);
            id
        };
        let reference = self.module.declare_func_in_func(id, self.builder.func);
        let call = self.builder.ins().call(reference, args);
        Ok(self.builder.inst_results(call).first().copied())
    }
    fn checked(&mut self, value: Value) -> Value {
        let failed = self.builder.ins().icmp_imm_u(IntCC::Equal, value, 0);
        let next = self.builder.create_block();
        self.builder
            .ins()
            .brif(failed, self.failure, &[], next, &[]);
        self.switch(next);
        value
    }
    fn handle(&mut self, name: &'static str, args: &[Value]) -> Result<Value, BackendError> {
        let result = self
            .raw(name, args)?
            .ok_or_else(|| BackendError::InvalidIr("runtime call has no result".into()))?;
        let result = self.checked(result);
        self.root(result)?;
        Ok(result)
    }
    fn direct(&mut self, id: FuncId, args: &[Value]) -> Result<Value, BackendError> {
        let reference = self.module.declare_func_in_func(id, self.builder.func);
        let address = self.builder.ins().func_addr(types::I64, reference);
        let checked = self
            .raw(
                "ril_rt_read_reservation_native",
                &[address, args[0], args[1]],
            )?
            .expect("read reservation check");
        self.checked(checked);
        let call = self.builder.ins().call(reference, args);
        let value = self.builder.inst_results(call)[0];
        let value = self.checked(value);
        self.root(value)?;
        Ok(value)
    }
    fn root(&mut self, value: Value) -> Result<(), BackendError> {
        let slot = self.i32(i64::from(self.slot));
        self.slot = self
            .slot
            .checked_add(1)
            .ok_or_else(|| BackendError::InvalidIr("too many roots".into()))?;
        let rooted = self
            .raw("ril_rt_root", &[slot, value])?
            .expect("root result");
        self.checked(rooted);
        Ok(())
    }
    fn string(&mut self, text: &str) -> Result<Value, BackendError> {
        self.bytes(text.as_bytes(), false)
    }
    fn bytes(&mut self, bytes: &[u8], binary: bool) -> Result<Value, BackendError> {
        let name = format!("__ril_data_{}", self.program.next_data);
        self.program.next_data += 1;
        let id = self
            .module
            .declare_data(&name, Linkage::Local, false, false)
            .map_err(codegen)?;
        let mut data = DataDescription::new();
        data.define(
            if bytes.is_empty() {
                vec![0]
            } else {
                bytes.to_vec()
            }
            .into_boxed_slice(),
        );
        self.module.define_data(id, &data).map_err(codegen)?;
        let global = self.module.declare_data_in_func(id, self.builder.func);
        let ptr = self.builder.ins().symbol_value(types::I64, global);
        let length = self.i64(bytes.len() as i64);
        self.handle(
            if binary { "ril_rt_bytes" } else { "ril_rt_str" },
            &[ptr, length],
        )
    }
    fn integer(&mut self, value: i128, bits: u8, signed: bool) -> Result<Value, BackendError> {
        let low = self.i64(value as i64);
        let high = self.i64((value >> 64) as i64);
        let bits = self.i32(i64::from(bits));
        let signed = self.i32(i64::from(signed));
        self.handle("ril_rt_int", &[low, high, bits, signed])
    }
    fn literal(&mut self, literal: &Literal) -> Result<Value, BackendError> {
        match literal {
            Literal::Unit => self.handle("ril_rt_unit", &[]),
            Literal::Bool(value) => {
                let value = self.i32(i64::from(*value));
                self.handle("ril_rt_bool", &[value])
            }
            Literal::Integer {
                value,
                bits,
                signed,
            } => self.integer(*value, *bits, *signed),
            Literal::BigInteger(value) => {
                let text = self.string(value)?;
                self.handle("ril_rt_bigint", &[text])
            }
            Literal::Float { value, bits } => {
                let value = self.builder.ins().f64const(*value);
                let bits = self.i32(i64::from(*bits));
                self.handle("ril_rt_float", &[value, bits])
            }
            Literal::String(value) => self.string(value),
            Literal::Bytes(value) => self.bytes(value, true),
        }
    }
    fn sequence(&mut self, kind: i64, values: &[Value]) -> Result<Value, BackendError> {
        let kind = self.i32(kind);
        let sequence = self.handle("ril_rt_sequence", &[kind])?;
        for value in values {
            self.handle("ril_rt_push", &[sequence, *value])?;
        }
        Ok(sequence)
    }
    fn index_constant(&mut self, base: Value, index: usize) -> Result<Value, BackendError> {
        let index = self.integer(index as i128, 64, true)?;
        let safe = self.i32(0);
        self.handle("ril_rt_index", &[base, index, safe])
    }
    fn sequence_rest(patterns: &[Pattern]) -> Result<Option<usize>, BackendError> {
        let mut rest = None;
        for (index, pattern) in patterns.iter().enumerate() {
            if matches!(pattern, Pattern::Rest(_)) && rest.replace(index).is_some() {
                return Err(BackendError::InvalidIr(
                    "sequence pattern has multiple rests".into(),
                ));
            }
        }
        Ok(rest)
    }
    fn length_integer(&mut self, raw: Value) -> Result<Value, BackendError> {
        let high = self.i64(0);
        let bits = self.i32(64);
        let signed = self.i32(1);
        self.handle("ril_rt_int", &[raw, high, bits, signed])
    }
    fn sequence_field(
        &mut self,
        value: Value,
        position: usize,
        rest: Option<usize>,
        patterns: usize,
    ) -> Result<Value, BackendError> {
        if rest.is_none_or(|rest| position < rest) {
            return self.index_constant(value, position);
        }
        let length = self.raw("ril_rt_len", &[value])?.expect("length result");
        let distance = i64::try_from(patterns - position).map_err(|_| {
            BackendError::InvalidIr("sequence pattern exceeds native length".into())
        })?;
        let offset = self.builder.ins().iadd_imm_s(length, -distance);
        let index = self.length_integer(offset)?;
        let safe = self.i32(0);
        self.handle("ril_rt_index", &[value, index, safe])
    }
    fn bind_sequence(
        &mut self,
        patterns: &[Pattern],
        value: Value,
        array: bool,
    ) -> Result<(), BackendError> {
        let rest = Self::sequence_rest(patterns)?;
        for (index, pattern) in patterns.iter().enumerate() {
            if let Pattern::Rest(binding) = pattern {
                if let Some(name) = binding {
                    if !array {
                        return Err(BackendError::InvalidIr(
                            "tuple remainder cannot have a binder".into(),
                        ));
                    }
                    let lower = self.integer(index as i128, 64, true)?;
                    let length = self.raw("ril_rt_len", &[value])?.expect("length result");
                    let suffix = i64::try_from(patterns.len() - index - 1).map_err(|_| {
                        BackendError::InvalidIr("array pattern exceeds native length".into())
                    })?;
                    let upper = self.builder.ins().iadd_imm_s(length, -suffix);
                    let upper = self.length_integer(upper)?;
                    let inclusive = self.i32(0);
                    let range = self.handle("ril_rt_range", &[lower, upper, inclusive])?;
                    let safe = self.i32(0);
                    let window = self.handle("ril_rt_index", &[value, range, safe])?;
                    self.bind(&Pattern::Name(name.clone()), window)?;
                }
            } else {
                let field = self.sequence_field(value, index, rest, patterns.len())?;
                self.bind(pattern, field)?;
            }
        }
        Ok(())
    }
    fn bind(&mut self, pattern: &Pattern, value: Value) -> Result<(), BackendError> {
        match pattern {
            Pattern::Name(name) => {
                let cell = if let Some(cell) = self.pending.remove(name) {
                    self.handle("ril_rt_cell_set", &[cell, value])?;
                    cell
                } else {
                    let cell = self.handle("ril_rt_cell", &[value])?;
                    self.root(cell)?;
                    cell
                };
                if self.global_init && self.program.globals.contains(name) {
                    let key = self.string(name)?;
                    self.handle("ril_rt_global_set", &[key, cell])?;
                }
                self.locals.insert(name.clone(), cell);
                Ok(())
            }
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Value(_) => Ok(()),
            Pattern::Tuple(patterns) => self.bind_sequence(patterns, value, false),
            Pattern::Array(patterns) => self.bind_sequence(patterns, value, true),
            Pattern::Rest(_) => Err(BackendError::InvalidIr(
                "standalone sequence remainder".into(),
            )),
            Pattern::Record(fields) => {
                for (name, pattern) in fields {
                    let key = self.string(name)?;
                    let item = self.handle("ril_rt_get_field", &[value, key])?;
                    self.bind(pattern, item)?;
                }
                Ok(())
            }
            Pattern::RecordRest { fields, rest } => {
                let mut labels = Vec::with_capacity(fields.len());
                for (name, pattern) in fields {
                    let key = self.string(name)?;
                    labels.push(key);
                    let item = self.handle("ril_rt_get_field", &[value, key])?;
                    self.bind(pattern, item)?;
                }
                let excluded = self.sequence(0, &labels)?;
                let remainder = self.handle("ril_rt_record_without", &[value, excluded])?;
                self.bind(&Pattern::Name(rest.clone()), remainder)
            }
            Pattern::Constructor { tag, arguments } => {
                let tuple_payload =
                    arguments.len() > 1
                        && (standard_payload_tag(tag)
                            || self.program.constructors.values().any(|constructor| {
                                constructor.tag == *tag && constructor.has_payload
                            }));
                let payload = if tuple_payload {
                    let zero = self.i32(0);
                    Some(self.handle("ril_rt_variant_field", &[value, zero])?)
                } else {
                    None
                };
                for (index, pattern) in arguments.iter().enumerate() {
                    let item = if let Some(payload) = payload {
                        self.index_constant(payload, index)?
                    } else {
                        let index = self.i32(index as i64);
                        self.handle("ril_rt_variant_field", &[value, index])?
                    };
                    self.bind(pattern, item)?;
                }
                Ok(())
            }
            Pattern::Alternative(patterns) => self.bind_alternative(patterns, value),
        }
    }
    fn cell(&mut self, name: &str) -> Result<Value, BackendError> {
        if let Some(cell) = self.locals.get(name) {
            Ok(*cell)
        } else if self.program.globals.contains(name) {
            let key = self.string(name)?;
            self.handle("ril_rt_global_get", &[key])
        } else {
            Err(BackendError::InvalidIr(format!(
                "unknown local cell {name}"
            )))
        }
    }
    fn name(&mut self, name: &str) -> Result<Value, BackendError> {
        if self.locals.contains_key(name) || self.program.globals.contains(name) {
            let cell = self.cell(name)?;
            return self.handle("ril_rt_cell_get", &[cell]);
        }
        if let Some(function) = self.program.functions.get(name).cloned() {
            let env = self.handle("ril_rt_unit", &[])?;
            return self.callable_value(&function, env);
        }
        if matches!(name, "None" | "Prelude::None") {
            let args = self.sequence(1, &[])?;
            let name = self.string(name)?;
            return self.handle("ril_rt_builtin", &[name, args]);
        }
        if let Some(constructor) = self.program.constructors.get(name).cloned() {
            let tag = self.string(&constructor.tag)?;
            let nominal = self.i32(i64::from(constructor.nominal));
            let payload = self.i32(i64::from(constructor.has_payload));
            return self.handle("ril_rt_constructor", &[tag, nominal, payload]);
        }
        if let Some(operation) = self.program.operations.get(name).copied() {
            let operation = self.i64(operation as i64);
            return self.handle("ril_rt_cps_operation", &[operation]);
        }
        if ril_runtime_api::builtins::constant(name) {
            let args = self.sequence(1, &[])?;
            let tag = self.string(name)?;
            return self.handle("ril_rt_variant", &[tag, args]);
        }
        if !ril_runtime_api::builtins::supported(name) {
            return Err(unsupported(format!("native builtin {name}")));
        }
        let name = self.string(name)?;
        self.handle("ril_rt_builtin_value", &[name])
    }
    fn block(&mut self, block: &core::Block, scoped: bool) -> Result<Value, BackendError> {
        let saved = self.locals.clone();
        let pending = std::mem::take(&mut self.pending);
        let marker = self
            .raw("ril_rt_scope_enter", &[])?
            .expect("cleanup marker");
        self.scopes.push(marker);
        let mut result = self.handle("ril_rt_unit", &[])?;
        self.hoist_named(block)?;
        for (index, statement) in block.statements.iter().enumerate() {
            if !self.reachable {
                break;
            }
            match statement {
                Statement::Bind {
                    pattern,
                    value,
                    scoped,
                } => {
                    result = self.expr(value)?;
                    if self.reachable {
                        if *scoped {
                            result = self.handle("ril_rt_scope_register", &[result])?;
                        }
                        self.bind(pattern, result)?;
                        self.raw("ril_rt_statement_end", &[])?;
                        result = self.handle("ril_rt_unit", &[])?;
                    }
                }
                Statement::Assign {
                    target,
                    operator,
                    value,
                } => {
                    result = self.assignment(target, operator, value)?;
                    if self.reachable {
                        self.raw("ril_rt_statement_end", &[])?;
                        result = self.handle("ril_rt_unit", &[])?;
                    }
                }
                Statement::Expr {
                    expression,
                    terminated,
                } => {
                    result = self.expr(expression)?;
                    if self.reachable && (*terminated || index + 1 < block.statements.len()) {
                        self.raw("ril_rt_statement_end", &[])?;
                        result = self.handle("ril_rt_unit", &[])?;
                    }
                }
                Statement::Function(_) => {}
                Statement::Handle { .. } => {
                    return Err(unsupported("native algebraic effect handlers"));
                }
            }
        }
        if scoped {
            self.locals = saved;
        }
        self.pending = pending;
        self.scopes.pop();
        if self.reachable {
            result = self.handle("ril_rt_scope_leave", &[marker, result])?;
        }
        Ok(result)
    }
    fn unwind_scopes(&mut self, depth: usize, mut value: Value) -> Result<Value, BackendError> {
        for index in (depth..self.scopes.len()).rev() {
            let marker = self.scopes[index];
            value = self.handle("ril_rt_scope_leave", &[marker, value])?;
        }
        Ok(value)
    }
    fn assignment(
        &mut self,
        target: &Expr,
        operator: &str,
        expression: &Expr,
    ) -> Result<Value, BackendError> {
        // Evaluate an address once, before its right-hand side.
        enum Address {
            Cell(Value),
            Field(Value, Value),
            Index(Value, Value),
        }
        let address = match &target.kind {
            ExprKind::Name(name) => Address::Cell(self.cell(name)?),
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let base = self.expr(base)?;
                let field = self.string(field)?;
                Address::Field(base, field)
            }
            ExprKind::Index {
                base,
                index,
                safe: false,
            } => {
                let base = self.expr(base)?;
                let index = self.expr(index)?;
                Address::Index(base, index)
            }
            _ => return Err(unsupported("native assignment target")),
        };
        let current = if operator != "=" {
            Some(match address {
                Address::Cell(cell) => self.handle("ril_rt_cell_get", &[cell])?,
                Address::Field(base, key) => self.handle("ril_rt_get_field", &[base, key])?,
                Address::Index(base, index) => {
                    let safe = self.i32(0);
                    self.handle("ril_rt_index", &[base, index, safe])?
                }
            })
        } else {
            None
        };
        let mut value = self.expr(expression)?;
        if !self.reachable {
            return Ok(value);
        }
        if let Some(current) = current {
            value = self.binary(
                operator.strip_suffix('=').unwrap_or(operator),
                current,
                value,
            )?;
        }
        match address {
            Address::Cell(cell) => self.handle("ril_rt_cell_set", &[cell, value]),
            Address::Field(base, key) => self.handle("ril_rt_set_field", &[base, key, value]),
            Address::Index(base, index) => self.handle("ril_rt_set_index", &[base, index, value]),
        }
    }
    fn binary(&mut self, operator: &str, left: Value, right: Value) -> Result<Value, BackendError> {
        if operator == "in" {
            return self.handle("ril_rt_contains", &[left, right]);
        }
        let operation = match operator {
            "+" => BinaryOp::Add,
            "-" => BinaryOp::Subtract,
            "*" => BinaryOp::Multiply,
            "/" => BinaryOp::Divide,
            "%" => BinaryOp::Remainder,
            "==" => BinaryOp::Equal,
            "!=" => BinaryOp::NotEqual,
            "<" => BinaryOp::Less,
            "<=" => BinaryOp::LessEqual,
            ">" => BinaryOp::Greater,
            ">=" => BinaryOp::GreaterEqual,
            "&" => BinaryOp::BitAnd,
            "|" => BinaryOp::BitOr,
            "^" => BinaryOp::BitXor,
            "<<" => BinaryOp::ShiftLeft,
            ">>" => BinaryOp::ShiftRight,
            "+%" => BinaryOp::WrappingAdd,
            "-%" => BinaryOp::WrappingSubtract,
            "*%" => BinaryOp::WrappingMultiply,
            "/?" => BinaryOp::SafeDivide,
            "%?" => BinaryOp::SafeRemainder,
            _ => return Err(unsupported(format!("native operator {operator}"))),
        };
        let op = self.i32(operation as i64);
        self.handle("ril_rt_binary", &[op, left, right])
    }
    fn boolean_raw(&mut self, value: Value) -> Result<Value, BackendError> {
        let result = self.raw("ril_rt_truth", &[value])?.expect("truth result");
        let status = self.raw("ril_rt_status", &[])?.expect("status result");
        let failed = self.builder.ins().icmp_imm_u(IntCC::NotEqual, status, 0);
        let next = self.builder.create_block();
        self.builder
            .ins()
            .brif(failed, self.failure, &[], next, &[]);
        self.switch(next);
        Ok(result)
    }
    fn conditional(
        &mut self,
        condition: Value,
        yes: &Expr,
        no: Option<&Expr>,
    ) -> Result<Value, BackendError> {
        let condition = self.boolean_raw(condition)?;
        let yes_block = self.builder.create_block();
        let no_block = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, types::I64);
        self.builder
            .ins()
            .brif(condition, yes_block, &[], no_block, &[]);
        self.switch(yes_block);
        let yes = self.expr(yes)?;
        let yes_reachable = self.reachable;
        if yes_reachable {
            self.builder.ins().jump(join, &[yes.into()]);
        }
        self.switch(no_block);
        let no = if let Some(no) = no {
            self.expr(no)?
        } else {
            self.handle("ril_rt_unit", &[])?
        };
        let no_reachable = self.reachable;
        if no_reachable {
            self.builder.ins().jump(join, &[no.into()]);
        }
        if yes_reachable || no_reachable {
            self.switch(join);
            Ok(self.builder.block_params(join)[0])
        } else {
            self.reachable = false;
            Ok(no)
        }
    }
    fn call(
        &mut self,
        callee: &Expr,
        arguments: &[core::Argument],
        span: ril_compiler_core::source::Span,
    ) -> Result<Value, BackendError> {
        let named = if let ExprKind::Name(name) = &callee.kind {
            Some(name.as_str())
        } else {
            None
        };
        let direct = named
            .filter(|name| {
                !self.locals.contains_key(*name) && !self.program.globals.contains(*name)
            })
            .and_then(|name| self.program.functions.get(name))
            .cloned();
        let builtin = named.filter(|name| {
            !self.locals.contains_key(*name)
                && !self.program.globals.contains(*name)
                && direct.is_none()
                && !self.program.constructors.contains_key(*name)
                && !self.program.operations.contains_key(*name)
        });
        if let Some(name) = builtin
            && ril_runtime_api::builtins::requires_native_step(name)
        {
            return Err(unsupported(format!(
                "native builtin {name} requires native continuation lowering"
            )));
        }
        if let Some(name) = builtin
            && !ril_runtime_api::builtins::supported(name)
        {
            return Err(unsupported(format!("native builtin {name}")));
        }
        let callable = if direct.is_none() && builtin.is_none() {
            Some(self.expr(callee)?)
        } else {
            None
        };
        if !self.reachable {
            return Ok(callable.expect("terminated callable expression"));
        }
        let mut values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let value = self.expr(&argument.value)?;
            if !self.reachable {
                return Ok(value);
            }
            values.push((argument.label.clone(), value));
        }
        if arguments.iter().any(|argument| argument.label.is_some()) {
            values = self
                .ordered_arguments(values, span, direct.as_ref())?
                .into_iter()
                .map(|value| (None, value))
                .collect();
        }
        let values: Vec<_> = values.into_iter().map(|(_, value)| value).collect();
        let args = self.sequence(1, &values)?;
        self.locate(span)?;
        if let Some(function) = direct {
            if function.cps {
                return Err(unsupported(
                    "CPS callee requires its caller to be converted",
                ));
            }
            let env = self.handle("ril_rt_unit", &[])?;
            return self.direct(function.id, &[env, args]);
        }
        if let Some(name) = builtin {
            let name = self.string(name)?;
            return self.handle("ril_rt_builtin", &[name, args]);
        }
        self.apply(callable.expect("dynamic callable"), args)
    }
    fn ordered_arguments(
        &mut self,
        values: Vec<(Option<String>, Value)>,
        span: ril_compiler_core::source::Span,
        direct: Option<&FunctionInfo>,
    ) -> Result<Vec<Value>, BackendError> {
        if values.iter().all(|(label, _)| label.is_none()) {
            return Ok(values.into_iter().map(|(_, value)| value).collect());
        }
        let key = (span.file.0, span.start, span.end);
        let fallback;
        let parameters = if let Some(signature) = self.program.call_signatures.get(&key) {
            signature
        } else if let Some(function) = direct {
            fallback = function
                .parameters
                .iter()
                .map(|parameter| core::CallParameter {
                    label: if let Pattern::Name(name) = &parameter.pattern {
                        Some(name.clone())
                    } else {
                        None
                    },
                    has_default: parameter.default.is_some(),
                })
                .collect();
            &fallback
        } else {
            return Err(unsupported(
                "native dynamic call lacks a typed label signature",
            ));
        };
        let mut slots = vec![None; parameters.len()];
        for (label, value) in values {
            let index = if let Some(label) = label {
                parameters
                    .iter()
                    .position(|parameter| parameter.label.as_ref() == Some(&label))
            } else {
                slots.iter().position(Option::is_none)
            }
            .ok_or_else(|| {
                BackendError::InvalidIr("argument has no typed parameter slot".into())
            })?;
            if slots[index].replace(value).is_some() {
                return Err(BackendError::InvalidIr(
                    "duplicate typed argument slot".into(),
                ));
            }
        }
        let supplied = slots
            .iter()
            .rposition(Option::is_some)
            .map_or(0, |index| index + 1);
        if slots[..supplied]
            .iter()
            .zip(parameters)
            .any(|(value, parameter)| value.is_none() && !parameter.has_default)
        {
            return Err(BackendError::InvalidIr(
                "missing required typed argument".into(),
            ));
        }
        if parameters[supplied..]
            .iter()
            .any(|parameter| !parameter.has_default)
        {
            return Err(BackendError::InvalidIr(
                "missing required typed argument".into(),
            ));
        }
        let missing = if slots[..supplied].iter().any(Option::is_none) {
            let tag = self.string(native::MISSING_ARGUMENT_TAG)?;
            let fields = self.sequence(1, &[])?;
            Some(self.handle("ril_rt_variant", &[tag, fields])?)
        } else {
            None
        };
        Ok(slots
            .into_iter()
            .take(supplied)
            .map(|value| value.or(missing).expect("certified argument slot"))
            .collect())
    }
    fn apply(&mut self, callable: Value, args: Value) -> Result<Value, BackendError> {
        let checked = self
            .raw("ril_rt_read_reservation_check", &[callable, args])?
            .expect("read reservation check");
        self.checked(checked);
        let address = self
            .raw("ril_rt_callable_address", &[callable])?
            .expect("callable address");
        let builtin = self.builder.ins().icmp_imm_u(IntCC::Equal, address, 0);
        let native = self.builder.create_block();
        let builtin_block = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, types::I64);
        self.builder
            .ins()
            .brif(builtin, builtin_block, &[], native, &[]);
        self.switch(builtin_block);
        let value = self.handle("ril_rt_apply_builtin", &[callable, args])?;
        self.builder.ins().jump(join, &[value.into()]);
        self.switch(native);
        let environment = self.handle("ril_rt_callable_environment", &[callable])?;
        let mut signature = self.module.make_signature();
        signature
            .params
            .extend([AbiParam::new(types::I64), AbiParam::new(types::I64)]);
        signature.returns.push(AbiParam::new(types::I64));
        let signature = self.builder.import_signature(signature);
        let call = self
            .builder
            .ins()
            .call_indirect(signature, address, &[environment, args]);
        let value = self.builder.inst_results(call)[0];
        let value = self.checked(value);
        self.root(value)?;
        self.builder.ins().jump(join, &[value.into()]);
        self.switch(join);
        Ok(self.builder.block_params(join)[0])
    }
    fn coalesce(&mut self, value: &Expr, fallback: &Expr) -> Result<Value, BackendError> {
        let value = self.expr(value)?;
        if !self.reachable {
            return Ok(value);
        }
        let some = self.string("Some")?;
        let some = self
            .raw("ril_rt_variant_is", &[value, some])?
            .expect("variant test");
        let ok = self.string("Ok")?;
        let ok = self
            .raw("ril_rt_variant_is", &[value, ok])?
            .expect("variant test");
        let present = self.builder.ins().bor(some, ok);
        let success = self.builder.create_block();
        let absent = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, types::I64);
        self.builder.ins().brif(present, success, &[], absent, &[]);
        self.switch(success);
        let index = self.i32(0);
        let payload = self.handle("ril_rt_variant_field", &[value, index])?;
        self.builder.ins().jump(join, &[payload.into()]);
        self.switch(absent);
        let err = self.string("Err")?;
        let error = self
            .raw("ril_rt_variant_is", &[value, err])?
            .expect("variant test");
        let recover = self.builder.create_block();
        let none = self.builder.create_block();
        self.builder.ins().brif(error, recover, &[], none, &[]);
        self.switch(recover);
        let index = self.i32(0);
        let error = self.handle("ril_rt_variant_field", &[value, index])?;
        let callback = self.expr(fallback)?;
        if self.reachable {
            let args = self.sequence(1, &[error])?;
            let result = self.apply(callback, args)?;
            self.builder.ins().jump(join, &[result.into()]);
        }
        self.switch(none);
        let result = self.expr(fallback)?;
        if self.reachable {
            self.builder.ins().jump(join, &[result.into()]);
        }
        self.switch(join);
        Ok(self.builder.block_params(join)[0])
    }
    fn locate(&mut self, span: ril_compiler_core::source::Span) -> Result<(), BackendError> {
        let file = self.i32(i64::from(span.file.0));
        let start = self.i32(i64::from(span.start));
        let end = self.i32(i64::from(span.end));
        self.raw("ril_rt_location", &[file, start, end])?;
        Ok(())
    }
    fn expr(&mut self, expr: &Expr) -> Result<Value, BackendError> {
        self.locate(expr.span)?;
        match &expr.kind {
            ExprKind::ConstRef(reference) => self.constant_ref(*reference),
            ExprKind::Charge(_) => self.handle("ril_rt_unit", &[]),
            ExprKind::Budget { .. } => Err(unsupported(
                "budget boundary requires native continuation lowering",
            )),
            ExprKind::Literal(literal) => self.literal(literal),
            ExprKind::Name(name) => self.name(name),
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let mut values = Vec::new();
                for item in items {
                    let value = self.expr(item)?;
                    if !self.reachable {
                        return Ok(value);
                    }
                    values.push(value);
                }
                self.sequence(
                    if matches!(expr.kind, ExprKind::Array(_)) {
                        0
                    } else {
                        1
                    },
                    &values,
                )
            }
            ExprKind::Range {
                lower,
                upper,
                inclusive,
            } => {
                let lower = if let Some(lower) = lower {
                    let value = self.expr(lower)?;
                    if !self.reachable {
                        return Ok(value);
                    }
                    value
                } else {
                    self.i64(0)
                };
                let upper = if let Some(upper) = upper {
                    let value = self.expr(upper)?;
                    if !self.reachable {
                        return Ok(value);
                    }
                    value
                } else {
                    self.i64(0)
                };
                let inclusive = self.i32(i64::from(*inclusive));
                self.locate(expr.span)?;
                self.handle("ril_rt_range", &[lower, upper, inclusive])
            }
            ExprKind::Record {
                fields,
                spread,
                members,
            } if members.is_empty() => {
                let record = if let Some(spread) = spread {
                    let base = self.expr(spread)?;
                    if !self.reachable {
                        return Ok(base);
                    }
                    self.handle("ril_rt_record_copy", &[base])?
                } else {
                    self.handle("ril_rt_record", &[])?
                };
                for (name, value) in fields {
                    let value = self.expr(value)?;
                    if !self.reachable {
                        return Ok(value);
                    }
                    let key = self.string(name)?;
                    self.handle("ril_rt_set_field", &[record, key, value])?;
                }
                Ok(record)
            }
            ExprKind::Record { members, .. } => {
                let mut fields = Vec::new();
                let mut spreads = Vec::new();
                for member in members {
                    match member {
                        core::RecordMember::Field(name, expression) => {
                            let value = self.expr(expression)?;
                            if !self.reachable {
                                return Ok(value);
                            }
                            fields.push((name, value));
                        }
                        core::RecordMember::Spread(expression) => {
                            let value = self.expr(expression)?;
                            if !self.reachable {
                                return Ok(value);
                            }
                            spreads.push(value);
                        }
                    }
                }
                let record = self.handle("ril_rt_record", &[])?;
                for spread in spreads {
                    self.handle("ril_rt_record_merge", &[record, spread])?;
                }
                for (name, value) in fields {
                    let name = self.string(name)?;
                    self.handle("ril_rt_set_field", &[record, name, value])?;
                }
                Ok(record)
            }
            ExprKind::Unary { operator, operand } => {
                let value = self.expr(operand)?;
                if !self.reachable {
                    return Ok(value);
                }
                if operator == "^mut" {
                    return Ok(value);
                }
                let operation = self.i32(match operator.as_str() {
                    "-" => 0,
                    "!" => 1,
                    "~" => 2,
                    _ => return Err(unsupported(format!("native unary operator {operator}"))),
                });
                self.locate(expr.span)?;
                self.handle("ril_rt_unary", &[operation, value])
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "&&" || operator == "||" => {
                let value = self.expr(left)?;
                if !self.reachable {
                    return Ok(value);
                }
                let fixed = Expr {
                    kind: ExprKind::Literal(Literal::Bool(operator == "||")),
                    span: expr.span,
                };
                if operator == "&&" {
                    self.conditional(value, right, Some(&fixed))
                } else {
                    self.conditional(value, &fixed, Some(right))
                }
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => self.coalesce(left, right),
            ExprKind::Binary { operator, .. } if operator == "|>" || operator == "!>" => {
                Err(unsupported("unlowered pipeline application"))
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                let left = self.expr(left)?;
                if !self.reachable {
                    return Ok(left);
                }
                let right = self.expr(right)?;
                if !self.reachable {
                    return Ok(right);
                }
                self.locate(expr.span)?;
                self.binary(operator, left, right)
            }
            ExprKind::Call {
                callee, arguments, ..
            } => self.call(callee, arguments, expr.span),
            ExprKind::Perform { .. } => Err(unsupported(
                "effect operation requires native CPS conversion",
            )),
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let base = self.expr(base)?;
                if !self.reachable {
                    return Ok(base);
                }
                let key = self.string(field)?;
                self.locate(expr.span)?;
                self.handle("ril_rt_get_field", &[base, key])
            }
            ExprKind::Index { base, index, safe } => {
                let base = self.expr(base)?;
                if !self.reachable {
                    return Ok(base);
                }
                if *safe {
                    return self.safe_index(base, index, expr.span);
                }
                let index = self.expr(index)?;
                if !self.reachable {
                    return Ok(index);
                }
                let safe = self.i32(i64::from(*safe));
                self.locate(expr.span)?;
                self.handle("ril_rt_index", &[base, index, safe])
            }
            ExprKind::Block(block) => self.block(block, true),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.expr(condition)?;
                if !self.reachable {
                    return Ok(condition);
                }
                self.conditional(condition, then_branch, else_branch.as_deref())
            }
            ExprKind::Lambda { .. } => {
                let key = callable_key(&self.owner, expr.span);
                let name = self
                    .program
                    .lambdas
                    .get(&key)
                    .ok_or_else(|| BackendError::InvalidIr("lambda was not declared".into()))?
                    .clone();
                self.closure(&name)
            }
            ExprKind::Control { operation, value } => {
                let value = if let Some(value) = value {
                    self.expr(value)?
                } else {
                    self.handle("ril_rt_unit", &[])?
                };
                if !self.reachable {
                    return Ok(value);
                }
                match operation {
                    ControlOperation::Return => {
                        let returned = self.raw("ril_rt_leave", &[value])?.expect("leave result");
                        self.builder.ins().return_(&[returned]);
                    }
                    ControlOperation::Last | ControlOperation::Next => {
                        let blocks = self.loops.last().ok_or_else(|| {
                            BackendError::InvalidIr("loop control outside loop".into())
                        })?;
                        let (exit, next, depth) = (blocks.exit, blocks.next, blocks.scope_depth);
                        let value = self.unwind_scopes(depth, value)?;
                        if *operation == ControlOperation::Last {
                            self.builder.ins().jump(exit, &[value.into()]);
                        } else {
                            self.builder.ins().jump(next, &[]);
                        }
                    }
                    ControlOperation::Resume => return Err(unsupported("native effect resume")),
                };
                self.reachable = false;
                Ok(value)
            }
            ExprKind::Loop { body, .. } => self.loop_expr(None, body),
            ExprKind::While {
                condition, body, ..
            } => self.loop_expr(Some(condition), body),
            ExprKind::For {
                iterable,
                pattern,
                body,
                ..
            } => self.for_expr(iterable, pattern, body),
            ExprKind::Derive { base, recipe } => {
                let base = self.expr(base)?;
                if !self.reachable {
                    return Ok(base);
                }
                let immutable = self.i32(0);
                let copy = self.handle("ril_rt_clone", &[base, immutable])?;
                let recipe = self.expr(recipe)?;
                if !self.reachable {
                    return Ok(recipe);
                }
                let args = self.sequence(1, &[copy])?;
                self.apply(recipe, args)?;
                Ok(copy)
            }
            ExprKind::Is { value, pattern } => {
                let value = self.expr(value)?;
                if !self.reachable {
                    return Ok(value);
                }
                let matched = self.pattern_test(pattern, value, false)?;
                if !self.reachable {
                    return Ok(value);
                }
                self.handle("ril_rt_bool", &[matched])
            }
            ExprKind::Match { value, arms } => self.match_expr(value, arms),
            ExprKind::Map(entries) => {
                let map = self.handle("ril_rt_map", &[])?;
                for (key, value) in entries {
                    let key = self.expr(key)?;
                    if !self.reachable {
                        return Ok(key);
                    }
                    let value = self.expr(value)?;
                    if !self.reachable {
                        return Ok(value);
                    }
                    self.handle("ril_rt_map_set", &[map, key, value])?;
                }
                Ok(map)
            }
            ExprKind::Field { safe: true, .. } => Err(unsupported("native safe field access")),
        }
    }

    fn safe_index(
        &mut self,
        base: Value,
        index: &Expr,
        span: ril_compiler_core::source::Span,
    ) -> Result<Value, BackendError> {
        let tag = self.string("Prelude::None")?;
        let absent = self
            .raw("ril_rt_variant_is", &[base, tag])?
            .expect("tag test");
        let skipped = self.builder.create_block();
        let lookup = self.builder.create_block();
        let joined = self.builder.create_block();
        self.builder.append_block_param(joined, types::I64);
        self.builder.ins().brif(absent, skipped, &[], lookup, &[]);
        self.switch(skipped);
        self.builder.ins().jump(joined, &[base.into()]);
        self.switch(lookup);
        let index = self.expr(index)?;
        if self.reachable {
            let safe = self.i32(1);
            self.locate(span)?;
            let result = self.handle("ril_rt_index", &[base, index, safe])?;
            self.builder.ins().jump(joined, &[result.into()]);
        }
        self.switch(joined);
        Ok(self.builder.block_params(joined)[0])
    }
    fn loop_expr(
        &mut self,
        condition: Option<&Expr>,
        body: &core::Block,
    ) -> Result<Value, BackendError> {
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit = self.builder.create_block();
        self.builder.append_block_param(exit, types::I64);
        self.builder.ins().jump(header, &[]);
        self.switch(header);
        if let Some(condition) = condition {
            let value = self.expr(condition)?;
            if !self.reachable {
                return Ok(value);
            }
            let truth = self.boolean_raw(value)?;
            let unit = self.handle("ril_rt_unit", &[])?;
            self.builder
                .ins()
                .brif(truth, body_block, &[], exit, &[unit.into()]);
        } else {
            self.builder.ins().jump(body_block, &[]);
        }
        self.switch(body_block);
        self.loops.push(LoopBlocks {
            exit,
            next: header,
            scope_depth: self.scopes.len(),
        });
        self.block(body, true)?;
        self.loops.pop();
        if self.reachable {
            self.raw("ril_rt_statement_end", &[])?;
            self.builder.ins().jump(header, &[]);
        }
        self.switch(exit);
        Ok(self.builder.block_params(exit)[0])
    }
    fn for_expr(
        &mut self,
        iterable: &Expr,
        pattern: &Pattern,
        body: &core::Block,
    ) -> Result<Value, BackendError> {
        let iterable = self.expr(iterable)?;
        if !self.reachable {
            return Ok(iterable);
        }
        let iterable = self.handle("ril_rt_iter_start", &[iterable])?;
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let next = self.builder.create_block();
        let exit = self.builder.create_block();
        self.builder.append_block_param(exit, types::I64);
        self.builder.ins().jump(header, &[]);
        self.switch(header);
        let item = self.handle("ril_rt_iter_next", &[iterable])?;
        let tag = self.string("Some")?;
        let more = self
            .raw("ril_rt_variant_is", &[item, tag])?
            .expect("iterator option tag");
        let unit = self.handle("ril_rt_unit", &[])?;
        self.builder
            .ins()
            .brif(more, body_block, &[], exit, &[unit.into()]);
        self.switch(body_block);
        let zero = self.i32(0);
        let item = self.handle("ril_rt_variant_field", &[item, zero])?;
        let saved = self.locals.clone();
        self.bind(pattern, item)?;
        self.loops.push(LoopBlocks {
            exit,
            next,
            scope_depth: self.scopes.len(),
        });
        self.block(body, false)?;
        self.loops.pop();
        self.locals = saved;
        if self.reachable {
            self.builder.ins().jump(next, &[]);
        }
        self.switch(next);
        self.raw("ril_rt_statement_end", &[])?;
        self.builder.ins().jump(header, &[]);
        self.switch(exit);
        Ok(self.builder.block_params(exit)[0])
    }
    fn sequence_pattern_test(
        &mut self,
        patterns: &[Pattern],
        value: Value,
        binding: bool,
        array: bool,
    ) -> Result<Value, BackendError> {
        let rest = Self::sequence_rest(patterns)?;
        let minimum =
            i64::try_from(patterns.len() - usize::from(rest.is_some())).map_err(|_| {
                BackendError::InvalidIr("sequence pattern exceeds native length".into())
            })?;
        let array = self.i32(i64::from(array));
        let minimum = self.i64(minimum);
        let has_rest = self.i32(i64::from(rest.is_some()));
        let matched = self
            .raw(
                "ril_rt_sequence_matches",
                &[value, array, minimum, has_rest],
            )?
            .expect("sequence pattern test result");
        let fields = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, types::I32);
        let zero = self.i32(0);
        self.builder
            .ins()
            .brif(matched, fields, &[], join, &[zero.into()]);
        self.switch(fields);
        for (index, pattern) in patterns.iter().enumerate() {
            if matches!(pattern, Pattern::Rest(_)) {
                continue;
            }
            let field = self.sequence_field(value, index, rest, patterns.len())?;
            let matched = self.pattern_test(pattern, field, binding)?;
            if !self.reachable {
                self.switch(join);
                return Ok(self.builder.block_params(join)[0]);
            }
            let next = self.builder.create_block();
            let zero = self.i32(0);
            self.builder
                .ins()
                .brif(matched, next, &[], join, &[zero.into()]);
            self.switch(next);
        }
        let one = self.i32(1);
        self.builder.ins().jump(join, &[one.into()]);
        self.switch(join);
        Ok(self.builder.block_params(join)[0])
    }
    fn pattern_test(
        &mut self,
        pattern: &Pattern,
        value: Value,
        binding: bool,
    ) -> Result<Value, BackendError> {
        match pattern {
            Pattern::Wildcard => Ok(self.i32(1)),
            Pattern::Rest(_) => Err(BackendError::InvalidIr(
                "standalone sequence remainder test".into(),
            )),
            Pattern::Name(_) if binding => Ok(self.i32(1)),
            Pattern::Name(name) => {
                let expected = self.name(name)?;
                let equal = self.binary("==", value, expected)?;
                self.boolean_raw(equal)
            }
            Pattern::Literal(literal) => {
                let expected = self.literal(literal)?;
                let equal = self.binary("==", value, expected)?;
                self.boolean_raw(equal)
            }
            Pattern::Value(expression) => {
                if let ExprKind::Range {
                    lower: Some(lower),
                    upper: Some(upper),
                    inclusive,
                } = &expression.kind
                {
                    let lower = self.expr(lower)?;
                    if !self.reachable {
                        return Ok(lower);
                    }
                    let low = self.binary(">=", value, lower)?;
                    let low = self.boolean_raw(low)?;
                    let upper = self.expr(upper)?;
                    if !self.reachable {
                        return Ok(upper);
                    }
                    let high = self.binary(if *inclusive { "<=" } else { "<" }, value, upper)?;
                    let high = self.boolean_raw(high)?;
                    Ok(self.builder.ins().band(low, high))
                } else if binding {
                    Err(unsupported("native computed binding pattern"))
                } else {
                    let expected = self.expr(expression)?;
                    if !self.reachable {
                        return Ok(expected);
                    }
                    let equal = self.binary("==", value, expected)?;
                    self.boolean_raw(equal)
                }
            }
            Pattern::Constructor { tag, arguments } => {
                let tuple_payload =
                    arguments.len() > 1
                        && (standard_payload_tag(tag)
                            || self.program.constructors.values().any(|constructor| {
                                constructor.tag == *tag && constructor.has_payload
                            }));
                let tag = match tag.as_str() {
                    "Prelude::Some" => "Some",
                    "Prelude::None" => "None",
                    "Prelude::Ok" => "Ok",
                    "Prelude::Err" => "Err",
                    tag => tag,
                };
                let tag = self.string(tag)?;
                let matched = self
                    .raw("ril_rt_variant_is", &[value, tag])?
                    .expect("variant test result");
                if arguments.is_empty() {
                    return Ok(matched);
                }
                let fields = self.builder.create_block();
                let join = self.builder.create_block();
                self.builder.append_block_param(join, types::I32);
                let zero = self.i32(0);
                self.builder
                    .ins()
                    .brif(matched, fields, &[], join, &[zero.into()]);
                self.switch(fields);
                let payload = if tuple_payload {
                    let zero = self.i32(0);
                    Some(self.handle("ril_rt_variant_field", &[value, zero])?)
                } else {
                    None
                };
                for (index, pattern) in arguments.iter().enumerate() {
                    let field = if let Some(payload) = payload {
                        self.index_constant(payload, index)?
                    } else {
                        let index = self.i32(index as i64);
                        self.handle("ril_rt_variant_field", &[value, index])?
                    };
                    let matched = self.pattern_test(pattern, field, binding)?;
                    if !self.reachable {
                        self.switch(join);
                        return Ok(self.builder.block_params(join)[0]);
                    }
                    let next = self.builder.create_block();
                    let zero = self.i32(0);
                    self.builder
                        .ins()
                        .brif(matched, next, &[], join, &[zero.into()]);
                    self.switch(next);
                }
                let one = self.i32(1);
                self.builder.ins().jump(join, &[one.into()]);
                self.switch(join);
                Ok(self.builder.block_params(join)[0])
            }
            Pattern::Tuple(patterns) => self.sequence_pattern_test(patterns, value, binding, false),
            Pattern::Array(patterns) => self.sequence_pattern_test(patterns, value, binding, true),
            Pattern::Record(fields) | Pattern::RecordRest { fields, .. } => {
                let join = self.builder.create_block();
                self.builder.append_block_param(join, types::I32);
                for (name, pattern) in fields {
                    let key = self.string(name)?;
                    let field = self.handle("ril_rt_get_field", &[value, key])?;
                    let matched = self.pattern_test(pattern, field, binding)?;
                    if !self.reachable {
                        self.switch(join);
                        return Ok(self.builder.block_params(join)[0]);
                    }
                    let next = self.builder.create_block();
                    let zero = self.i32(0);
                    self.builder
                        .ins()
                        .brif(matched, next, &[], join, &[zero.into()]);
                    self.switch(next);
                }
                let one = self.i32(1);
                self.builder.ins().jump(join, &[one.into()]);
                self.switch(join);
                Ok(self.builder.block_params(join)[0])
            }
            Pattern::Alternative(patterns) => {
                let join = self.builder.create_block();
                self.builder.append_block_param(join, types::I32);
                for pattern in patterns {
                    let matched = self.pattern_test(pattern, value, binding)?;
                    if !self.reachable {
                        self.switch(join);
                        return Ok(self.builder.block_params(join)[0]);
                    }
                    let next = self.builder.create_block();
                    let one = self.i32(1);
                    self.builder
                        .ins()
                        .brif(matched, join, &[one.into()], next, &[]);
                    self.switch(next);
                }
                let zero = self.i32(0);
                self.builder.ins().jump(join, &[zero.into()]);
                self.switch(join);
                Ok(self.builder.block_params(join)[0])
            }
        }
    }
    fn match_expr(&mut self, value: &Expr, arms: &[core::MatchArm]) -> Result<Value, BackendError> {
        let value = self.expr(value)?;
        if !self.reachable {
            return Ok(value);
        }
        let join = self.builder.create_block();
        self.builder.append_block_param(join, types::I64);
        let saved = self.locals.clone();
        let mut any = false;
        for arm in arms {
            let accepted = self.builder.create_block();
            let next = self.builder.create_block();
            let condition = self.pattern_test(&arm.pattern, value, true)?;
            self.builder.ins().brif(condition, accepted, &[], next, &[]);
            self.switch(accepted);
            self.bind(&arm.pattern, value)?;
            if let Some(guard) = &arm.guard {
                let condition = self.expr(guard)?;
                if !self.reachable {
                    self.locals = saved.clone();
                    self.switch(next);
                    continue;
                }
                let truth = self.boolean_raw(condition)?;
                let body = self.builder.create_block();
                self.builder.ins().brif(truth, body, &[], next, &[]);
                self.switch(body);
            }
            let result = self.expr(&arm.body)?;
            if self.reachable {
                any = true;
                self.builder.ins().jump(join, &[result.into()]);
            }
            self.locals = saved.clone();
            self.switch(next);
        }
        // A verified exhaustive match cannot reach this path; make malformed public IR fail.
        let message = self.string("nonexhaustive native match")?;
        let args = self.sequence(1, &[message])?;
        let panic = self.string("panic")?;
        self.handle("ril_rt_builtin", &[panic, args])?;
        self.builder.ins().jump(self.failure, &[]);
        if any {
            self.switch(join);
            Ok(self.builder.block_params(join)[0])
        } else {
            self.reachable = false;
            Ok(value)
        }
    }
}

fn standard_payload_tag(tag: &str) -> bool {
    matches!(
        tag,
        "Some" | "Ok" | "Err" | "Prelude::Some" | "Prelude::Ok" | "Prelude::Err"
    )
}
fn runtime_signature(name: &str) -> Result<(Vec<Type>, Option<Type>), BackendError> {
    let i = types::I64;
    let w = types::I32;
    let (args, result) = match name {
        "ril_rt_init" | "ril_rt_enter" | "ril_rt_statement_end" | "ril_rt_begin_entry" => {
            (vec![], None)
        }
        "ril_rt_location" => (vec![w, w, w], None),
        "ril_rt_status" => (vec![], Some(w)),
        "ril_rt_require_contract" => (vec![w], Some(w)),
        "ril_rt_read_reservation_native" => (vec![i, i, i], Some(w)),
        "ril_rt_read_reservation_check" => (vec![i, i], Some(w)),
        "ril_rt_scope_enter" => (vec![], Some(w)),
        "ril_rt_cps_end" | "ril_rt_cps_handlers" | "ril_rt_cps_activation_new" => (vec![], Some(i)),
        "ril_rt_cps_activation_attach" => (vec![i], None),
        "ril_rt_cps_budget" | "ril_rt_cps_handle" | "ril_rt_cps_scope_leave_then" => {
            (vec![i, i, i, i], Some(i))
        }
        "ril_rt_cps_charge" => (vec![w, i], Some(i)),
        "ril_rt_callable_with_budget" => (vec![i, i, i, w], Some(i)),
        "ril_rt_cps_callable"
        | "ril_rt_cps_retain"
        | "ril_rt_cps_continuation"
        | "ril_rt_cps_return"
        | "ril_rt_cps_resume" => (vec![i, i], Some(i)),
        "ril_rt_cps_call"
        | "ril_rt_cps_callback_call"
        | "ril_rt_cps_perform"
        | "ril_rt_cps_handler_add"
        | "ril_rt_cps_resume_then"
        | "ril_rt_cps_activation_return"
        | "ril_rt_cps_scope_leave" => (vec![i, i, i], Some(i)),
        "ril_rt_cps_run" | "ril_rt_cps_operation" | "ril_rt_cps_scope_enter" => (vec![i], Some(i)),
        "ril_rt_constructor" => (vec![i, w, w], Some(i)),
        "ril_rt_scope_leave" => (vec![w, i], Some(i)),
        "ril_rt_unit" | "ril_rt_record" | "ril_rt_map" => (vec![], Some(i)),
        "ril_rt_bool" | "ril_rt_sequence" => (vec![w], Some(i)),
        "ril_rt_int" => (vec![i, i, w, w], Some(i)),
        "ril_rt_float" => (vec![types::F64, w], Some(i)),
        "ril_rt_str"
        | "ril_rt_bytes"
        | "ril_rt_push"
        | "ril_rt_get_field"
        | "ril_rt_record_merge"
        | "ril_rt_record_without"
        | "ril_rt_global_set"
        | "ril_rt_cell_set"
        | "ril_rt_callable"
        | "ril_rt_variant"
        | "ril_rt_contains"
        | "ril_rt_cps_scope_register"
        | "ril_rt_builtin"
        | "ril_rt_iter_item"
        | "ril_rt_apply_builtin" => (vec![i, i], Some(i)),
        "ril_rt_leave"
        | "ril_rt_global_get"
        | "ril_rt_cell"
        | "ril_rt_cell_get"
        | "ril_rt_callable_address"
        | "ril_rt_callable_environment"
        | "ril_rt_len"
        | "ril_rt_record_copy"
        | "ril_rt_bigint"
        | "ril_rt_iter_start"
        | "ril_rt_iter_next"
        | "ril_rt_scope_register"
        | "ril_rt_builtin_value" => (vec![i], Some(i)),
        "ril_rt_foreign_install" => (vec![i], Some(i)),
        "ril_rt_finish" | "ril_rt_truth" => (vec![i], Some(w)),
        "ril_rt_root" | "ril_rt_unary" => (vec![w, i], Some(i)),
        "ril_rt_set_field" | "ril_rt_set_index" | "ril_rt_map_set" => (vec![i, i, i], Some(i)),
        "ril_rt_index" => (vec![i, i, w], Some(i)),
        "ril_rt_binary" => (vec![w, i, i], Some(i)),
        "ril_rt_variant_is" => (vec![i, i], Some(w)),
        "ril_rt_sequence_matches" => (vec![i, w, i, w], Some(w)),
        "ril_rt_variant_field" => (vec![i, w], Some(i)),
        "ril_rt_clone" => (vec![i, w], Some(i)),
        "ril_rt_range" => (vec![i, i, w], Some(i)),
        _ => {
            return Err(BackendError::InvalidIr(format!(
                "unknown runtime import {name}"
            )));
        }
    };
    Ok((args, result))
}
