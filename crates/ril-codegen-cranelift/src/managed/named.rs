//! Lexical named-callable lifting. Captures retain the declaring storage cells.
use super::*;

pub(super) fn prepare(
    function: &core::Function,
    prepared: &mut Prepared,
    known_cps: &mut BTreeSet<String>,
    operations: &[core::Operation],
    retained: &BTreeSet<(u32, u32, u32)>,
) -> Result<(), BackendError> {
    let mut outer = BTreeSet::new();
    for parameter in &function.parameters {
        names(&parameter.pattern, &mut outer);
    }
    if let Some(captures) = prepared.captures.get(&function.name) {
        outer.extend(captures.iter().cloned());
    }
    let mut found = Vec::new();
    discover_block(&function.body, &outer, &mut found);
    for (mut child, bound) in found {
        let key = callable_key(&function.name, child.span);
        let site = key.span;
        let callable = CallableOwner::Function(child.definition);
        if prepared.named.contains_key(&key) {
            continue;
        }
        let mut own = BTreeSet::new();
        let mut used = BTreeSet::new();
        for parameter in &child.parameters {
            if let Some(default) = &parameter.default {
                free_names(default, &own, &mut used);
            }
            names(&parameter.pattern, &mut own);
        }
        free_block(&child.body, &own, &mut used);
        let captures: Vec<_> = used.intersection(&bound).cloned().collect();
        let mut dynamic: BTreeSet<_> = captures.iter().cloned().collect();
        dynamic.extend(own);
        dynamic.extend(prepared.globals.iter().cloned());
        let body = Expr {
            span: child.span,
            kind: ExprKind::Block(child.body.clone()),
        };
        let operations = operations.iter().map(|op| op.name.clone()).collect();
        let suspends = ril_codegen::cps::callable_suspends(
            &child.parameters,
            &body,
            &dynamic,
            known_cps,
            &operations,
        );
        if prepared.unproven_retained.contains(&callable)
            || (suspends
                && retained.contains(&site)
                && !prepared.retained_proofs.contains_key(&callable))
        {
            return Err(unsupported(
                "CPS named callable creation under a retained handler context",
            ));
        }
        let symbol = format!("__ril_nested_{}", prepared.named.len());
        let name = format!("\0ril.named.{}", prepared.named.len());
        prepared.callable_owners.insert(name.clone(), callable);
        if let Some(definitions) = prepared.retained_proofs.get(&callable) {
            prepared
                .retained_handlers
                .insert(name.clone(), definitions.clone());
        }
        prepared.named.insert(key, name.clone());
        prepared.captures.insert(name.clone(), captures.clone());
        child.name = name.clone();
        let captures = captures.into_iter().collect();
        if !prepared.budget_entries.is_empty() {
            child = ril_codegen::cps::normalize(&child).map_err(BackendError::NotImplemented)?;
            let mut graph = ril_codegen::cps::lower_metered_with_captures(&child, &captures)
                .map_err(BackendError::NotImplemented)?;
            let budget_name = native::budget_entry_name(&name);
            graph.name = budget_name.clone();
            prepared
                .budget_entries
                .insert(name.clone(), budget_name.clone());
            prepared
                .captures
                .insert(budget_name, captures.iter().cloned().collect());
            prepared.functions.push(native::Function {
                symbol: format!("{symbol}__budget"),
                body: Body::Cps(std::sync::Arc::new(graph)),
            });
        }
        let body = if suspends {
            let graph = ril_codegen::cps::lower_with_captures(&child, &captures)
                .map_err(BackendError::NotImplemented)?;
            known_cps.insert(name);
            Body::Cps(std::sync::Arc::new(graph))
        } else {
            Body::Managed(child)
        };
        prepared.functions.push(native::Function { symbol, body });
    }
    Ok(())
}

fn discover_block(
    block: &core::Block,
    outer: &BTreeSet<String>,
    found: &mut Vec<(core::Function, BTreeSet<String>)>,
) {
    let mut bound = outer.clone();
    // Where declarations are hoisted, so their environments include later locals.
    for statement in &block.statements {
        match statement {
            Statement::Bind { pattern, .. } => names(pattern, &mut bound),
            Statement::Function(function) => {
                bound.insert(function.name.clone());
            }
            _ => {}
        }
    }
    for statement in &block.statements {
        match statement {
            Statement::Function(function) => found.push((function.clone(), bound.clone())),
            Statement::Bind { value, .. } => discover_expr(value, &bound, found),
            Statement::Assign { target, value, .. } => {
                discover_expr(target, &bound, found);
                discover_expr(value, &bound, found);
            }
            Statement::Expr { expression, .. } => discover_expr(expression, &bound, found),
            Statement::Handle { .. } => {}
        }
    }
}

fn discover_expr(
    expr: &Expr,
    bound: &BTreeSet<String>,
    found: &mut Vec<(core::Function, BTreeSet<String>)>,
) {
    visit_expr(expr, &mut |expr| match &expr.kind {
        ExprKind::Lambda { .. } => false,
        ExprKind::Block(block) | ExprKind::Loop { body: block, .. } => {
            discover_block(block, bound, found);
            false
        }
        ExprKind::While {
            condition, body, ..
        } => {
            discover_expr(condition, bound, found);
            discover_block(body, bound, found);
            false
        }
        ExprKind::For {
            iterable,
            pattern,
            body,
            ..
        } => {
            discover_expr(iterable, bound, found);
            let mut own = bound.clone();
            names(pattern, &mut own);
            discover_block(body, &own, found);
            false
        }
        ExprKind::Match { value, arms } => {
            discover_expr(value, bound, found);
            for arm in arms {
                let mut own = bound.clone();
                names(&arm.pattern, &mut own);
                if let Some(guard) = &arm.guard {
                    discover_expr(guard, &own, found);
                }
                discover_expr(&arm.body, &own, found);
            }
            false
        }
        _ => true,
    });
}

impl Emitter<'_, '_> {
    pub(super) fn hoist_named(&mut self, block: &core::Block) -> Result<(), BackendError> {
        if !block
            .statements
            .iter()
            .any(|statement| matches!(statement, Statement::Function(_)))
        {
            return Ok(());
        }
        let mut declarations = BTreeSet::new();
        for statement in &block.statements {
            match statement {
                Statement::Bind { pattern, .. } => names(pattern, &mut declarations),
                Statement::Function(function) => {
                    declarations.insert(function.name.clone());
                }
                _ => {}
            }
        }
        let functions = block
            .statements
            .iter()
            .filter_map(|statement| match statement {
                Statement::Function(function) => Some(function.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        self.hoist_declarations(&declarations, &functions)
    }

    pub(super) fn hoist_declarations(
        &mut self,
        declarations: &BTreeSet<String>,
        functions: &[core::Function],
    ) -> Result<(), BackendError> {
        for name in declarations {
            let unit = self.handle("ril_rt_unit", &[])?;
            let cell = self.handle("ril_rt_cell", &[unit])?;
            self.locals.insert(name.clone(), cell);
            self.pending.insert(name.clone(), cell);
        }
        for function in functions {
            let key = callable_key(&self.owner, function.span);
            let name = self.program.named.get(&key).cloned().ok_or_else(|| {
                BackendError::InvalidIr("nested named callable was not declared".into())
            })?;
            let value = self.closure(&name)?;
            self.bind(&Pattern::Name(function.name.clone()), value)?;
        }
        Ok(())
    }

    pub(super) fn closure(&mut self, name: &str) -> Result<Value, BackendError> {
        let function =
            self.program.functions.get(name).cloned().ok_or_else(|| {
                BackendError::InvalidIr("lifted callable function is missing".into())
            })?;
        let environment = self.handle("ril_rt_record", &[])?;
        for name in &function.captures {
            let cell = self.cell(name)?;
            let key = self.string(name)?;
            self.handle("ril_rt_set_field", &[environment, key, cell])?;
        }
        let callable = self.callable_value(&function, environment)?;
        if let Some(definitions) = self.program.retained_handlers.get(name).cloned() {
            let mut values = Vec::new();
            for definition in definitions {
                values.push(self.integer(definition as i64 as i128, 64, true)?);
            }
            let definitions = self.sequence(1, &values)?;
            self.handle("ril_rt_cps_retain", &[callable, definitions])
        } else {
            Ok(callable)
        }
    }
    pub(super) fn callable_value(
        &mut self,
        function: &FunctionInfo,
        environment: Value,
    ) -> Result<Value, BackendError> {
        let reference = self
            .module
            .declare_func_in_func(function.id, self.builder.func);
        let address = self.builder.ins().func_addr(types::I64, reference);
        if let Some(budget) = function.budget {
            let reference = self.module.declare_func_in_func(budget, self.builder.func);
            let budget = self.builder.ins().func_addr(types::I64, reference);
            let flags = (u32::from(function.cps) * ril_runtime_api::abi::CALLABLE_NORMAL_IS_CPS)
                | (u32::from(function.metered_entry_event)
                    * ril_runtime_api::abi::CALLABLE_METERED_ENTRY_EVENT);
            let cps = self.i32(i64::from(flags));
            return self.handle(
                "ril_rt_callable_with_budget",
                &[address, budget, environment, cps],
            );
        }
        self.handle(
            if function.cps {
                "ril_rt_cps_callable"
            } else {
                "ril_rt_callable"
            },
            &[address, environment],
        )
    }
}
