//! Independently select numeric declarations from their actual callee
//! observation and original static Type arguments.
use super::*;
use ril_compiler_core::numeric_builtins::NumericBuiltin;

impl Replay<'_> {
    pub(super) fn numeric_static_callee_source(
        &self,
        expression: &Expr,
        value: &Value,
        root: usize,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let ExprKind::Generic { base, arguments } = &expression.kind else {
            return Ok(None);
        };
        let observation = self.source_child_observation(
            root,
            base.hir_id
                .ok_or("numeric generic base has no original HIR")?,
            context,
            work,
        )?;
        let actual = &self.facts.expressions[observation];
        if !matches!(actual.value.callables.as_slice(), [Callable::Builtin(name)] if name == NumericBuiltin::Convert.name())
        {
            return Ok(None);
        }
        if !crate::sema::checker::BuiltinNameIndex::is_candidate(base, work)? {
            return Ok(None);
        }
        let names = self.builtin_source_names(work)?;
        let mut budget = WorkLimit::new(*work);
        let declaration = crate::sema::checker::original_numeric_builtin_declaration(
            self.facts,
            &crate::sema::checker::CanonicalBuiltinUse {
                value: &actual.value,
                actual: base,
                context,
                observation,
            },
            &names,
            &mut budget,
        );
        *work = budget.remaining();
        drop(names);
        require(
            declaration? == Some(NumericBuiltin::Convert) && arguments.len() == 2,
            "numeric conversion lost its actual generic declaration or Type arguments",
        )?;
        let environment = self.source_graph_environment(context, Some(root), work)?;
        let scope = reception::environment_scope(&environment, work)?;
        let (source, source_environment) =
            self.source_type_header(&arguments[0], &scope, environment.clone(), work)?;
        let (destination, destination_environment) =
            self.source_type_header(&arguments[1], &scope, environment.clone(), work)?;
        require(
            !source_environment.is_poisoned() && !destination_environment.is_poisoned(),
            "numeric conversion selected a poisoned original environment",
        )?;
        let (schema, from, to) = graph_sources::schema_work(work, |budget| {
            crate::sema::source_types::numeric::conversion(&source, &destination, budget)
        })?
        .ok_or("numeric conversion Type arguments are not proved numeric scalars")?;
        let identity = format!("Num::__convert_{}_to_{}", from.name(), to.name());
        *work = work
            .checked_sub(1 + identity.len().div_ceil(32))
            .ok_or("numeric conversion identity work exhausted")?;
        require(
            matches!(value.callables.as_slice(), [Callable::Builtin(name)] if name == &identity),
            "numeric conversion runtime target differs from its original static Type arguments",
        )?;
        Ok(Some((schema, environment)))
    }

    pub(super) fn public_builtin_result_source(
        &self,
        expression: &Expr,
        root: usize,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let Some(application) = AstApplication::from_ast(expression) else {
            return Ok(None);
        };
        *work = work
            .checked_sub(self.facts.copy_call_events.len())
            .ok_or("builtin result event work exhausted")?;
        let mut events = self
            .facts
            .copy_call_events
            .iter()
            .filter(|event| event.result_expression == Some(root));
        let Some(event) = events.next() else {
            return Ok(None);
        };
        require(
            events.next().is_none()
                && event.matches_source(expression)
                && event.owner == context.owner
                && event.parent == context.invocation,
            "builtin result borrowed another physical application",
        )?;
        let token = event
            .callee_expression
            .ok_or("builtin result lost its actual callee")?;
        require(
            self.source_child_observation(
                root,
                application
                    .callee
                    .hir_id
                    .ok_or("builtin callee has no original HIR")?,
                context,
                work,
            )? == token,
            "builtin result borrowed another application's callee observation",
        )?;
        let callee = self
            .facts
            .expressions
            .get(token)
            .ok_or("builtin callee observation is absent")?;
        if !matches!(callee.value.callables.as_slice(), [Callable::Builtin(_)]) {
            return Ok(None);
        }
        let Some((schema, environment)) = self.original_observed_source_schema_with_work(
            application.callee,
            token,
            context,
            sites,
            work,
        )?
        else {
            return Ok(None);
        };
        let Some((_, result)) =
            graph_sources::schema_work(work, |budget| schema.callable_parts(budget))?
        else {
            return Ok(None);
        };
        Ok(Some((result, environment)))
    }
}
