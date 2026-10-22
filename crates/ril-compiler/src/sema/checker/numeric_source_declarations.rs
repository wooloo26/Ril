//! A numeric conversion instance is selected by the actual Generic expression
//! and its original Type headers, not by its private runtime builtin spelling.
use super::*;
use ril_compiler_core::numeric_builtins::NumericBuiltin;

impl Checker {
    pub(super) fn numeric_static_callee_source(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
    ) -> InputSource {
        let ExprKind::Generic { base, arguments } = &syntax.kind else {
            return Ok(None);
        };
        let context = self.invocation_context(frame.callable_owner);
        let root = self.source_projection_occurrence(
            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
            value,
            context,
            work,
        )?;
        let observation = self.source_projection_receipts().child_observation(
            root,
            base.hir_id.ok_or(SourceTypesError::MissingNode)?,
            work,
        )?;
        let actual = self
            .application_effect
            .expressions
            .get(observation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if !matches!(actual.value.callables.as_slice(), [Callable::Builtin(name)] if name == NumericBuiltin::Convert.name())
        {
            return Ok(None);
        }
        if self.numeric_builtin_observation(observation.0 as usize, context, work)?
            != Some(NumericBuiltin::Convert)
            || arguments.len() != 2
        {
            return Err(SourceTypesError::Unresolved);
        }
        let environment = self.capture_typing_environment();
        let (source, source_environment) = self
            .input_original_header_schema(&arguments[0], environment.clone(), work)?
            .ok_or(SourceTypesError::MissingNode)?;
        let (destination, destination_environment) = self
            .input_original_header_schema(&arguments[1], environment.clone(), work)?
            .ok_or(SourceTypesError::MissingNode)?;
        if source_environment.is_poisoned() || destination_environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let Some((schema, from, to)) =
            crate::sema::source_types::numeric::conversion(&source, &destination, work)?
        else {
            return Err(SourceTypesError::Unresolved);
        };
        let identity = format!("Num::__convert_{}_to_{}", from.name(), to.name());
        work.text(&identity)?;
        if !matches!(value.callables.as_slice(), [Callable::Builtin(name)] if name == &identity) {
            return Err(SourceTypesError::Unresolved);
        }
        // scalar_representation proved both types' transparent closed shape;
        // no caller lexical interpretation is imported into this declaration.
        Ok(Some((schema, environment)))
    }
}
