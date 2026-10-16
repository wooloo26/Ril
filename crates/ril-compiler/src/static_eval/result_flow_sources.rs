//! Type metadata follows this proof's lexical values. Actual evaluation does
//! not supply argument tags, inspections, or an unknown member graph.
use super::*;
use crate::sema::model::SourceTypeWitness;

impl<'a> Engine<'a> {
    pub(super) fn metadata_typer(&self, state: &State) -> Typer<'a> {
        let mut typer =
            Typer::with_bound_environment(self.evaluator, None, state.bound_scope.clone());
        typer.function_contexts = self.contexts.clone();
        // None is a lexical tombstone. A local unknown must never fall back to
        // an unrelated same-spelled global's complete schema.
        typer.schema_bindings.borrow_mut().extend(
            state
                .env
                .iter()
                .map(|(name, value)| (name.clone(), value.source_type.clone())),
        );
        typer
    }

    pub(super) fn expression_source(
        &self,
        expression: &Expr,
        value: &Value,
        state: &State,
        context: Option<&ResultContext>,
    ) -> std::result::Result<Option<Arc<SourceTypeWitness>>, Problem> {
        if let Some(witness) = &value.source_type {
            return Ok(Some(witness.clone()));
        }
        at(
            self.metadata_typer(state)
                .expression_source_schema_expected(
                    expression,
                    &value.ty,
                    &Self::types(state),
                    &state.bound_scope,
                    context,
                    0,
                ),
            expression.span,
        )
    }

    fn annotated_source(
        &self,
        syntax: &TypeExpr,
        state: &State,
    ) -> std::result::Result<Option<Arc<SourceTypeWitness>>, Problem> {
        at(
            self.metadata_typer(state)
                .complete_source_syntax(syntax, &state.bound_scope),
            syntax.span,
        )
    }

    pub(super) fn receive_annotation(
        &self,
        value: Value,
        syntax: &TypeExpr,
        state: &State,
    ) -> std::result::Result<Value, Problem> {
        let typer = self.metadata_typer(state);
        let expected = at(typer.ty(syntax, &Self::types(state)), syntax.span)?;
        let expected = at(
            typer.receive_type_interfaces(value.ty.clone(), syntax, &expected, &state.bound_scope),
            syntax.span,
        )?;
        let mask = at(
            generic_receiving::for_types(
                syntax,
                &state.bound_scope.type_binders,
                &self.evaluator.declarations,
                self.evaluator.layout,
                &self.evaluator.budget,
            ),
            syntax.span,
        )?;
        let mask = mask.as_ref().map(|mask| (&mask.syntax, &mask.markers));
        let source = self
            .annotated_source(syntax, state)?
            .map(|source| receiving::received_source(&value, source, mask, syntax.span))
            .transpose()?;
        let mut value = value.receive_type(&expected, mask, syntax.span)?;
        value.source_type = source;
        Ok(value)
    }
}
