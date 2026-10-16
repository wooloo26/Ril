//! Const scalar roles are separate from ordinary bindings and Result custody.
use super::*;

impl Engine<'_> {
    pub(super) fn seed_const_bindings(
        &self,
        state: &mut State,
        span: Span,
    ) -> std::result::Result<(), Problem> {
        let views = at(
            Self::typer(self.evaluator, state).const_binding_views(&state.bound_scope),
            span,
        )?;
        for view in views {
            // This receives a selected const scalar, never an observed runtime
            // parameter, array cardinality or Result payload. Universal own
            // binders have no closed value in their declaration environment.
            if let Some(value) = view.closed {
                let bits = self.evaluator.layout.pointer_bits;
                if !matches!(bits, 32 | 64)
                    || value < -(1i128 << (bits - 1))
                    || value >= (1i128 << (bits - 1))
                {
                    return Err(incomplete(
                        span,
                        &format!(
                            "static const {} has no target-int scalar witness",
                            view.id.key()
                        ),
                    ));
                }
            }
            state.env.insert(
                view.name,
                Value {
                    source_type: None,
                    ty: Ty::Number("int".into()),
                    shape: view.closed.map_or(Shape::Plain, Shape::Integer),
                },
            );
        }
        Ok(())
    }

    pub(super) fn mask_const_bindings(
        &self,
        state: &mut State,
        names: &BTreeSet<String>,
        span: Span,
    ) -> std::result::Result<(), Problem> {
        let typer = Self::typer(self.evaluator, state);
        if typer.has_visible_const(&state.bound_scope, names) {
            at(
                typer.mask_const_values(Arc::make_mut(&mut state.bound_scope), names),
                span,
            )?;
        }
        Ok(())
    }
}
