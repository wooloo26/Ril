//! Optional presence selects a path without inspecting any nested Result.
//! The selected payload retains its original producer and callable descriptors.
use super::*;

impl Engine<'_> {
    pub(super) fn optional_fallback(
        &mut self,
        left: &Expr,
        right: &Expr,
        state: State,
        span: Span,
        context: Option<&ResultContext>,
    ) -> Paths {
        let mut output = Vec::new();
        let left_context = context
            .map(|context| {
                at(
                    self.metadata_typer(&state).optional_result_context(context),
                    left.span,
                )
            })
            .transpose()?;
        for path in self.expr_expected(left, state, left_context.as_ref())? {
            if path.exit != Exit::Normal {
                output.push(path);
                continue;
            }
            let payload_context = if let Some(context) = context {
                Some(context.clone())
            } else {
                // A proved source interface may supply the payload's written
                // type even for an unannotated `optional ?? fallback`. Never
                // construct that interface from a concrete payload or tag.
                let source_context = self.annotation_context(
                    path.value.source_type.as_ref().map(|source| &source.syntax),
                    &path.state,
                )?;
                self.project_context(
                    source_context.as_ref(),
                    applications::ResultProjection::OptionalPayload,
                    &path.state,
                    left.span,
                )?
            };
            let Shape::Optional {
                tag,
                choice,
                payload,
            } = path.value.shape
            else {
                return Err(incomplete(
                    span,
                    "static Result fallback handler needs its explicit error-consumption proof",
                ));
            };
            let known = choice
                .and_then(|id| path.state.booleans.get(&id).copied())
                .or(tag);
            if known.is_none() && choice.is_none() {
                return Err(incomplete(
                    span,
                    "static Optional fallback has no immutable presence identity",
                ));
            }
            if known != Some(false) {
                let mut present = path.state.clone();
                if let Some(id) = choice {
                    present.booleans.insert(id, true);
                }
                // Moving the immutable payload descriptor makes no new
                // producer and changes no existing inspection obligation.
                output.push(Path::normal(present, payload.as_ref().clone()));
            }
            if known != Some(true) {
                let mut absent = path.state;
                if let Some(id) = choice {
                    absent.booleans.insert(id, false);
                }
                output.extend(self.expr_expected(right, absent, payload_context.as_ref())?);
            }
        }
        Ok(output)
    }
}
