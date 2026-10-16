//! Record assignment observations without turning a type view into authority.
use super::*;
use crate::sema::bound_writes::{BoundFieldWrite, ObservedAccess, ObservedAccessId};

pub(super) struct ObservedStore<'a> {
    pub projection_index: usize,
    pub rhs_expression: Option<usize>,
    pub receiver_expression: Option<usize>,
    pub access: ObservedAccessId,
    pub operator: &'a str,
    pub replacement: &'a Value,
    pub receiver: &'a Value,
    pub span: Span,
}

impl Checker {
    pub(super) fn bound_write_access(
        &mut self,
        value: &Value,
        slot: Slot,
        span: Span,
        frame: &mut Frame,
    ) -> ObservedAccessId {
        self.access(value, Some(slot), Mode::Write, span, frame);
        let id = ObservedAccessId(self.observed_accesses.len() as u32);
        self.observed_accesses.push(ObservedAccess {
            id,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            // access always appends exactly one observation. Keep the historical
            // loan participants and original epoch before summary normalization.
            access: frame.obligations.accesses.last().unwrap().clone(),
        });
        id
    }

    pub(super) fn record_bound_field_write(&mut self, write: ObservedStore<'_>) {
        let ObservedStore {
            projection_index,
            rhs_expression,
            receiver_expression,
            access,
            operator,
            replacement,
            receiver,
            span,
        } = write;
        let (Some(rhs_expression), Some(receiver_expression)) =
            (rhs_expression, receiver_expression)
        else {
            self.unsupported(
                span,
                "bounded assignment has no actual expression observations",
            );
            return;
        };
        let projection = &self.generic_bound_projections[projection_index];
        self.bound_field_writes.push(BoundFieldWrite {
            projection_index,
            rhs_expression,
            receiver_expression,
            access,
            operator: operator.to_owned(),
            replacement: self.copy_value_snapshot(replacement),
            updated_receiver: self.copy_value_snapshot(receiver),
            cause: projection.cause,
            span,
        });
    }
}
