//! Checker admission and diagnostics for the shared evaluated packet.
use super::*;
use crate::sema::{evaluated::EvaluatedValue, source_types::SourceTypesError};

impl Checker {
    pub(super) fn read_evaluation_packet(
        &mut self,
        packet: &EvaluatedValue,
        work_span: Span,
    ) -> Result<Value, SourceTypesError> {
        let moves = &self.recency_moves;
        let result = self
            .application_effect
            .with_work(|work| packet.current_read(moves, work));
        if let Err(error) = &result {
            self.unsupported(
                work_span,
                format!("evaluation packet read admission: {error}"),
            );
        }
        result
    }
    pub(super) fn transport_evaluation_packet(&mut self, packet: &mut EvaluatedValue, span: Span) {
        let moves = &self.recency_moves;
        if let Err(error) = self
            .application_effect
            .with_work(|work| packet.transport_checked(moves, work))
        {
            self.unsupported(span, format!("evaluation packet epoch transport: {error}"));
            packet.fail_current_source(error);
            // Keep the original untransported graph and duties inspectable;
            // the failed Source/receiver state prevents their certification.
            packet.value.ty = Ty::Unknown;
        }
    }

    pub(super) fn clone_evaluation_packet(
        &mut self,
        packet: &EvaluatedValue,
        span: Span,
    ) -> Result<EvaluatedValue, SourceTypesError> {
        let result = self
            .application_effect
            .with_work(|work| packet.try_clone(work));
        if let Err(error) = &result {
            self.unsupported(span, format!("evaluation packet clone admission: {error}"));
        }
        result
    }
}
