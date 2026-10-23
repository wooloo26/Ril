//! Checker admission and diagnostics for the shared evaluated packet.
use super::*;
use crate::sema::{
    evaluated::EvaluatedValue,
    numeric_selection::NumericBirth,
    source_types::{SourceTypesError, WorkLimit},
};
use ril_compiler_core::ids::NumericHoleId;

impl Checker {
    pub(super) fn pending_numeric_packet_birth(
        &self,
        packet: &EvaluatedValue,
        hole: NumericHoleId,
        work: &mut WorkLimit,
    ) -> Result<NumericBirth, SourceTypesError> {
        work.charge(5)?;
        let observation = packet.observation.ok_or(SourceTypesError::MissingNode)?;
        let actual = self
            .application_effect
            .expressions
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let numeric = self
            .numeric
            .holes
            .get(hole.0 as usize)
            .filter(|record| record.id == hole)
            .ok_or(SourceTypesError::MissingNode)?;
        let activation = self
            .application_effect
            .activations
            .get(numeric.birth.occurrence.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let origin = activation.result.ok_or(SourceTypesError::MissingNode)?;
        let origin_record = self
            .application_effect
            .evaluations
            .get(origin.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let original = self
            .application_effect
            .expressions
            .get(origin.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        work.charge(original.value.numeric.uses.len() + actual.value.numeric.uses.len())?;
        if actual.value.ty != Ty::NumericHole(hole)
            || packet.value.ty != actual.value.ty
            || actual.source_id != packet.identity.map(|identity| identity.source)
            || activation.source != Some(numeric.birth.occurrence.source)
            || activation.kind != crate::sema::application_effect::ActivationKind::Expression
            || activation.scope != numeric.birth.scope
            || activation.context != numeric.birth.context
            || origin_record.identity != Some(numeric.birth.occurrence)
            || origin_record.scope != numeric.birth.scope
            || origin_record.context != numeric.birth.context
            || origin_record.allocation_epoch != numeric.birth.allocation_epoch
            || original.value.ty != Ty::NumericHole(hole)
            || numeric.birth.allocation_epoch > packet.allocation_epoch
            || original.value.numeric.uses != actual.value.numeric.uses
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(numeric.birth)
    }

    pub(super) fn select_numeric_packet(
        &mut self,
        packet: &mut EvaluatedValue,
        expected: &Ty,
        span: Span,
    ) -> Result<(), SourceTypesError> {
        self.prepare_evaluation_packet(packet, span)?;
        if matches!(packet.value.ty, Ty::NumericHole(_)) {
            let moves = &self.recency_moves;
            let unchanged = self.application_effect.with_evaluation_work(
                |expressions, evaluations, activations, work| {
                    *work = work
                        .checked_sub(5)
                        .ok_or(SourceTypesError::BudgetExceeded)?;
                    let observation = packet.observation.ok_or(SourceTypesError::MissingNode)?;
                    let fact = expressions
                        .get(observation)
                        .ok_or(SourceTypesError::MissingNode)?;
                    let record = evaluations
                        .get(observation)
                        .ok_or(SourceTypesError::MissingNode)?;
                    let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
                    let activation = activations
                        .get(identity.activation.0 as usize)
                        .ok_or(SourceTypesError::MissingNode)?;
                    if record.id.0 as usize != observation
                        || record.identity != packet.identity
                        || Some(record.context) != packet.birth_context
                        || record.allocation_epoch != packet.allocation_epoch
                        || fact.source_id != Some(identity.source)
                        || fact.allocation_epoch != record.allocation_epoch
                        || activation.id != identity.activation
                        || activation.source != Some(identity.source)
                        || activation.scope != record.scope
                        || activation.context != record.context
                        || activation.kind
                            != crate::sema::application_effect::ActivationKind::Expression
                        || activation.result != Some(record.id)
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    if crate::sema::evaluated::same_transported_birth(
                        &fact.value,
                        record.allocation_epoch,
                        &packet.value,
                        moves.len(),
                        moves,
                        work,
                    )? {
                        Ok(())
                    } else {
                        Err(SourceTypesError::Unresolved)
                    }
                },
            );
            if let Err(error) = unchanged {
                packet.fail_current_source(error.clone());
                self.unsupported(
                    span,
                    format!("numeric admission changed its complete birth value: {error}"),
                );
                return Err(error);
            }
        }
        let hole = match self.commit_numeric_value(&mut packet.value, expected) {
            Ok(Some(hole)) => hole,
            Ok(None) => return Ok(()),
            Err(error) => {
                packet.fail_current_source(error.clone());
                return Err(error);
            }
        };
        if !self.application_effect.admit(1) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let resolution = self.numeric.resolution(hole)?.clone();
        let types = self.type_source.storage.live_types_mut();
        let result = self
            .application_effect
            .with_work(|work| packet.apply_numeric_resolution(hole, resolution, types, work));
        if let Err(error) = &result {
            packet.fail_current_source(error.clone());
            self.unsupported(
                span,
                format!("numeric packet Source derivation failed: {error}"),
            );
        }
        result
    }

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
