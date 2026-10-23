//! Scope callback inputs belong to the physical application that creates them.
use super::*;
use crate::sema::application_effect::{EntryOrigin, InputOrigin, ScopeInput};
use crate::sema::source_types::SourceTypesError;
use std::sync::Arc;

impl Checker {
    pub(super) fn scope_callback_entry(
        &mut self,
        node: NodeId,
        cause: CauseId,
        frame: &Frame,
    ) -> Result<(Arc<EvaluatedValue>, EntryOrigin), SourceTypesError> {
        let mut lease = self.application_effect.lease_work(32768);
        let selected = (|| {
            let work = lease.work();
            work.charge(5 + self.call_arguments.len())?;
            let anchor = self
                .application_effect
                .current_activation()
                .ok_or(SourceTypesError::MissingNode)?;
            let application = self
                .application_effect
                .current_call_event()
                .ok_or(SourceTypesError::MissingNode)?;
            let mut rows = self
                .call_arguments
                .iter()
                .filter(|row| row.source_event == application);
            let row = rows.next().ok_or(SourceTypesError::MissingNode)?;
            if rows.next().is_some() || !row.evaluation_complete {
                return Err(SourceTypesError::Unresolved);
            }
            let callee = row
                .supplied
                .get(&0)
                .ok_or(SourceTypesError::MissingNode)?
                .expression;
            let record = self
                .application_effect
                .evaluations
                .get(callee)
                .ok_or(SourceTypesError::MissingNode)?;
            if record.context != self.invocation_context(frame.callable_owner) {
                return Err(SourceTypesError::Unresolved);
            }
            let index = self
                .concurrent_boundaries
                .len()
                .checked_sub(1)
                .ok_or(SourceTypesError::MissingNode)?;
            let index = u32::try_from(index).map_err(|_| SourceTypesError::IdentityExhausted)?;
            let callee_id = u32::try_from(callee)
                .map(ril_compiler_core::ids::EvaluationOccurrenceId)
                .map_err(|_| SourceTypesError::IdentityExhausted)?;
            Ok((
                callee,
                EntryOrigin::Generated {
                    anchor,
                    callee: callee_id,
                    inputs: vec![InputOrigin::Scope(index)],
                },
                index,
                ScopeInput {
                    application,
                    anchor,
                    node,
                    cause,
                    allocation_epoch: self.recency_moves.len(),
                },
            ))
        })();
        let returned = self.application_effect.return_work(lease);
        let (callee, origin, index, input) = selected?;
        returned?;
        let callee = self.application_effect.packet_at(callee)?;
        self.concurrent_boundaries[index as usize].input = Some(input);
        Ok((callee, origin))
    }
}
