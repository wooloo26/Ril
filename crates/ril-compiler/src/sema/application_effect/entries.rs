//! Immutable callable inputs. Generated calls retain their actual value
//! derivations instead of borrowing an enclosing written application's slots.
use crate::sema::{
    copy_contract::{CopyBoundaryId, CopyCallEventId, CopyHeapSnapshot, CopyValueView},
    evaluated::EvaluatedValue,
    model::Value,
    source_types::{SourceTypesError, WorkLimit},
};
use ril_compiler_core::{
    ids::{ActivationEpochId, EvaluationOccurrenceId},
    source::Span,
};
use ril_syntax::ast::ParameterMode;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct EntryArgument {
    pub mode: ParameterMode,
    pub packet: Arc<EvaluatedValue>,
    pub span: Span,
    pub heap: Option<Arc<CopyHeapSnapshot>>,
}

impl EntryArgument {
    pub fn value(&self) -> &Value {
        self.packet.value()
    }

    pub(crate) fn snapshot_view(
        &self,
        work: &mut WorkLimit,
    ) -> Result<CopyValueView<'_>, SourceTypesError> {
        work.charge(1)?;
        let heap = self.heap.as_deref().ok_or(SourceTypesError::MissingNode)?;
        if self.packet.current_epoch() != heap.allocation_epoch {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(CopyValueView {
            value: self.packet.value(),
            nodes: &heap.nodes,
            relations: &heap.relations,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputOrigin {
    Scope(u32),
    Observed(EvaluationOccurrenceId),
    Widened(EvaluationOccurrenceId),
    Scalar(ScalarInput),
    Copied {
        observation: EvaluationOccurrenceId,
        boundary: CopyBoundaryId,
    },
}

/// Historical coordinates of the scope token created by one physical
/// Concurrent::scope application. Recency transport never rewrites this birth.
#[derive(Debug, Clone)]
pub struct ScopeInput {
    pub application: CopyCallEventId,
    pub anchor: ActivationEpochId,
    pub node: crate::sema::facts::NodeId,
    pub cause: ril_compiler_core::diagnostic::CauseId,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarInput {
    PositiveInt,
    ByteSuffix(EvaluationOccurrenceId),
    BufferedBytes(EvaluationOccurrenceId),
}

pub(crate) struct RecordCallback {
    pub receiver: u32,
    pub operations: u32,
    pub field: &'static str,
    pub scalar_source: ScalarSource,
}
pub(crate) enum ScalarSource {
    PositiveInt,
    ByteSuffix(u32),
    BufferedBytes(u32),
}
pub(crate) fn record_callback(name: &str) -> Option<RecordCallback> {
    Some(match name {
        "Io::read_all" => RecordCallback {
            receiver: 0,
            operations: 1,
            field: "read",
            scalar_source: ScalarSource::PositiveInt,
        },
        "Io::write_all" => RecordCallback {
            receiver: 0,
            operations: 2,
            field: "write",
            scalar_source: ScalarSource::ByteSuffix(1),
        },
        "Io::read_buffered" => RecordCallback {
            receiver: 1,
            operations: 2,
            field: "read",
            scalar_source: ScalarSource::PositiveInt,
        },
        "Io::write_buffered" | "Io::flush" | "Io::close_write_buffer" => RecordCallback {
            receiver: 1,
            operations: 2,
            field: "write",
            scalar_source: ScalarSource::BufferedBytes(0),
        },
        _ => return None,
    })
}

/// A physical field operand of a record construction, without synthesizing
/// another evaluation of that construction or guessing by source position.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryOrigin {
    Application(CopyCallEventId),
    Generated {
        anchor: ActivationEpochId,
        callee: EvaluationOccurrenceId,
        inputs: Vec<InputOrigin>,
    },
    DeclarationProbe,
    SignatureProbe(Arc<super::SignatureProbeSource>),
    /// No written application or exact generated origin. Receiving still
    /// requires the complete types carried by the actual argument packets.
    Unresolved,
}

#[derive(Debug, Clone)]
pub struct CallableEntry {
    pub parent: Option<ActivationEpochId>,
    pub caller_context: super::InvocationContext,
    pub origin: EntryOrigin,
    pub allocation_epoch: usize,
    pub callee: Option<Arc<EvaluatedValue>>,
    /// The original argument vector is moved into shared immutable storage;
    /// entry recording never recursively clones the values or their syntax.
    pub arguments: Arc<Vec<EntryArgument>>,
}

impl super::ApplicationEffectDomain {
    pub(crate) fn snapshot_origin(&mut self, origin: &EntryOrigin) -> Option<EntryOrigin> {
        let cost = match origin {
            EntryOrigin::Generated { inputs, .. } => inputs.len() + 1,
            EntryOrigin::SignatureProbe(_) => 1,
            _ => 0,
        };
        self.admit(cost).then(|| origin.clone())
    }
}
