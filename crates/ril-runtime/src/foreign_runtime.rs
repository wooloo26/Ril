//! Task-owned foreign invocations. Only immutable binding descriptions cross
//! task creation; managed callback tokens remain with their logical owner while
//! a live Session moves exclusively into that owner's outstanding host request.
use crate::{
    foreign_process::{Request, Session},
    heap::Handle,
};
use ril_runtime_api::foreign::{BoundCall, CallbackToken, RequestId};
use std::{collections::BTreeMap, sync::Arc};

pub(crate) struct Invocation {
    pub binding: Arc<BoundCall>,
    pub transport: Transport,
    pub next_ticket: u64,
    pub cancellation: Arc<crate::process_io::Cancellation>,
    pub arguments: Handle,
    pub continuation: Handle,
    pub handlers: Handle,
    pub activation: Handle,
    pub callbacks: BTreeMap<CallbackToken, (Handle, usize)>,
    pub next_request: RequestId,
    pub pending_request: Option<(RequestId, usize)>,
}

/// The only owner of a live transport is either this invocation or its one
/// outstanding host job. A missing session never means permission to restart.
pub(crate) enum Transport {
    Ready { ticket: u64, request: Box<Request> },
    Waiting { ticket: u64 },
    Callback(Session),
    Closing { ticket: u64 },
    Closed,
}
impl std::fmt::Debug for Invocation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ForeignInvocation")
            .field("declaration", &self.binding.declaration)
            .field("activation", &self.activation)
            .field("pending_request", &self.pending_request)
            .finish_non_exhaustive()
    }
}
impl Invocation {
    pub(crate) fn references(&self) -> Vec<Handle> {
        [
            self.arguments,
            self.continuation,
            self.handlers,
            self.activation,
        ]
        .into_iter()
        .chain(self.callbacks.values().map(|(value, _)| *value))
        .filter(|&value| value != Handle::INVALID)
        .collect()
    }
}
