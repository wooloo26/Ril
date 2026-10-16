//! Task-owned exit work survives native steps without retaining a Rust stack.
//! A pending cleanup owns its masks, original outcome and precise graph roots.
use crate::{budget::CleanupMask, heap::Handle, value::RuntimeError};

#[derive(Debug, Clone)]
pub(crate) enum Work {
    Scope {
        activation: Handle,
        marker: u32,
    },
    Close(Handle),
    Closed {
        activation: Handle,
        parent: Handle,
    },
    Unwind(Handle),
    /// Retire a faulted dynamic region, including arms created by its cleanup.
    Region {
        target: Handle,
        scopes: Vec<Handle>,
    },
    Cross {
        target: Handle,
        scopes: Vec<Handle>,
        base: usize,
        aborted: bool,
    },
    FinishCross {
        delimiter: Handle,
        checkpoint: Handle,
    },
    BeginAbort,
    EndAbort,
    RequireSuccess,
    Budgets(usize),
}
#[derive(Debug, Clone)]
pub(crate) struct Waiting {
    pub resource: Handle,
    pub activation: Handle,
    pub handlers: Handle,
    pub concurrent_depth: usize,
    pub delimiters: Vec<Handle>,
    pub budget_depth: usize,
}
#[derive(Debug)]
pub(crate) enum After {
    DelimiterAnswer {
        delimiter: Handle,
        outer: Handle,
        handlers: Handle,
        checkpoint: Handle,
    },
    Return {
        continuation: Handle,
        handlers: Option<Handle>,
        activation: Option<Handle>,
    },
    Native {
        function: u64,
        environment: Handle,
        handlers: Handle,
    },
    Stop,
    Complete,
    RecoverScope {
        scope: Option<Handle>,
        minimum_depth: usize,
    },
    Budget {
        boundary: Handle,
        state: Box<crate::cps::BudgetBoundary>,
        aborted: bool,
    },
    CallbackComplete {
        owner: u64,
        waiting: Waiting,
    },
}
#[derive(Debug)]
pub(crate) struct Frame {
    pub id: u64,
    /// A nonlocal exit has taken over this frame's remaining cleanup work.
    pub abandoned: bool,
    /// Last entry executes first, including dynamically expanded unwind work.
    pub work: Vec<Work>,
    pub scope: Option<(Handle, u32)>,
    pub waiting: Option<Waiting>,
    pub after: After,
    pub value: Handle,
    pub primary: Option<RuntimeError>,
    pub allowances: CleanupMask,
    pub cancellation_mask: u32,
}
impl Waiting {
    fn references(&self) -> impl Iterator<Item = Handle> + '_ {
        [self.resource, self.activation, self.handlers]
            .into_iter()
            .chain(self.delimiters.iter().copied())
    }
}
impl Frame {
    pub(crate) fn references(&self) -> Vec<Handle> {
        let mut roots = vec![self.value];
        for work in &self.work {
            match work {
                Work::Scope { activation, .. }
                | Work::Close(activation)
                | Work::Unwind(activation) => roots.push(*activation),
                Work::Closed { activation, parent } => roots.extend([*activation, *parent]),
                Work::Cross { target, scopes, .. } | Work::Region { target, scopes } => {
                    roots.push(*target);
                    roots.extend(scopes);
                }
                Work::FinishCross {
                    delimiter,
                    checkpoint,
                } => roots.extend([*delimiter, *checkpoint]),
                Work::BeginAbort | Work::EndAbort | Work::RequireSuccess | Work::Budgets(_) => {}
            }
        }
        if let Some((activation, _)) = self.scope {
            roots.push(activation);
        }
        if let Some(waiting) = &self.waiting {
            roots.extend(waiting.references());
        }
        match &self.after {
            After::DelimiterAnswer {
                delimiter,
                outer,
                handlers,
                checkpoint,
            } => roots.extend([*delimiter, *outer, *handlers, *checkpoint]),
            After::Return {
                continuation,
                handlers,
                activation,
            } => {
                roots.push(*continuation);
                roots.extend(*handlers);
                roots.extend(*activation);
            }
            After::Native {
                environment,
                handlers,
                ..
            } => roots.extend([*environment, *handlers]),
            After::Stop | After::Complete => {}
            After::RecoverScope { scope, .. } => roots.extend(*scope),
            After::Budget {
                boundary, state, ..
            } => {
                roots.push(*boundary);
                roots.extend(state.references());
            }
            After::CallbackComplete { waiting, .. } => roots.extend(waiting.references()),
        }
        roots.retain(|root| *root != Handle::INVALID);
        roots
    }
}
