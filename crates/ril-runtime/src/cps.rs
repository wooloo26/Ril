//! GC-traced control data for native continuation steps. No Ril syntax or IR
//! is interpreted here; executable continuations contain native entry addresses.
use crate::heap::Handle;
use std::collections::BTreeMap;
#[derive(Debug, Clone, PartialEq)]
pub enum Continuation {
    End,
    Cleanup {
        owner: u64,
    },
    Native {
        function: u64,
        environment: Handle,
        handlers: Handle,
        activation: Handle,
        delimiters: Vec<Handle>,
        budget_depth: usize,
    },
    Delimiter {
        outer: Handle,
        handlers: Handle,
        activation: Handle,
        resumptions: Vec<Handle>,
        budget_depth: usize,
    },
    FinishArm {
        activation: Handle,
        delimiter: Handle,
    },
    BudgetFinish {
        boundary: Handle,
    },
    ConcurrentFinish {
        scope: Handle,
    },
    IoBuffered(Box<crate::io_buffered::Invocation>),
    ForeignCallback {
        call: u64,
        request: u64,
    },
}
impl Continuation {
    pub fn references(&self) -> Vec<Handle> {
        match self {
            Self::End | Self::Cleanup { .. } => vec![],
            Self::Native {
                environment,
                handlers,
                activation,
                delimiters,
                ..
            } => std::iter::once(*environment)
                .chain([*handlers, *activation])
                .chain(delimiters.iter().copied())
                .collect(),
            Self::Delimiter {
                outer,
                handlers,
                activation,
                resumptions,
                ..
            } => std::iter::once(*outer)
                .chain([*handlers, *activation])
                .chain(resumptions.iter().copied())
                .collect(),
            Self::FinishArm {
                activation,
                delimiter,
            } => vec![*activation, *delimiter],
            Self::BudgetFinish { boundary } => vec![*boundary],
            Self::ConcurrentFinish { scope } => vec![*scope],
            Self::IoBuffered(invocation) => invocation.references(),
            Self::ForeignCallback { .. } => vec![],
        }
        .into_iter()
        .filter(|&handle| handle != Handle::INVALID)
        .collect()
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct HandlerFrame {
    pub definition: u64,
    pub table: Handle,
    pub parent: Handle,
    pub delimiter: Handle,
}
#[derive(Debug, Clone, PartialEq)]
pub struct HandlerRecipe {
    pub definition: u64,
    pub arms: HandlerTable,
}
#[derive(Debug, Clone, PartialEq)]
pub struct Resumption {
    pub non_resumable: bool,
    pub continuation: Handle,
    pub handlers: Handle,
    pub used: bool,
    pub delimiter: Handle,
    pub activation: Handle,
}
#[derive(Debug, Clone, PartialEq)]
pub struct BudgetHandler {
    pub frame: Handle,
    pub arm: Handle,
    pub parent: Handle,
    pub delimiter: Handle,
}
#[derive(Debug, Clone, PartialEq)]
pub struct BudgetBoundary {
    pub id: Option<crate::budget::BudgetId>,
    pub active: bool,
    pub continuation: Handle,
    pub operation: u64,
    pub handlers: Handle,
    pub activation: Handle,
    pub delimiters: Vec<Handle>,
    pub selection: Option<BudgetHandler>,
}
impl BudgetBoundary {
    pub fn references(&self) -> Vec<Handle> {
        let mut roots = vec![self.continuation, self.handlers, self.activation];
        roots.extend(self.delimiters.iter().copied());
        if let Some(selected) = &self.selection {
            roots.extend([
                selected.frame,
                selected.arm,
                selected.parent,
                selected.delimiter,
            ]);
        }
        roots.retain(|handle| *handle != Handle::INVALID);
        roots
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct Activation {
    pub parent: Handle,
    /// The dynamic handler extent in which this frame's cleanup is registered.
    pub handlers: Handle,
    pub cleanups: Vec<Handle>,
    pub closed: bool,
}
#[derive(Debug, Clone, PartialEq)]
pub enum Step {
    Foreign {
        call: u64,
    },
    ForeignClose {
        owner: u64,
        activation: Handle,
    },
    Complete {
        value: Handle,
    },
    Exit {
        owner: u64,
    },
    HostCleanup {
        owner: u64,
    },
    ConcurrentDrain {
        scope: Handle,
        body: Option<Handle>,
    },
    ConcurrentClose {
        scope: Handle,
        activation: Handle,
        owner: u64,
    },
    Budget {
        limit: Handle,
        action: Handle,
        continuation: Handle,
        operation: u64,
        handlers: Handle,
        activation: Handle,
        delimiters: Vec<Handle>,
    },
    Charge {
        event: ril_runtime_api::abi::BudgetEvent,
        next: Handle,
    },
    BudgetExhaust {
        boundary: Handle,
        abandoned: Vec<Handle>,
    },
    Call {
        callable: Handle,
        arguments: Handle,
        continuation: Handle,
        handlers: Handle,
        /// A library-specified callback invocation, including a budget action.
        callback_entry: bool,
    },
    Return {
        continuation: Handle,
        value: Handle,
    },
    Perform {
        operation: u64,
        arguments: Handle,
        continuation: Handle,
        handlers: Handle,
    },
    Handle {
        definition: u64,
        body: Handle,
        table: Handle,
        continuation: Handle,
        handlers: Handle,
    },
    Resume {
        resumption: Handle,
        value: Handle,
        next: Option<Handle>,
    },
}
impl Step {
    pub fn references(&self) -> Vec<Handle> {
        match self {
            Self::Foreign { .. } => vec![],
            Self::ForeignClose { activation, .. } => vec![*activation],
            Self::Complete { value } => vec![*value],
            Self::Exit { .. } | Self::HostCleanup { .. } => vec![],
            Self::ConcurrentDrain { scope, body } => std::iter::once(*scope).chain(*body).collect(),
            Self::ConcurrentClose {
                scope, activation, ..
            } => vec![*scope, *activation],
            Self::Budget {
                limit,
                action,
                continuation,
                handlers,
                activation,
                delimiters,
                ..
            } => vec![*limit, *action, *continuation, *handlers, *activation]
                .into_iter()
                .chain(delimiters.iter().copied())
                .collect(),
            Self::Charge { next, .. } => vec![*next],
            Self::BudgetExhaust {
                boundary,
                abandoned,
            } => std::iter::once(*boundary)
                .chain(abandoned.iter().copied())
                .collect(),
            Self::Call {
                callable,
                arguments,
                continuation,
                handlers,
                ..
            } => vec![*callable, *arguments, *continuation, *handlers],
            Self::Return {
                continuation,
                value,
            } => vec![*continuation, *value],
            Self::Perform {
                arguments,
                continuation,
                handlers,
                ..
            } => vec![*arguments, *continuation, *handlers],
            Self::Handle {
                body,
                table,
                continuation,
                handlers,
                ..
            } => vec![*body, *table, *continuation, *handlers],
            Self::Resume {
                resumption,
                value,
                next,
            } => [Some(*resumption), Some(*value), *next]
                .into_iter()
                .flatten()
                .collect(),
        }
        .into_iter()
        .filter(|&handle| handle != Handle::INVALID)
        .collect()
    }
}
pub type HandlerTable = BTreeMap<u64, Handle>;
