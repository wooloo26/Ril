//! Independent parallel jobs. Completion never cancels another invocation, and
//! every result remains traced until the caller has selected its outcome.
use crate::{
    heap::Handle,
    value::{Result, RuntimeError},
};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
};

#[derive(Debug, Clone)]
pub(crate) enum Job {
    Call {
        callable: Handle,
        arguments: Vec<Handle>,
    },
    Merge {
        callable: Handle,
        arguments: Vec<Handle>,
    },
    Fold {
        init: Handle,
        local: Handle,
        items: Vec<Handle>,
        start: usize,
    },
}

impl Job {
    fn references(&self) -> Vec<Handle> {
        match self {
            Self::Call {
                callable,
                arguments,
            }
            | Self::Merge {
                callable,
                arguments,
            } => std::iter::once(*callable)
                .chain(arguments.iter().copied())
                .collect(),
            Self::Fold {
                init, local, items, ..
            } => [*init, *local]
                .into_iter()
                .chain(items.iter().copied())
                .collect(),
        }
    }
}

#[derive(Debug)]
pub struct Group {
    jobs: Vec<Job>,
    next: AtomicUsize,
    outcomes: Mutex<Vec<Option<Result<Handle>>>>,
}

impl PartialEq for Group {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Group {
    pub(crate) fn new(jobs: Vec<Job>) -> Arc<Self> {
        Arc::new(Self {
            outcomes: Mutex::new(vec![None; jobs.len()]),
            jobs,
            next: AtomicUsize::new(0),
        })
    }
    pub(crate) fn claim(&self) -> Option<(usize, Job)> {
        let index = self.next.fetch_add(1, Ordering::Relaxed);
        self.jobs.get(index).cloned().map(|job| (index, job))
    }
    /// Publish only while holding the shared managed heap gate. This overlaps
    /// the worker's result root with the group root, including worker retirement.
    pub(crate) fn complete(&self, index: usize, outcome: Result<Handle>) {
        self.outcomes
            .lock()
            .unwrap_or_else(|error| error.into_inner())[index] = Some(outcome);
    }
    pub(crate) fn outcomes(&self) -> Result<Vec<Result<Handle>>> {
        self.outcomes
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .iter()
            .cloned()
            .map(|outcome| {
                outcome.ok_or_else(|| RuntimeError::internal("parallel job did not complete"))
            })
            .collect()
    }
    pub(crate) fn references(&self) -> Vec<Handle> {
        let outcomes = self
            .outcomes
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        self.jobs
            .iter()
            .flat_map(Job::references)
            .chain(
                outcomes
                    .iter()
                    .filter_map(|outcome| outcome.as_ref()?.as_ref().ok().copied()),
            )
            .collect()
    }
}
