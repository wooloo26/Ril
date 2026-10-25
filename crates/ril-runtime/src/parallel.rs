//! Independent parallel jobs. Completion never cancels another invocation, and
//! every result remains traced until the caller has selected its outcome.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use ril_runtime_api::abi::OutcomeTag;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
};

impl Runtime {
    pub(crate) fn branch_outcome(&mut self, outcome: Result<Handle>) -> Result<Handle> {
        match outcome {
            Ok(value) => self.variant("Ok", vec![value]),
            Err(error) => {
                if let Some(hard) = error.internal_fault() {
                    return Err(hard.clone());
                }
                if !matches!(
                    error.tag,
                    OutcomeTag::LanguagePanic | OutcomeTag::DoubleFault | OutcomeTag::Cancelled
                ) {
                    return Err(if error.tag == OutcomeTag::InternalFault {
                        error
                    } else {
                        RuntimeError::internal("a transient unwind escaped a completed branch")
                    });
                }
                let fault = self.allocate(Object::BranchFault(Box::new(error)))?;
                self.variant("Err", vec![fault])
            }
        }
    }
    pub(crate) fn branch_primitive(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let error = *args
            .first()
            .ok_or_else(|| RuntimeError::internal("missing branch fault"))?;
        let Object::BranchFault(error) = self.heap.get(error)? else {
            return Err(RuntimeError::internal("expected a completed branch fault"));
        };
        match name {
            "\0ril.control.branch_rethrow" => Err(*error.clone()),
            "\0ril.control.branch_rank" => {
                let rank = crate::concurrent::fault_rank(error);
                self.int(i128::from(rank))
            }
            "\0ril.control.branch_with_index" => {
                let mut error = *error.clone();
                let token = *args
                    .get(1)
                    .ok_or_else(|| RuntimeError::internal("missing branch source index"))?;
                let index = match self.heap.get(token)? {
                    Object::Variant { tag, fields } if tag == "None" && fields.is_empty() => None,
                    Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => Some(
                        usize::try_from(self.as_integer(fields[0])?)
                            .map_err(|_| RuntimeError::internal("invalid branch source index"))?,
                    ),
                    _ => {
                        return Err(RuntimeError::internal(
                            "expected optional branch source index",
                        ));
                    }
                };
                set_index(&mut error, index);
                self.allocate(Object::BranchFault(Box::new(error)))
            }
            _ => Err(RuntimeError::internal("unknown branch control primitive")),
        }
    }
}
fn set_index(error: &mut RuntimeError, index: Option<usize>) {
    error.index = index;
    if let Some(primary) = &mut error.primary {
        set_index(primary, index);
    }
    if let Some(cleanup) = &mut error.cleanup {
        set_index(cleanup, index);
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Job {
    pub(crate) callable: Handle,
    pub(crate) arguments: Vec<Handle>,
}
impl Job {
    fn references(&self) -> impl Iterator<Item = Handle> + '_ {
        std::iter::once(self.callable).chain(self.arguments.iter().copied())
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

#[cfg(test)]
mod tests {
    use super::*;

    fn fault(runtime: &Runtime, outcome: Handle) -> Handle {
        let Object::Variant { tag, fields } = runtime.heap.get(outcome).unwrap() else {
            panic!("branch outcome")
        };
        assert_eq!(tag, "Err");
        fields[0]
    }

    #[test]
    fn fault_transport_preserves_locations_causes_and_original_index() {
        let mut runtime = Runtime::default();
        let mut primary = RuntimeError::panic("primary");
        primary.location = Some((1, 20, 30));
        primary.index = Some(17);
        let mut cleanup = RuntimeError::panic("cleanup");
        cleanup.location = Some((2, 40, 50));
        cleanup.index = Some(17);
        let error = RuntimeError::double_fault(primary, cleanup);
        let outcome = runtime.branch_outcome(Err(error.clone())).unwrap();
        let original = fault(&runtime, outcome);
        let copied = runtime.heap.deep_clone(original).unwrap();
        runtime.root(0, copied).unwrap();
        runtime.statement_end();
        runtime.collect().unwrap();
        let number = runtime.int(65).unwrap();
        let index = runtime.variant("Some", vec![number]).unwrap();
        let indexed = runtime
            .branch_primitive("\0ril.control.branch_with_index", &[copied, index])
            .unwrap();
        let ranked = runtime
            .branch_primitive("\0ril.control.branch_rank", &[indexed])
            .unwrap();
        assert_eq!(runtime.as_integer(ranked).unwrap(), 3);
        let raised = runtime
            .branch_primitive("\0ril.control.branch_rethrow", &[indexed])
            .unwrap_err();
        assert_eq!(raised.location, error.location);
        assert_eq!(
            raised.primary.as_ref().unwrap().location,
            error.primary.as_ref().unwrap().location
        );
        assert_eq!(
            raised.cleanup.as_ref().unwrap().location,
            error.cleanup.as_ref().unwrap().location
        );
        assert_eq!(raised.index, Some(65));
        assert_eq!(raised.primary.as_ref().unwrap().index, Some(65));
        assert_eq!(raised.cleanup.as_ref().unwrap().index, Some(65));
        assert_eq!(
            runtime
                .branch_primitive("\0ril.control.branch_rethrow", &[copied])
                .unwrap_err(),
            error
        );
        let absent = runtime.variant("None", vec![]).unwrap();
        let reset = runtime
            .branch_primitive("\0ril.control.branch_with_index", &[indexed, absent])
            .unwrap();
        let reset = runtime
            .branch_primitive("\0ril.control.branch_rethrow", &[reset])
            .unwrap_err();
        assert_eq!(reset.index, None);
        assert_eq!(reset.primary.unwrap().index, None);
        assert_eq!(reset.cleanup.unwrap().index, None);
    }

    #[test]
    fn only_completed_language_faults_are_ordinary_outcomes() {
        let mut runtime = Runtime::default();
        let hard = RuntimeError::internal("broken host contract");
        assert_eq!(runtime.branch_outcome(Err(hard.clone())).unwrap_err(), hard);
        let nested =
            RuntimeError::double_fault(RuntimeError::panic("language panic"), hard.clone());
        assert_eq!(
            crate::concurrent::choose_fault(None, Some(nested.clone())),
            Some(hard.clone())
        );
        assert_eq!(runtime.branch_outcome(Err(nested)).unwrap_err(), hard);
        let mut transient = RuntimeError::cancelled();
        transient.tag = OutcomeTag::EffectAborted;
        assert_eq!(
            runtime.branch_outcome(Err(transient)).unwrap_err().tag,
            OutcomeTag::InternalFault
        );
        for (error, expected) in [
            (RuntimeError::cancelled(), 1),
            (RuntimeError::panic("panic"), 2),
        ] {
            let outcome = runtime.branch_outcome(Err(error)).unwrap();
            let token = fault(&runtime, outcome);
            let rank = runtime
                .branch_primitive("\0ril.control.branch_rank", &[token])
                .unwrap();
            assert_eq!(runtime.as_integer(rank).unwrap(), expected);
        }
    }
}
