//! Opt-in shared managed heap. Every worker publishes its precise roots before
//! releasing the heap gate. Native code outside the gate carries handles only;
//! it cannot inspect a managed object until the next ABI safepoint.
use crate::{
    heap::{Handle, Heap},
    value::{Result, Runtime, RuntimeError},
};
use std::{
    collections::BTreeMap,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    sync::{Arc, Mutex},
};

#[derive(Debug)]
struct Group {
    heap: Heap,
    roots: BTreeMap<u64, Vec<Handle>>,
    next_worker: u64,
}
#[derive(Debug)]
struct Registration {
    group: Arc<Mutex<Group>>,
    id: u64,
}
impl Drop for Registration {
    fn drop(&mut self) {
        self.group
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .roots
            .remove(&self.id);
    }
}
#[derive(Debug, Clone)]
pub(crate) struct Membership(Arc<Registration>);
impl Membership {
    fn activate(runtime: &mut Runtime) -> Self {
        let group = Arc::new(Mutex::new(Group {
            heap: std::mem::take(&mut runtime.heap),
            roots: [(1, runtime.strong_roots())].into(),
            next_worker: 2,
        }));
        Self(Arc::new(Registration { group, id: 1 }))
    }
    fn fork(&self, roots: Vec<Handle>) -> Result<Self> {
        let mut group = self
            .0
            .group
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for &handle in &roots {
            group.heap.get(handle)?;
        }
        let id = group.next_worker;
        group.next_worker = id
            .checked_add(1)
            .ok_or_else(|| RuntimeError::internal("shared worker identity exhausted"))?;
        group.roots.insert(id, roots);
        Ok(Self(Arc::new(Registration {
            group: self.0.group.clone(),
            id,
        })))
    }
    fn run<T>(&self, runtime: &mut Runtime, operation: impl FnOnce(&mut Runtime) -> T) -> T {
        let mut group = self
            .0
            .group
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        runtime.external_roots = group
            .roots
            .iter()
            .filter(|(id, _)| **id != self.0.id)
            .flat_map(|(_, roots)| roots.iter().copied())
            .collect();
        std::mem::swap(&mut runtime.heap, &mut group.heap);
        let outcome = catch_unwind(AssertUnwindSafe(|| operation(runtime)));
        group.roots.insert(self.0.id, runtime.strong_roots());
        std::mem::swap(&mut runtime.heap, &mut group.heap);
        runtime.external_roots.clear();
        drop(group);
        match outcome {
            Ok(value) => value,
            Err(payload) => resume_unwind(payload),
        }
    }
}
pub(crate) fn with_runtime<T>(
    runtime: &mut Runtime,
    operation: impl FnOnce(&mut Runtime) -> T,
) -> T {
    match runtime.shared_worker.clone() {
        Some(worker) => worker.run(runtime, operation),
        None => operation(runtime),
    }
}
pub(crate) fn activate(runtime: &mut Runtime) {
    if runtime.shared_worker.is_none() {
        runtime.shared_worker = Some(Membership::activate(runtime));
    }
}

/// Prepare a native child outside `with_runtime`: registering a worker acquires
/// the group gate itself. Child effects, activations and host authority start empty.
pub(crate) fn fork_runtime(
    parent: &Runtime,
    initial: &[Handle],
    cancellation: Arc<crate::process_io::Cancellation>,
) -> Result<Runtime> {
    let roots: Vec<_> = initial
        .iter()
        .copied()
        .chain(parent.globals.values().copied())
        .collect();
    let membership = parent
        .shared_worker
        .as_ref()
        .ok_or_else(|| RuntimeError::internal("native task requires a shared heap"))?
        .fork(roots.clone())?;
    let mut child = Runtime::default();
    child.shared_worker = Some(membership);
    child.executor = parent.executor.clone();
    child.cancellation = cancellation;
    child.foreign_bindings = parent.foreign_bindings.clone();
    child.scope_lineage.clone_from(&parent.scope_lineage);
    child.scope_registry.clone_from(&parent.scope_registry);
    child.globals.clone_from(&parent.globals);
    child.seed_shared_roots(&roots);
    Ok(child)
}

/// A runtime worker for trusted embedding/infrastructure code. This API grants
/// no Ril permission or task-transfer certificate. Callbacks execute outside
/// `with`; blocking host operations must also leave this gate before task use.
#[derive(Debug)]
pub struct Worker {
    runtime: Runtime,
}
impl Worker {
    pub fn new(mut runtime: Runtime) -> Self {
        activate(&mut runtime);
        Self { runtime }
    }
    pub fn fork(&self, roots: &[Handle]) -> Result<Self> {
        Ok(Self {
            runtime: fork_runtime(&self.runtime, roots, Arc::default())?,
        })
    }
    pub fn with<T>(&mut self, operation: impl FnOnce(&mut Runtime) -> T) -> T {
        with_runtime(&mut self.runtime, operation)
    }
}

#[cfg(test)]
#[path = "shared_tests.rs"]
mod tests;
