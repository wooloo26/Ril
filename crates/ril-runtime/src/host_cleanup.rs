//! Implicit host cleanup extracts authority under the heap gate and releases it
//! after leaving that gate. No managed handle is dereferenced during host waits.
use crate::{
    file::FileState,
    heap::{Handle, Object},
    process::ChildState,
    value::{Result, Runtime, RuntimeError},
};
use std::sync::{Arc, Mutex};

pub(crate) enum Action {
    File(Arc<Mutex<FileState>>),
    Child(Arc<Mutex<ChildState>>),
}
pub(crate) fn prepare(runtime: &Runtime, resource: Handle) -> Result<Option<Action>> {
    Ok(match runtime.heap.get(resource)? {
        Object::File(id) => Some(Action::File(
            runtime
                .files
                .get(*id as usize)
                .cloned()
                .ok_or_else(|| RuntimeError::internal("invalid file cleanup authority"))?,
        )),
        Object::Child(id) => Some(Action::Child(
            runtime
                .children
                .get(*id as usize)
                .cloned()
                .ok_or_else(|| RuntimeError::internal("invalid child cleanup authority"))?,
        )),
        _ => None,
    })
}
impl Action {
    pub(crate) fn perform(self) -> Result<()> {
        match self {
            Self::File(file) => {
                crate::file::release_host(&file);
                Ok(())
            }
            Self::Child(child) => crate::process::release_host(&child),
        }
    }
}
