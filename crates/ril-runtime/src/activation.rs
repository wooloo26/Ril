//! Logical CPS frames outlive each physical native step and remain GC roots.
use crate::{
    cps::Activation,
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
impl Runtime {
    pub(crate) fn new_activation(&mut self) -> Result<Handle> {
        let activation = self.allocate(Object::CpsActivation(Activation {
            parent: self.cps_activation,
            handlers: self.cps_handlers,
            cleanups: vec![],
            closed: false,
        }))?;
        self.cps_activation = activation;
        Ok(activation)
    }
    pub(crate) fn activation(&self, handle: Handle) -> Result<&Activation> {
        match self.heap.get(handle)? {
            Object::CpsActivation(activation) => Ok(activation),
            _ => Err(RuntimeError::internal("invalid logical activation")),
        }
    }
    pub(crate) fn attach_activation(&mut self, handle: Handle) -> Result<()> {
        if handle != Handle::INVALID && self.activation(handle)?.closed {
            return Err(RuntimeError::internal("logical activation has ended"));
        }
        self.cps_activation = handle;
        Ok(())
    }
    pub(crate) fn register_activation_cleanup(
        &mut self,
        activation: Handle,
        resource: Handle,
    ) -> Result<Handle> {
        if matches!(
            self.heap.get(resource)?,
            Object::File(_) | Object::Child(_) | Object::ReadGuard(_)
        ) {
            let Object::CpsActivation(state) = self.heap.get_mut(activation)? else {
                return Err(RuntimeError::internal("invalid logical activation"));
            };
            if state.closed {
                return Err(RuntimeError::internal("logical activation has ended"));
            }
            state.cleanups.push(resource);
            return Ok(resource);
        }
        let action = self.field(resource, "on_close")?;
        if !matches!(
            self.heap.get(action)?,
            Object::Closure { .. }
                | Object::CpsClosure { .. }
                | Object::BudgetClosure { .. }
                | Object::RetainedClosure { .. }
                | Object::CpsOperation(_)
                | Object::DataConstructor { .. }
                | Object::Builtin(_)
        ) {
            return Err(RuntimeError::internal(
                "logical cleanup contract is not callable",
            ));
        }
        let Object::CpsActivation(state) = self.heap.get_mut(activation)? else {
            return Err(RuntimeError::internal("invalid logical activation"));
        };
        if state.closed {
            return Err(RuntimeError::internal("logical activation has ended"));
        }
        state.cleanups.push(resource);
        Ok(resource)
    }
    pub(crate) fn pop_cleanup_stack(
        &mut self,
        activation: Option<Handle>,
        marker: u32,
    ) -> Result<Option<Handle>> {
        let Some(activation) = activation else {
            return self.pop_cleanup(marker);
        };
        let Object::CpsActivation(state) = self.heap.get_mut(activation)? else {
            return Err(RuntimeError::internal("invalid logical activation"));
        };
        if marker as usize > state.cleanups.len() {
            return Err(RuntimeError::internal("invalid logical cleanup marker"));
        }
        if marker as usize == state.cleanups.len() {
            return Ok(None);
        }
        let resource = state.cleanups.pop().unwrap();
        self.keep_temporary(resource);
        Ok(Some(resource))
    }
    pub(crate) fn abandon_cleanup_stack(&mut self, activation: Option<Handle>, marker: u32) {
        if let Some(activation) = activation {
            if let Ok(Object::CpsActivation(state)) = self.heap.get_mut(activation) {
                state.cleanups.truncate(marker as usize);
            }
        } else {
            self.abandon_cleanups(marker);
        }
    }
}
