//! Reader-position reservations contain generation identities, not GC roots.
//! Only a live buffered invocation owns a temporary permission to read ahead.
use crate::{
    heap::{Handle, Object},
    stream_identity::{self, CallableIdentity},
    value::{Result, Runtime, RuntimeError},
};

#[derive(Debug)]
pub(crate) struct ReadPermit {
    pub(crate) activation: Handle,
    guard: Handle,
    buffer: Handle,
    receiver: Handle,
    position: Handle,
    callback: Handle,
}

impl ReadPermit {
    pub(crate) fn references(&self) -> impl Iterator<Item = Handle> {
        [self.activation, self.buffer, self.receiver, self.callback]
            .into_iter()
            .filter(|handle| *handle != Handle::INVALID)
    }
}
impl Runtime {
    pub(crate) fn read_position_identity(&self, position: Handle) -> Result<Handle> {
        match self.heap.get(position)? {
            crate::heap::Object::ReadPosition(identity) if *identity != Handle::INVALID => {
                Ok(*identity)
            }
            _ => Err(RuntimeError::internal("expected read position identity")),
        }
    }

    fn reservation_covers(
        &self,
        buffer: Handle,
        binding: &stream_identity::Binding,
        position: Handle,
    ) -> bool {
        binding.receiver == position
            || binding.position == position
            || self
                .heap
                .read_sources
                .get(&buffer)
                .is_some_and(|sources| sources.contains(&position))
    }

    /// Only the nearest buffered invocation supplies access permission. An
    /// inner buffer cannot borrow an outer buffer's pending-position permit.
    fn active_read_buffer(&self) -> Result<Option<Handle>> {
        let mut activation = self.cps_activation;
        loop {
            if let Some(permit) = self
                .read_permits
                .iter()
                .rev()
                .find(|permit| permit.activation == activation)
            {
                return Ok(Some(permit.buffer));
            }
            if activation == Handle::INVALID {
                break;
            }
            activation = self.activation(activation)?.parent;
        }
        Ok(None)
    }

    pub(crate) fn check_buffered_position(&self, buffer: Handle, position: Handle) -> Result<()> {
        if self.heap.read_reservations.iter().any(|(&other, binding)| {
            other != buffer && self.reservation_covers(other, binding, position)
        }) {
            return Err(RuntimeError::panic(
                "reader position is reserved by unread buffered input",
            ));
        }
        Ok(())
    }

    /// All protected accesses share this position check, independently of the
    /// operation callable. Delegation records non-owning identities only.
    pub(crate) fn guard_read_position(&mut self, position: Handle, seek: bool) -> Result<()> {
        let active = self.active_read_buffer()?;
        let permitted = if seek { None } else { active };
        if self
            .heap
            .read_reservations
            .iter()
            .any(|(&buffer, binding)| {
                self.reservation_covers(buffer, binding, position) && permitted != Some(buffer)
            })
        {
            return Err(RuntimeError::panic(
                "reader position is reserved by unread buffered input",
            ));
        }
        if let Some(buffer) = active {
            self.heap
                .read_sources
                .entry(buffer)
                .or_default()
                .insert(position);
        }
        Ok(())
    }

    /// Seeking is forbidden while any buffer has an unread/deferred claim on
    /// this cursor. A read-ahead permit never authorizes repositioning it.
    pub(crate) fn check_reserved_seek(&self, receiver: Handle) -> Result<()> {
        if self
            .heap
            .read_reservations
            .iter()
            .any(|(buffer, binding)| self.reservation_covers(*buffer, binding, receiver))
        {
            return Err(RuntimeError::panic(
                "reader position is reserved by unread buffered input",
            ));
        }
        Ok(())
    }

    pub(crate) fn end_buffered_reads(&mut self, activation: Handle) {
        for permit in self
            .read_permits
            .iter()
            .filter(|permit| permit.activation == activation)
        {
            if !self.heap.read_reservations.contains_key(&permit.buffer) {
                self.heap.read_sources.remove(&permit.buffer);
            }
        }
        self.read_permits
            .retain(|permit| permit.activation != activation);
    }
    fn begin_read_guard(
        &mut self,
        buffer: Handle,
        receiver: Handle,
        callback: Handle,
        position: Handle,
        cached: bool,
    ) -> Result<Handle> {
        self.heap.get(buffer)?;
        self.heap.get(receiver)?;
        stream_identity::callable_identity(self, callback)?;
        if !cached {
            self.check_buffered_position(buffer, receiver)?;
            self.check_buffered_position(buffer, position)?;
        }
        let activation = self.cps_activation;
        if activation != Handle::INVALID && self.activation(activation)?.closed {
            return Err(RuntimeError::internal(
                "read guard entered an ended activation",
            ));
        }
        let guard = self.allocate(Object::ReadGuard(Handle::INVALID))?;
        *self.heap.get_mut(guard)? = Object::ReadGuard(guard);
        self.read_permits.push(ReadPermit {
            activation,
            guard,
            buffer,
            receiver,
            position,
            callback,
        });
        Ok(guard)
    }

    /// Release by exact permission key: an already-ended inner activation must
    /// never pop its caller's still-live permission.
    pub(crate) fn release_read_guard(&mut self, value: Handle) -> Result<bool> {
        let Object::ReadGuard(key) = self.heap.get(value)? else {
            return Ok(false);
        };
        let key = *key;
        if let Some(index) = self
            .read_permits
            .iter()
            .position(|permit| permit.guard == key)
        {
            let permit = self.read_permits.remove(index);
            if !self.heap.read_reservations.contains_key(&permit.buffer) {
                self.heap.read_sources.remove(&permit.buffer);
            }
        }
        Ok(true)
    }

    pub(crate) fn identity_primitive(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing identity primitive argument"))
        };
        match name {
            "\0ril.identity.fresh" => {
                let token = self.allocate(Object::ReadPosition(Handle::INVALID))?;
                *self.heap.get_mut(token)? = Object::ReadPosition(token);
                Ok(token)
            }
            "\0ril.identity.reference" => {
                let value = arg(0)?;
                self.heap.get(value)?;
                self.allocate(Object::ReadPosition(value))
            }
            "\0ril.identity.callable" => {
                let identity = stream_identity::callable_identity(self, arg(0)?)?;
                self.allocate(Object::CallableIdentity(identity))
            }
            "\0ril.identity.guard_read" | "\0ril.identity.guard_seek" => {
                let position = self.read_position_identity(arg(0)?)?;
                self.guard_read_position(position, name == "\0ril.identity.guard_seek")?;
                self.unit()
            }
            "\0ril.identity.read_guard" => {
                let receiver = arg(1)?;
                let position = match self.heap.get(arg(3)?)? {
                    Object::Variant { tag, fields } if tag == "None" && fields.is_empty() => {
                        receiver
                    }
                    Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => {
                        self.read_position_identity(fields[0])?
                    }
                    _ => return Err(RuntimeError::internal("invalid optional read position")),
                };
                let Object::Bool(cached) = self.heap.get(arg(4)?)? else {
                    return Err(RuntimeError::internal("invalid read cache flag"));
                };
                self.begin_read_guard(arg(0)?, receiver, arg(2)?, position, *cached)
            }
            "\0ril.identity.read_reservation" => {
                let Object::ReadGuard(key) = self.heap.get(arg(0)?)? else {
                    return Err(RuntimeError::internal("expected active read guard"));
                };
                let permit = self
                    .read_permits
                    .iter()
                    .find(|permit| permit.guard == *key)
                    .ok_or_else(|| RuntimeError::internal("read guard has ended"))?;
                let buffer = permit.buffer;
                let binding = stream_identity::Binding {
                    receiver: permit.receiver,
                    position: permit.position,
                    operation: stream_identity::callable_identity(self, permit.callback)?,
                };
                let Object::Bool(pending) = self.heap.get(arg(1)?)? else {
                    return Err(RuntimeError::internal("invalid read reservation flag"));
                };
                self.heap
                    .set_read_reservation(buffer, pending.then_some(binding));
                self.unit()
            }
            _ => Err(RuntimeError::internal("unknown identity primitive")),
        }
    }
    pub(crate) fn check_read_reservation(
        &mut self,
        callable: Handle,
        arguments: Handle,
    ) -> Result<()> {
        if self.heap.read_reservations.is_empty() && self.read_permits.is_empty() {
            return Ok(());
        }
        if matches!(
            self.heap.get(callable)?,
            crate::heap::Object::DataConstructor { .. }
        ) {
            return Ok(());
        }
        self.check_read_identity(
            &stream_identity::callable_identity(self, callable)?,
            arguments,
        )
    }
    pub(crate) fn check_native_read_reservation(
        &mut self,
        function: u64,
        environment: Handle,
        arguments: Handle,
    ) -> Result<()> {
        if self.heap.read_reservations.is_empty() {
            return Ok(());
        }
        self.check_read_identity(
            &stream_identity::native_identity(self, function, environment)?,
            arguments,
        )
    }
    fn check_read_identity(
        &mut self,
        operation: &CallableIdentity,
        arguments: Handle,
    ) -> Result<()> {
        let arguments = self.sequence(arguments)?;
        let Some(&receiver) = arguments.first() else {
            return Ok(());
        };
        if matches!(operation, CallableIdentity::Builtin(name) if name == "File::seek") {
            self.check_reserved_seek(receiver)?;
        }
        let direct_stream_access = matches!(operation, CallableIdentity::Builtin(name)
            if matches!(name.as_str(), "File::read_chunk" | "File::seek"));
        if direct_stream_access {
            return self.guard_read_position(
                receiver,
                matches!(operation, CallableIdentity::Builtin(name) if name == "File::seek"),
            );
        }
        let permitted = self.active_read_buffer()?;
        for (&buffer, binding) in &self.heap.read_reservations {
            let selected = binding.receiver == receiver && &binding.operation == operation;
            if selected && permitted != Some(buffer) {
                return Err(RuntimeError::panic(
                    "reader position is reserved by unread buffered input",
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{shared::Worker, stream_identity::Binding};

    fn record(runtime: &mut Runtime) -> Handle {
        runtime
            .allocate(Object::Record(Default::default()))
            .unwrap()
    }
    fn reserve(runtime: &mut Runtime, buffer: Handle, receiver: Handle, callback: Handle) {
        runtime.heap.set_read_reservation(
            buffer,
            Some(Binding {
                receiver,
                position: receiver,
                operation: stream_identity::callable_identity(runtime, callback).unwrap(),
            }),
        );
    }
    fn callable(runtime: &mut Runtime) -> Handle {
        runtime
            .allocate(Object::Builtin("custom_read".into()))
            .unwrap()
    }

    #[test]
    fn copied_position_tokens_and_idle_reservations_do_not_root_receiver_authority() {
        let mut runtime = Runtime::default();
        let token = runtime
            .identity_primitive("\0ril.identity.fresh", &[])
            .unwrap();
        let position = runtime.read_position_identity(token).unwrap();
        let copy = runtime.heap.deep_clone(token).unwrap();
        let receiver = runtime.allocate(Object::File(0)).unwrap();
        let buffer = record(&mut runtime);
        runtime.heap.set_read_reservation(
            buffer,
            Some(Binding {
                receiver,
                position,
                operation: CallableIdentity::Opaque(receiver),
            }),
        );
        runtime.heap.collect([copy, buffer]).unwrap();
        assert!(runtime.heap.get(token).is_err());
        assert!(runtime.heap.get(receiver).is_err());
        assert_eq!(runtime.read_position_identity(copy).unwrap(), position);
        assert!(runtime.guard_read_position(position, false).is_err());
        let fresh = runtime
            .identity_primitive("\0ril.identity.fresh", &[])
            .unwrap();
        let fresh = runtime.read_position_identity(fresh).unwrap();
        assert_ne!(fresh, position);
        assert!(runtime.guard_read_position(fresh, false).is_ok());
        runtime.heap.collect([]).unwrap();
        assert!(runtime.heap.read_reservations.is_empty());
    }

    #[test]
    fn nested_guards_cannot_combine_permissions_or_release_an_outer_guard() {
        let mut runtime = Runtime::default();
        let receiver = record(&mut runtime);
        let callback = callable(&mut runtime);
        let outer = record(&mut runtime);
        reserve(&mut runtime, outer, receiver, callback);
        let first = runtime
            .begin_read_guard(outer, receiver, callback, receiver, true)
            .unwrap();
        runtime.collect().unwrap();
        assert!(runtime.guard_read_position(receiver, false).is_ok());
        assert!(runtime.guard_read_position(receiver, true).is_err());
        let inner = record(&mut runtime);
        assert!(
            runtime
                .begin_read_guard(inner, receiver, callback, receiver, false)
                .is_err()
        );
        let second = runtime
            .begin_read_guard(inner, receiver, callback, receiver, true)
            .unwrap();
        assert!(runtime.guard_read_position(receiver, false).is_err());
        runtime.release_read_guard(second).unwrap();
        runtime.release_read_guard(second).unwrap();
        assert!(runtime.guard_read_position(receiver, false).is_ok());
        runtime.release_read_guard(first).unwrap();
        assert!(runtime.guard_read_position(receiver, false).is_err());
    }

    #[test]
    fn cloned_reservations_and_delegated_sources_require_independent_release() {
        let mut runtime = Runtime::default();
        let receiver = record(&mut runtime);
        let callback = callable(&mut runtime);
        let buffer = record(&mut runtime);
        let file = runtime.allocate(Object::File(0)).unwrap();
        let guard = runtime
            .begin_read_guard(buffer, receiver, callback, receiver, false)
            .unwrap();
        runtime.guard_read_position(file, false).unwrap();
        let pending = runtime.boolean(true).unwrap();
        runtime
            .identity_primitive("\0ril.identity.read_reservation", &[guard, pending])
            .unwrap();
        runtime.release_read_guard(guard).unwrap();
        let copy = runtime.heap.deep_clone(buffer).unwrap();
        runtime.heap.set_read_reservation(buffer, None);
        assert!(runtime.check_reserved_seek(file).is_err());
        assert!(runtime.guard_read_position(file, false).is_err());
        runtime.heap.set_read_reservation(copy, None);
        assert!(runtime.guard_read_position(file, false).is_ok());
    }

    #[test]
    fn metered_callable_entries_preserve_non_owning_operation_identity() {
        let mut runtime = Runtime::default();
        let receiver = record(&mut runtime);
        let environment = runtime.unit().unwrap();
        let callback = runtime
            .allocate(Object::Closure {
                function: 10,
                environment,
            })
            .unwrap();
        runtime.heap.register_native_entries(10, 20);
        let buffer = record(&mut runtime);
        reserve(&mut runtime, buffer, receiver, callback);
        let arguments = runtime.allocate(Object::Tuple(vec![receiver])).unwrap();
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_err()
        );
        let guard = runtime
            .begin_read_guard(buffer, receiver, callback, receiver, true)
            .unwrap();
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_ok()
        );
        let copy = runtime.heap.deep_clone(buffer).unwrap();
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_err()
        );
        runtime.heap.set_read_reservation(copy, None);
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_ok()
        );
        assert!(runtime.heap.deep_clone(guard).is_err());
        runtime.release_read_guard(guard).unwrap();
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_err()
        );
    }

    #[test]
    fn ended_activation_guard_cleanup_cannot_revoke_a_parent_permission() {
        let mut runtime = Runtime::default();
        let receiver = record(&mut runtime);
        let callback = callable(&mut runtime);
        let buffer = record(&mut runtime);
        reserve(&mut runtime, buffer, receiver, callback);
        let parent = runtime.new_activation().unwrap();
        let outer = runtime
            .begin_read_guard(buffer, receiver, callback, receiver, true)
            .unwrap();
        let child = runtime.new_activation().unwrap();
        let inner = runtime
            .begin_read_guard(buffer, receiver, callback, receiver, true)
            .unwrap();
        runtime.end_buffered_reads(child);
        runtime.cps_activation = parent;
        runtime.release_read_guard(inner).unwrap();
        assert!(runtime.guard_read_position(receiver, false).is_ok());
        runtime.release_read_guard(outer).unwrap();
        assert!(runtime.guard_read_position(receiver, false).is_err());
    }

    #[test]
    fn shared_workers_observe_the_same_persistent_reservations() {
        let mut runtime = Runtime::default();
        let receiver = record(&mut runtime);
        let callback = callable(&mut runtime);
        let buffer = record(&mut runtime);
        reserve(&mut runtime, buffer, receiver, callback);
        let arguments = runtime.allocate(Object::Tuple(vec![receiver])).unwrap();
        let mut parent = Worker::new(runtime);
        let mut child = parent.fork(&[buffer, callback, arguments]).unwrap();
        child.with(|runtime| assert!(runtime.check_read_reservation(callback, arguments).is_err()));
        child.with(|runtime| runtime.heap.set_read_reservation(buffer, None));
        parent.with(|runtime| assert!(runtime.check_read_reservation(callback, arguments).is_ok()));
    }
}
