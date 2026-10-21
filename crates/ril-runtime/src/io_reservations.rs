//! Reader-position reservations contain generation identities, not GC roots.
//! Only a live buffered invocation owns a temporary permission to read ahead.
use crate::{
    heap::Handle,
    io_buffered::{self, CallableIdentity},
    value::{Result, Runtime, RuntimeError},
};

#[derive(Debug)]
pub(crate) struct ReadPermit {
    pub(crate) activation: Handle,
    buffer: Handle,
    receiver: Handle,
    callback: Handle,
}
impl ReadPermit {
    pub(crate) fn references(&self) -> [Handle; 4] {
        [self.activation, self.buffer, self.receiver, self.callback]
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
        binding: &io_buffered::Binding,
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
        while activation != Handle::INVALID {
            if let Some(permit) = self
                .read_permits
                .iter()
                .rev()
                .find(|permit| permit.activation == activation)
            {
                return Ok(Some(permit.buffer));
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
    pub(crate) fn permit_buffered_read(
        &mut self,
        activation: Handle,
        buffer: Handle,
        receiver: Handle,
        callback: Handle,
    ) -> Result<()> {
        self.activation(activation)?;
        self.read_permits.push(ReadPermit {
            activation,
            buffer,
            receiver,
            callback,
        });
        Ok(())
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
        self.check_read_identity(&io_buffered::callable_identity(self, callable)?, arguments)
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
            &io_buffered::native_identity(self, function, environment)?,
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
    use crate::{
        heap::{Heap, Object},
        io_buffered::{Binding, Pending, ReadBuffer},
        shared::Worker,
    };

    fn pending(receiver: Handle, operation: CallableIdentity) -> Object {
        Object::ReadBuffer(ReadBuffer {
            capacity: 4,
            pending: Pending::new(b"abcd".to_vec().into()),
            end: false,
            binding: Some(Binding {
                receiver,
                position: receiver,
                operation,
            }),
        })
    }

    #[test]
    fn copied_position_identity_survives_its_original_token_without_rooting_a_receiver() {
        let mut runtime = Runtime::default();
        let token = runtime.io_builtin("Io::read_position", &[]).unwrap();
        let identity = runtime.read_position_identity(token).unwrap();
        let copy = runtime.heap.deep_clone(token).unwrap();
        assert_eq!(runtime.read_position_identity(copy).unwrap(), identity);
        let receiver = runtime
            .allocate(Object::Record(Default::default()))
            .unwrap();
        let mut state = pending(receiver, CallableIdentity::Builtin("read".into()));
        let Object::ReadBuffer(buffer) = &mut state else {
            unreachable!()
        };
        buffer.binding.as_mut().unwrap().position = identity;
        let buffer = runtime.allocate(state).unwrap();
        runtime.heap.collect([copy, buffer]).unwrap();
        assert!(runtime.heap.get(token).is_err());
        assert!(runtime.heap.get(receiver).is_err());
        assert!(runtime.guard_read_position(identity, false).is_err());
        let fresh = runtime.io_builtin("Io::read_position", &[]).unwrap();
        let fresh_identity = runtime.read_position_identity(fresh).unwrap();
        assert_ne!(identity, fresh_identity);
        assert!(runtime.guard_read_position(fresh_identity, false).is_ok());
        runtime.heap.set_read_reservation(buffer, None);
        assert!(runtime.guard_read_position(identity, true).is_ok());
    }

    #[test]
    fn nested_buffers_cannot_combine_their_position_permissions() {
        let mut runtime = Runtime::default();
        let token = runtime.io_builtin("Io::read_position", &[]).unwrap();
        let position = runtime.read_position_identity(token).unwrap();
        let receiver = runtime
            .allocate(Object::Record(Default::default()))
            .unwrap();
        let callback = runtime
            .allocate(Object::Builtin("custom_read".into()))
            .unwrap();
        let mut state = pending(receiver, CallableIdentity::Builtin("custom_read".into()));
        let Object::ReadBuffer(buffer) = &mut state else {
            unreachable!()
        };
        buffer.binding.as_mut().unwrap().position = position;
        let outer = runtime.allocate(state).unwrap();
        let parent = runtime.new_activation().unwrap();
        runtime
            .permit_buffered_read(parent, outer, receiver, callback)
            .unwrap();
        assert!(runtime.guard_read_position(position, false).is_ok());
        assert!(runtime.guard_read_position(position, true).is_err());
        let inner = runtime
            .allocate(Object::ReadBuffer(ReadBuffer::new(2)))
            .unwrap();
        assert!(runtime.check_buffered_position(inner, position).is_err());
        let child = runtime.new_activation().unwrap();
        runtime
            .permit_buffered_read(child, inner, receiver, callback)
            .unwrap();
        assert!(runtime.guard_read_position(position, false).is_err());
        let args = runtime.allocate(Object::Tuple(vec![receiver])).unwrap();
        assert!(runtime.check_read_reservation(callback, args).is_err());
        runtime.end_buffered_reads(child);
        runtime.cps_activation = parent;
        assert!(runtime.guard_read_position(position, false).is_ok());
        runtime.end_buffered_reads(parent);
        runtime.cps_activation = Handle::INVALID;
        assert!(runtime.guard_read_position(position, false).is_err());
    }
    #[test]
    fn position_identity_never_keeps_receiver_authority_alive() {
        let mut heap = Heap::default();
        let receiver = heap.allocate(Object::File(0)).unwrap();
        let buffer = heap
            .allocate(pending(
                receiver,
                CallableIdentity::Builtin("File::read_chunk".into()),
            ))
            .unwrap();
        heap.collect([buffer]).unwrap();
        assert!(heap.get(receiver).is_err());
        assert!(heap.read_reservations.contains_key(&buffer));
        heap.collect([]).unwrap();
        assert!(heap.read_reservations.is_empty());
    }
    #[test]
    fn cloned_pending_buffers_reserve_independently_and_metered_entry_is_the_same_operation() {
        let mut runtime = Runtime::default();
        let receiver = runtime
            .allocate(Object::Record(Default::default()))
            .unwrap();
        let environment = runtime.unit().unwrap();
        let callback = runtime
            .allocate(Object::Closure {
                function: 10,
                environment,
            })
            .unwrap();
        runtime.heap.register_native_entries(10, 20);
        let identity = io_buffered::callable_identity(&runtime, callback).unwrap();
        let buffer = runtime.allocate(pending(receiver, identity)).unwrap();
        let duplicate = runtime.heap.deep_clone(buffer).unwrap();
        let arguments = runtime.allocate(Object::Tuple(vec![receiver])).unwrap();
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_err()
        );
        let owner = runtime.new_activation().unwrap();
        runtime
            .permit_buffered_read(owner, buffer, receiver, callback)
            .unwrap();
        // Owning one read-ahead boundary cannot bypass a second buffer's unread
        // snapshot of the same stream position.
        assert!(runtime.check_read_reservation(callback, arguments).is_err());
        runtime.heap.set_read_reservation(duplicate, None);
        assert!(
            runtime
                .check_native_read_reservation(20, environment, arguments)
                .is_ok()
        );
        runtime.read_permits.clear();
        assert!(runtime.check_read_reservation(callback, arguments).is_err());
        runtime.heap.set_read_reservation(buffer, None);
        assert!(runtime.check_read_reservation(callback, arguments).is_ok());
    }
    #[test]
    fn another_shared_worker_observes_the_same_position_reservation() {
        let mut runtime = Runtime::default();
        let receiver = runtime
            .allocate(Object::Record(Default::default()))
            .unwrap();
        let environment = runtime.unit().unwrap();
        let callback = runtime
            .allocate(Object::Closure {
                function: 10,
                environment,
            })
            .unwrap();
        let identity = io_buffered::callable_identity(&runtime, callback).unwrap();
        let buffer = runtime.allocate(pending(receiver, identity)).unwrap();
        let arguments = runtime.allocate(Object::Tuple(vec![receiver])).unwrap();
        let mut parent = Worker::new(runtime);
        let mut child = parent.fork(&[buffer, callback, arguments]).unwrap();
        child.with(|runtime| assert!(runtime.check_read_reservation(callback, arguments).is_err()));
        child.with(|runtime| runtime.heap.set_read_reservation(buffer, None));
        parent.with(|runtime| assert!(runtime.check_read_reservation(callback, arguments).is_ok()));
    }
    #[test]
    fn a_delegated_file_endpoint_cannot_bypass_its_wrapper_reservation() {
        let mut runtime = Runtime::default();
        let file = runtime.allocate(Object::File(0)).unwrap();
        let receiver = runtime
            .allocate(Object::Record([("file".into(), file)].into()))
            .unwrap();
        let callback = runtime
            .allocate(Object::Builtin("wrapper_read".into()))
            .unwrap();
        let buffer = runtime
            .allocate(Object::ReadBuffer(ReadBuffer::new(4)))
            .unwrap();
        let activation = runtime.new_activation().unwrap();
        runtime
            .permit_buffered_read(activation, buffer, receiver, callback)
            .unwrap();
        let direct = runtime
            .allocate(Object::Builtin("File::read_chunk".into()))
            .unwrap();
        let arguments = runtime.allocate(Object::Tuple(vec![file])).unwrap();
        assert!(runtime.check_read_reservation(direct, arguments).is_ok());
        let binding = Binding::new(&runtime, receiver, callback).unwrap();
        let Object::ReadBuffer(state) = runtime.heap.get_mut(buffer).unwrap() else {
            unreachable!()
        };
        state.binding = Some(binding.clone());
        state.pending = Pending::new(b"ab".to_vec().into());
        runtime.heap.set_read_reservation(buffer, Some(binding));
        runtime.end_buffered_reads(activation);
        assert!(runtime.check_read_reservation(direct, arguments).is_err());
        let cloned = runtime.heap.deep_clone(buffer).unwrap();
        runtime.heap.set_read_reservation(buffer, None);
        assert!(runtime.check_read_reservation(direct, arguments).is_err());
        runtime.heap.set_read_reservation(cloned, None);
        assert!(runtime.check_read_reservation(direct, arguments).is_ok());
    }

    #[test]
    fn seek_uses_cursor_identity_and_cannot_borrow_a_read_ahead_permit() {
        let mut runtime = Runtime::default();
        let file = runtime.allocate(Object::File(0)).unwrap();
        let reader = runtime
            .allocate(Object::Builtin("File::read_chunk".into()))
            .unwrap();
        let seek = runtime
            .allocate(Object::Builtin("File::seek".into()))
            .unwrap();
        let buffer = runtime
            .allocate(pending(
                file,
                CallableIdentity::Builtin("File::read_chunk".into()),
            ))
            .unwrap();
        let arguments = runtime.allocate(Object::Tuple(vec![file])).unwrap();
        let activation = runtime.new_activation().unwrap();
        runtime
            .permit_buffered_read(activation, buffer, file, reader)
            .unwrap();
        runtime.cps_activation = activation;
        assert!(runtime.check_read_reservation(reader, arguments).is_ok());
        assert!(runtime.check_read_reservation(seek, arguments).is_err());
        // Guarding happens before host request/position validation, including
        // direct host entry rather than only the generic invocation bridge.
        let error = crate::file::host::prepare(&runtime, "File::seek", &[file, Handle::INVALID])
            .err()
            .unwrap();
        assert_eq!(error.tag, ril_runtime_api::abi::OutcomeTag::LanguagePanic);
        assert!(
            matches!(runtime.heap.get(buffer).unwrap(), Object::ReadBuffer(state) if state.pending.len()==4)
        );
        runtime.heap.set_read_reservation(buffer, None);
        assert!(runtime.check_read_reservation(seek, arguments).is_ok());
    }

    #[test]
    fn seek_checks_a_delegated_cursor_even_when_the_callback_identity_changes() {
        let mut runtime = Runtime::default();
        let file = runtime.allocate(Object::File(0)).unwrap();
        let other = runtime.allocate(Object::File(1)).unwrap();
        let receiver = runtime
            .allocate(Object::Record([("cursor".into(), file)].into()))
            .unwrap();
        let buffer = runtime
            .allocate(pending(
                receiver,
                CallableIdentity::Builtin("custom_reader".into()),
            ))
            .unwrap();
        runtime
            .heap
            .read_sources
            .entry(buffer)
            .or_default()
            .insert(file);
        assert!(runtime.check_reserved_seek(file).is_err());
        assert!(runtime.check_reserved_seek(other).is_ok());
        let copy = runtime.heap.deep_clone(buffer).unwrap();
        runtime.heap.set_read_reservation(buffer, None);
        assert!(runtime.check_reserved_seek(file).is_err());
        runtime.heap.set_read_reservation(copy, None);
        assert!(runtime.check_reserved_seek(file).is_ok());
    }
}
