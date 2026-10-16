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
        let mut permitted = std::collections::BTreeSet::new();
        for permit in &self.read_permits {
            let mut current = self.cps_activation;
            while current != Handle::INVALID {
                if current == permit.activation {
                    permitted.insert(permit.buffer);
                    break;
                }
                current = self.activation(current)?.parent;
            }
        }
        let direct_stream_read =
            matches!(operation, CallableIdentity::Builtin(name) if name == "File::read_chunk");
        for (&buffer, binding) in &self.heap.read_reservations {
            let delegated = direct_stream_read
                && self
                    .heap
                    .read_sources
                    .get(&buffer)
                    .is_some_and(|sources| sources.contains(&receiver));
            let selected = binding.receiver == receiver
                && (&binding.operation == operation || direct_stream_read);
            if (delegated || selected) && !permitted.contains(&buffer) {
                return Err(RuntimeError::panic(
                    "reader position is reserved by unread buffered input",
                ));
            }
        }
        if direct_stream_read {
            for buffer in permitted {
                self.heap
                    .read_sources
                    .entry(buffer)
                    .or_default()
                    .insert(receiver);
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
                operation,
            }),
        })
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
}
