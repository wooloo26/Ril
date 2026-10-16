//! Ordinary buffered bytes and non-owning stream identities. Only an active
//! invocation roots its receiver/callback; an idle buffer retains no authority.
use crate::{
    byte_string::Bytes,
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallableIdentity {
    Native { function: u64, environment: Handle },
    Builtin(String),
    Opaque(Handle),
}

pub(crate) fn native_identity(
    runtime: &Runtime,
    function: u64,
    environment: Handle,
) -> Result<CallableIdentity> {
    let empty = matches!(runtime.heap.get(environment)?, Object::Unit)
        || matches!(runtime.heap.get(environment)?, Object::Record(fields) if fields.is_empty());
    Ok(CallableIdentity::Native {
        function: runtime.heap.canonical_native_entry(function),
        environment: if empty { Handle::INVALID } else { environment },
    })
}

pub(crate) fn callable_identity(runtime: &Runtime, callable: Handle) -> Result<CallableIdentity> {
    Ok(match runtime.heap.get(callable)? {
        Object::Closure {
            function,
            environment,
        }
        | Object::CpsClosure {
            function,
            environment,
        } => return native_identity(runtime, *function, *environment),
        Object::BudgetClosure {
            normal,
            environment,
            ..
        } => return native_identity(runtime, *normal, *environment),
        Object::Builtin(name) | Object::String(name) => {
            let name = name.strip_prefix("Prelude::").unwrap_or(name);
            CallableIdentity::Builtin(
                ril_runtime_api::builtins::canonical_builtin(name)
                    .unwrap_or(name)
                    .into(),
            )
        }
        Object::RetainedClosure { .. } | Object::CpsOperation(_) => {
            CallableIdentity::Opaque(callable)
        }
        _ => return Err(RuntimeError::internal("buffer operation is not callable")),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub receiver: Handle,
    pub operation: CallableIdentity,
}

impl Binding {
    pub(crate) fn new(runtime: &Runtime, receiver: Handle, callback: Handle) -> Result<Self> {
        Ok(Self {
            receiver,
            operation: callable_identity(runtime, callback)?,
        })
    }
    pub(crate) fn check(&self, incoming: &Self) -> Result<()> {
        if self != incoming {
            return Err(RuntimeError::panic(
                "buffer has pending data for another receiver or operation",
            ));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pending {
    data: Bytes,
    tail: Vec<u8>,
}
impl Pending {
    pub(crate) fn new(data: Bytes) -> Self {
        Self { data, tail: vec![] }
    }
    pub(crate) fn len(&self) -> usize {
        self.data.len() + self.tail.len()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub(crate) fn draining(&self) -> bool {
        !self.data.is_empty()
    }
    pub(crate) fn append(&mut self, bytes: &[u8]) -> Result<()> {
        self.tail
            .try_reserve(bytes.len())
            .map_err(|_| RuntimeError::panic("stream allocation failed"))?;
        self.tail.extend_from_slice(bytes);
        Ok(())
    }
    pub(crate) fn snapshot(&mut self) -> Result<Bytes> {
        if !self.tail.is_empty() {
            let mut data = Vec::new();
            data.try_reserve_exact(self.len())
                .map_err(|_| RuntimeError::panic("stream allocation failed"))?;
            data.extend_from_slice(&self.data);
            data.append(&mut self.tail);
            self.data = data.into();
        }
        Ok(self.data.clone())
    }
    pub(crate) fn take(&mut self, count: usize) -> Result<Bytes> {
        let data = self.snapshot()?;
        let prefix = data
            .slice(0..count)
            .ok_or_else(|| RuntimeError::internal("buffer prefix exceeds pending bytes"))?;
        self.data = if count == data.len() {
            vec![].into()
        } else {
            data.slice(count..data.len())
                .expect("validated pending suffix")
        };
        Ok(prefix)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReadBuffer {
    pub capacity: usize,
    pub pending: Pending,
    pub end: bool,
    pub binding: Option<Binding>,
}
impl ReadBuffer {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            capacity,
            pending: Pending::new(vec![].into()),
            end: false,
            binding: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct WriteBuffer {
    pub capacity: usize,
    pub pending: Pending,
    pub binding: Option<Binding>,
}
impl WriteBuffer {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            capacity,
            pending: Pending::new(vec![].into()),
            binding: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Phase {
    Read {
        maximum: usize,
    },
    Write {
        input: Bytes,
        accepted: usize,
        flush: bool,
        validate_empty: bool,
        draining: bool,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Invocation {
    pub buffer: Handle,
    pub receiver: Handle,
    pub callback: Handle,
    pub outer: Handle,
    pub handlers: Handle,
    pub activation: Handle,
    pub offered: Handle,
    pub phase: Phase,
}
impl Invocation {
    pub(crate) fn references(&self) -> Vec<Handle> {
        [
            self.buffer,
            self.receiver,
            self.callback,
            self.outer,
            self.handlers,
            self.activation,
            self.offered,
        ]
        .into_iter()
        .filter(|&handle| handle != Handle::INVALID)
        .collect()
    }
}
