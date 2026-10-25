//! Non-owning stream identities. Only an active
//! invocation roots its receiver/callback; an idle buffer retains no authority.
use crate::{
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
    pub position: Handle,
    pub operation: CallableIdentity,
}
