//! Host transfer threads own host authority and byte storage only. A cancellation
//! request is followed by worker completion; no borrowed buffer or IO is detached.
use crate::{
    process_io::Cancellation,
    value::{Result, RuntimeError},
};
use std::{sync::Arc, thread, time::Duration};

pub(crate) fn run<T: Send + 'static>(
    cancellation: Arc<Cancellation>,
    operation: impl FnOnce() -> Result<T> + Send + 'static,
) -> Result<T> {
    if cancellation.requested() {
        return Err(RuntimeError::cancelled());
    }
    let worker = thread::Builder::new()
        .name("ril-host-transfer".into())
        .spawn(operation)
        .map_err(|error| RuntimeError::internal(format!("cannot start host transfer: {error}")))?;
    while !worker.is_finished() {
        if cancellation.requested() {
            // Windows synchronous IO may begin just after an earlier request.
            // Repeat cancellation until the worker actually completes.
            crate::platform_io::cancel(&worker);
        }
        thread::sleep(Duration::from_millis(1));
    }
    let result = worker
        .join()
        .map_err(|_| RuntimeError::internal("unexpected Rust panic in host transfer"))?;
    if matches!(&result, Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::InternalFault)
    {
        result
    } else if cancellation.requested() {
        Err(RuntimeError::cancelled())
    } else {
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unexpected_host_failure_survives_concurrent_cancellation() {
        for panics in [false, true] {
            let cancellation = Arc::new(Cancellation::default());
            let worker_token = cancellation.clone();
            let result = run::<()>(cancellation, move || {
                worker_token.request();
                if panics {
                    panic!("host worker failure");
                }
                Err(RuntimeError::internal("host operation failed"))
            });
            assert_eq!(
                result.unwrap_err().tag,
                ril_runtime_api::abi::OutcomeTag::InternalFault
            );
        }
    }
}
