//! Host requests own bytes/scalars and cancellation only. Their blocking work
//! runs after the native ABI has released the Runtime borrow and shared GC gate.
use crate::{
    heap::{Handle, Object},
    process_io::Cancellation,
    value::{Result, Runtime, RuntimeError},
};
use std::{sync::Arc, time::Duration};

pub(crate) enum Request {
    Sleep {
        duration: Duration,
        cancellation: Arc<Cancellation>,
    },
    Entropy {
        count: usize,
        cancellation: Arc<Cancellation>,
    },
}
pub(crate) enum Reply {
    Slept,
    Entropy(std::io::Result<Vec<u8>>),
}
pub(crate) fn is_operation(name: &str) -> bool {
    matches!(name, "Time::sleep" | "Random::entropy")
}
pub(crate) fn prepare(runtime: &Runtime, name: &str, arguments: &[Handle]) -> Result<Request> {
    let first = *arguments
        .first()
        .ok_or_else(|| RuntimeError::internal("missing host service argument"))?;
    match name {
        "Time::sleep" => {
            let nanos = runtime.duration_value(first)?;
            if nanos < 0 {
                return Err(RuntimeError::panic("negative sleep duration"));
            }
            Ok(Request::Sleep {
                duration: Duration::from_nanos(nanos as u64),
                cancellation: runtime.host_cancellation(),
            })
        }
        "Random::entropy" => {
            let count = usize::try_from(runtime.as_integer(first)?)
                .map_err(|_| RuntimeError::panic("negative entropy count"))?;
            Ok(Request::Entropy {
                count,
                cancellation: runtime.host_cancellation(),
            })
        }
        _ => Err(RuntimeError::internal("invalid host service")),
    }
}
impl Request {
    pub(crate) fn with_cancellation(mut self, token: Arc<Cancellation>) -> Self {
        match &mut self {
            Self::Sleep { cancellation, .. } | Self::Entropy { cancellation, .. } => {
                *cancellation = token
            }
        }
        self
    }
    pub(crate) fn perform(self) -> Result<Reply> {
        match self {
            Self::Sleep {
                duration,
                cancellation,
            } => {
                if !cancellation.sleep(duration) {
                    return Err(RuntimeError::cancelled());
                }
                Ok(Reply::Slept)
            }
            Self::Entropy {
                count,
                cancellation,
            } => {
                if cancellation.requested() {
                    return Err(RuntimeError::cancelled());
                }
                let mut data = Vec::new();
                data.try_reserve_exact(count)
                    .map_err(|_| RuntimeError::panic("entropy allocation failed"))?;
                data.resize(count, 0);
                // A zero request neither consults nor waits on the host.
                let result = if count == 0 {
                    Ok(())
                } else {
                    entropy_fill(&mut data, &cancellation)?
                };
                Ok(Reply::Entropy(result.map(|()| data)))
            }
        }
    }
}
pub(crate) fn finish(runtime: &mut Runtime, reply: Reply) -> Result<Handle> {
    match reply {
        Reply::Slept => runtime.unit(),
        Reply::Entropy(Ok(data)) => {
            let data = runtime.allocate(Object::Bytes(data.into()))?;
            runtime.variant("Ok", vec![data])
        }
        Reply::Entropy(Err(error)) => {
            let kind = if error.kind() == std::io::ErrorKind::Unsupported {
                "Unsupported"
            } else {
                "Other"
            };
            let error = runtime.io_error(kind, error.to_string(), error.raw_os_error())?;
            runtime.variant("Err", vec![error])
        }
    }
}

fn entropy_fill(data: &mut [u8], cancellation: &Cancellation) -> Result<std::io::Result<()>> {
    fill_chunks(data, cancellation, entropy_chunk)
}
fn fill_chunks(
    data: &mut [u8],
    cancellation: &Cancellation,
    mut fill: impl FnMut(&mut [u8]) -> std::io::Result<usize>,
) -> Result<std::io::Result<()>> {
    let mut written = 0;
    while written < data.len() {
        if cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        let end = (written + 256).min(data.len());
        match fill(&mut data[written..end]) {
            Ok(0) => {
                return Ok(Err(std::io::Error::other(
                    "entropy source made no progress",
                )));
            }
            Ok(count) if count <= end - written => written += count,
            Ok(_) => {
                return Err(RuntimeError::internal(
                    "entropy source returned invalid count",
                ));
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                if !cancellation.sleep(Duration::from_millis(1)) {
                    return Err(RuntimeError::cancelled());
                }
            }
            Err(error) => return Ok(Err(error)),
        }
    }
    if cancellation.requested() {
        return Err(RuntimeError::cancelled());
    }
    Ok(Ok(()))
}
#[cfg(target_os = "linux")]
fn entropy_chunk(data: &mut [u8]) -> std::io::Result<usize> {
    // Never wait for initial kernel seeding in an uninterruptible syscall.
    rustix::rand::getrandom(data, rustix::rand::GetRandomFlags::NONBLOCK).map_err(Into::into)
}
#[cfg(not(target_os = "linux"))]
fn entropy_chunk(data: &mut [u8]) -> std::io::Result<usize> {
    // The supported Windows backend uses the user-mode ProcessPrng. Bound each
    // call and check cancellation between chunks instead of one giant request.
    getrandom::fill(data).map(|()| data.len()).map_err(|error| {
        if error == getrandom::Error::UNSUPPORTED {
            std::io::Error::new(std::io::ErrorKind::Unsupported, error.to_string())
        } else if let Some(code) = error.raw_os_error() {
            std::io::Error::from_raw_os_error(code)
        } else {
            std::io::Error::other(error.to_string())
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn entropy_chunks_retry_short_reads_and_interrupts_without_skipping_bytes() {
        let mut data = vec![0; 777];
        let mut calls = 0;
        fill_chunks(&mut data, &Cancellation::default(), |chunk| {
            assert!(chunk.len() <= 256);
            calls += 1;
            if calls == 1 {
                return Err(std::io::ErrorKind::Interrupted.into());
            }
            let count = chunk.len().min(17);
            chunk[..count].fill(29);
            Ok(count)
        })
        .unwrap()
        .unwrap();
        assert_eq!(data, vec![29; 777]);
        assert!(calls > 3);
    }
    #[test]
    fn entropy_wait_and_final_chunk_cancellation_never_publish_partial_success() {
        for wait in [false, true] {
            let token = Cancellation::default();
            let result = fill_chunks(&mut [0; 1], &token, |chunk| {
                token.request();
                if wait {
                    Err(std::io::ErrorKind::WouldBlock.into())
                } else {
                    chunk.fill(1);
                    Ok(chunk.len())
                }
            });
            assert!(
                matches!(result, Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::Cancelled)
            );
        }
        let token = Arc::new(Cancellation::default());
        token.request();
        assert!(
            matches!(Request::Entropy { count: usize::MAX, cancellation: token }.perform(), Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::Cancelled)
        );
        fill_chunks(&mut [], &Cancellation::default(), |_| {
            panic!("zero entropy must not consult the host")
        })
        .unwrap()
        .unwrap();
    }
    #[test]
    fn entropy_reports_stalled_sources_and_real_nonblocking_host_bytes() {
        let failed = fill_chunks(&mut [0; 1], &Cancellation::default(), |_| Ok(0))
            .unwrap()
            .unwrap_err();
        assert_eq!(failed.kind(), std::io::ErrorKind::Other);
        let Reply::Entropy(bytes) = (Request::Entropy {
            count: 513,
            cancellation: Arc::default(),
        })
        .perform()
        .unwrap() else {
            panic!();
        };
        assert_eq!(bytes.unwrap().len(), 513);
    }
    #[test]
    fn cancellation_wakes_a_host_sleep_and_never_returns_success() {
        let cancellation = Arc::new(Cancellation::default());
        let (ready, waiting) = std::sync::mpsc::channel();
        let (send, answer) = std::sync::mpsc::channel();
        let token = cancellation.clone();
        let worker = std::thread::spawn(move || {
            ready.send(()).unwrap();
            let result = Request::Sleep {
                duration: Duration::from_secs(60),
                cancellation: token,
            }
            .perform();
            send.send(result.err().map(|error| error.tag)).unwrap();
        });
        waiting.recv().unwrap();
        cancellation.request();
        assert_eq!(
            answer.recv_timeout(Duration::from_secs(3)).unwrap(),
            Some(ril_runtime_api::abi::OutcomeTag::Cancelled)
        );
        worker.join().unwrap();
    }
}
