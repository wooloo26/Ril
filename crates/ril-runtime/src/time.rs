//! Exact timestamp arithmetic and process-local monotonic observations.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use std::{
    sync::OnceLock,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

const NANOS: i128 = 1_000_000_000;
static CLOCK_ORIGIN: OnceLock<Instant> = OnceLock::new();

impl Runtime {
    #[cfg(test)]
    fn duration(&mut self, nanos: i64) -> Result<Handle> {
        let payload = self.integer(i128::from(nanos), 64, true)?;
        self.allocate(Object::Nominal {
            tag: "Time::Duration".into(),
            payload,
        })
    }
    pub(crate) fn duration_value(&self, value: Handle) -> Result<i64> {
        let Object::Nominal { tag, payload } = self.heap.get(value)? else {
            return Err(RuntimeError::internal("expected Duration"));
        };
        if tag != "Time::Duration" {
            return Err(RuntimeError::internal("expected Duration"));
        }
        i64::try_from(self.as_integer(*payload)?)
            .map_err(|_| RuntimeError::internal("invalid Duration"))
    }
    fn timestamp(&mut self, nanos: i128) -> Result<Handle> {
        let seconds = nanos.div_euclid(NANOS);
        let fraction = nanos.rem_euclid(NANOS);
        let seconds = self.integer(seconds, 64, true)?;
        let fraction = self.integer(fraction, 32, false)?;
        self.allocate(Object::Record(
            [("seconds".into(), seconds), ("nanos".into(), fraction)].into(),
        ))
    }
    pub(crate) fn time_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing time argument"))
        };
        match name {
            "Clock::now" => {
                let now = SystemTime::now();
                let nanos = match now.duration_since(UNIX_EPOCH) {
                    Ok(value) => i128::try_from(value.as_nanos()).ok(),
                    Err(error) => i128::try_from(error.duration().as_nanos())
                        .ok()
                        .and_then(i128::checked_neg),
                }
                .ok_or_else(|| RuntimeError::panic("wall clock out of range"))?;
                if i64::try_from(nanos.div_euclid(NANOS)).is_err() {
                    return Err(RuntimeError::panic("wall clock out of range"));
                }
                self.timestamp(nanos)
            }
            "Time::monotonic" => {
                let elapsed = CLOCK_ORIGIN.get_or_init(Instant::now).elapsed();
                self.allocate(Object::MonotonicInstant {
                    domain: 1,
                    nanos: elapsed.as_nanos(),
                })
            }
            "\0ril.storage.instant_parts" => {
                let Object::MonotonicInstant { domain, nanos } = self.heap.get(arg(0)?)? else {
                    return Err(RuntimeError::internal("expected monotonic instant"));
                };
                let domain = num_bigint::BigInt::from(*domain);
                let nanos = num_bigint::BigInt::from(*nanos);
                let domain = self.allocate(Object::BigInteger(domain))?;
                let nanos = self.allocate(Object::BigInteger(nanos))?;
                self.allocate(Object::Tuple(vec![domain, nanos]))
            }
            "Time::sleep" => {
                let request = crate::host_service::prepare(self, name, args)?;
                crate::host_service::finish(self, request.perform()?)
            }
            _ => Err(RuntimeError::internal("unknown time operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    #[test]
    fn sleep_observes_the_requested_lower_bound_and_rejects_negative() {
        let mut runtime = Runtime::default();
        let negative = runtime.duration(-1).unwrap();
        assert!(runtime.time_builtin("Time::sleep", &[negative]).is_err());
        let requested = runtime.duration(1_000_000).unwrap();
        let start = Instant::now();
        runtime.time_builtin("Time::sleep", &[requested]).unwrap();
        assert!(start.elapsed() >= Duration::from_millis(1));
    }
}
