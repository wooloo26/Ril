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
    fn time_error(&mut self, name: &str) -> Result<Handle> {
        let error = self.variant(&format!("Time::TimeError::{name}"), vec![])?;
        self.variant("Err", vec![error])
    }
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
    fn timestamp_value(&self, value: Handle) -> Result<Option<i128>> {
        let Object::Record(fields) = self.heap.get(value)? else {
            return Err(RuntimeError::internal("expected Timestamp"));
        };
        let seconds = self.as_integer(
            *fields
                .get("seconds")
                .ok_or_else(|| RuntimeError::internal("missing timestamp seconds"))?,
        )?;
        let nanos = self.as_integer(
            *fields
                .get("nanos")
                .ok_or_else(|| RuntimeError::internal("missing timestamp nanos"))?,
        )?;
        Ok(
            (i64::try_from(seconds).is_ok() && (0..NANOS).contains(&nanos))
                .then_some(seconds * NANOS + nanos),
        )
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
            "Time::duration_nanos" => {
                let nanos = i64::try_from(self.as_integer(arg(0)?)?)
                    .map_err(|_| RuntimeError::internal("invalid duration input"))?;
                self.duration(nanos)
            }
            "Time::timestamp" => {
                let seconds = self.as_integer(arg(0)?)?;
                let nanos = self.as_integer(arg(1)?)?;
                if i64::try_from(seconds).is_err() || !(0..NANOS).contains(&nanos) {
                    return self.time_error("OutOfRange");
                }
                let value = self.timestamp(seconds * NANOS + nanos)?;
                self.variant("Ok", vec![value])
            }
            "Time::add" => {
                let Some(base) = self.timestamp_value(arg(0)?)? else {
                    return self.time_error("OutOfRange");
                };
                let nanos = base + i128::from(self.duration_value(arg(1)?)?);
                if i64::try_from(nanos.div_euclid(NANOS)).is_err() {
                    return self.time_error("OutOfRange");
                }
                let value = self.timestamp(nanos)?;
                self.variant("Ok", vec![value])
            }
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
            "Time::elapsed" => {
                let Object::MonotonicInstant {
                    domain: a,
                    nanos: start,
                } = self.heap.get(arg(0)?)?
                else {
                    return Err(RuntimeError::internal("expected Instant"));
                };
                let Object::MonotonicInstant {
                    domain: b,
                    nanos: end,
                } = self.heap.get(arg(1)?)?
                else {
                    return Err(RuntimeError::internal("expected Instant"));
                };
                if a != b {
                    return self.time_error("DifferentClock");
                }
                let Some(nanos) = end
                    .checked_sub(*start)
                    .and_then(|value| i64::try_from(value).ok())
                else {
                    return self.time_error("OutOfRange");
                };
                let duration = self.duration(nanos)?;
                self.variant("Ok", vec![duration])
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
    fn timestamps_normalize_negative_fraction_and_detect_overflow() {
        let mut runtime = Runtime::default();
        let second = runtime.integer(1, 64, true).unwrap();
        let zero = runtime.integer(0, 32, false).unwrap();
        let initial = runtime
            .time_builtin("Time::timestamp", &[second, zero])
            .unwrap();
        let Object::Variant { fields, .. } = runtime.heap.get(initial).unwrap() else {
            panic!("result")
        };
        let initial = fields[0];
        let delta = runtime.duration(-1).unwrap();
        let result = runtime
            .time_builtin("Time::add", &[initial, delta])
            .unwrap();
        let Object::Variant { fields, .. } = runtime.heap.get(result).unwrap() else {
            panic!("result")
        };
        assert_eq!(
            runtime.timestamp_value(fields[0]).unwrap(),
            Some(999_999_999)
        );
        let max = runtime
            .timestamp(i128::from(i64::MAX) * NANOS + NANOS - 1)
            .unwrap();
        let one = runtime.duration(1).unwrap();
        let overflow = runtime.time_builtin("Time::add", &[max, one]).unwrap();
        assert!(
            matches!(runtime.heap.get(overflow).unwrap(), Object::Variant{tag,..} if tag=="Err")
        );
        let negative = runtime.timestamp(-1).unwrap();
        let seconds = runtime.field(negative, "seconds").unwrap();
        let nanos = runtime.field(negative, "nanos").unwrap();
        assert_eq!(runtime.as_integer(seconds).unwrap(), -1);
        assert_eq!(runtime.as_integer(nanos).unwrap(), 999_999_999);
    }
    #[test]
    fn elapsed_rejects_other_domains_backwards_and_unrepresentable_differences() {
        let mut runtime = Runtime::default();
        let start = runtime
            .allocate(Object::MonotonicInstant {
                domain: 1,
                nanos: 10,
            })
            .unwrap();
        for (domain, nanos, error) in [
            (2, 10, "DifferentClock"),
            (1, 9, "OutOfRange"),
            (1, i64::MAX as u128 + 11, "OutOfRange"),
        ] {
            let end = runtime
                .allocate(Object::MonotonicInstant { domain, nanos })
                .unwrap();
            let result = runtime
                .time_builtin("Time::elapsed", &[start, end])
                .unwrap();
            let Object::Variant { tag, fields } = runtime.heap.get(result).unwrap() else {
                panic!("result")
            };
            assert_eq!(tag, "Err");
            assert_eq!(
                runtime.heap.get(fields[0]).unwrap(),
                &Object::Variant {
                    tag: format!("Time::TimeError::{error}"),
                    fields: vec![]
                }
            );
        }
    }
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
