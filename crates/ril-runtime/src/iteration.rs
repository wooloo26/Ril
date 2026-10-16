//! Streaming iteration never computes a range cardinality or a successor past
//! its final value. Bigint and full fixed-width domains use the same cursor.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use num_traits::One;
impl Runtime {
    pub fn iterator_next(&mut self, cursor: Handle) -> Result<Option<Handle>> {
        let (source, index, next, range_next, exhausted) = match self.heap.get(cursor)? {
            Object::Iterator {
                source,
                index,
                next,
                range_next,
                exhausted,
            } => (*source, *index, *next, *range_next, *exhausted),
            _ => return Err(RuntimeError::internal("expected native iterator")),
        };
        if exhausted {
            return Ok(None);
        }
        let mut successor = None;
        let mut range_successor = None;
        let result = match self.heap.get(source)? {
            Object::Map(entries) | Object::Set(entries) => {
                if let Some(slot) = next {
                    let (key, value, after) = entries.slot(slot).ok_or_else(|| {
                        RuntimeError::internal("collection changed during iteration")
                    })?;
                    successor = after;
                    Some(if matches!(self.heap.get(source)?, Object::Map(_)) {
                        self.allocate(Object::Tuple(vec![key, value]))?
                    } else {
                        key
                    })
                } else {
                    None
                }
            }
            Object::Array(values) => usize::try_from(index)
                .ok()
                .and_then(|index| values.get(index).copied()),
            Object::ArrayWindow { .. } => {
                let values = self
                    .heap
                    .array_elements(source)?
                    .ok_or_else(|| RuntimeError::internal("invalid array window"))?;
                usize::try_from(index)
                    .ok()
                    .and_then(|index| values.get(index).copied())
            }
            Object::Range {
                upper: Some(upper),
                inclusive,
                ..
            } => {
                let (upper, inclusive) = (*upper, *inclusive);
                if let Some(current) = range_next {
                    let order = match (self.heap.get(current)?, self.heap.get(upper)?) {
                        (
                            Object::Integer {
                                value: a,
                                bits: a_bits,
                                signed: a_signed,
                            },
                            Object::Integer {
                                value: b,
                                bits: b_bits,
                                signed: b_signed,
                            },
                        ) if a_bits == b_bits && a_signed == b_signed => a.cmp(b),
                        (Object::BigInteger(a), Object::BigInteger(b)) => a.cmp(b),
                        _ => return Err(RuntimeError::internal("incompatible range endpoints")),
                    };
                    if order.is_gt() || order.is_eq() && !inclusive {
                        None
                    } else {
                        if order.is_lt() {
                            range_successor = Some(match self.heap.get(current)?.clone() {
                                Object::Integer {
                                    value,
                                    bits,
                                    signed,
                                } => self.integer(
                                    value.checked_add(1).ok_or_else(|| {
                                        RuntimeError::internal(
                                            "range successor exceeded its upper bound",
                                        )
                                    })?,
                                    bits,
                                    signed,
                                )?,
                                Object::BigInteger(value) => self.allocate(Object::BigInteger(
                                    value + num_bigint::BigInt::one(),
                                ))?,
                                _ => unreachable!(),
                            });
                        }
                        Some(current)
                    }
                } else {
                    None
                }
            }
            _ => {
                return Err(RuntimeError::internal(
                    "inadmissible implicit iteration source",
                ));
            }
        };
        if let Some(value) = result {
            self.keep_temporary(value);
        }
        let is_range = matches!(self.heap.get(source)?, Object::Range { .. });
        *self.heap.get_mut(cursor)? = Object::Iterator {
            source,
            index: index.saturating_add(1),
            next: successor,
            range_next: range_successor,
            exhausted: result.is_none() || is_range && range_successor.is_none(),
        };
        Ok(result)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn full_width_and_bigint_ranges_start_without_computing_their_cardinality() {
        let mut runtime = Runtime::default();
        for (lower, upper) in [(i64::MIN as i128, i64::MAX as i128), (0, u64::MAX as i128)] {
            let signed = lower < 0;
            let a = runtime.integer(lower, 64, signed).unwrap();
            let b = runtime.integer(upper, 64, signed).unwrap();
            let range = runtime
                .allocate(Object::Range {
                    lower: Some(a),
                    upper: Some(b),
                    inclusive: true,
                })
                .unwrap();
            let cursor = runtime.iterator(range).unwrap();
            for offset in 0..3 {
                let item = runtime.iterator_next(cursor).unwrap().unwrap();
                assert_eq!(runtime.as_integer(item).unwrap(), lower + offset);
            }
        }
        let large: num_bigint::BigInt = num_bigint::BigInt::one() << 256usize;
        let a = runtime.allocate(Object::BigInteger(large.clone())).unwrap();
        let b = runtime.allocate(Object::BigInteger(&large + 1)).unwrap();
        let range = runtime
            .allocate(Object::Range {
                lower: Some(a),
                upper: Some(b),
                inclusive: true,
            })
            .unwrap();
        let cursor = runtime.iterator(range).unwrap();
        runtime.root(1, cursor).unwrap();
        assert_eq!(runtime.iterator_next(cursor).unwrap(), Some(a));
        runtime.statement_end();
        runtime.collect().unwrap();
        let next = runtime.iterator_next(cursor).unwrap().unwrap();
        assert_eq!(
            runtime.heap.get(next).unwrap(),
            &Object::BigInteger(large + 1)
        );
        assert_eq!(runtime.iterator_next(cursor).unwrap(), None);
    }
    #[test]
    fn the_last_fixed_value_is_emitted_once_without_successor_overflow() {
        let mut runtime = Runtime::default();
        let maximum = runtime.integer(u64::MAX as i128, 64, false).unwrap();
        let range = runtime
            .allocate(Object::Range {
                lower: Some(maximum),
                upper: Some(maximum),
                inclusive: true,
            })
            .unwrap();
        let cursor = runtime.iterator(range).unwrap();
        assert_eq!(runtime.iterator_next(cursor).unwrap(), Some(maximum));
        assert_eq!(runtime.iterator_next(cursor).unwrap(), None);
        let empty = runtime
            .allocate(Object::Range {
                lower: Some(maximum),
                upper: Some(maximum),
                inclusive: false,
            })
            .unwrap();
        let cursor = runtime.iterator(empty).unwrap();
        assert_eq!(runtime.iterator_next(cursor).unwrap(), None);
    }
}
