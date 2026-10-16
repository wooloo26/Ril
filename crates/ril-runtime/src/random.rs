//! Reproducible SplitMix64 state and the independent host entropy boundary.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};

fn draw(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let z = (*state ^ (*state >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    let w = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    w ^ (w >> 31)
}

impl Runtime {
    pub(crate) fn random_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing random argument"))
        };
        match name {
            "Random::seeded" => {
                let seed = u64::try_from(self.as_integer(arg(0)?)?)
                    .map_err(|_| RuntimeError::internal("expected u64 seed"))?;
                self.allocate(Object::RandomState(seed))
            }
            "Random::next_u64" | "Random::below" => {
                // Validate the bound before drawing, including on a zero bound.
                let upper = if name == "Random::below" {
                    let upper = u64::try_from(self.as_integer(arg(1)?)?)
                        .map_err(|_| RuntimeError::internal("expected u64 bound"))?;
                    if upper == 0 {
                        return Err(RuntimeError::panic("zero random upper bound"));
                    }
                    Some(upper)
                } else {
                    None
                };
                let Object::RandomState(state) = self.heap.get_mut(arg(0)?)? else {
                    return Err(RuntimeError::internal("expected random generator"));
                };
                let value = if let Some(upper) = upper {
                    let threshold = upper.wrapping_neg() % upper;
                    loop {
                        let value = draw(state);
                        if value >= threshold {
                            break value % upper;
                        }
                    }
                } else {
                    draw(state)
                };
                self.integer(i128::from(value), 64, false)
            }
            "Random::entropy" => {
                let request = crate::host_service::prepare(self, name, args)?;
                crate::host_service::finish(self, request.perform()?)
            }
            _ => Err(RuntimeError::internal("unknown random operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known_sequence_clone_and_rejected_bound_preserve_state() {
        let mut runtime = Runtime::default();
        let seed = runtime.integer(0, 64, false).unwrap();
        let rng = runtime.random_builtin("Random::seeded", &[seed]).unwrap();
        let first = runtime.random_builtin("Random::next_u64", &[rng]).unwrap();
        assert_eq!(runtime.as_integer(first).unwrap(), 0xe220a8397b1dcdaf);
        assert!(
            runtime
                .random_builtin("Random::below", &[rng, seed])
                .is_err()
        );
        let copy = runtime.copy(rng).unwrap();
        let a = runtime.random_builtin("Random::next_u64", &[rng]).unwrap();
        let b = runtime.random_builtin("Random::next_u64", &[copy]).unwrap();
        assert_eq!(runtime.as_integer(a).unwrap(), 0x6e789e6aa1b965f4);
        assert!(runtime.heap.structurally_equal(a, b).unwrap());
        runtime.random_builtin("Random::next_u64", &[rng]).unwrap();
        assert_ne!(
            runtime.heap.get(rng).unwrap(),
            runtime.heap.get(copy).unwrap()
        );
        let upper = runtime
            .integer(i128::from((1u64 << 63) + 1), 64, false)
            .unwrap();
        for _ in 0..128 {
            let value = runtime
                .random_builtin("Random::below", &[rng, upper])
                .unwrap();
            assert!(runtime.as_integer(value).unwrap() < (1i128 << 63) + 1);
        }
    }
    #[test]
    fn entropy_zero_and_negative_have_distinct_outcomes() {
        let mut runtime = Runtime::default();
        let zero = runtime.int(0).unwrap();
        let empty = runtime.random_builtin("Random::entropy", &[zero]).unwrap();
        let Object::Variant { tag, fields } = runtime.heap.get(empty).unwrap() else {
            panic!("result")
        };
        assert_eq!(tag, "Ok");
        assert_eq!(
            runtime.heap.get(fields[0]).unwrap(),
            &Object::Bytes(vec![].into())
        );
        let negative = runtime.int(-1).unwrap();
        assert!(
            runtime
                .random_builtin("Random::entropy", &[negative])
                .is_err()
        );
    }
}
