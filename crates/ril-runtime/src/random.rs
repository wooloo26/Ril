//! Reproducible SplitMix64 state and the independent host entropy boundary.
use crate::{
    heap::Handle,
    value::{Result, Runtime, RuntimeError},
};

impl Runtime {
    pub(crate) fn random_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        match name {
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
    use crate::heap::Object;
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
