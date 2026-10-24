//! Solver visits may create different closure objects with the same immutable
//! abstract environment. Compare their summaries without replacing object IDs,
//! captured bindings, allocation identities or invocation records.
use super::*;
use crate::sema::source_types::{SourceTypesError, WorkLimit};

impl Checker {
    pub(in crate::sema::checker) fn same_loop_value(
        &self,
        left: &Value,
        right: &Value,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        fn callable(
            checker: &Checker,
            left: &Callable,
            right: &Callable,
            seen: &mut BTreeSet<(usize, usize)>,
            work: &mut WorkLimit,
        ) -> Result<bool, SourceTypesError> {
            work.charge(1)?;
            if left == right {
                return Ok(true);
            }
            let (Callable::Closure(left), Callable::Closure(right)) = (left, right) else {
                return Ok(false);
            };
            let a = &checker.closures[*left];
            let b = &checker.closures[*right];
            work.charge(
                a.captures.len() + b.captures.len() + a.parameters.len() + b.parameters.len(),
            )?;
            if a.site.is_none()
                || a.site != b.site
                || a.handler_context != b.handler_context
                || !a.writes.is_empty()
                || !b.writes.is_empty()
                || a.parameters != b.parameters
                || a.contract.annotations != b.contract.annotations
                || *std::ops::Deref::deref(&a.contract.typing_environment)
                    != *std::ops::Deref::deref(&b.contract.typing_environment)
                || (!a.contract.annotations.is_empty()
                    && a.contract.typing_environment.contract_bindings()
                        != b.contract.typing_environment.contract_bindings())
                || a.captures.len() != b.captures.len()
            {
                return Ok(false);
            }
            if !seen.insert((*left, *right)) {
                return Ok(true);
            }
            let result = (|| {
                for (left, right) in a.captures.iter().zip(&b.captures) {
                    let left = &checker.bindings[*left];
                    let right = &checker.bindings[*right];
                    if left.pattern != right.pattern
                        || left.mode != right.mode
                        || !value(checker, &left.value, &right.value, seen, work)?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            })();
            seen.remove(&(*left, *right));
            result
        }
        fn value(
            checker: &Checker,
            left: &Value,
            right: &Value,
            seen: &mut BTreeSet<(usize, usize)>,
            work: &mut WorkLimit,
        ) -> Result<bool, SourceTypesError> {
            work.charge(2 + left.callables.len() + right.callables.len())?;
            if left.same_abstract_value(right) {
                return Ok(true);
            }
            // Mutable and observing environments retain their separate access
            // domains. Equivalence cannot erase their authority correlations.
            if left.mutable_environment
                || right.mutable_environment
                || left.observer_environment
                || right.observer_environment
            {
                return Ok(false);
            }
            for (candidates, other) in [
                (&left.callables, &right.callables),
                (&right.callables, &left.callables),
            ] {
                for candidate in candidates {
                    let mut found = false;
                    for alternative in other {
                        if callable(checker, candidate, alternative, seen, work)? {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Ok(false);
                    }
                }
            }
            match (&left.signature, &right.signature) {
                (Some(a), Some(b))
                    if a.parameters == b.parameters
                        && *std::ops::Deref::deref(&a.environment)
                            == *std::ops::Deref::deref(&b.environment) => {}
                (None, None) => {}
                _ => return Ok(false),
            }
            let mut right = right.clone();
            right.callables.clone_from(&left.callables);
            right.signature.clone_from(&left.signature);
            for (a, b) in [
                (&left.option_payload, &mut right.option_payload),
                (&left.variant_payload, &mut right.variant_payload),
                (&left.result_payload, &mut right.result_payload),
                (&left.result_success, &mut right.result_success),
                (&left.result_error, &mut right.result_error),
            ] {
                match (a.as_deref(), b.as_deref_mut()) {
                    (Some(a), Some(b)) if value(checker, a, b, seen, work)? => {
                        *b = a.clone();
                    }
                    (None, None) => {}
                    _ => return Ok(false),
                }
            }
            if !left
                .variant_witnesses
                .keys()
                .eq(right.variant_witnesses.keys())
            {
                return Ok(false);
            }
            for (tag, a) in &left.variant_witnesses {
                let b = right.variant_witnesses.get_mut(tag).unwrap();
                if !value(checker, a, b, seen, work)? {
                    return Ok(false);
                }
                b.clone_from(a);
            }
            Ok(left.same_abstract_value(&right))
        }
        value(self, left, right, &mut BTreeSet::new(), work)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn immutable_closure_summaries_keep_capture_values_and_object_identities() {
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/regressions/evaluation-identity.ril::closure-objects-share-lexical-site",
        ));
        assert!(parsed.is_ok());
        let mut checker = Checker::new(FileId(0));
        checker.run(&parsed.program);
        assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
        assert!(checker.unsupported.is_empty(), "{:?}", checker.unsupported);
        let instance = |number| {
            checker
                .closures
                .iter()
                .enumerate()
                .find_map(|(id, closure)| {
                    closure
                        .captures
                        .iter()
                        .any(|binding| {
                            let binding = &checker.bindings[*binding];
                            binding.name == "base"
                                && binding.value.constant == Some(Constant::Integer(number))
                        })
                        .then_some(id)
                })
                .unwrap()
        };
        let ten = instance(10);
        let twenty = instance(20);
        assert_ne!(ten, twenty);
        assert_eq!(checker.closures[ten].site, checker.closures[twenty].site);
        let repeated = checker.closures.len();
        checker.closures.push(checker.closures[ten].clone());
        let packet = |id| {
            let mut value = Value::scalar(
                Ty::Callable(vec![Ty::Int("int".into())], Box::new(Ty::Int("int".into()))),
                None,
                CauseId(0),
            );
            value.callables.push(Callable::Closure(id));
            value
        };
        let left = packet(ten);
        let same = packet(repeated);
        let distinct = packet(twenty);
        let mut work = WorkLimit::new(8192);
        assert!(checker.same_loop_value(&left, &same, &mut work).unwrap());
        assert!(
            !checker
                .same_loop_value(&left, &distinct, &mut work)
                .unwrap()
        );
        let mut mutable = same.clone();
        mutable.mutable_environment = true;
        assert!(!checker.same_loop_value(&left, &mutable, &mut work).unwrap());
        assert!(
            checker
                .same_loop_value(&left, &same, &mut WorkLimit::new(0))
                .is_err()
        );
        assert_eq!(left.callables, vec![Callable::Closure(ten)]);
        assert_eq!(same.callables, vec![Callable::Closure(repeated)]);
    }
}
