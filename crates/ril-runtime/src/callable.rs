//! Code selection preserves the original environment and retained handler recipes.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use std::collections::BTreeSet;

#[derive(PartialEq, Eq)]
enum CodeIdentity {
    Managed(u64),
    Cps(u64),
    Metered(u64, u64, bool, bool),
}

impl Runtime {
    fn callable_leaf(&self, mut value: Handle) -> Result<Handle> {
        let mut seen = BTreeSet::new();
        loop {
            if !seen.insert(value) {
                return Err(RuntimeError::internal("cyclic callable wrapper"));
            }
            match self.heap.get(value)? {
                Object::RetainedClosure { callable, .. } => value = *callable,
                Object::Closure { .. }
                | Object::CpsClosure { .. }
                | Object::BudgetClosure { .. } => return Ok(value),
                _ => {
                    return Err(RuntimeError::internal(
                        "instantiation requires a native callable",
                    ));
                }
            }
        }
    }

    fn callable_code(&self, value: Handle) -> Result<CodeIdentity> {
        match self.heap.get(self.callable_leaf(value)?)? {
            Object::Closure { function, .. } => Ok(CodeIdentity::Managed(*function)),
            Object::CpsClosure { function, .. } => Ok(CodeIdentity::Cps(*function)),
            Object::BudgetClosure {
                normal,
                metered,
                normal_is_cps,
                metered_entry_event,
                ..
            } => Ok(CodeIdentity::Metered(
                *normal,
                *metered,
                *normal_is_cps,
                *metered_entry_event,
            )),
            _ => Err(RuntimeError::internal("invalid callable leaf")),
        }
    }

    pub(crate) fn instantiate_callable(&mut self, base: Handle, choices: Handle) -> Result<Handle> {
        let code = self.callable_code(base)?;
        let mut selected = None;
        for choice in self.sequence(choices)? {
            let pair = self.sequence(choice)?;
            let [source, target] = pair.as_slice() else {
                return Err(RuntimeError::internal("invalid callable instance mapping"));
            };
            if self.callable_code(*source)? == code {
                if selected.is_some() {
                    return Err(RuntimeError::internal(
                        "ambiguous callable instance mapping",
                    ));
                }
                selected = Some(*target);
            }
        }
        let target = selected
            .ok_or_else(|| RuntimeError::internal("callable has no selected static instance"))?;
        if self.callable_code(target)? == code {
            return Ok(base);
        }
        let mut wrappers = Vec::new();
        let mut leaf = base;
        while let Object::RetainedClosure { callable, recipes } = self.heap.get(leaf)? {
            wrappers.push(recipes.clone());
            leaf = *callable;
        }
        let environment = match self.heap.get(leaf)? {
            Object::Closure { environment, .. }
            | Object::CpsClosure { environment, .. }
            | Object::BudgetClosure { environment, .. } => *environment,
            _ => {
                return Err(RuntimeError::internal(
                    "invalid source callable environment",
                ));
            }
        };
        let selected = match self.heap.get(self.callable_leaf(target)?)? {
            Object::Closure { function, .. } => Object::Closure {
                function: *function,
                environment,
            },
            Object::CpsClosure { function, .. } => Object::CpsClosure {
                function: *function,
                environment,
            },
            Object::BudgetClosure {
                normal,
                metered,
                normal_is_cps,
                metered_entry_event,
                ..
            } => Object::BudgetClosure {
                normal: *normal,
                metered: *metered,
                environment,
                normal_is_cps: *normal_is_cps,
                metered_entry_event: *metered_entry_event,
            },
            _ => {
                return Err(RuntimeError::internal(
                    "invalid callable instance prototype",
                ));
            }
        };
        let mut value = self.allocate(selected)?;
        for recipes in wrappers.into_iter().rev() {
            value = self.allocate(Object::RetainedClosure {
                callable: value,
                recipes,
            })?;
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{budget::Decision, cps::HandlerRecipe};
    use ril_runtime_api::abi::BudgetEvent;
    use std::collections::BTreeMap;

    fn mapping(runtime: &mut Runtime, pairs: &[(Handle, Handle)]) -> Handle {
        let values = pairs
            .iter()
            .map(|(from, to)| runtime.allocate(Object::Tuple(vec![*from, *to])).unwrap())
            .collect();
        runtime.allocate(Object::Tuple(values)).unwrap()
    }

    #[test]
    fn selection_preserves_environment_metered_entries_and_gc_edges() {
        let mut runtime = Runtime::default();
        runtime.enter();
        let environment = runtime.allocate(Object::Record(BTreeMap::new())).unwrap();
        let other = runtime.allocate(Object::Unit).unwrap();
        let base = runtime
            .allocate(Object::Closure {
                function: 11,
                environment,
            })
            .unwrap();
        runtime.heap.register_native_entries(21, 22);
        let prototype = runtime
            .allocate(Object::BudgetClosure {
                normal: 21,
                metered: 22,
                environment: other,
                normal_is_cps: true,
                metered_entry_event: true,
            })
            .unwrap();
        let choices = mapping(&mut runtime, &[(base, prototype)]);
        let selected = runtime.instantiate_callable(base, choices).unwrap();
        runtime.leave(selected);
        runtime.collect().unwrap();
        assert!(runtime.heap.get(base).is_err());
        assert!(runtime.heap.get(environment).is_ok());
        assert!(
            matches!(runtime.heap.get(selected).unwrap(), Object::BudgetClosure {
            normal: 21, metered: 22, environment: env, normal_is_cps: true, metered_entry_event: true,
        } if *env == environment)
        );
    }

    #[test]
    fn selection_keeps_source_recipes_and_does_not_consume_allowance() {
        let mut runtime = Runtime::default();
        let environment = runtime.allocate(Object::Record(BTreeMap::new())).unwrap();
        let leaf = runtime
            .allocate(Object::Closure {
                function: 11,
                environment,
            })
            .unwrap();
        let arm = runtime
            .allocate(Object::Closure {
                function: 31,
                environment,
            })
            .unwrap();
        let base = runtime
            .allocate(Object::RetainedClosure {
                callable: leaf,
                recipes: vec![HandlerRecipe {
                    definition: 9,
                    arms: BTreeMap::from([(7, arm)]),
                }],
            })
            .unwrap();
        let prototype = runtime
            .allocate(Object::CpsClosure {
                function: 21,
                environment,
            })
            .unwrap();
        let choices = mapping(&mut runtime, &[(leaf, prototype)]);
        runtime.budgets.begin(1, environment).unwrap();
        let selected = runtime.instantiate_callable(base, choices).unwrap();
        assert_eq!(
            runtime.budgets.charge(BudgetEvent::FunctionEntry),
            Decision::Execute
        );
        let Object::RetainedClosure { callable, recipes } = runtime.heap.get(selected).unwrap()
        else {
            panic!()
        };
        assert_eq!(recipes[0].definition, 9);
        assert_eq!(recipes[0].arms[&7], arm);
        assert!(
            matches!(runtime.heap.get(*callable).unwrap(), Object::CpsClosure { function: 21, environment: env } if *env == environment)
        );
    }

    #[test]
    fn missing_or_ambiguous_choices_do_not_select_arbitrary_code() {
        let mut runtime = Runtime::default();
        let environment = runtime.allocate(Object::Unit).unwrap();
        let base = runtime
            .allocate(Object::Closure {
                function: 11,
                environment,
            })
            .unwrap();
        let target = runtime
            .allocate(Object::Closure {
                function: 21,
                environment,
            })
            .unwrap();
        let absent = mapping(&mut runtime, &[(target, target)]);
        assert!(runtime.instantiate_callable(base, absent).is_err());
        let duplicate = mapping(&mut runtime, &[(base, base), (base, target)]);
        assert!(runtime.instantiate_callable(base, duplicate).is_err());
        let identity = mapping(&mut runtime, &[(base, base)]);
        assert_eq!(runtime.instantiate_callable(base, identity).unwrap(), base);
    }
}
