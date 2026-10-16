//! Retained handler recipes capture lexical data, never a live continuation.
//! Invocation installs fresh delimiters in the existing native trampoline.
use super::*;
use crate::cps::HandlerRecipe;
#[cfg(test)]
#[path = "ffi_retained_tests.rs"]
mod tests;

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_retain(callable: u64, definitions: u64) -> u64 {
    handle(|runtime| {
        let callable = Handle(callable);
        runtime.heap.get(callable)?;
        let mut recipes = Vec::new();
        for value in runtime.sequence(Handle(definitions))? {
            let definition = runtime.as_integer(value)? as u64;
            let mut cursor = runtime.cps_handlers;
            let table = loop {
                if cursor == Handle::INVALID {
                    return Err(RuntimeError::internal(
                        "retained handler definition is not active",
                    ));
                }
                let Object::CpsHandlerFrame(frame) = runtime.heap.get(cursor)? else {
                    return Err(RuntimeError::internal("invalid retained handler chain"));
                };
                if frame.definition == definition {
                    break frame.table;
                }
                cursor = frame.parent;
            };
            let Object::CpsHandlers(arms) = runtime.heap.get(table)? else {
                return Err(RuntimeError::internal("invalid retained handler table"));
            };
            let mut captured = crate::cps::HandlerTable::new();
            for (operation, arm) in arms.clone() {
                captured.insert(operation, capture_arm(runtime, arm)?);
            }
            recipes.push(HandlerRecipe {
                definition,
                arms: captured,
            });
        }
        runtime.allocate(Object::RetainedClosure { callable, recipes })
    })
}

fn capture_arm(runtime: &mut Runtime, arm: Handle) -> Result<Handle> {
    let mut closure = runtime.heap.get(arm)?.clone();
    let environment = match &mut closure {
        Object::CpsClosure { environment, .. } | Object::BudgetClosure { environment, .. } => {
            environment
        }
        _ => return Err(RuntimeError::internal("retained handler has no native arm")),
    };
    let Object::Record(fields) = runtime.heap.get(*environment)? else {
        return Err(RuntimeError::internal(
            "retained arm environment is not a record",
        ));
    };
    let fields = fields
        .iter()
        .filter(|(key, _)| {
            !matches!(
                key.as_str(),
                "\0ril.cps.continuation"
                    | "\0ril.cps.function-return"
                    | "\0ril.cps.resumption"
                    | "\0ril.cps.activation"
                    | "\0ril.cps.arguments"
            )
        })
        .map(|(key, &value)| (key.clone(), value))
        .collect();
    *environment = runtime.allocate(Object::Record(fields))?;
    runtime.allocate(closure)
}

pub(super) fn dispatch(
    callable: Handle,
    arguments: Handle,
    mut continuation: Handle,
    mut handlers: Handle,
    callback_entry: bool,
) -> Option<u64> {
    let recipe = with_runtime(|runtime| match runtime.heap.get(callable) {
        Ok(Object::RetainedClosure { callable, recipes }) => Some((*callable, recipes.clone())),
        _ => None,
    })?;
    Some(handle(|runtime| {
        for recipe in recipe.1 {
            let delimiter = runtime.allocate(Object::CpsContinuation {
                state: Continuation::Delimiter {
                    outer: continuation,
                    handlers,
                    activation: runtime.cps_activation,
                    resumptions: vec![],
                    budget_depth: runtime.budgets.depth(),
                },
                used: false,
            })?;
            runtime.cps_delimiters.push(delimiter);
            let table = runtime.allocate(Object::CpsHandlers(recipe.arms))?;
            handlers = runtime.allocate(Object::CpsHandlerFrame(HandlerFrame {
                definition: recipe.definition,
                table,
                parent: handlers,
                delimiter,
            }))?;
            continuation = delimiter;
        }
        runtime.allocate(Object::CpsStep(Step::Call {
            callable: recipe.0,
            arguments,
            continuation,
            handlers,
            callback_entry,
        }))
    }))
}
