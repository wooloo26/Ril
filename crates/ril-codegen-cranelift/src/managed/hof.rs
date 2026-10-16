//! A pure runtime builtin cannot invoke a native CPS callback. Structured Core
//! expansion removes supported direct calls before this availability check.
use super::*;

pub(super) fn validate(prepared: &Prepared) -> Result<(), BackendError> {
    // The bootstrap continuation alone does not make ordinary callbacks CPS.
    if !prepared
        .functions
        .iter()
        .any(|function| matches!(&function.body, Body::Cps(graph) if canonical_owner(&graph.name) != native::GLOBAL_INITIALIZER))
    {
        return Ok(());
    }
    let names: BTreeSet<_> = prepared
        .functions
        .iter()
        .filter_map(|function| match &function.body {
            Body::Managed(body) => Some(body.name.as_str()),
            Body::Cps(body) => Some(body.name.as_str()),
            _ => None,
        })
        .collect();
    let mut unavailable = None;
    for function in &prepared.functions {
        let body = match &function.body {
            Body::Managed(body) => body.body.clone(),
            Body::Cps(body) => core::Block {
                statements: body
                    .blocks
                    .iter()
                    .flat_map(|block| block.instructions.iter().flat_map(cps_statements))
                    .collect(),
            },
            _ => continue,
        };
        visit_block(&body, &mut |expression| {
            if let ExprKind::Name(name) = &expression.kind
                && !names.contains(name.as_str())
                && requires_callback_bridge(name)
            {
                unavailable = Some(name.clone());
            }
            true
        });
    }
    if let Some(name) = unavailable {
        return Err(unsupported(format!(
            "higher-order builtin {name} requires structured continuation lowering for this callback context"
        )));
    }
    Ok(())
}
fn requires_callback_bridge(name: &str) -> bool {
    let name = name.strip_prefix("Prelude::").unwrap_or(name);
    let name = ril_runtime_api::builtins::canonical_builtin(name).unwrap_or(name);
    matches!(
        name,
        "Array::map"
            | "Array::filter"
            | "Array::fold"
            | "Array::find"
            | "Array::any"
            | "Array::all"
            | "Array::for_each"
            | "Options::map"
            | "Options::and_then"
            | "Options::unwrap_or_else"
            | "Results::map"
            | "Results::map_err"
            | "Results::and_then"
            | "Results::recover"
            | "Order::sorted"
            | "Order::binary_search"
            | "Heap::new"
            | "Heap::push"
            | "Heap::pop"
            | "File::with_file"
            | "Process::with_child"
            | "Io::read_all"
            | "Io::write_all"
    )
}
