//! Keep the synchronous compatibility ABI limited to pure cleanup callbacks.
//! CPS bodies register logical cleanup and use the owner exit trampoline.
use super::*;
use std::collections::BTreeMap;

pub(super) fn validate(prepared: &Prepared) -> Result<(), BackendError> {
    let mut bodies = Vec::new();
    let mut pure = BTreeSet::new();
    let mut suspending = BTreeSet::new();
    let mut bound = BTreeSet::new();
    for function in &prepared.functions {
        match &function.body {
            Body::Managed(body) => {
                for parameter in &body.parameters {
                    names(&parameter.pattern, &mut bound);
                }
                pure.insert(body.name.clone());
                bodies.push((body.name.clone(), body.body.clone()));
            }
            Body::Cps(body) => {
                suspending.insert(body.name.clone());
            }
            _ => {}
        }
    }
    let mut scoped = false;
    let mut all_callbacks = Vec::new();
    for (owner, body) in &bodies {
        let mut callbacks = Vec::new();
        let mut definitions = BTreeMap::new();
        statements(
            body,
            &mut scoped,
            &mut callbacks,
            &mut bound,
            &mut definitions,
        );
        visit_block(body, &mut |expr| {
            match &expr.kind {
                ExprKind::Record {
                    members, fields, ..
                } if members.is_empty() => {
                    callbacks.extend(
                        fields
                            .iter()
                            .filter(|(name, _)| name == "on_close")
                            .map(|(_, value)| value.clone()),
                    );
                }
                ExprKind::Record { members, .. } => {
                    callbacks.extend(members.iter().filter_map(|member| match member {
                        core::RecordMember::Field(name, value) if name == "on_close" => {
                            Some(value.clone())
                        }
                        _ => None,
                    }));
                }
                ExprKind::Block(block)
                | ExprKind::Loop { body: block, .. }
                | ExprKind::While { body: block, .. }
                | ExprKind::For { body: block, .. } => statements(
                    block,
                    &mut scoped,
                    &mut callbacks,
                    &mut bound,
                    &mut definitions,
                ),
                _ => {}
            }
            true
        });
        all_callbacks.push((owner, callbacks, definitions));
    }
    if !scoped {
        return Ok(());
    }
    for (owner, callbacks, definitions) in all_callbacks {
        let callables = Callables { prepared, owner };
        for callback in callbacks {
            if !pure_callback(
                &callback,
                &callables,
                &pure,
                &suspending,
                &bound,
                &definitions,
                &mut BTreeSet::new(),
            ) {
                return Err(unsupported(
                    "scoped cleanup callback needs a continuation-aware callback ABI",
                ));
            }
        }
    }
    Ok(())
}

struct Callables<'a> {
    prepared: &'a Prepared,
    owner: &'a str,
}

fn pure_callback(
    callback: &Expr,
    callables: &Callables<'_>,
    pure: &BTreeSet<String>,
    suspending: &BTreeSet<String>,
    bound: &BTreeSet<String>,
    definitions: &BTreeMap<String, Vec<Expr>>,
    visiting: &mut BTreeSet<String>,
) -> bool {
    match &callback.kind {
        ExprKind::Name(name) if name.starts_with("\0ril.cps.value.") => {
            if !visiting.insert(name.clone()) {
                return false;
            }
            let supported = definitions.get(name).is_some_and(|values| {
                !values.is_empty()
                    && values.iter().all(|value| {
                        pure_callback(
                            value,
                            callables,
                            pure,
                            suspending,
                            bound,
                            definitions,
                            visiting,
                        )
                    })
            });
            visiting.remove(name);
            supported
        }
        ExprKind::Name(name) => {
            !bound.contains(name)
                && !suspending.contains(name)
                && (pure.contains(name) || ril_runtime_api::builtins::supported(name))
        }
        ExprKind::Lambda { .. } => callables
            .prepared
            .lambdas
            .get(&callable_key(callables.owner, callback.span))
            .is_some_and(|name| pure.contains(name)),
        _ => false,
    }
}

fn statements(
    block: &core::Block,
    scoped: &mut bool,
    callbacks: &mut Vec<Expr>,
    bound: &mut BTreeSet<String>,
    definitions: &mut BTreeMap<String, Vec<Expr>>,
) {
    for statement in &block.statements {
        if let Statement::Bind { pattern, .. } = statement {
            names(pattern, bound);
        }
        if let Statement::Bind {
            pattern: Pattern::Name(name),
            value,
            ..
        } = statement
            && name.starts_with("\0ril.cps.value.")
        {
            definitions
                .entry(name.clone())
                .or_default()
                .push(value.clone());
        }
        match statement {
            Statement::Bind { scoped: true, .. } => *scoped = true,
            Statement::Assign { target, value, .. } if matches!(&target.kind,ExprKind::Field{field,..}if field=="on_close") => {
                callbacks.push(value.clone())
            }
            _ => {}
        }
    }
}
