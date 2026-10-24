//! Summary identity is reconstructed from the entered frame and invocation.
//! These checks authenticate the claim's owner, not the truth of its rows.
use crate::sema::{SemanticFacts, copy_contract::CopyInvocationStatus, scopes::ScopeOrigin};
use ril_compiler_core::ids::CallableOwner;

pub(crate) fn validate(facts: &SemanticFacts, work: &mut usize) -> Result<(), String> {
    let cost = facts
        .invocations
        .len()
        .checked_mul(2)
        .and_then(|n| n.checked_add(facts.copy_invocations.len()))
        .and_then(|n| n.checked_add(facts.closure_invocations.len()))
        .ok_or("invocation summary identity work overflow")?;
    *work = work
        .checked_sub(cost)
        .ok_or("invocation summary identity exceeds its work bound")?;
    let mut linked = vec![false; facts.invocations.len()];
    for call in &facts.copy_invocations {
        let Some(id) = call.summary else {
            if call.status == CopyInvocationStatus::Completed {
                return Err("completed named call lost its retained invocation summary".into());
            }
            continue;
        };
        let summary = facts
            .invocations
            .get(id.0 as usize)
            .ok_or("named summary is outside its arena")?;
        let context = summary
            .context
            .ok_or("named summary lost its actual context")?;
        let scope = summary
            .activation
            .and_then(|id| facts.scopes.get(&id))
            .ok_or("named summary lost its entered frame")?;
        if std::mem::replace(&mut linked[id.0 as usize], true)
            || context.invocation != Some(call.id)
            || context.owner != Some(CallableOwner::Function(call.target))
            || context.closure_invocation != call.entry.caller_context.closure_invocation
            || context.closure != call.entry.caller_context.closure
            || !matches!(scope.origin, ScopeOrigin::Named(id) if id == call.id)
        {
            return Err("named invocation summary borrowed another call, owner or frame".into());
        }
    }
    for call in &facts.closure_invocations {
        let Some(id) = call.summary else {
            if call.status == CopyInvocationStatus::Completed {
                return Err("completed closure call lost its retained invocation summary".into());
            }
            continue;
        };
        let summary = facts
            .invocations
            .get(id.0 as usize)
            .ok_or("closure summary is outside its arena")?;
        let context = summary
            .context
            .ok_or("closure summary lost its actual context")?;
        let scope = summary
            .activation
            .and_then(|id| facts.scopes.get(&id))
            .ok_or("closure summary lost its entered frame")?;
        let site = facts
            .closures
            .get(call.closure)
            .and_then(|closure| closure.site)
            .ok_or("closure summary lost its original closure object")?;
        if std::mem::replace(&mut linked[id.0 as usize], true)
            || context.invocation != call.parent_named
            || context.closure_invocation != Some(call.id)
            || context.closure != Some(call.closure)
            || context.owner != Some(CallableOwner::Lambda(site))
            || Some(scope.id) != call.activation
            || !matches!(scope.origin, ScopeOrigin::Closure(id) if id == call.id)
        {
            return Err("closure invocation summary borrowed another call, object or frame".into());
        }
    }
    if linked.iter().any(|linked| !linked) {
        return Err("retained invocation summary has no unique entered call".into());
    }
    Ok(())
}
