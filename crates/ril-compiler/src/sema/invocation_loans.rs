//! Formal borrowing ends at its actual invocation boundary. Captured values
//! retain their source authority, not an indefinitely active callee participant.
use super::{
    copy_templates::InstanceId,
    effect_identity::ClosureInvocationId,
    facts::{LoanId, Participant, ScopeId},
    model::{Origins, Value},
};
use ril_compiler_core::{diagnostic::CauseId, ids::CallableOwner, source::Span};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct InvocationLoanStart {
    pub loan: LoanId,
    pub activation: ScopeId,
    pub owner: Option<CallableOwner>,
    pub named: Option<InstanceId>,
    pub closure: Option<ClosureInvocationId>,
    pub parameter: u32,
    pub retained: bool,
    pub origins: Origins,
    pub source: Value,
    pub parents: BTreeSet<Participant>,
    pub bindings: BTreeSet<usize>,
    pub allocation_epoch: usize,
    pub cause: CauseId,
    pub span: Span,
}

pub fn validate(facts: &super::SemanticFacts) -> Result<(), (Span, Option<CauseId>, String)> {
    use super::copy_contract::CopyInvocationStatus;
    let mut starts = BTreeMap::new();
    for start in &facts.invocation_loan_starts {
        let fail = |message: &str| (start.span, Some(start.cause), message.to_owned());
        if starts.insert(start.loan, start).is_some()
            || facts.loan_parents.get(&start.loan) != Some(&start.parents)
            || start.source.participants != start.parents
            || start.source.origins != start.origins
            || !facts.scopes.contains(&start.activation)
            || start.allocation_epoch > facts.allocation_history.len()
            || start.bindings.iter().any(|id| {
                facts
                    .bindings
                    .get(*id)
                    .is_none_or(|binding| !binding.parameter || binding.owner != start.activation)
            })
        {
            return Err(fail(
                "formal loan entry does not match its actual source and loan registry",
            ));
        }
        let mode = match start.owner {
            Some(CallableOwner::Function(owner)) => {
                start
                    .named
                    .and_then(|id| facts.copy_invocations.get(id.0 as usize))
                    .filter(|call| {
                        Some(call.id) == start.named
                            && call.target == owner
                            && call.status == CopyInvocationStatus::Completed
                    })
                    .ok_or_else(|| {
                        fail("formal loan has no matching completed named invocation")
                    })?;
                facts
                    .functions
                    .iter()
                    .find(|function| function.definition == owner)
                    .and_then(|function| function.syntax.parameters.get(start.parameter as usize))
                    .map(|parameter| parameter.mode)
            }
            Some(CallableOwner::Lambda(site)) => {
                let call = start
                    .closure
                    .and_then(|id| facts.closure_invocations.get(id.0 as usize))
                    .filter(|call| {
                        Some(call.id) == start.closure
                            && call.parent_named == start.named
                            && call.status == CopyInvocationStatus::Completed
                    })
                    .ok_or_else(|| {
                        fail("formal loan has no matching completed closure invocation")
                    })?;
                facts
                    .closures
                    .get(call.closure)
                    .filter(|closure| closure.site == Some(site))
                    .and_then(|closure| closure.parameters.get(start.parameter as usize))
                    .map(|parameter| parameter.mode)
            }
            _ => None,
        };
        if mode
            != Some(if start.retained {
                ril_syntax::ast::ParameterMode::SharedMut
            } else {
                ril_syntax::ast::ParameterMode::Mut
            })
        {
            return Err(fail(
                "formal loan parameter or lexical owner differs from the declaration",
            ));
        }
    }
    let mut ended = BTreeMap::new();
    for end in &facts.invocation_loan_ends {
        let fail = |message: &str| (end.span, Some(end.cause), message.to_owned());
        if end.loans.is_empty() || !facts.scopes.contains(&end.activation) {
            return Err(fail("invocation loan end has no actual local loans"));
        }
        for (loan, parents) in &end.loans {
            let start = starts
                .get(loan)
                .ok_or_else(|| fail("invocation loan end has no formal entry"))?;
            if start.activation != end.activation
                || start.owner != end.owner
                || start.named != end.named
                || start.closure != end.closure
                || start.parents != *parents
                || ended.insert(*loan, parents.clone()).is_some()
            {
                return Err(fail(
                    "invocation loan end differs from its exact entry context",
                ));
            }
            if normalize(&[Participant::Loan(*loan)].into(), &ended).is_err() {
                return Err(fail("invocation loan ends form a cycle"));
            }
        }
    }
    for (loan, start) in starts {
        if !ended.contains_key(&loan) {
            return Err((
                start.span,
                Some(start.cause),
                "completed invocation did not end its formal loan".into(),
            ));
        }
    }
    for call in &facts.copy_invocations {
        if call.status != CopyInvocationStatus::Completed {
            continue;
        }
        let Some(function) = facts
            .functions
            .iter()
            .find(|function| function.definition == call.target)
        else {
            return Err((
                call.span,
                None,
                "completed named invocation has no declaration".into(),
            ));
        };
        for (index, parameter) in function.syntax.parameters.iter().enumerate() {
            if parameter.mode == ril_syntax::ast::ParameterMode::Read {
                continue;
            }
            if facts
                .invocation_loan_starts
                .iter()
                .filter(|start| {
                    start.owner == Some(CallableOwner::Function(call.target))
                        && start.named == Some(call.id)
                        && start.parameter == index as u32
                })
                .count()
                != 1
            {
                return Err((
                    call.span,
                    None,
                    "completed named invocation lacks its unique formal loan entry".into(),
                ));
            }
        }
    }
    for call in &facts.closure_invocations {
        if call.status != CopyInvocationStatus::Completed {
            continue;
        }
        let Some(closure) = facts.closures.get(call.closure) else {
            return Err((
                call.site,
                None,
                "completed closure invocation has no object".into(),
            ));
        };
        for (index, parameter) in closure.parameters.iter().enumerate() {
            if parameter.mode == ril_syntax::ast::ParameterMode::Read {
                continue;
            }
            if facts
                .invocation_loan_starts
                .iter()
                .filter(|start| {
                    start.owner == closure.site.map(CallableOwner::Lambda)
                        && start.closure == Some(call.id)
                        && start.parameter == index as u32
                })
                .count()
                != 1
            {
                return Err((
                    call.site,
                    None,
                    "completed closure invocation lacks its unique formal loan entry".into(),
                ));
            }
        }
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct InvocationLoanEnd {
    pub activation: ScopeId,
    pub owner: Option<CallableOwner>,
    pub named: Option<InstanceId>,
    pub closure: Option<ClosureInvocationId>,
    pub loans: BTreeMap<LoanId, BTreeSet<Participant>>,
    pub cause: CauseId,
    pub span: Span,
}

/// Only explicitly ended loans are replaced. Unknown or still-active loans
/// remain independent participants; malformed cycles are never erased.
pub fn normalize(
    participants: &BTreeSet<Participant>,
    ended: &BTreeMap<LoanId, BTreeSet<Participant>>,
) -> Result<BTreeSet<Participant>, LoanId> {
    fn visit(
        participant: Participant,
        ended: &BTreeMap<LoanId, BTreeSet<Participant>>,
        active: &mut BTreeSet<LoanId>,
        output: &mut BTreeSet<Participant>,
    ) -> Result<(), LoanId> {
        if let Participant::Loan(loan) = participant
            && let Some(parents) = ended.get(&loan)
        {
            if !active.insert(loan) {
                return Err(loan);
            }
            for parent in parents {
                visit(*parent, ended, active, output)?;
            }
            active.remove(&loan);
        } else {
            output.insert(participant);
        }
        Ok(())
    }
    let mut output = BTreeSet::new();
    for participant in participants {
        visit(*participant, ended, &mut BTreeSet::new(), &mut output)?;
    }
    Ok(output)
}

pub(crate) fn normalize_value(value: &mut Value, ended: &BTreeMap<LoanId, BTreeSet<Participant>>) {
    if let Ok(participants) = normalize(&value.participants, ended) {
        value.participants = participants;
    }
    for nested in [
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.option_payload,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        normalize_value(nested, ended);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::facts::RootId;
    #[test]
    fn ending_one_reborrow_preserves_active_parent_and_unrelated_ambient_roots() {
        let ended = [(LoanId(2), [Participant::Loan(LoanId(1))].into())].into();
        let input = [
            Participant::Loan(LoanId(2)),
            Participant::Root(RootId(7)),
            Participant::Loan(LoanId(3)),
        ]
        .into();
        assert_eq!(
            normalize(&input, &ended).unwrap(),
            [
                Participant::Loan(LoanId(1)),
                Participant::Root(RootId(7)),
                Participant::Loan(LoanId(3))
            ]
            .into()
        );
        let mut ended = ended;
        ended.insert(LoanId(1), [Participant::Root(RootId(4))].into());
        assert_eq!(
            normalize(&input, &ended).unwrap(),
            [
                Participant::Root(RootId(4)),
                Participant::Root(RootId(7)),
                Participant::Loan(LoanId(3))
            ]
            .into()
        );
        ended.insert(LoanId(1), [Participant::Loan(LoanId(2))].into());
        assert!(normalize(&input, &ended).is_err());
    }

    #[test]
    fn nested_transport_changes_only_ended_participants_not_authority_or_duties() {
        use crate::sema::{
            copy_contract::CopyBoundaryId,
            facts::{NodeId, Permission},
            model::Ty,
        };
        let mut source = Value::scalar(Ty::Unknown, None, CauseId(9));
        source.origins = Origins::one(NodeId(8));
        source.participants = [Participant::Loan(LoanId(2))].into();
        source.permission = Permission::Write;
        source.temporary = true;
        source.scoped.insert(7);
        source.results.insert(11);
        source.must_results.insert(11);
        source.pending_copies.insert(CopyBoundaryId(4));
        let mut outer = source.clone();
        outer.option_payload = Some(Box::new(source.clone()));
        outer.result_error = Some(Box::new(source.clone()));
        outer
            .variant_witnesses
            .insert("Item".into(), Box::new(source.clone()));
        let mut expected = outer.clone();
        let parent: BTreeSet<Participant> = [Participant::Loan(LoanId(1))].into();
        expected.participants = parent.clone();
        expected.option_payload.as_mut().unwrap().participants = parent.clone();
        expected.result_error.as_mut().unwrap().participants = parent.clone();
        expected
            .variant_witnesses
            .get_mut("Item")
            .unwrap()
            .participants = parent.clone();
        normalize_value(&mut outer, &[(LoanId(2), parent)].into());
        assert_eq!(outer, expected);
    }
}
