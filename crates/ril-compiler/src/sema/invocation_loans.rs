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
