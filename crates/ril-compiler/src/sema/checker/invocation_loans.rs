use super::super::invocation_loans::{self as domain, InvocationLoanEnd, InvocationLoanStart};
use super::*;

impl Checker {
    pub(super) fn start_invocation_loan(
        &mut self,
        loan: LoanId,
        source: &Value,
        frame: &Frame,
        parameter: usize,
        retained: bool,
        span: Span,
    ) {
        self.invocation_loan_starts.push(InvocationLoanStart {
            loan,
            activation: frame.owner,
            owner: frame.callable_owner,
            named: self.copy_invocation_stack.last().copied(),
            closure: self.closure_invocation_stack.last().copied(),
            parameter: parameter as u32,
            retained,
            origins: source.origins.clone(),
            source: source.clone(),
            parents: source.participants.clone(),
            bindings: BTreeSet::new(),
            allocation_epoch: self.recency_moves.len(),
            cause: source.cause,
            span,
        });
    }

    pub(super) fn end_invocation_loans(
        &mut self,
        result: &mut Value,
        frame: &Frame,
        loans: &BTreeMap<LoanId, BTreeSet<Participant>>,
        span: Span,
    ) {
        if loans.is_empty() {
            return;
        }
        for start in &mut self.invocation_loan_starts {
            if loans.contains_key(&start.loan) {
                start.bindings = frame
                    .locals
                    .iter()
                    .copied()
                    .filter(|id| {
                        let binding = &self.bindings[*id];
                        binding.parameter
                            && binding
                                .value
                                .participants
                                .contains(&Participant::Loan(start.loan))
                    })
                    .collect();
            }
        }
        let mut candidate = self.ended_invocation_loans.clone();
        candidate.extend(loans.clone());
        if loans
            .keys()
            .any(|loan| domain::normalize(&[Participant::Loan(*loan)].into(), &candidate).is_err())
        {
            self.unsupported(
                span,
                "invocation loan end contains a cyclic participant mapping",
            );
            return;
        }
        let cause = self.cause(
            CauseKind::Call,
            span,
            "actual invocation ends only its local formal borrowing participants",
            [result.cause],
        );
        self.invocation_loan_ends.push(InvocationLoanEnd {
            activation: frame.owner,
            owner: frame.callable_owner,
            named: self.copy_invocation_stack.last().copied(),
            closure: self.closure_invocation_stack.last().copied(),
            loans: loans.clone(),
            cause,
            span,
        });
        self.ended_invocation_loans = candidate;
        for binding in &mut self.bindings {
            domain::normalize_value(&mut binding.value, &self.ended_invocation_loans);
        }
        for value in self.fields.values_mut() {
            domain::normalize_value(value, &self.ended_invocation_loans);
        }
        domain::normalize_value(result, &self.ended_invocation_loans);
    }
}
