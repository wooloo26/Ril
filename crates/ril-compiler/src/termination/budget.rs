//! Budget termination consumes source coverage certificates. Neither an empty
//! effect row nor the spelling of a callable supplies a coverage certificate.
use super::*;
use crate::sema::BudgetProof;
use ril_compiler_core::diagnostic::CauseId;

#[derive(Debug, Clone)]
pub struct BudgetTerminationWitness {
    pub span: Span,
    pub cause: CauseId,
    pub exhaustion_operation: u64,
    pub callee_coverage: Vec<CauseId>,
    pub cleanup_coverage: Vec<CauseId>,
    /// The callee and written arguments are evaluated before the boundary.
    pub explicit_evaluation: Judgment,
    /// This judgment is audited, but its divergence is covered by the budget.
    pub action_invocation: Judgment,
    /// Recovery executes after the exhausted budget has been removed.
    pub recovery: Judgment,
}

fn same_evidence(left: &BudgetProof, right: &BudgetProof) -> bool {
    let set = |causes: &[CauseId]| causes.iter().map(|cause| cause.0).collect::<BTreeSet<_>>();
    left.cause == right.cause
        && left.exhaustion_operation == right.exhaustion_operation
        && set(&left.callee_coverage) == set(&right.callee_coverage)
        && set(&left.cleanup_coverage) == set(&right.cleanup_coverage)
}

fn action_argument<'a>(
    arguments: &[crate::hir::application::Operand<'_, &'a Expr>],
) -> Option<&'a Expr> {
    if arguments.len() != 2 {
        return None;
    }
    let mut slots = [None, None];
    for argument in arguments {
        let slot = match argument.label {
            Some("limit") => 0,
            Some("action") => 1,
            None => slots.iter().position(Option::is_none)?,
            _ => return None,
        };
        if slots[slot].replace(argument.expression).is_some() {
            return None;
        }
    }
    slots[0]?;
    slots[1]
}

impl Visitor<'_> {
    pub(super) fn budget_call(
        &mut self,
        span: Span,
        arguments: &[crate::hir::application::Operand<'_, &Expr>],
        explicit_evaluation: &Judgment,
    ) -> Option<Judgment> {
        let mut proofs = self.budget_proofs.iter().filter(|proof| proof.span == span);
        let proof = proofs.next()?.clone();
        // Multiple observations are finalized by sema into one joined witness.
        // Unfinalized disagreement cannot select one observation arbitrarily.
        if proof.callee_coverage.is_empty() || proofs.any(|other| !same_evidence(&proof, other)) {
            return Some(Judgment::unresolved());
        }
        let Some(action) = action_argument(arguments) else {
            return Some(Judgment::unresolved());
        };
        // Auditing the body still discovers invalid nested halt callbacks. The
        // certificate covers invocation divergence, not ordinary diagnostics.
        let action_invocation = self.callable(action, &mut BTreeSet::new());
        let recovery = self
            .handlers
            .get("Div::exhausted")
            .cloned()
            // An unhandled exhaustion raises a finite language panic. Sema is
            // independently responsible for the residual effect contract.
            .unwrap_or_default();
        self.budget_witnesses.push(BudgetTerminationWitness {
            span,
            cause: proof.cause,
            exhaustion_operation: proof.exhaustion_operation,
            callee_coverage: proof.callee_coverage,
            cleanup_coverage: proof.cleanup_coverage,
            explicit_evaluation: explicit_evaluation.clone(),
            action_invocation,
            recovery: recovery.clone(),
        });
        Some(recovery)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(source: &str) -> (Program, BudgetProof) {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        // Fixtures exercise certificate consumption, not source certification.
        let marker = source.find("Div::budget(").unwrap() as u32;
        let function = parsed
            .program
            .statements
            .iter()
            .find_map(|statement| {
                let StmtKind::Function(function) = &statement.kind else {
                    return None;
                };
                function.body.as_ref().and_then(|body| {
                    body.statements.iter().find_map(|statement| {
                        let StmtKind::Expr { expression, .. } = &statement.kind else {
                            return None;
                        };
                        (expression.span.start == marker).then_some(expression)
                    })
                })
            })
            .unwrap();
        let span = function.span;
        (
            parsed.program,
            BudgetProof {
                span,
                exhaustion_operation: 41,
                callee_coverage: vec![CauseId(1)],
                cleanup_coverage: vec![],
                cause: CauseId(2),
            },
        )
    }

    #[test]
    fn only_a_complete_call_span_certificate_bounds_action_invocation() {
        let (program, proof) =
            fixture("fn spin()->int{loop{}}\nhalt fn bounded()->int{Div::budget(5,spin)}");
        assert!(analyze(&program).judgments["bounded"].unresolved);
        let analyzed = analyze_with_budgets(&program, std::slice::from_ref(&proof));
        assert_eq!(analyzed.judgments["bounded"], Judgment::default());
        assert!(analyzed.budget_witnesses[0].action_invocation.may_diverge);
        assert_eq!(
            analyzed.budget_witnesses[0].explicit_evaluation,
            Judgment::default()
        );
        let mut nearby = proof.clone();
        nearby.span.end -= 1;
        assert!(analyze_with_budgets(&program, &[nearby]).judgments["bounded"].unresolved);
        let mut empty = proof.clone();
        empty.callee_coverage.clear();
        assert!(analyze_with_budgets(&program, &[empty]).judgments["bounded"].unresolved);
        let mut conflict = proof.clone();
        conflict.exhaustion_operation += 1;
        assert!(analyze_with_budgets(&program, &[proof, conflict]).judgments["bounded"].unresolved);
    }

    #[test]
    fn explicit_evaluation_and_recovery_are_not_covered_by_action_fuel() {
        for source in [
            "fn spin()->int{loop{}}\nhalt fn bounded()->int{Div::budget(spin(),\\->1)}",
            "fn spin()->fn()->int{loop{}}\nhalt fn bounded()->int{Div::budget(5,spin())}",
            "halt fn bounded()->int{with Div::exhausted()->loop{};Div::budget(5,\\->loop{})}",
        ] {
            let (program, proof) = fixture(source);
            let analyzed = analyze_with_budgets(&program, &[proof]);
            assert!(analyzed.judgments["bounded"].may_diverge, "{source}");
            assert!(
                analyzed
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0820")
            );
        }
        let (program, proof) = fixture(
            "halt fn bounded()->int{with Div::exhausted()->external();Div::budget(5,\\->loop{})}",
        );
        assert!(analyze_with_budgets(&program, &[proof]).judgments["bounded"].unresolved);
    }

    #[test]
    fn covered_action_keeps_nested_halt_diagnostics_and_written_named_arguments() {
        let (program, proof) = fixture(
            "halt fn invoke(action:fn()->int)->int{action()}\nfn spin()->int{loop{}}\nhalt fn bounded()->int{Div::budget(action:\\->invoke(spin),limit:5)}",
        );
        let analyzed = analyze_with_budgets(&program, &[proof]);
        assert_eq!(analyzed.judgments["bounded"], Judgment::default());
        assert!(
            analyzed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0534")
        );
    }
}
