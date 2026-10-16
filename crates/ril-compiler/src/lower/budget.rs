//! A budget boundary consumes semantic coverage evidence, never a bare CauseId.
use super::*;
use crate::sema::{BudgetProof, SemanticFacts, model::Callable};

fn same_evidence(left: &BudgetProof, right: &BudgetProof) -> bool {
    let set = |values: &[ril_compiler_core::diagnostic::CauseId]| {
        values
            .iter()
            .map(|cause| cause.0)
            .collect::<std::collections::BTreeSet<_>>()
    };
    left.exhaustion_operation == right.exhaustion_operation
        && left.cause == right.cause
        && set(&left.callee_coverage) == set(&right.callee_coverage)
        && set(&left.cleanup_coverage) == set(&right.cleanup_coverage)
}
fn proof(facts: &SemanticFacts, span: Span) -> Result<&BudgetProof, NotImplemented> {
    let mut observations = facts
        .budget_proofs
        .iter()
        .filter(|proof| proof.span == span);
    let first = observations.next().ok_or_else(|| {
        unsupported("Div::budget has no complete semantic BudgetProof for this invocation")
    })?;
    if first.callee_coverage.is_empty() || observations.any(|other| !same_evidence(first, other)) {
        return Err(unsupported(
            "budget coverage observations do not supply one complete common proof",
        ));
    }
    for cause in std::iter::once(&first.cause)
        .chain(&first.callee_coverage)
        .chain(&first.cleanup_coverage)
    {
        if !facts
            .explanations
            .causes
            .iter()
            .any(|explanation| explanation.id == *cause)
        {
            return Err(unsupported(
                "budget coverage proof references missing semantic evidence",
            ));
        }
    }
    Ok(first)
}
impl Lower<'_> {
    pub(super) fn budget_call(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Argument],
        span: Span,
    ) -> Result<Option<ir::ExprKind>, NotImplemented> {
        let observations: Vec<_> = self.facts.expressions_at(callee.span).collect();
        let exact = |fact: &&crate::sema::ExpressionFact| matches!(fact.value.callables.as_slice(),[Callable::Builtin(name)]if name=="Div::budget");
        let recorded = self
            .facts
            .budget_proofs
            .iter()
            .any(|proof| proof.span == span);
        if !recorded && !observations.iter().any(exact) {
            return Ok(None);
        }
        if observations.is_empty() || !observations.iter().all(exact) {
            return Err(unsupported(
                "budget callee identity is not common to every semantic observation",
            ));
        }
        let proof = proof(self.facts, span)?.clone();
        let base = if let ast::ExprKind::Generic { base, .. } = &callee.kind {
            base.as_ref()
        } else {
            callee
        };
        if expression_name(base).as_deref() != Some("Div::budget") {
            return Err(unsupported(
                "stored budget callable lowering needs its certified coverage-contract bridge",
            ));
        }
        if arguments.len() != 2 {
            return Err(unsupported(
                "explicit budget lowering requires its checked limit and action",
            ));
        }
        let mut slots: [Option<ir::Expr>; 2] = [None, None];
        let mut written_slots = vec![];
        for argument in arguments {
            let slot = match argument.label.as_deref() {
                Some("limit") => 0,
                Some("action") => 1,
                None => slots
                    .iter()
                    .position(Option::is_none)
                    .ok_or_else(|| unsupported("duplicate budget argument slot"))?,
                _ => {
                    return Err(unsupported(
                        "budget argument label lacks a checked parameter identity",
                    ));
                }
            };
            if slots[slot].is_some() {
                return Err(unsupported("duplicate budget argument slot"));
            }
            slots[slot] = Some(self.expression(&argument.value)?);
            written_slots.push(slot);
        }
        let [Some(limit), Some(action)] = slots else {
            return Err(unsupported("budget arguments leave an unproved slot"));
        };
        // The boundary itself evaluates limit then action. Keep a direct
        // lambda visible here when that is exactly the written argument order;
        // its immediate invocation does not retain a handler beyond this call.
        if written_slots == [0, 1] {
            return Ok(Some(ir::ExprKind::Budget {
                limit: Box::new(limit),
                action: Box::new(action),
                exhaustion_operation: proof.exhaustion_operation,
                coverage: proof.cause,
            }));
        }
        let mut values = [Some(limit), Some(action)];
        let mut slots: [Option<ir::Expr>; 2] = [None, None];
        let mut statements = vec![];
        for slot in written_slots {
            let value = values[slot].take().expect("checked unique budget slot");
            let argument_span = value.span;
            let name = format!("\0ril.budget.argument.{}", self.next_temporary);
            self.next_temporary += 1;
            statements.push(ir::Statement::Bind {
                pattern: ir::Pattern::Name(name.clone()),
                value,
                scoped: false,
            });
            slots[slot] = Some(ir::Expr {
                kind: ir::ExprKind::Name(name),
                span: argument_span,
            });
        }
        let [Some(limit), Some(action)] = slots else {
            return Err(unsupported("budget arguments leave an unproved slot"));
        };
        statements.push(ir::Statement::Expr {
            expression: ir::Expr {
                kind: ir::ExprKind::Budget {
                    limit: Box::new(limit),
                    action: Box::new(action),
                    exhaustion_operation: proof.exhaustion_operation,
                    coverage: proof.cause,
                },
                span,
            },
            terminated: false,
        });
        Ok(Some(ir::ExprKind::Block(ir::Block { statements })))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::source::FileId;
    #[test]
    fn a_cause_or_a_proof_for_a_nearby_expression_cannot_authorize_a_budget() {
        let span = Span {
            file: FileId(0),
            start: 1,
            end: 3,
        };
        let mut facts = SemanticFacts::default();
        let cause = facts.explanations.add(
            crate::sema::facts::CauseKind::Source,
            Some(span),
            "ordinary literal evidence",
            [],
        );
        assert!(proof(&facts, span).is_err());
        facts.budget_proofs.push(BudgetProof {
            span: Span { end: 2, ..span },
            exhaustion_operation: 29,
            callee_coverage: vec![cause],
            cleanup_coverage: vec![],
            cause,
        });
        assert!(proof(&facts, span).is_err());
        facts.budget_proofs[0].span = span;
        // This registered fixture tests the lowering protocol only. It is not
        // a source coverage certificate, and never reaches a public Session.
        assert!(proof(&facts, span).is_ok());
        let mut inconsistent = facts.budget_proofs[0].clone();
        inconsistent.exhaustion_operation = 30;
        facts.budget_proofs.push(inconsistent);
        assert!(proof(&facts, span).is_err());
    }
}
