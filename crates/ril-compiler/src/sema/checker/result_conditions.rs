//! Actual boolean values carry path-specific inspection evidence. No consumer
//! searches by source span or re-evaluates a pattern's expected expression.
use super::super::result_conditions::{
    ConditionEvaluation, ConditionEvaluationId, ConditionInspections, ConditionKind,
};
use super::*;

impl Checker {
    pub(super) fn current_condition_inspections(&self) -> ConditionInspections {
        let inspected: BTreeSet<_> = self
            .result_duties
            .iter()
            .filter(|duty| duty.inspected && !duty.abnormal)
            .map(|duty| duty.id)
            .collect();
        ConditionInspections {
            when_true: inspected.clone(),
            when_false: inspected.clone(),
            versions: inspected
                .into_iter()
                .map(|id| {
                    (
                        id,
                        self.result_inspection_versions
                            .get(&id)
                            .copied()
                            .unwrap_or(0),
                    )
                })
                .collect(),
            evaluations: BTreeSet::new(),
            ..Default::default()
        }
    }

    pub(super) fn record_condition_evaluation(
        &mut self,
        value: &mut Value,
        kind: ConditionKind,
        span: Span,
        frame: &Frame,
    ) -> ConditionEvaluationId {
        let id = ConditionEvaluationId(self.condition_evaluations.len() as u32);
        self.condition_evaluations.push(ConditionEvaluation {
            id,
            context: self.invocation_context(frame.callable_owner),
            span,
            cause: value.cause,
            kind,
            constant: match value.constant {
                Some(Constant::Bool(value)) => Some(value),
                _ => None,
            },
            inspections: value.condition_inspections.clone(),
        });
        value.condition_inspections.evaluations.insert(id);
        self.channel_record_boolean_identity(value, id, frame.owner);
        id
    }

    pub(super) fn apply_condition_inspections(
        &mut self,
        evidence: &ConditionInspections,
        truth: bool,
        span: Span,
        cause: CauseId,
    ) {
        self.channel_select_condition(evidence, truth, span, cause);
        let selected: BTreeSet<_> = evidence
            .outcome(truth)
            .iter()
            .copied()
            .filter(|id| {
                evidence.versions.get(id).copied()
                    == Some(
                        self.result_inspection_versions
                            .get(id)
                            .copied()
                            .unwrap_or(0),
                    )
                    && self
                        .result_duties
                        .get(*id as usize)
                        .is_none_or(|duty| !duty.inspected || !duty.covered)
            })
            .collect();
        let mut carrier = Value::scalar(Ty::Unknown, None, cause);
        carrier.outer_results = selected.clone();
        if !selected.is_empty()
            && self.loop_depth > 0
            && !self.loop_result_inspection_allowed(&carrier)
        {
            self.unsupported(
                span,
                "stored boolean inspection needs the current iteration's Result family proof",
            );
            return;
        }
        for id in selected {
            let Some(duty) = self.result_duties.get(id as usize) else {
                continue;
            };
            if duty.inspected && duty.covered {
                continue;
            }
            let proof=self.cause(CauseKind::Projection,span,
                format!("boolean {truth} continuation necessarily performed the recorded tag inspection of producer {id}"),
                [cause,duty.cause]);
            let duty = &mut self.result_duties[id as usize];
            duty.inspected = true;
            duty.covered = true;
            duty.cause = proof;
        }
    }

    pub(super) fn inspect_condition_value(&mut self, value: &Value, truth: bool, span: Span) {
        if self.expanded_at(&value.ty, span.file) != Ty::Bool {
            return;
        }
        if !self.pending_copy_dependencies(value).is_empty() {
            self.require_copy_dependencies(
                value,
                span,
                "Result inspection through a stored boolean",
            );
            return;
        }
        self.apply_condition_inspections(&value.condition_inspections, truth, span, value.cause);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn successful_assertion_requires_the_right_conjunction_inspection() {
        for source in [
            "fn example(flag:bool){let result:Result<int,str>=Ok(2);assert(flag && result is Ok(2))}",
            "fn example(flag:bool){let result:Result<int,str>=Ok(2);assert(!(flag || result is Err(_)))}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_some(),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        for source in [
            "fn example(flag:bool){let result:Result<int,str>=Ok(2);assert(flag || result is Ok(2))}",
            "fn example(flag:bool){let result:Result<int,str>=Ok(2);let _=flag && result is Ok(2)}",
            "fn assert(value:bool){}\nfn example(flag:bool){let result:Result<int,str>=Ok(2);assert(flag && result is Ok(2))}",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
}
