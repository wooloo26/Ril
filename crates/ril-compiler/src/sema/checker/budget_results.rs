//! Result evidence belongs to one actual budget exit, not to the syntax span.
use super::*;

fn disposition(duty: Option<&ResultDuty>, answer: &Value) -> &'static str {
    match duty {
        None => "not produced on this path",
        Some(duty) if duty.abnormal => "absent or abandoned on an abnormal path",
        Some(duty) if duty.inspected => "inspected on this path",
        Some(duty) if duty.returned => "returned with its producer obligation",
        Some(duty) if duty.covered => "covered on this path",
        Some(duty) if answer.results.contains(&duty.id) => "pending, carried by this answer",
        Some(_) => "pending and not carried by this answer",
    }
}

impl Checker {
    pub(super) fn budget_result_exit_causes(
        &mut self,
        entry: &flow::FlowSnapshot,
        normal: &flow::FlowSnapshot,
        recovery: &flow::FlowSnapshot,
        answers: [&Value; 2],
        normal_continues: bool,
        span: Span,
    ) -> BTreeMap<u32, CauseId> {
        let [normal_answer, recovery_answer] = answers;
        let mut causes = BTreeMap::new();
        for index in 0..normal
            .result_duties()
            .len()
            .max(recovery.result_duties().len())
        {
            let initial = entry.result_duties().get(index);
            let ordinary = normal.result_duties().get(index);
            let exhausted = recovery.result_duties().get(index);
            if initial.is_some_and(|duty| duty.covered || duty.abnormal)
                && !normal_answer.results.contains(&(index as u32))
                && !recovery_answer.results.contains(&(index as u32))
            {
                continue;
            }
            let Some(origin) = initial.or(ordinary).or(exhausted) else {
                continue;
            };
            let cause = self.cause(CauseKind::BranchJoin, span,
                format!("budget producer {index}: normal {}; exhaustion {}; exhaustion starts at entry and cannot inherit a completed action's inspection",
                    if normal_continues { disposition(ordinary, normal_answer) }
                    else { "has no continuing action exit" },
                    disposition(exhausted, recovery_answer)),
                [origin.cause, normal_answer.cause, recovery_answer.cause]);
            causes.insert(index as u32, cause);
        }
        causes
    }

    pub(super) fn apply_budget_result_causes(&mut self, causes: &BTreeMap<u32, CauseId>) {
        for (&id, &cause) in causes {
            if let Some(duty) = self.result_duties.get_mut(id as usize) {
                duty.cause = cause;
            }
        }
    }
}
