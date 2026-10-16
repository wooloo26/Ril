//! Complete normal pattern evaluation; no inspection or ownership is granted.
use super::*;
use crate::sema::{
    channel_messages::{ChannelAction, ChannelMessageFact},
    result_conditions::ConditionEvaluationId,
};

impl Checker {
    pub(in crate::sema::checker) fn channel_condition_evaluated(
        &mut self,
        evaluation: ConditionEvaluationId,
        subject_expression: usize,
        subject: &Value,
        span: Span,
        cause: CauseId,
        frame: &Frame,
    ) {
        // Ordinary Result tests before the first transport are relevant too.
        // Other pattern types do not enlarge the initial receipt phase.
        if !matches!(self.expanded_at(&subject.ty, span.file), Ty::Result(..)) {
            return;
        }
        let guard = self.concurrency.message_flow.guard();
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        self.channel_message_facts.push(ChannelMessageFact {
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            source_event: self.channel_source_event(frame),
            repetition: self.active_channel_repetitions.last().copied(),
            context: self.invocation_context(frame.callable_owner),
            task: self.concurrency.task_context.last().copied(),
            activation: frame.owner,
            span,
            cause,
            allocation_epoch: self.recency_moves.len(),
            guard,
            action: ChannelAction::ConditionEvaluated {
                evaluation,
                subject_expression,
                subject: self.channel_value_snapshot(subject),
            },
        });
    }
}
