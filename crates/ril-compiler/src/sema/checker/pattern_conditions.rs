//! Conditional receivers bind from one protected subject evaluation. Their
//! lexical names exist only on the matching branch or current loop iteration.
use super::*;

impl Checker {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::sema::checker) fn check_if_let(
        &mut self,
        pattern: &Pattern,
        subject: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
        span: Span,
        frame: &mut Frame,
        context: SourceContext<'_>,
    ) -> SourceExpression {
        let packet = self.expression_source_packet(subject, frame, None, None);
        let value = match self.read_evaluation_packet(&packet, subject.span) {
            Ok(value) => value,
            Err(_) => {
                return SourceExpression::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        if value.ty == Ty::Never {
            self.unsupported(
                pattern.span,
                "abrupt conditional subject needs an unreachable binding context",
            );
            return SourceExpression::unobserved(
                value,
                self.recency_moves.len(),
                packet.source_valid,
            );
        }
        self.check_pattern_binder_uniqueness(pattern);
        self.inspect_guaranteed_pattern_head(&value, pattern, span, frame);
        let matched = self.binding_pattern_match(pattern, &value, frame);
        let before = self.snapshot_flow();
        let original_env = frame.env.clone();
        let local_start = frame.locals.len();
        let bindings = self.checked_pattern_bindings(pattern, &value, None, Some(&packet), frame);
        self.bind_pattern_aliases(pattern, bindings, frame, Some(&packet));
        let then = if matched == Some(false) {
            self.preview_expression_source(then_branch, frame, context.ordinary, context.source)
        } else {
            self.expression_expected_source(then_branch, frame, context.ordinary, context.source)
        };
        self.end_pattern_aliases(frame, local_start, matched != Some(false));
        frame.env = original_env.clone();
        let then_state = self.snapshot_flow();
        self.restore_definition_state(&before);
        let other = if let Some(other) = else_branch {
            if matched == Some(true) {
                self.preview_expression_source(other, frame, context.ordinary, context.source)
            } else {
                self.expression_expected_source(other, frame, context.ordinary, context.source)
            }
        } else {
            SourceExpression::unobserved(self.unit(span), self.recency_moves.len(), true)
        };
        frame.env = original_env;
        let valid = packet.source_valid && then.source_valid && other.source_valid;
        let mut left = self.transport_flow_value(&then.value, &then_state, span);
        let mut right = other.value;
        self.require_branch_types(&mut left, &mut right, span);
        let value = match matched {
            Some(true) => {
                self.restore_definition_state(&then_state);
                left
            }
            Some(false) => right,
            None => self.branch_flow(&before, &then_state, &left, &right, span),
        };
        SourceExpression::unobserved(value, self.recency_moves.len(), valid)
    }

    pub(in crate::sema::checker) fn check_while_let_iteration(
        &mut self,
        pattern: &Pattern,
        subject: &Expr,
        body: &Block,
        frame: &mut Frame,
    ) -> (Value, bool) {
        let packet = self.expression_source_packet(subject, frame, None, None);
        let value = match self.read_evaluation_packet(&packet, subject.span) {
            Ok(value) => value,
            Err(_) => return (Value::scalar(Ty::Unknown, None, CauseId(0)), true),
        };
        if value.ty == Ty::Never {
            return (value, true);
        }
        self.inspect_guaranteed_pattern_head(&value, pattern, pattern.span, frame);
        let matched = self.binding_pattern_match(pattern, &value, frame);
        let original_env = frame.env.clone();
        let local_start = frame.locals.len();
        let failure = self.snapshot_flow();
        let bindings = self.checked_pattern_bindings(pattern, &value, None, Some(&packet), frame);
        self.bind_pattern_aliases(pattern, bindings, frame, Some(&packet));
        let body_value = if matched == Some(false) {
            self.preview_block_source(body, frame, None, None).value
        } else {
            self.block(body, frame)
        };
        self.require_type(&body_value, &Ty::Unit, body.span);
        self.end_pattern_aliases(frame, local_start, matched != Some(false));
        frame.env = original_env;
        if matched == Some(false) {
            self.restore_definition_state(&failure);
            return (self.unit(pattern.span), true);
        }
        if matched.is_none() {
            let success = self.snapshot_flow();
            self.restore_definition_state(&failure);
            let unit = self.unit(pattern.span);
            let joined = self.branch_flow(&failure, &success, &body_value, &unit, pattern.span);
            return (joined, false);
        }
        (body_value, false)
    }

    fn end_pattern_aliases(&mut self, frame: &mut Frame, start: usize, check_authority: bool) {
        for id in frame.locals.drain(start..).collect::<Vec<_>>() {
            if check_authority {
                self.check_authority_use(id);
            }
            self.bindings[id].alive = false;
        }
    }
}
