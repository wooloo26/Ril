//! A non-tail arm resumes only after the protected computation has produced its
//! actual answer. Its suffix therefore runs against the resulting heap state.
use super::*;

#[derive(Clone)]
pub(super) struct ArmSuffix {
    pub identity: bool,
    pub binding: Option<Binding>,
    pub statements: Vec<Stmt>,
    pub span: Span,
    pub body_source: Option<ril_compiler_core::ids::ExprId>,
    pub definitions_start: usize,
    pub handler: usize,
    pub operation: String,
    pub boundary: u32,
    pub handler_boundary: u32,
    pub resume: Span,
    pub resume_source: Option<ril_compiler_core::ids::ExprId>,
    pub context: super::super::effect_identity::InvocationContext,
    pub ended_operation_loans: BTreeSet<LoanId>,
    pub operation_receptions: Vec<super::super::resumption::OperationReception>,
}

pub(super) fn linear_resume(expr: &Expr) -> Option<usize> {
    let ExprKind::Block(block) = &expr.kind else {
        return None;
    };
    block
        .statements
        .iter()
        .position(|statement| match &statement.kind {
            StmtKind::Expr { expression, .. } => is_resume(expression),
            StmtKind::Binding(binding) => {
                is_resume(&binding.value)
                    && binding.fallback.is_none()
                    && matches!(
                        binding.pattern.kind,
                        PatternKind::Name(_) | PatternKind::Wildcard
                    )
            }
            _ => false,
        })
}

fn is_resume(expression: &Expr) -> bool {
    matches!(
        expression.kind,
        ExprKind::Control {
            operation: ControlOperation::Resume,
            ..
        }
    )
}

impl Checker {
    pub(super) fn arm_prefix(
        &mut self,
        body: &Expr,
        handler: usize,
        operation: &str,
        frame: &mut Frame,
    ) -> Option<(Value, ArmSuffix)> {
        let index = linear_resume(body)?;
        let ExprKind::Block(block) = &body.kind else {
            return None;
        };
        if index + 1 == block.statements.len()
            && matches!(block.statements[index].kind, StmtKind::Expr { .. })
        {
            return None;
        }
        if block.statements.iter().any(|statement| {
            matches!(
                statement.kind,
                StmtKind::Handler(_) | StmtKind::HandlerApplication(_)
            )
        }) {
            self.unsupported(body.span,"nested handler definitions across a non-tail resumption require an activation-local handler suffix");
        }
        let definitions_start = self.functions.len();
        let start = frame.locals.len();
        let boundary = self.next_boundary;
        self.next_boundary += 1;
        self.block_boundaries.push(boundary);
        let handlers = self.active_handlers.len();
        self.declarations(&block.statements, frame);
        self.declarations(&block.where_items, frame);
        let mut result = self.unit(body.span);
        for statement in &block.statements[..index] {
            if !matches!(
                statement.kind,
                StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
            ) {
                result = self.statement(statement, frame);
                if result.ty == Ty::Never {
                    self.unsupported(body.span,"a non-tail arm prefix exits before its resumption; suffix typing needs a bottom-context proof");
                    break;
                }
            }
        }
        let (resume, binding) = match &block.statements[index].kind {
            StmtKind::Expr { expression, .. } => (expression, None),
            StmtKind::Binding(binding) => (&binding.value, Some(binding.clone())),
            _ => unreachable!(),
        };
        if result.ty != Ty::Never
            && let ExprKind::Control { value, .. } = &resume.kind
        {
            let operand = value
                .as_ref()
                .map(|value| self.expression(value, frame))
                .unwrap_or_else(|| self.unit(resume.span));
            if operand.ty == Ty::Never {
                self.unsupported(
                    resume.span,
                    "a non-tail resumption operand has no normal continuation",
                );
                result = operand;
            } else {
                result = self.resume_operation(operand, resume.span, frame);
            }
        }
        self.exit_cleanups(start, &result, body.span, frame);
        self.active_handlers.truncate(handlers);
        self.block_boundaries.pop();
        Some((
            result,
            ArmSuffix {
                identity: retained_answers::identity_suffix(body),
                binding,
                statements: block.statements[index + 1..].to_vec(),
                span: block.span,
                body_source: body.hir_id,
                definitions_start,
                handler,
                operation: operation.into(),
                boundary,
                handler_boundary: self.handler_answer_boundary(handler),
                resume: resume.span,
                resume_source: resume.hir_id,
                context: self.invocation_context(frame.callable_owner),
                ended_operation_loans: self
                    .resume_contexts
                    .last()
                    .map(|context| context.loans.clone())
                    .unwrap_or_default(),
                operation_receptions: self
                    .resume_contexts
                    .last()
                    .map(|context| context.receptions.clone())
                    .unwrap_or_default(),
            },
        ))
    }

    pub(super) fn run_arm_suffix(
        &mut self,
        suffix: ArmSuffix,
        answer: &Value,
        frame: &mut Frame,
        scope_exit: Option<super::super::resumption::ContinuationScopeExit>,
    ) -> Value {
        let transport = if suffix.identity && self.identity_handler_answer(answer) {
            AnswerTransport::Identity
        } else if self.copy_handler_answer(answer) {
            AnswerTransport::CopyChecked
        } else if self.ordinary_handler_answer(answer) {
            AnswerTransport::OrdinaryChecked
        } else {
            self.unsupported(suffix.span,"non-tail resumption answer requires a complete ordinary graph; Result, resource, scoped or callable transfer needs a separate proof");
            return answer.clone();
        };
        let continuation_epoch = self.recency_moves.len();
        let continuation_value = self.copy_value_snapshot(answer);
        let mut held_answer = EvaluatedValue::new(answer.clone(), continuation_epoch);
        let continuation_expression = self.expression_facts.len();
        self.block_boundaries.push(suffix.boundary);
        self.invocation_expressions
            .push(super::super::effect_identity::InvocationExpression {
                context: suffix.context,
                expression: self.expression_facts.len(),
                argument_of: None,
            });
        self.expression_facts.push(super::super::ExpressionFact {
            source_id: suffix.resume_source,
            span: suffix.resume,
            value: answer.clone(),
        });
        if let Some(binding) = &suffix.binding {
            let mut value = answer.clone();
            if let Some(syntax) = &binding.ty {
                self.set_contract_environment(&frame.env);
                self.ascribe_signature(&mut value, syntax);
                let expected = self.ty(syntax);
                self.require_type(&value, &expected, binding.value.span);
                value.ty = expected;
            }
            self.bind_pattern(&binding.pattern, binding.mode, value, frame, false);
        }
        let mut result = self.unit(suffix.span);
        for statement in &suffix.statements {
            if !matches!(
                statement.kind,
                StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
            ) {
                result = self.statement(statement, frame);
                if result.ty == Ty::Never {
                    break;
                }
            }
        }
        let mut held_result = EvaluatedValue::new(result, self.recency_moves.len());
        self.verify_local_definitions(suffix.definitions_start, frame);
        let mut result = held_result.current(&self.recency_moves);
        let answer = held_answer.current(&self.recency_moves);
        self.block_boundaries.pop();
        if !frame.obligations.performed_operations.is_empty()
            || self.pending_abort.is_some()
            || !frame.returned.is_empty()
        {
            self.unsupported(suffix.span,"post-resumption outward control and effect requests require a composed activation transfer summary");
        }
        let numeric = result.unsuffixed_numeric
            && matches!(
                (&result.ty, &answer.ty),
                (Ty::Int(_), Ty::Int(_)) | (Ty::Float(_), Ty::Float(_))
            );
        if result.ty != Ty::Never && !self.compatible(&result.ty, &answer.ty) && !numeric {
            self.error(
                "E0625",
                suffix.span,
                "handler suffix answer does not match its protected block answer",
                [result.cause, answer.cause],
            );
        }
        self.require_type(&result, &answer.ty, suffix.span);
        if result.ty != Ty::Never {
            result.ty = answer.ty.clone();
        }
        let cleanup_epoch = self.recency_moves.len();
        self.exit_cleanups(0, &result, suffix.span, frame);
        self.transport_value_since(&mut result, cleanup_epoch);
        result.cause = self.cause(
            CauseKind::Handler,
            suffix.span,
            "handler suffix runs after the actual continuation answer",
            [answer.cause, result.cause],
        );
        let arm_expression = self.expression_facts.len();
        self.invocation_expressions
            .push(super::super::effect_identity::InvocationExpression {
                context: suffix.context,
                expression: arm_expression,
                argument_of: None,
            });
        self.expression_facts.push(super::super::ExpressionFact {
            source_id: suffix.body_source,
            span: suffix.span,
            value: result.clone(),
        });
        self.resumption_steps.push(super::super::ResumptionStep {
            span: suffix.resume,
            owner: frame.owner,
            handler: suffix.handler,
            operation: self.operations[&suffix.operation].identity,
            body_answer: answer.ty.clone(),
            arm_answer: result.ty.clone(),
            continuation: answer.cause,
            cause: result.cause,
            boundary: suffix.handler_boundary,
            context: suffix.context,
            continuation_value,
            arm_value: self.copy_value_snapshot(&result),
            continuation_epoch,
            completion_epoch: self.recency_moves.len(),
            ended_operation_loans: suffix.ended_operation_loans,
            operation_receptions: suffix.operation_receptions,
            continuation_expression,
            arm_expression,
            transport,
            scope_exit,
        });
        self.mark_post_resume_checked(suffix.handler, &suffix.operation);
        result
    }
}
