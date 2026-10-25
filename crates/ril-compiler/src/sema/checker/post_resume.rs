//! A non-tail arm resumes only after the protected computation has produced its
//! actual answer. Its suffix therefore runs against the resulting heap state.
use super::*;

#[derive(Clone)]
pub(super) struct ArmSuffix {
    pub identity: bool,
    pub receiver: ResumeReceiver,
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

#[derive(Clone)]
pub(super) enum ResumeReceiver {
    Expression(Box<Expr>),
    Statement(Box<Stmt>),
}

pub(super) struct AnswerInput {
    pub owner: ScopeId,
    pub source: ril_compiler_core::ids::ExprId,
    pub packet: Option<EvaluatedValue>,
}

/// Follow only the leading evaluation spine. No preceding operand may be
/// evaluated a second time when the real continuation answer becomes available.
/// Contexts with a preceding operand need their own suspended evaluation cursor.
fn leading_resume(mut expression: &Expr) -> Option<&Expr> {
    for _ in 0..64 {
        expression = match &expression.kind {
            ExprKind::Control {
                operation: ControlOperation::Resume,
                ..
            } => {
                return Some(expression);
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Field { base: operand, .. }
            | ExprKind::ComputedField { base: operand, .. }
            | ExprKind::Index { base: operand, .. }
            | ExprKind::Generic { base: operand, .. }
            | ExprKind::Binary { left: operand, .. }
            | ExprKind::Call {
                callee: operand, ..
            } => operand,
            ExprKind::Tuple(items) | ExprKind::Array(items) => items.first()?,
            ExprKind::Map(entries) => &entries.first()?.0,
            ExprKind::Record { members, .. } => match members.first()? {
                RecordMember::Field(field) => &field.value,
                RecordMember::Spread(expression) => expression,
            },
            ExprKind::Derive {
                base: Some(base), ..
            } => base,
            _ => return None,
        };
    }
    None
}

pub(super) fn linear_resume(expr: &Expr) -> Option<usize> {
    let ExprKind::Block(block) = &expr.kind else {
        return leading_resume(expr).map(|_| 0);
    };
    block
        .statements
        .iter()
        .position(|statement| match &statement.kind {
            StmtKind::Expr { expression, .. } => leading_resume(expression).is_some(),
            StmtKind::Binding(binding) => {
                leading_resume(&binding.value).is_some()
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
    pub(super) fn resumed_expression_input(
        &mut self,
        expression: &Expr,
        frame: &mut Frame,
        expected: Option<&Ty>,
        target: Option<&super::super::source_reception::Target>,
    ) -> Option<EvaluatedValue> {
        let source = expression.hir_id?;
        let input = self.resumption_inputs.last_mut()?;
        if input.owner != frame.owner || input.source != source {
            return None;
        }
        let mut packet = input.packet.take()?;
        self.transport_evaluation_packet(&mut packet, expression.span);
        if let Some(target) = target {
            self.receive_boundary_target(&mut packet, expected, target, expression.span);
        } else if let Some(expected) = expected {
            self.require_type(&packet.value, expected, expression.span);
        }
        Some(packet)
    }

    pub(super) fn arm_prefix(
        &mut self,
        body: &Expr,
        handler: usize,
        operation: &str,
        frame: &mut Frame,
    ) -> Option<(Value, ArmSuffix)> {
        let index = linear_resume(body)?;
        let block = if let ExprKind::Block(block) = &body.kind {
            Some(block)
        } else {
            None
        };
        if let Some(block) = block
            && index + 1 == block.statements.len()
            && matches!(&block.statements[index].kind,
                StmtKind::Expr { expression, terminated: false } if is_resume(expression))
        {
            return None;
        }
        if block.is_some_and(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    StmtKind::Handler(_) | StmtKind::HandlerApplication(_)
                )
            })
        }) {
            self.unsupported(body.span,"nested handler definitions across a non-tail resumption require an activation-local handler suffix");
        }
        let definitions_start = self.functions.len();
        let start = frame.locals.len();
        let boundary = self.next_boundary;
        self.next_boundary += 1;
        self.block_boundaries.push(boundary);
        let handlers = self.active_handlers.len();
        if let Some(block) = block {
            self.declarations(&block.statements, frame);
            self.declarations(&block.where_items, frame);
        }
        let mut result = self.unit(body.span);
        for statement in block.map_or(&[][..], |block| &block.statements[..index]) {
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
        let (resume, receiver) = if let Some(block) = block {
            let statement = &block.statements[index];
            let expression = match &statement.kind {
                StmtKind::Expr { expression, .. } => expression,
                StmtKind::Binding(binding) => &binding.value,
                _ => unreachable!(),
            };
            (
                leading_resume(expression)?,
                ResumeReceiver::Statement(Box::new(statement.clone())),
            )
        } else {
            (
                leading_resume(body)?,
                ResumeReceiver::Expression(Box::new(body.clone())),
            )
        };
        if result.ty != Ty::Never {
            // Resume is an actual HIR expression even when its operand is
            // implicit unit. Use the common occurrence/activation recorder.
            result = self.expression(resume, frame);
        }
        self.exit_cleanups(start, &result, body.span, frame);
        self.active_handlers.truncate(handlers);
        self.block_boundaries.pop();
        Some((
            result,
            ArmSuffix {
                identity: retained_answers::identity_suffix(body),
                receiver,
                statements: block
                    .map_or_else(Vec::new, |block| block.statements[index + 1..].to_vec()),
                span: body.span,
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
        input: &EvaluatedValue,
        frame: &mut Frame,
        scope_exit: Option<super::super::resumption::ContinuationScopeExit>,
    ) -> EvaluatedValue {
        let answer_value = input.value.clone();
        let answer = &answer_value;
        let (Some(resume_source), Some(arm_source)) = (suffix.resume_source, suffix.body_source)
        else {
            self.unsupported(
                suffix.span,
                "resumed answer lost its original Resume or arm HIR identity",
            );
            return input.clone();
        };
        let transport = if suffix.identity && self.identity_handler_answer(answer) {
            AnswerTransport::Identity
        } else if self.copy_handler_answer(answer) {
            AnswerTransport::CopyChecked
        } else if self.ordinary_handler_answer(answer) {
            AnswerTransport::OrdinaryChecked
        } else {
            self.unsupported(suffix.span,"non-tail resumption answer requires a complete ordinary graph; Result, resource, scoped or callable transfer needs a separate proof");
            return input.clone();
        };
        let continuation_epoch = self.recency_moves.len();
        let continuation_value = self.copy_value_snapshot(answer);
        let emitted_answer = match self.copy_value_for_emission(answer) {
            Ok(value) => value,
            Err(error) => {
                self.unsupported(
                    suffix.resume,
                    format!("continuation physical emission: {error}"),
                );
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        self.block_boundaries.push(suffix.boundary);
        let evaluation_context = suffix.context;
        let continuation_environment = self.physical_evaluation_environment(suffix.resume);
        let Some(completion_activation) = self.application_effect.enter_kind(
            Some(resume_source),
            frame.owner,
            evaluation_context,
            super::super::application_effect::ActivationKind::ControlTransfer,
        ) else {
            self.block_boundaries.pop();
            self.unsupported(
                suffix.resume,
                "continuation completion activation is unavailable",
            );
            return input.clone();
        };
        let continuation_expression = self.application_effect.observe_in(
            completion_activation,
            || super::super::application_effect::ObservationInput {
                allocation_epoch: continuation_epoch,
                source_id: Some(resume_source),
                span: suffix.resume,
                value: emitted_answer,
            },
            evaluation_context,
            frame.owner,
            continuation_environment,
            None,
        );
        self.application_effect.leave(completion_activation);
        let Some(continuation_expression) = continuation_expression else {
            self.block_boundaries.pop();
            return input.clone();
        };
        let mut held_answer = match self
            .application_effect
            .packet_at(continuation_expression)
            .and_then(|packet| self.clone_evaluation_packet(&packet, suffix.resume))
        {
            Ok(packet) => packet,
            Err(error) => {
                self.block_boundaries.pop();
                self.unsupported(
                    suffix.resume,
                    format!("continuation physical packet: {error}"),
                );
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        self.inherit_result_type(&mut held_answer, input, suffix.resume);
        self.resumption_inputs.push(AnswerInput {
            owner: frame.owner,
            source: resume_source,
            packet: Some(held_answer.clone()),
        });
        let mut result_packet = match &suffix.receiver {
            ResumeReceiver::Expression(expression) => {
                self.expression_expected_source(expression, frame, None, None)
            }
            ResumeReceiver::Statement(statement) => {
                self.statement_expected_source(statement, frame, None, None)
            }
        };
        if self
            .resumption_inputs
            .pop()
            .is_none_or(|input| input.packet.is_some())
        {
            self.unsupported(
                suffix.resume,
                "the resumed expression did not consume its actual answer",
            );
        }
        for statement in &suffix.statements {
            if result_packet.value.ty == Ty::Never {
                break;
            }
            if !matches!(
                statement.kind,
                StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
            ) {
                result_packet = self.statement_expected_source(statement, frame, None, None);
                if result_packet.value.ty == Ty::Never {
                    break;
                }
            }
        }
        let mut held_result = result_packet;
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
        held_result.value = result.clone();
        self.receive_boundary_type(&mut held_result, &mut held_answer, suffix.span);
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
        let evaluation_context = suffix.context;
        let arm_environment = self.physical_evaluation_environment(suffix.span);
        let mut emitted = Some(result);
        let Some(arm_expression) = self.application_effect.observe(
            || super::super::application_effect::ObservationInput {
                allocation_epoch: self.recency_moves.len(),
                source_id: Some(arm_source),
                span: suffix.span,
                value: emitted.take().expect("arm answer moves once"),
            },
            evaluation_context,
            frame.owner,
            arm_environment,
            None,
        ) else {
            return EvaluatedValue::unobserved(
                emitted.unwrap_or_else(|| Value::scalar(Ty::Unknown, None, CauseId(0))),
                self.recency_moves.len(),
                false,
            );
        };
        let mut result_packet = match self
            .application_effect
            .packet_at(arm_expression)
            .and_then(|packet| self.clone_evaluation_packet(&packet, suffix.span))
        {
            Ok(value) => value,
            Err(error) => {
                self.unsupported(suffix.span, format!("arm physical packet: {error}"));
                return EvaluatedValue::unobserved(
                    Value::scalar(Ty::Unknown, None, CauseId(0)),
                    self.recency_moves.len(),
                    false,
                );
            }
        };
        self.inherit_result_type(&mut result_packet, &held_result, suffix.span);
        let result = &result_packet.value;
        self.resumption_steps.push(super::super::ResumptionStep {
            id: ril_compiler_core::ids::ProtectedAnswerId(continuation_expression as u32),
            resume_source,
            arm_source,
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
            arm_value: self.copy_value_snapshot(result),
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
        result_packet
    }
}
