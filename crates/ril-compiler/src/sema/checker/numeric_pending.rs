//! Pending scalar arithmetic keeps its source operator tree. Solving it only
//! selects types and leaf encodings; it never evaluates a runtime expression.
use super::super::numeric_selection::{
    NumericBirth, NumericDomain, NumericHole, NumericHoleState, NumericOperand, NumericSelection,
    NumericTerm, NumericUse,
};
use super::*;
use crate::numeric_literals::{ExactLiteral, NumberType, ParseLimit};
use crate::sema::source_types::SourceTypesError;
use ril_compiler_core::ids::{NumericHoleId, NumericSelectionId, NumericUseId};

pub(super) fn candidate(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Literal(Literal::Integer(_) | Literal::Float(_)) => true,
        ExprKind::Unary { operator, operand } => operator == "-" && candidate(operand),
        ExprKind::Binary {
            operator,
            left,
            right,
        } => {
            matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%")
                && candidate(left)
                && candidate(right)
        }
        _ => false,
    }
}

impl Checker {
    fn numeric_operand(
        &mut self,
        value: &Value,
        source: ril_compiler_core::ids::ExprId,
        birth: NumericBirth,
    ) -> Result<NumericOperand, SourceTypesError> {
        let start = self
            .application_effect
            .activations
            .get(birth.occurrence.activation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?
            .start_expression;
        let end = self.application_effect.expressions.len();
        let candidates = self.application_effect.occurrences(source, birth.context);
        let from = candidates.partition_point(|index| *index < start);
        let to = candidates.partition_point(|index| *index < end);
        let cost = to - from + 4 + value.numeric.uses.len() + value.numeric.selections.len();
        if !self.application_effect.admit(cost) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        self.application_effect
            .with_work(|work| crate::sema::clone_work::ty(work, &value.ty, 0))
            .ok_or(SourceTypesError::BudgetExceeded)?;
        let candidates = self.application_effect.occurrences(source, birth.context);
        let mut children = candidates[from..to].iter().filter_map(|index| {
            let record = self.application_effect.evaluations.get(*index)?;
            let identity = record.identity?;
            let activation = self
                .application_effect
                .activations
                .get(identity.activation.0 as usize)?;
            (activation.parent == Some(birth.occurrence.activation)
                && activation.kind != crate::sema::application_effect::ActivationKind::Emission)
                .then_some((record.id, activation))
        });
        let (observation, child) = children.next().ok_or(SourceTypesError::MissingNode)?;
        if children.next().is_some() || child.context != birth.context || child.scope != birth.scope
        {
            return Err(SourceTypesError::Unresolved);
        }
        let fact = self
            .application_effect
            .expressions
            .get(observation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let record = self
            .application_effect
            .evaluations
            .get(observation.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if record.id != observation
            || record.identity
                != Some(crate::sema::application_effect::OccurrenceIdentity {
                    source,
                    activation: child.id,
                })
            || fact.source_id != Some(source)
            || fact.allocation_epoch != record.allocation_epoch
        {
            return Err(SourceTypesError::Unresolved);
        }
        let hole = match fact.value.ty {
            Ty::NumericHole(id) => Some(id),
            _ => None,
        };
        Ok(NumericOperand {
            observation,
            hole,
            ty: value.ty.clone(),
            constant: value.constant.clone(),
            encoded: None,
            dependencies: value.numeric.clone(),
        })
    }
    pub(super) fn resolve_numeric_operands(
        &mut self,
        left: &mut Value,
        right: &mut Value,
        span: Span,
    ) {
        if !matches!(left.ty, Ty::NumericHole(_)) && !matches!(right.ty, Ty::NumericHole(_)) {
            return;
        }
        let roots: Vec<_> = [&*left, &*right]
            .into_iter()
            .filter_map(|value| match value.ty {
                Ty::NumericHole(id) => Some(id),
                _ => None,
            })
            .collect();
        let preferences = match self.numeric_preferences(&roots) {
            Ok(preferences) => preferences,
            Err(error) => {
                self.unsupported(span, format!("numeric preferences failed: {error}"));
                return;
            }
        };
        let mut selected = [&*left, &*right].into_iter().find_map(|value| {
            (!value.unsuffixed_numeric && super::numeric::numeric_type(&value.ty).is_some())
                .then(|| value.ty.clone())
        });
        for defaults in [false, true] {
            if selected.is_some() {
                break;
            }
            for value in [&*left, &*right] {
                let Ty::NumericHole(id) = value.ty else {
                    continue;
                };
                selected = match preferences.get(id, defaults) {
                    Ok(preferred) => preferred,
                    Err(error) => {
                        self.unsupported(
                            span,
                            format!("numeric preference lookup failed: {error}"),
                        );
                        return;
                    }
                };
                if selected.is_some() {
                    break;
                }
            }
        }
        let selected = selected.unwrap_or_else(|| Ty::Int("int".into()));
        for value in [left, right] {
            if matches!(value.ty, Ty::NumericHole(_)) {
                if let Err(error) = self.commit_numeric_value(value, &selected) {
                    self.unsupported(span, format!("numeric operand resolution failed: {error}"));
                }
            } else if value.unsuffixed_numeric && value.ty != selected {
                self.unsupported(
                    span,
                    "late numeric operand selection requires a deferred expression certificate",
                );
            }
        }
    }

    pub(super) fn numeric_pending_literal(
        &mut self,
        expression: &Expr,
        frame: &Frame,
    ) -> Option<Value> {
        let (literal, span, minus) = match &expression.kind {
            ExprKind::Literal(literal @ (Literal::Integer(_) | Literal::Float(_))) => {
                (literal, expression.span, None)
            }
            ExprKind::Unary { operator, operand } if operator == "-" => match &operand.kind {
                ExprKind::Literal(literal @ (Literal::Integer(_) | Literal::Float(_))) => {
                    (literal, operand.span, Some(expression.span))
                }
                _ => return None,
            },
            _ => return None,
        };
        let limit = ParseLimit {
            max_bytes: 1_048_576,
        };
        let text_len = match literal {
            Literal::Integer(text) | Literal::Float(text) => text.len(),
            _ => 0,
        };
        if !self
            .application_effect
            .admit(text_len.saturating_mul(4).saturating_add(16))
        {
            self.unsupported(
                expression.span,
                "pending numeric literal exceeds its work bound",
            );
            return Some(Value::scalar(Ty::Unknown, None, CauseId(0)));
        }
        let parsed = match literal {
            Literal::Integer(text) => ExactLiteral::integer(text, minus.is_some(), limit),
            Literal::Float(text) => ExactLiteral::decimal(text, minus.is_some(), limit),
            _ => unreachable!(),
        };
        let exact = match parsed {
            Ok(exact) => exact,
            Err(error) => {
                let cause = self.cause(
                    CauseKind::Source,
                    expression.span,
                    "pending exact numeric literal",
                    [],
                );
                self.numeric_error(error, expression.span, cause);
                return Some(Value::scalar(Ty::Unknown, None, cause));
            }
        };
        if let Some(selected) = exact.written_type().or_else(|| {
            (self.numeric.deferred_depth == 0).then_some(if matches!(literal, Literal::Float(_)) {
                NumberType::F64
            } else {
                NumberType::Int
            })
        }) {
            return self.numeric_expected_literal(
                expression,
                &crate::sema::numeric_selection::selected_ty(selected),
                frame,
            );
        }
        let cause = self.cause(
            CauseKind::Source,
            expression.span,
            "unselected exact numeric literal",
            [],
        );
        let context = self.invocation_context(frame.callable_owner);
        let birth = match self.numeric_birth() {
            Ok(birth)
                if birth.context == context
                    && Some(birth.occurrence.source) == expression.hir_id =>
            {
                birth
            }
            _ => {
                self.unsupported(
                    expression.span,
                    "pending numeric literal has no actual activation",
                );
                return Some(Value::scalar(Ty::Unknown, None, cause));
            }
        };
        let site = self.numeric_literal_site(expression)?;
        let use_id = NumericUseId(self.numeric.uses.len() as u32);
        let id = NumericHoleId(self.numeric.holes.len() as u32);
        self.numeric.uses.push(NumericUse {
            id: use_id,
            hole: id,
            site,
            birth,
            selection: None,
            exact,
            span,
            cause,
        });
        self.numeric.holes.push(NumericHole {
            id,
            birth,
            domain: if matches!(literal, Literal::Float(_)) {
                NumericDomain::FloatOnly
            } else {
                NumericDomain::IntegerOrFloat
            },
            term: NumericTerm::Literal(use_id),
            state: NumericHoleState::Pending,
            span: expression.span,
        });
        let mut value = Value::scalar(Ty::NumericHole(id), None, cause);
        value.numeric.uses.insert(use_id);
        value.literal_number = true;
        if minus.is_some() {
            let evaluation_context = context;
            let environment = self.physical_evaluation_environment(span);
            let operand = match self.copy_value_for_emission(&value) {
                Ok(operand) => operand,
                Err(error) => {
                    self.unsupported(
                        span,
                        format!("pending signed operand emission admission: {error}"),
                    );
                    return Some(value);
                }
            };
            let _ = self.application_effect.observe(
                || super::super::application_effect::ObservationInput {
                    allocation_epoch: self.recency_moves.len(),
                    source_id: match &expression.kind {
                        ExprKind::Unary { operand, .. } => operand.hir_id,
                        _ => None,
                    },
                    span,
                    value: operand,
                },
                evaluation_context,
                frame.owner,
                environment,
                None,
            );
        }
        Some(value)
    }

    pub(super) fn numeric_pending_binary(
        &mut self,
        left: &Value,
        right: &Value,
        operator: &str,
        span: Span,
    ) -> Option<Value> {
        if !matches!(left.ty, Ty::NumericHole(_)) && !matches!(right.ty, Ty::NumericHole(_)) {
            return None;
        }
        let cause = self.cause(
            CauseKind::Source,
            span,
            "numeric arithmetic awaits one selected operand type",
            [left.cause, right.cause],
        );
        let id = NumericHoleId(self.numeric.holes.len() as u32);
        let prepared = (|| {
            let birth = self.numeric_birth()?;
            let original = self
                .semantic_hir
                .expression(birth.occurrence.source)
                .ok_or(SourceTypesError::MissingNode)?;
            let crate::hir::nodes::ExprKind::Binary {
                operator: actual,
                left: left_id,
                right: right_id,
            } = &original.kind
            else {
                return Err(SourceTypesError::Unresolved);
            };
            if actual != operator {
                return Err(SourceTypesError::Unresolved);
            }
            let (left_id, right_id) = (*left_id, *right_id);
            let left = self.numeric_operand(left, left_id, birth)?;
            let right = self.numeric_operand(right, right_id, birth)?;
            Ok((birth, left, right))
        })();
        let (birth, left_operand, right_operand) = match prepared {
            Ok(prepared) => prepared,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("numeric binary lost its actual operand occurrences: {error}"),
                );
                return Some(Value::scalar(Ty::Unknown, None, cause));
            }
        };
        let float_only = |value: &Value| match value.ty {
            Ty::NumericHole(id) => {
                self.numeric.holes[id.0 as usize].domain == NumericDomain::FloatOnly
            }
            Ty::Float(_) => true,
            _ => false,
        };
        let domain = if float_only(left) || float_only(right) {
            NumericDomain::FloatOnly
        } else {
            NumericDomain::IntegerOrFloat
        };
        self.numeric.holes.push(NumericHole {
            id,
            birth,
            domain,
            term: NumericTerm::Binary {
                operator: operator.into(),
                left: Box::new(left_operand),
                right: Box::new(right_operand),
            },
            state: NumericHoleState::Pending,
            span,
        });
        let mut value = Value::scalar(Ty::NumericHole(id), None, cause);
        value.numeric.include(&left.numeric);
        value.numeric.include(&right.numeric);
        Some(value)
    }

    pub(super) fn numeric_pending_unary(
        &mut self,
        value: &Value,
        operator: &str,
        span: Span,
    ) -> Option<Value> {
        let Ty::NumericHole(child) = value.ty else {
            return None;
        };
        let id = NumericHoleId(self.numeric.holes.len() as u32);
        let prepared = (|| {
            let birth = self.numeric_birth()?;
            let original = self
                .semantic_hir
                .expression(birth.occurrence.source)
                .ok_or(SourceTypesError::MissingNode)?;
            let crate::hir::nodes::ExprKind::Unary {
                operator: actual,
                operand,
            } = &original.kind
            else {
                return Err(SourceTypesError::Unresolved);
            };
            if actual != operator {
                return Err(SourceTypesError::Unresolved);
            }
            let operand = *operand;
            Ok((birth, self.numeric_operand(value, operand, birth)?))
        })();
        let (birth, operand) = match prepared {
            Ok(prepared) => prepared,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("numeric unary lost its actual operand occurrence: {error}"),
                );
                return Some(Value::scalar(Ty::Unknown, None, value.cause));
            }
        };
        self.numeric.holes.push(NumericHole {
            id,
            birth,
            domain: self.numeric.holes[child.0 as usize].domain,
            term: NumericTerm::Unary {
                operator: operator.into(),
                operand: Box::new(operand),
            },
            state: NumericHoleState::Pending,
            span,
        });
        let mut result = value.clone();
        result.ty = Ty::NumericHole(id);
        Some(result)
    }

    pub(super) fn numeric_preferences(
        &mut self,
        roots: &[NumericHoleId],
    ) -> Result<crate::sema::numeric_selection::NumericPreferences, SourceTypesError> {
        let holes = &self.numeric.holes;
        self.application_effect
            .with_work(|work| crate::sema::numeric_selection::preferences(holes, roots, work))
    }
    pub(super) fn numeric_preference(
        &mut self,
        id: NumericHoleId,
    ) -> Result<Option<Ty>, SourceTypesError> {
        self.numeric_preferences(&[id])?.get(id, true)
    }

    pub(super) fn numeric_arithmetic_constant(
        &self,
        ty: &Ty,
        constant: Option<Constant>,
    ) -> Option<Constant> {
        if !matches!(constant, Some(Constant::Integer(_))) {
            return constant;
        }
        crate::sema::numeric_selection::arithmetic_constant(
            super::numeric::numeric_type(ty)?,
            constant,
            self.layout,
        )
    }

    fn resolve_numeric_hole(
        &mut self,
        id: NumericHoleId,
        selected: NumberType,
        cause: CauseId,
    ) -> Result<std::sync::Arc<crate::sema::numeric_selection::NumericResolution>, SourceTypesError>
    {
        if let Ok(resolution) = self.numeric.resolution(id) {
            if resolution.number_type != selected {
                let span = self.numeric.holes[id.0 as usize].span;
                self.error(
                    "E0301",
                    span,
                    "numeric expression has contradictory selected types",
                    [cause],
                );
                return Err(SourceTypesError::Unresolved);
            }
            return Ok(resolution.clone());
        }
        if !self.application_effect.admit(4) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let hole = self
            .numeric
            .holes
            .get(id.0 as usize)
            .filter(|hole| hole.id == id)
            .ok_or(SourceTypesError::MissingNode)?;
        if matches!(hole.state, NumericHoleState::Invalid) {
            return Err(SourceTypesError::Unresolved);
        }
        let span = hole.span;
        let (literal, children) = match &hole.term {
            NumericTerm::Literal(use_id) => (Some(*use_id), vec![]),
            NumericTerm::Unary { operand, .. } => (None, operand.hole.into_iter().collect()),
            NumericTerm::Binary { left, right, .. } => {
                (None, left.hole.into_iter().chain(right.hole).collect())
            }
            NumericTerm::Join(_) => {
                self.unsupported(
                    span,
                    "deferred branch numeric selection requires an exit-aware term proof",
                );
                return Err(SourceTypesError::Unresolved);
            }
        };
        for child in &children {
            if child.0 >= id.0 {
                return Err(SourceTypesError::Unresolved);
            }
            self.resolve_numeric_hole(*child, selected, cause)?;
        }
        if let Some(use_id) = literal {
            let use_ = self
                .numeric
                .uses
                .get(use_id.0 as usize)
                .filter(|use_| use_.id == use_id && use_.hole == id)
                .ok_or(SourceTypesError::MissingNode)?;
            let cost = use_.exact.magnitude().map_or_else(
                || use_.exact.decimal_magnitude().map_or(0, str::len),
                |n| n.bits().div_ceil(8) as usize,
            );
            if !self.application_effect.admit(cost.saturating_add(4)) {
                return Err(SourceTypesError::BudgetExceeded);
            }
            let encoded = match use_.exact.select(selected, self.layout) {
                Ok(encoded) => encoded,
                Err(error) => {
                    self.numeric_error(error, span, cause);
                    self.numeric.holes[id.0 as usize].state = NumericHoleState::Invalid;
                    return Err(SourceTypesError::Unresolved);
                }
            };
            let use_ = &self.numeric.uses[use_id.0 as usize];
            let selection = NumericSelection {
                id: NumericSelectionId(self.numeric.selections.len() as u32),
                literal: use_id,
                site: use_.site,
                birth: use_.birth,
                span: use_.span,
                ty: selected,
                layout: self.layout,
                encoded,
                cause: use_.cause,
            };
            self.numeric.selections.push(selection.clone());
            self.numeric.uses[use_id.0 as usize].selection = Some(selection.id);
            self.invocation_witnesses
                .push(super::super::effect_identity::InvocationWitness {
                    context: selection.birth.context,
                    span: selection.span,
                    kind: super::super::effect_identity::InvocationWitnessKind::NumericSelection(
                        selection,
                    ),
                });
        }
        let numeric = &self.numeric;
        let result = self.application_effect.with_work(|work| {
            let mut memo = BTreeMap::new();
            for child in &children {
                let result = numeric.resolution(*child)?.try_clone(work)?;
                *work = work
                    .checked_sub(1)
                    .ok_or(SourceTypesError::BudgetExceeded)?;
                memo.insert(*child, result);
            }
            crate::sema::numeric_selection::evaluate_cached(
                crate::sema::numeric_selection::NumericInputs {
                    holes: &numeric.holes,
                    uses: &numeric.uses,
                    selections: &numeric.selections,
                    layout: self.layout,
                },
                id,
                selected,
                work,
                &mut memo,
            )
        });
        let result = match result {
            Ok(result) => std::sync::Arc::new(result),
            Err(error) => {
                self.numeric.holes[id.0 as usize].state = NumericHoleState::Invalid;
                self.unsupported(span, format!("numeric term could not be resolved: {error}"));
                return Err(error);
            }
        };
        self.numeric.holes[id.0 as usize].state = NumericHoleState::Committed {
            cause,
            resolution: result.clone(),
        };
        Ok(result)
    }

    pub(super) fn commit_numeric_value(
        &mut self,
        value: &mut Value,
        expected: &Ty,
    ) -> Result<Option<NumericHoleId>, SourceTypesError> {
        let Ty::NumericHole(id) = value.ty else {
            return Ok(None);
        };
        let Some(selected) = super::numeric::numeric_type(expected) else {
            let span = self
                .numeric
                .holes
                .get(id.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?
                .span;
            self.error(
                "E0301",
                span,
                "numeric literal expression requires a numeric selected type",
                [value.cause],
            );
            return Err(SourceTypesError::Unresolved);
        };
        let resolved = self.resolve_numeric_hole(id, selected, value.cause)?;
        self.application_effect
            .with_work(|work| resolved.apply(value, work))?;
        Ok(Some(id))
    }
}
