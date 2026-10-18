//! Pending scalar arithmetic keeps its source operator tree. Solving it only
//! selects types and leaf encodings; it never evaluates a runtime expression.
use super::super::numeric_selection::{
    NumericDomain, NumericHole, NumericHoleState, NumericOperand, NumericSelection, NumericTerm,
    NumericUse,
};
use super::*;
use crate::numeric_literals::{EncodedNumber, ExactLiteral, NumberType, ParseLimit};
use num_traits::ToPrimitive;
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

fn operand(value: &Value) -> NumericOperand {
    NumericOperand {
        ty: value.ty.clone(),
        constant: value.constant.clone(),
        encoded: None,
        dependencies: value.numeric.clone(),
    }
}

impl Checker {
    pub(super) fn resolve_numeric_operands(
        &mut self,
        left: &mut Value,
        right: &mut Value,
        span: Span,
    ) {
        if !matches!(left.ty, Ty::NumericHole(_)) && !matches!(right.ty, Ty::NumericHole(_)) {
            return;
        }
        let mut selected = [&*left, &*right].into_iter().find_map(|value| {
            (!value.unsuffixed_numeric && super::numeric::numeric_type(&value.ty).is_some())
                .then(|| value.ty.clone())
        });
        for defaults in [false, true] {
            if selected.is_some() {
                break;
            }
            selected = [&*left, &*right].into_iter().find_map(|value| {
                let Ty::NumericHole(id) = value.ty else {
                    return None;
                };
                if defaults {
                    self.numeric_preference(id)
                } else {
                    self.numeric_rigid_preference(id)
                }
            });
        }
        let selected = selected.unwrap_or_else(|| Ty::Int("int".into()));
        for value in [left, right] {
            if matches!(value.ty, Ty::NumericHole(_)) {
                self.commit_numeric_value(value, &selected);
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
        if self.numeric.deferred_depth == 0 {
            return None;
        }
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
        if let Literal::Float(text) = literal
            && !matches!(crate::static_eval::committed_float::decode(text), Ok(None))
        {
            return None;
        }
        let limit = ParseLimit {
            max_bytes: 1_048_576,
        };
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
        if exact.written_type().is_some() {
            return None;
        }
        let cause = self.cause(
            CauseKind::Source,
            expression.span,
            "unselected exact numeric literal",
            [],
        );
        let context = self.invocation_context(frame.callable_owner);
        let use_id = NumericUseId(self.numeric.uses.len() as u32);
        self.numeric.uses.push(NumericUse {
            id: use_id,
            exact,
            span,
            immediate_minus: minus,
            cause,
            context,
        });
        let id = NumericHoleId(self.numeric.holes.len() as u32);
        self.numeric.holes.push(NumericHole {
            id,
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
            self.invocation_expressions
                .push(super::super::effect_identity::InvocationExpression {
                    context,
                    expression: self.expression_facts.len(),
                    argument_of: None,
                });
            self.expression_facts.push(super::super::ExpressionFact {
                allocation_epoch: self.recency_moves.len(),
                source_id: match &expression.kind {
                    ExprKind::Unary { operand, .. } => operand.hir_id,
                    _ => None,
                },
                span,
                value: value.clone(),
            });
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
            domain,
            term: NumericTerm::Binary {
                operator: operator.into(),
                left: Box::new(operand(left)),
                right: Box::new(operand(right)),
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
        self.numeric.holes.push(NumericHole {
            id,
            domain: self.numeric.holes[child.0 as usize].domain,
            term: NumericTerm::Unary {
                operator: operator.into(),
                operand: Box::new(operand(value)),
            },
            state: NumericHoleState::Pending,
            span,
        });
        let mut result = value.clone();
        result.ty = Ty::NumericHole(id);
        Some(result)
    }

    pub(super) fn numeric_rigid_preference(&self, id: NumericHoleId) -> Option<Ty> {
        fn visit(checker: &Checker, value: &NumericOperand) -> Option<Ty> {
            match value.ty {
                Ty::NumericHole(id) => checker.numeric_rigid_preference(id),
                _ => super::numeric::numeric_type(&value.ty).map(|_| value.ty.clone()),
            }
        }
        match &self.numeric.holes[id.0 as usize].term {
            NumericTerm::Unary { operand, .. } => visit(self, operand),
            NumericTerm::Binary { left, right, .. } => {
                visit(self, left).or_else(|| visit(self, right))
            }
            _ => None,
        }
    }
    pub(super) fn numeric_preference(&self, id: NumericHoleId) -> Option<Ty> {
        self.numeric_rigid_preference(id).or_else(|| {
            (self.numeric.holes[id.0 as usize].domain == NumericDomain::FloatOnly)
                .then(|| Ty::Float("f64".into()))
        })
    }

    pub(super) fn numeric_arithmetic_constant(
        &self,
        ty: &Ty,
        constant: Option<Constant>,
    ) -> Option<Constant> {
        let Some(Constant::Integer(number)) = constant else {
            return constant;
        };
        let selected = super::numeric::numeric_type(ty)?;
        if matches!(selected, NumberType::F32 | NumberType::F64) {
            return None;
        }
        let text = number.to_string();
        let (text, negative) = text
            .strip_prefix('-')
            .map_or((text.as_str(), false), |text| (text, true));
        ExactLiteral::integer(text, negative, ParseLimit { max_bytes: 128 })
            .ok()?
            .select(selected, self.layout)
            .ok()?;
        Some(Constant::Integer(number))
    }

    fn resolve_numeric_operand(
        &mut self,
        value: NumericOperand,
        selected: NumberType,
        cause: CauseId,
        span: Span,
    ) -> NumericOperand {
        if let Ty::NumericHole(id) = value.ty {
            return self.resolve_numeric_hole(id, selected, cause);
        }
        if super::numeric::numeric_type(&value.ty) != Some(selected) {
            self.error(
                "E0301",
                span,
                "stored or suffixed numeric operand cannot be reselected",
                [cause],
            );
        }
        value
    }

    fn resolve_numeric_hole(
        &mut self,
        id: NumericHoleId,
        selected: NumberType,
        cause: CauseId,
    ) -> NumericOperand {
        if let Some(value) = self.numeric.resolved.get(&id) {
            let value = value.clone();
            if super::numeric::numeric_type(&value.ty) != Some(selected) {
                self.error(
                    "E0301",
                    self.numeric.holes[id.0 as usize].span,
                    "numeric expression has contradictory selected types",
                    [cause],
                );
            }
            return value;
        }
        let hole = self.numeric.holes[id.0 as usize].clone();
        let signed_operand = match &hole.term {
            NumericTerm::Literal(use_id) => {
                let use_ = &self.numeric.uses[use_id.0 as usize];
                use_.immediate_minus.map(|_| use_.span)
            }
            _ => None,
        };
        let ty = super::numeric_application::selected_type(selected);
        let mut output = NumericOperand {
            ty: ty.clone(),
            constant: None,
            encoded: None,
            dependencies: Default::default(),
        };
        match hole.term {
            NumericTerm::Literal(use_id) => {
                let use_ = self.numeric.uses[use_id.0 as usize].clone();
                output.dependencies.uses.insert(use_id);
                match use_.exact.select(selected, self.layout) {
                    Ok(encoded) => {
                        output.constant = match &encoded {
                            EncodedNumber::Integer { value, .. } => Some(Constant::Integer(*value)),
                            EncodedNumber::BigInteger(value) => {
                                value.to_i128().map(Constant::Integer)
                            }
                            EncodedNumber::Float(_) => None,
                        };
                        let selection_id = NumericSelectionId(self.numeric.selections.len() as u32);
                        output.dependencies.selections.insert(selection_id);
                        let selection = NumericSelection {
                            id: selection_id,
                            literal: use_id,
                            span: use_.span,
                            context: use_.context,
                            ty: selected,
                            layout: self.layout,
                            encoded: encoded.clone(),
                            cause: use_.cause,
                        };
                        self.numeric.selections.push(selection.clone());
                        self.invocation_witnesses.push(super::super::effect_identity::InvocationWitness{context:use_.context,span:use_.span,kind:super::super::effect_identity::InvocationWitnessKind::NumericSelection(selection)});
                        output.encoded = Some(encoded);
                    }
                    Err(error) => {
                        self.numeric_error(error, hole.span, cause);
                        self.numeric.holes[id.0 as usize].state = NumericHoleState::Invalid;
                        return output;
                    }
                }
            }
            NumericTerm::Binary {
                operator,
                left,
                right,
            } => {
                let left = self.resolve_numeric_operand(*left, selected, cause, hole.span);
                let right = self.resolve_numeric_operand(*right, selected, cause, hole.span);
                output.dependencies.include(&left.dependencies);
                output.dependencies.include(&right.dependencies);
                // This optional diagnostic fact has the same conservative
                // arithmetic folding as the ordinary path. Division, overflow
                // and floating arithmetic keep their runtime execution.
                output.constant = match (&left.constant, &right.constant, operator.as_str()) {
                    (Some(Constant::Integer(left)), Some(Constant::Integer(right)), "+") => {
                        left.checked_add(*right).map(Constant::Integer)
                    }
                    (Some(Constant::Integer(left)), Some(Constant::Integer(right)), "-") => {
                        left.checked_sub(*right).map(Constant::Integer)
                    }
                    (Some(Constant::Integer(left)), Some(Constant::Integer(right)), "*") => {
                        left.checked_mul(*right).map(Constant::Integer)
                    }
                    _ => None,
                };
            }
            NumericTerm::Unary { operator, operand } => {
                let value = self.resolve_numeric_operand(*operand, selected, cause, hole.span);
                output.dependencies = value.dependencies;
                output.constant = if operator == "-" {
                    match value.constant {
                        Some(Constant::Integer(value)) => {
                            value.checked_neg().map(Constant::Integer)
                        }
                        _ => None,
                    }
                } else {
                    None
                };
            }
            NumericTerm::Join(_) => {
                self.unsupported(
                    hole.span,
                    "deferred branch numeric selection requires an exit-aware term proof",
                );
                return output;
            }
        }
        output.constant = self.numeric_arithmetic_constant(&output.ty, output.constant);
        self.numeric.holes[id.0 as usize].state = NumericHoleState::Committed {
            ty: selected,
            cause,
        };
        self.numeric.resolved.insert(id, output.clone());
        for fact in &mut self.expression_facts {
            if fact.value.ty == Ty::NumericHole(id) {
                fact.value.ty = output.ty.clone();
                fact.value.constant = if signed_operand == Some(fact.span) {
                    None
                } else {
                    output.constant.clone()
                };
                fact.value.numeric = output.dependencies.clone();
                fact.value.unsuffixed_numeric = false;
            }
        }
        output
    }

    pub(super) fn commit_numeric_value(&mut self, value: &mut Value, expected: &Ty) {
        let Ty::NumericHole(id) = value.ty else {
            return;
        };
        let Some(selected) = super::numeric::numeric_type(expected) else {
            self.error(
                "E0301",
                self.numeric.holes[id.0 as usize].span,
                "numeric literal expression requires a numeric selected type",
                [value.cause],
            );
            return;
        };
        let resolved = self.resolve_numeric_hole(id, selected, value.cause);
        value.ty = resolved.ty;
        value.constant = resolved.constant;
        value.numeric = resolved.dependencies;
        value.unsuffixed_numeric = false;
    }
}
