//! Numeric selection is owned by the producing evaluation, not its span cache.
use super::*;
use crate::numeric_literals::{
    EncodedNumber, Error as NumericError, ExactLiteral, NumberType, ParseLimit,
};
use crate::sema::numeric_selection::{
    NumericDomain, NumericHole, NumericHoleState, NumericSelection, NumericTerm, NumericUse,
};
use num_traits::ToPrimitive;
use ril_compiler_core::ids::{NumericHoleId, NumericSelectionId, NumericUseId};

pub(super) fn numeric_type(ty: &Ty) -> Option<NumberType> {
    Some(match ty {
        Ty::Int(name) => match name.as_str() {
            "int" => NumberType::Int,
            "i8" => NumberType::I8,
            "i16" => NumberType::I16,
            "i32" => NumberType::I32,
            "i64" => NumberType::I64,
            "u8" => NumberType::U8,
            "u16" => NumberType::U16,
            "u32" => NumberType::U32,
            "u64" => NumberType::U64,
            "bigint" => NumberType::BigInt,
            _ => return None,
        },
        Ty::Float(name) if name == "f32" => NumberType::F32,
        Ty::Float(name) if name == "f64" => NumberType::F64,
        _ => return None,
    })
}

impl Checker {
    pub(super) fn legacy_numeric_context(
        &mut self,
        value: &Value,
        expected: &Ty,
        span: Span,
    ) -> bool {
        match (&value.ty, expected) {
            (Ty::Int(_), Ty::Float(_)) => {
                self.unsupported(span,"integer-to-float operand selection requires its exact deferred producer certificate");
                false
            }
            (Ty::Float(_), Ty::Int(_)) => {
                self.error(
                    "E0301",
                    span,
                    "a floating-point literal cannot select an integer type",
                    [value.cause],
                );
                false
            }
            _ => {
                self.numeric_context(value, expected, span);
                true
            }
        }
    }

    pub(super) fn numeric_expected_literal(
        &mut self,
        expression: &Expr,
        expected: &Ty,
        frame: &Frame,
    ) -> Option<Value> {
        let selected_type = numeric_type(expected)?;
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
            // A normalized static value is already typed. The ordinary
            // literal path validates it; no receiving context can reopen it.
            return None;
        }
        let cause = self.cause(
            CauseKind::Source,
            expression.span,
            "exact numeric literal selection",
            [],
        );
        // This is an implementation input limit, never a source budget unit.
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
                self.numeric_error(error, expression.span, cause);
                return Some(Value::scalar(Ty::Unknown, None, cause));
            }
        };
        let context = self.invocation_context(frame.callable_owner);
        let use_id = NumericUseId(self.numeric.uses.len() as u32);
        let hole_id = NumericHoleId(self.numeric.holes.len() as u32);
        self.numeric.uses.push(NumericUse {
            id: use_id,
            exact: exact.clone(),
            span,
            immediate_minus: minus,
            cause,
            context,
        });
        self.numeric.holes.push(NumericHole {
            id: hole_id,
            domain: if matches!(literal, Literal::Integer(_)) {
                NumericDomain::IntegerOrFloat
            } else {
                NumericDomain::FloatOnly
            },
            term: NumericTerm::Literal(use_id),
            state: NumericHoleState::Pending,
            span: expression.span,
        });
        let mut value = Value::scalar(Ty::NumericHole(hole_id), None, cause);
        value.numeric.uses.insert(use_id);
        let encoded = match exact.select(selected_type, self.layout) {
            Ok(encoded) => encoded,
            Err(error) => {
                self.numeric.holes[hole_id.0 as usize].state = NumericHoleState::Invalid;
                self.numeric_error(error, expression.span, cause);
                return Some(value);
            }
        };
        let id = NumericSelectionId(self.numeric.selections.len() as u32);
        value.ty = expected.clone();
        value.constant = match &encoded {
            EncodedNumber::Integer { value, .. } => Some(Constant::Integer(*value)),
            EncodedNumber::BigInteger(value) => value.to_i128().map(Constant::Integer),
            EncodedNumber::Float(_) => None,
        };
        if selected_type == NumberType::Int {
            value.static_coordinate = value.constant.as_ref().and_then(|constant| {
                if let Constant::Integer(value) = constant {
                    Some(StaticCoordinate::Index(*value))
                } else {
                    None
                }
            });
        }
        value.literal_number = true;
        value.numeric.selections.insert(id);
        let selection = NumericSelection {
            id,
            literal: use_id,
            span,
            context,
            ty: selected_type,
            layout: self.layout,
            encoded,
            cause,
        };
        self.numeric.selections.push(selection.clone());
        self.invocation_witnesses
            .push(super::super::effect_identity::InvocationWitness {
                context,
                span,
                kind: super::super::effect_identity::InvocationWitnessKind::NumericSelection(
                    selection,
                ),
            });
        self.numeric.holes[hole_id.0 as usize].state = NumericHoleState::Committed {
            ty: selected_type,
            cause,
        };
        if minus.is_some() {
            // The atomic signed-literal rule still covers the operand syntax
            // site, without materializing an out-of-range positive temporary.
            let mut operand = value.clone();
            operand.constant = None;
            let evaluation_context = context;
            let _ = self.application_effect.observe(
                || super::super::ExpressionFact {
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
                None,
            );
        }
        Some(value)
    }

    pub(super) fn numeric_error(&mut self, error: NumericError, span: Span, cause: CauseId) {
        match error {
            NumericError::InvalidSyntax => {
                self.error("E0111", span, "invalid numeric literal spelling", [cause])
            }
            NumericError::IncompatibleSelection => self.error(
                "E0301",
                span,
                "written numeric type does not fit the selected context",
                [cause],
            ),
            NumericError::OutOfRange => self.error(
                "E0326",
                span,
                "integer literal is outside its selected type's range",
                [cause],
            ),
            NumericError::ResourceLimit => {
                self.unsupported(span, "exact numeric literal parsing implementation limit")
            }
            NumericError::UnsupportedTarget | NumericError::UnsupportedDecimal => {
                self.unsupported(span, "exact numeric literal representation is unavailable")
            }
        }
    }
}
