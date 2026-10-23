//! Numeric selection is owned by the producing evaluation, not its span cache.
use super::*;
use crate::numeric_literals::{Error as NumericError, ExactLiteral, NumberType, ParseLimit};
use crate::sema::numeric_selection::{
    NumericBirth, NumericDomain, NumericHole, NumericHoleState, NumericSelection, NumericSite,
    NumericTerm, NumericUse,
};
use ril_compiler_core::ids::{NumericHoleId, NumericSelectionId, NumericUseId};

pub(super) fn numeric_type(ty: &Ty) -> Option<NumberType> {
    crate::sema::numeric_selection::number_type(ty)
}

impl Checker {
    fn numeric_pattern_type(
        &mut self,
        pattern: ril_compiler_core::ids::PatternId,
        birth: NumericBirth,
        subject: Option<&EvaluatedValue>,
    ) -> Result<NumberType, crate::sema::source_types::SourceTypesError> {
        use crate::sema::numeric_selection::NumericReplayInputs;
        use crate::sema::source_types_ref::SourceTypesRef;
        let numeric = &self.numeric;
        let hir = &self.semantic_hir;
        let bindings = &self.bindings;
        let constructors = &self.constructors;
        let source_types = self.type_source.storage.live_types();
        let witnesses = &self.invocation_witnesses;
        let explanations = &self.explanations;
        let allocation_history = &self.recency_moves;
        let target_layout = Some(self.layout);
        let open = self.application_effect.current_activation();
        self.application_effect.with_evaluation_work(
            |expressions, evaluations, activations, work| {
                crate::sema::numeric_selection::pattern_number_type_inputs(
                    NumericReplayInputs {
                        semantic_hir: Some(hir),
                        target_layout,
                        numeric_holes: &numeric.holes,
                        numeric_uses: &numeric.uses,
                        numeric_selections: &numeric.selections,
                        activations,
                        evaluations,
                        expressions,
                        allocation_history,
                        bindings,
                        constructors,
                        source_types: SourceTypesRef::Live(source_types),
                        witnesses,
                        explanations,
                        open,
                        session: Some(&numeric.replay),
                        subject,
                        frozen: None,
                        query: None,
                    },
                    pattern,
                    birth,
                    work,
                )
            },
        )
    }
    pub(super) fn numeric_birth(
        &mut self,
    ) -> Result<NumericBirth, crate::sema::source_types::SourceTypesError> {
        use crate::sema::source_types::SourceTypesError;
        if !self.application_effect.admit(4) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let id = self
            .application_effect
            .current_activation()
            .ok_or(SourceTypesError::MissingNode)?;
        let activation = self
            .application_effect
            .activations
            .get(id.0 as usize)
            .filter(|activation| activation.id == id)
            .ok_or(SourceTypesError::MissingNode)?;
        let source = activation.source.ok_or(SourceTypesError::MissingNode)?;
        self.semantic_hir
            .expression(source)
            .ok_or(SourceTypesError::MissingNode)?;
        Ok(NumericBirth {
            occurrence: crate::sema::application_effect::OccurrenceIdentity {
                source,
                activation: id,
            },
            scope: activation.scope,
            context: activation.context,
            allocation_epoch: self.recency_moves.len(),
        })
    }

    pub(super) fn numeric_literal_site(&self, expression: &Expr) -> Option<NumericSite> {
        let original = self.semantic_hir.expression(expression.hir_id?)?;
        if let crate::hir::nodes::NodeOrigin::Generated {
            anchor: crate::hir::nodes::NodeId::Pattern(pattern),
            kind: crate::hir::nodes::GeneratedKind::PatternValue,
            ..
        } = original.info.origin
        {
            return Some(NumericSite::Pattern(pattern));
        }
        let (literal, immediate_minus) = match &expression.kind {
            ExprKind::Literal(Literal::Integer(_) | Literal::Float(_)) => {
                (expression.hir_id?, None)
            }
            ExprKind::Unary { operator, operand } if operator == "-" => {
                (operand.hir_id?, Some(expression.hir_id?))
            }
            _ => return None,
        };
        Some(NumericSite::Expression {
            literal,
            immediate_minus,
        })
    }
    pub(super) fn numeric_expected_literal(
        &mut self,
        expression: &Expr,
        expected: &Ty,
        frame: &Frame,
        subject: Option<&EvaluatedValue>,
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
        let cause = self.cause(
            CauseKind::Source,
            expression.span,
            "exact numeric literal selection",
            [],
        );
        let site = self.numeric_literal_site(expression)?;
        let selected_type = match site {
            NumericSite::Expression { .. } => numeric_type(expected)?,
            NumericSite::Pattern(pattern) => {
                let selected = self
                    .numeric_birth()
                    .and_then(|birth| self.numeric_pattern_type(pattern, birth, subject));
                match selected {
                    Ok(selected) => selected,
                    Err(error) => {
                        self.unsupported(
                            expression.span,
                            format!("numeric pattern requires its actual subject Source: {error}"),
                        );
                        return Some(Value::scalar(Ty::Unknown, None, cause));
                    }
                }
            }
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
                "numeric literal admission exceeds its work bound",
            );
            return Some(Value::scalar(Ty::Unknown, None, cause));
        }
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
                    "numeric literal has no actual producing activation",
                );
                return Some(Value::scalar(Ty::Unknown, None, cause));
            }
        };
        let use_id = NumericUseId(self.numeric.uses.len() as u32);
        let hole_id = NumericHoleId(self.numeric.holes.len() as u32);
        self.numeric.uses.push(NumericUse {
            id: use_id,
            hole: hole_id,
            site,
            birth,
            selection: None,
            exact: exact.clone(),
            span,
            cause,
        });
        self.numeric.holes.push(NumericHole {
            id: hole_id,
            birth,
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
        value.ty = crate::sema::numeric_selection::selected_ty(selected_type);
        value.constant = crate::sema::numeric_selection::encoded_constant(&encoded);
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
            site,
            birth,
            span,
            ty: selected_type,
            layout: self.layout,
            encoded,
            cause,
        };
        self.numeric.selections.push(selection.clone());
        self.numeric.uses[use_id.0 as usize].selection = Some(id);
        let numeric = &self.numeric;
        let resolution = self.application_effect.with_work(|work| {
            crate::sema::numeric_selection::evaluate(
                &numeric.holes,
                &numeric.uses,
                &numeric.selections,
                hole_id,
                selected_type,
                self.layout,
                work,
            )
        });
        let resolution = match resolution {
            Ok(resolution) => std::sync::Arc::new(resolution),
            Err(error) => {
                self.numeric.holes[hole_id.0 as usize].state = NumericHoleState::Invalid;
                self.unsupported(
                    expression.span,
                    format!("numeric literal resolution failed: {error}"),
                );
                return Some(value);
            }
        };
        self.invocation_witnesses
            .push(super::super::effect_identity::InvocationWitness {
                context,
                span,
                kind: super::super::effect_identity::InvocationWitnessKind::NumericSelection(
                    selection,
                ),
            });
        self.numeric.holes[hole_id.0 as usize].state =
            NumericHoleState::Committed { cause, resolution };
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
