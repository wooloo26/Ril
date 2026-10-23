//! Retain numeric birth and resolution history without making another selection.
use super::*;
use crate::numeric_literals::{EncodedNumber, FloatFormat, NumberType};
use crate::sema::numeric_selection as n;

pub(super) fn retain(graph: &mut p::Graph, facts: &SemanticFacts) -> Result<(), NotImplemented> {
    graph.numeric_uses = facts
        .numeric_uses
        .iter()
        .map(|usage| {
            let magnitude = if let Some(value) = usage.exact.committed_float() {
                p::NumericMagnitude::CommittedFloat {
                    bits: match value.format() {
                        FloatFormat::F32 => 32,
                        FloatFormat::F64 => 64,
                    },
                    payload: value.bits(),
                }
            } else if let Some(value) = usage.exact.magnitude() {
                p::NumericMagnitude::Integer(value.to_string())
            } else if let Some(value) = usage.exact.decimal_magnitude() {
                p::NumericMagnitude::Decimal(value.to_owned())
            } else {
                return Err(NotImplemented::new(
                    ril_compiler_core::phase::Stage::Lowering,
                    "verified numeric use has no exact literal magnitude",
                ));
            };
            Ok(p::NumericUse {
                id: usage.id,
                hole: usage.hole,
                selection: usage.selection,
                site: site(usage.site),
                birth: birth(usage.birth),
                exact: p::ExactNumericLiteral {
                    magnitude,
                    suffix: usage.exact.written_type().map(number_type),
                    negative: usage.exact.is_negative(),
                },
                span: usage.span,
                cause: usage.cause,
            })
        })
        .collect::<Result<_, _>>()?;
    graph.numeric_holes = facts
        .numeric_holes
        .iter()
        .map(|hole| p::NumericHole {
            id: hole.id,
            birth: birth(hole.birth),
            domain: match hole.domain {
                n::NumericDomain::IntegerOrFloat => p::NumericDomain::IntegerOrFloat,
                n::NumericDomain::FloatOnly => p::NumericDomain::FloatOnly,
            },
            term: term(&mut graph.types, &hole.term),
            state: match &hole.state {
                n::NumericHoleState::Pending => p::NumericHoleState::Pending,
                n::NumericHoleState::Invalid => p::NumericHoleState::Invalid,
                n::NumericHoleState::Committed { cause, resolution } => {
                    p::NumericHoleState::Committed {
                        cause: *cause,
                        resolution: self::resolution(resolution),
                    }
                }
            },
            span: hole.span,
        })
        .collect();
    graph.numeric_selections = facts
        .numeric_selections
        .iter()
        .map(|selection| p::NumericSelection {
            id: selection.id,
            literal: selection.literal,
            site: site(selection.site),
            birth: birth(selection.birth),
            span: selection.span,
            ty: ty(&mut graph.types, &n::selected_ty(selection.ty)),
            layout: selection.layout,
            encoded: encoding(&selection.encoded),
            cause: selection.cause,
        })
        .collect();
    Ok(())
}

fn site(site: n::NumericSite) -> p::NumericSite {
    match site {
        n::NumericSite::Expression {
            literal,
            immediate_minus,
        } => p::NumericSite::Expression {
            literal,
            immediate_minus,
        },
        n::NumericSite::Pattern(pattern) => p::NumericSite::Pattern(pattern),
    }
}

pub(super) fn birth(birth: n::NumericBirth) -> p::NumericBirth {
    p::NumericBirth {
        source: birth.occurrence.source,
        activation: birth.occurrence.activation,
        scope: birth.scope.0,
        context: resumption_context(birth.context),
        allocation_epoch: birth.allocation_epoch as u64,
    }
}

pub(super) fn resolution(resolution: &n::NumericResolution) -> p::NumericResolution {
    p::NumericResolution {
        number_type: number_type(resolution.number_type),
        constant: resolution.constant.as_ref().map(constant),
        encoded: resolution.encoded.as_ref().map(encoding),
        dependencies: dependencies(&resolution.dependencies),
    }
}

fn dependencies(dependencies: &n::NumericDependencies) -> p::NumericDependencies {
    p::NumericDependencies {
        uses: dependencies.uses.iter().copied().collect(),
        selections: dependencies.selections.iter().copied().collect(),
    }
}

fn constant(constant: &m::Constant) -> p::Constant {
    match constant {
        m::Constant::Integer(value) => p::Constant::Integer(*value),
        m::Constant::Bool(value) => p::Constant::Bool(*value),
        m::Constant::Unit => p::Constant::Unit,
    }
}

fn operand(types: &mut Vec<p::Type>, operand: &n::NumericOperand) -> p::NumericOperand {
    p::NumericOperand {
        observation: operand.observation,
        hole: operand.hole,
        ty: ty(types, &operand.ty),
        constant: operand.constant.as_ref().map(constant),
        encoded: operand.encoded.as_ref().map(encoding),
        dependencies: dependencies(&operand.dependencies),
    }
}

fn term(types: &mut Vec<p::Type>, term: &n::NumericTerm) -> p::NumericTerm {
    match term {
        n::NumericTerm::Literal(id) => p::NumericTerm::Literal(*id),
        n::NumericTerm::Unary {
            operator,
            operand: value,
        } => p::NumericTerm::Unary {
            operator: operator.clone(),
            operand: Box::new(operand(types, value)),
        },
        n::NumericTerm::Binary {
            operator,
            left,
            right,
        } => p::NumericTerm::Binary {
            operator: operator.clone(),
            left: Box::new(operand(types, left)),
            right: Box::new(operand(types, right)),
        },
        n::NumericTerm::Join(values) => {
            p::NumericTerm::Join(values.iter().map(|value| operand(types, value)).collect())
        }
    }
}

fn number_type(ty: NumberType) -> p::NumericType {
    match ty {
        NumberType::Int => p::NumericType::Int,
        NumberType::I8 => p::NumericType::I8,
        NumberType::I16 => p::NumericType::I16,
        NumberType::I32 => p::NumericType::I32,
        NumberType::I64 => p::NumericType::I64,
        NumberType::U8 => p::NumericType::U8,
        NumberType::U16 => p::NumericType::U16,
        NumberType::U32 => p::NumericType::U32,
        NumberType::U64 => p::NumericType::U64,
        NumberType::BigInt => p::NumericType::BigInt,
        NumberType::F32 => p::NumericType::F32,
        NumberType::F64 => p::NumericType::F64,
    }
}

fn encoding(encoded: &EncodedNumber) -> p::NumericEncoding {
    match encoded {
        EncodedNumber::Integer {
            value,
            bits,
            signed,
            ..
        } => p::NumericEncoding::Integer {
            value: *value,
            bits: *bits,
            signed: *signed,
        },
        EncodedNumber::BigInteger(value) => p::NumericEncoding::BigInteger(value.to_string()),
        EncodedNumber::Float(value) => p::NumericEncoding::Float {
            bits: match value.format() {
                FloatFormat::F32 => 32,
                FloatFormat::F64 => 64,
            },
            payload: value.bits(),
        },
    }
}
