//! Invocation-owned numeric constraints. No diagnostic span selects a type.
use super::{
    application_effect::OccurrenceIdentity,
    copy_contract::CopyCallEventId,
    effect_identity::{InvocationContext, StaticArgumentWitness},
    facts::ScopeId,
    model::{Constant, Ty, Value},
    source_types::SourceTypesError,
};
use crate::numeric_literals::{EncodedNumber, ExactLiteral, NumberType};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{
        DefinitionId, EvaluationOccurrenceId, ExprId, NumericHoleId, NumericSelectionId,
        NumericUseId, PatternId,
    },
    source::Span,
    target::TargetLayout,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

mod preferences;
mod replay;
mod solve;
pub(crate) use preferences::{NumericPreferences, preferences};
pub(crate) use replay::{
    NumericReplayInputs, NumericReplaySession, checked_resolution_at_inputs,
    checked_resolution_in_query, pattern_number_type_inputs, validate, validate_literal_in_query,
};
#[cfg(test)]
pub(crate) use replay::{checked_resolution_at, checked_resolution_in_session};
pub(crate) use solve::{
    NumericInputs, arithmetic_constant, encoded_constant, evaluate, evaluate_cached, number_type,
};
#[cfg(test)]
mod review_tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumericSite {
    Expression {
        literal: ExprId,
        immediate_minus: Option<ExprId>,
    },
    Pattern(PatternId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumericBirth {
    pub occurrence: OccurrenceIdentity,
    pub scope: ScopeId,
    pub context: InvocationContext,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NumericDependencies {
    pub uses: BTreeSet<NumericUseId>,
    pub selections: BTreeSet<NumericSelectionId>,
}
impl NumericDependencies {
    pub fn include(&mut self, other: &Self) {
        self.uses.extend(&other.uses);
        self.selections.extend(&other.selections);
    }
}

#[derive(Debug, Clone)]
pub struct NumericUse {
    pub id: NumericUseId,
    pub hole: NumericHoleId,
    pub site: NumericSite,
    pub birth: NumericBirth,
    pub selection: Option<NumericSelectionId>,
    pub exact: ExactLiteral,
    pub span: Span,
    pub cause: CauseId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericDomain {
    IntegerOrFloat,
    FloatOnly,
}

#[derive(Debug, Clone)]
pub struct NumericOperand {
    pub observation: EvaluationOccurrenceId,
    pub hole: Option<NumericHoleId>,
    pub ty: Ty,
    pub constant: Option<Constant>,
    pub encoded: Option<EncodedNumber>,
    pub dependencies: NumericDependencies,
}

#[derive(Debug, Clone)]
pub enum NumericTerm {
    Literal(NumericUseId),
    Unary {
        operator: String,
        operand: Box<NumericOperand>,
    },
    Binary {
        operator: String,
        left: Box<NumericOperand>,
        right: Box<NumericOperand>,
    },
    Join(Vec<NumericOperand>),
}

#[derive(Debug, Clone)]
pub enum NumericHoleState {
    Pending,
    Committed {
        cause: CauseId,
        resolution: Arc<NumericResolution>,
    },
    Invalid,
}

#[derive(Debug, Clone)]
pub struct NumericHole {
    pub id: NumericHoleId,
    pub birth: NumericBirth,
    pub domain: NumericDomain,
    pub term: NumericTerm,
    pub state: NumericHoleState,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumericSelection {
    pub id: NumericSelectionId,
    pub literal: NumericUseId,
    pub site: NumericSite,
    pub birth: NumericBirth,
    pub span: Span,
    pub ty: NumberType,
    pub layout: TargetLayout,
    pub encoded: EncodedNumber,
    pub cause: CauseId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumericResolution {
    pub number_type: NumberType,
    pub constant: Option<Constant>,
    pub encoded: Option<EncodedNumber>,
    pub dependencies: NumericDependencies,
}

impl NumericResolution {
    pub(crate) fn try_clone(&self, work: &mut usize) -> Result<Self, SourceTypesError> {
        solve::clone_resolution(self, work)
    }
    pub(crate) fn value_type(&self) -> Ty {
        selected_ty(self.number_type)
    }
    pub(crate) fn matches_value(
        &self,
        value: &Value,
        work: &mut usize,
    ) -> Result<bool, SourceTypesError> {
        *work = work
            .checked_sub(
                4 + self.dependencies.uses.len()
                    + self.dependencies.selections.len()
                    + value.numeric.uses.len()
                    + value.numeric.selections.len(),
            )
            .ok_or(SourceTypesError::BudgetExceeded)?;
        Ok(value.ty == self.value_type()
            && value.constant == self.constant
            && value.numeric == self.dependencies
            && !value.unsuffixed_numeric)
    }
    pub(crate) fn apply(
        &self,
        value: &mut Value,
        work: &mut usize,
    ) -> Result<(), SourceTypesError> {
        *work = work
            .checked_sub(4 + self.dependencies.uses.len() + self.dependencies.selections.len())
            .ok_or(SourceTypesError::BudgetExceeded)?;
        value.ty = self.value_type();
        value.constant = self.constant.clone();
        value.numeric = self.dependencies.clone();
        value.unsuffixed_numeric = false;
        Ok(())
    }
}

pub(crate) fn selected_ty(selected: NumberType) -> Ty {
    match selected {
        NumberType::F32 => Ty::Float("f32".into()),
        NumberType::F64 => Ty::Float("f64".into()),
        _ => Ty::Int(
            match selected {
                NumberType::Int => "int",
                NumberType::I8 => "i8",
                NumberType::I16 => "i16",
                NumberType::I32 => "i32",
                NumberType::I64 => "i64",
                NumberType::U8 => "u8",
                NumberType::U16 => "u16",
                NumberType::U32 => "u32",
                NumberType::U64 => "u64",
                NumberType::BigInt => "bigint",
                NumberType::F32 | NumberType::F64 => unreachable!(),
            }
            .into(),
        ),
    }
}

pub(crate) fn source_number_type(
    scalar: crate::sema::source_types::SourceScalar,
) -> Option<NumberType> {
    use crate::sema::source_types::SourceScalar;
    Some(match scalar {
        SourceScalar::Int => NumberType::Int,
        SourceScalar::I8 => NumberType::I8,
        SourceScalar::I16 => NumberType::I16,
        SourceScalar::I32 => NumberType::I32,
        SourceScalar::I64 => NumberType::I64,
        SourceScalar::U8 => NumberType::U8,
        SourceScalar::U16 => NumberType::U16,
        SourceScalar::U32 => NumberType::U32,
        SourceScalar::U64 => NumberType::U64,
        SourceScalar::BigInt => NumberType::BigInt,
        SourceScalar::F32 => NumberType::F32,
        SourceScalar::F64 => NumberType::F64,
        _ => return None,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApplicationPhase {
    Collecting,
    Solved,
    Frozen,
    Invalid,
}

#[derive(Debug, Clone)]
pub struct NumericPreparedApplication {
    pub event: CopyCallEventId,
    pub span: Span,
    pub target: Option<DefinitionId>,
    pub context: InvocationContext,
    pub expected_result: Option<Ty>,
    pub arguments: Vec<NumericDependencies>,
    /// Constraints solved before evaluating the written arguments. The body
    /// invocation must independently infer exactly these canonical binders.
    pub substitutions: BTreeMap<String, Ty>,
    pub parameter_templates: Vec<Option<Ty>>,
    pub binders: BTreeSet<String>,
    pub static_arguments: Vec<StaticArgumentWitness>,
    pub phase: ApplicationPhase,
}

#[derive(Debug, Default)]
pub(crate) struct State {
    pub uses: Vec<NumericUse>,
    pub holes: Vec<NumericHole>,
    pub selections: Vec<NumericSelection>,
    pub applications: BTreeMap<CopyCallEventId, NumericPreparedApplication>,
    pub deferred_depth: usize,
    pub replay: std::cell::RefCell<NumericReplaySession>,
}

impl State {
    pub(crate) fn resolution(
        &self,
        id: NumericHoleId,
    ) -> Result<&Arc<NumericResolution>, SourceTypesError> {
        match &self
            .holes
            .get(id.0 as usize)
            .filter(|hole| hole.id == id)
            .ok_or(SourceTypesError::MissingNode)?
            .state
        {
            NumericHoleState::Committed { resolution, .. } => Ok(resolution),
            NumericHoleState::Pending | NumericHoleState::Invalid => {
                Err(SourceTypesError::Unresolved)
            }
        }
    }
    /// The additive migration does not yet normalize holes in all executable
    /// facts. Until that complete pass exists, even selected holes fail closed.
    pub fn incomplete(&self) -> Option<Span> {
        self.holes
            .iter()
            .find(|hole| !matches!(hole.state, NumericHoleState::Committed { .. }))
            .map(|hole| hole.span)
            .or_else(|| {
                self.applications
                    .values()
                    .find(|application| application.phase != ApplicationPhase::Frozen)
                    .map(|application| application.span)
            })
    }
}
