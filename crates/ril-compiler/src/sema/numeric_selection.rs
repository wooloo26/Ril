//! Invocation-owned numeric constraints. No diagnostic span selects a type.
use super::{
    copy_contract::CopyCallEventId,
    effect_identity::{InvocationContext, StaticArgumentWitness},
    model::{Constant, Ty},
};
use crate::numeric_literals::{EncodedNumber, ExactLiteral, NumberType};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{DefinitionId, NumericHoleId, NumericSelectionId, NumericUseId},
    source::Span,
    target::TargetLayout,
};
use std::collections::{BTreeMap, BTreeSet};

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
    pub exact: ExactLiteral,
    pub span: Span,
    pub immediate_minus: Option<Span>,
    pub cause: CauseId,
    pub context: InvocationContext,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericDomain {
    IntegerOrFloat,
    FloatOnly,
}

#[derive(Debug, Clone)]
pub struct NumericOperand {
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
    Selected { ty: NumberType, cause: CauseId },
    Committed { ty: NumberType, cause: CauseId },
    Invalid,
}

#[derive(Debug, Clone)]
pub struct NumericHole {
    pub id: NumericHoleId,
    pub domain: NumericDomain,
    pub term: NumericTerm,
    pub state: NumericHoleState,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumericSelection {
    pub id: NumericSelectionId,
    pub literal: NumericUseId,
    pub span: Span,
    pub context: InvocationContext,
    pub ty: NumberType,
    pub layout: TargetLayout,
    pub encoded: EncodedNumber,
    pub cause: CauseId,
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
    pub resolved: BTreeMap<NumericHoleId, NumericOperand>,
}

impl State {
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
