//! Exact numeric producers and their immutable resolution receipts.
use super::*;
use ril_compiler_core::ids::{
    ActivationEpochId, EvaluationOccurrenceId, ExprId, NumericHoleId, NumericSelectionId,
    NumericUseId, PatternId,
};

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
    pub source: ExprId,
    pub activation: ActivationEpochId,
    pub scope: u32,
    pub context: ResumptionContext,
    pub allocation_epoch: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericType {
    Int,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    BigInt,
    F32,
    F64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumericMagnitude {
    /// A private static-evaluation carrier has already selected its width and
    /// payload. It is never reopened as an unrounded decimal literal.
    CommittedFloat { bits: u8, payload: u64 },
    /// Unsigned exact magnitude written in base ten, without separators.
    Integer(String),
    /// Unrounded decimal magnitude, including its original decimal exponent.
    Decimal(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactNumericLiteral {
    pub magnitude: NumericMagnitude,
    pub suffix: Option<NumericType>,
    pub negative: bool,
}

#[derive(Debug, Clone)]
pub struct NumericUse {
    pub id: NumericUseId,
    pub hole: NumericHoleId,
    pub selection: Option<NumericSelectionId>,
    pub site: NumericSite,
    pub birth: NumericBirth,
    pub exact: ExactNumericLiteral,
    pub span: Span,
    pub cause: CauseId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericDomain {
    IntegerOrFloat,
    FloatOnly,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NumericDependencies {
    pub uses: Vec<NumericUseId>,
    pub selections: Vec<NumericSelectionId>,
}

#[derive(Debug, Clone)]
pub struct NumericOperand {
    pub observation: EvaluationOccurrenceId,
    pub hole: Option<NumericHoleId>,
    pub ty: TypeId,
    pub constant: Option<Constant>,
    pub encoded: Option<NumericEncoding>,
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
pub struct NumericResolution {
    pub number_type: NumericType,
    pub constant: Option<Constant>,
    pub encoded: Option<NumericEncoding>,
    pub dependencies: NumericDependencies,
}

#[derive(Debug, Clone)]
pub enum NumericHoleState {
    Pending,
    Committed {
        cause: CauseId,
        resolution: NumericResolution,
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
pub enum NumericEncoding {
    Integer { value: i128, bits: u8, signed: bool },
    BigInteger(String),
    Float { bits: u8, payload: u64 },
}

#[derive(Debug, Clone)]
pub struct NumericSelection {
    pub id: NumericSelectionId,
    pub literal: NumericUseId,
    pub site: NumericSite,
    pub birth: NumericBirth,
    pub span: Span,
    pub ty: TypeId,
    pub layout: ril_compiler_core::target::TargetLayout,
    pub encoded: NumericEncoding,
    pub cause: CauseId,
}
