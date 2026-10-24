//! Structured, backend-independent executable IR. Only the compiler certifies
//! semantic validity; these public data structures are not certificates.
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{ConstRef, DefinitionId},
    source::Span,
};

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Unit,
    Bool(bool),
    Integer { value: i128, bits: u8, signed: bool },
    BigInteger(String),
    Float { value: f64, bits: u8 },
    String(String),
    Bytes(Vec<u8>),
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// Read a verified immutable pool node without allocating or copying it.
    ConstRef(ConstRef),
    Literal(Literal),
    Name(String),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    Range {
        lower: Option<Box<Expr>>,
        upper: Option<Box<Expr>>,
        inclusive: bool,
    },
    Record {
        fields: Vec<(String, Expr)>,
        spread: Option<Box<Expr>>,
        members: Vec<RecordMember>,
    },
    Unary {
        operator: String,
        operand: Box<Expr>,
    },
    Binary {
        operator: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        /// A callback entry required by the surrounding language contract.
        /// Internal helper and ordinary primitive calls do not add this event.
        callback_entry: bool,
        callee: Box<Expr>,
        arguments: Vec<Argument>,
    },
    Perform {
        operation: u64,
        arguments: Vec<Argument>,
    },
    /// A compiler-certified finite-evaluation boundary, not an effect arm.
    Budget {
        limit: Box<Expr>,
        action: Box<Expr>,
        exhaustion_operation: u64,
        coverage: CauseId,
    },
    /// An abstract language event. Only the metered entry executes the charge.
    Charge(ChargeEvent),
    Field {
        base: Box<Expr>,
        field: String,
        safe: bool,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
        safe: bool,
    },
    Lambda {
        parameters: Vec<Parameter>,
        body: Box<Expr>,
    },
    Block(Block),
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    Match {
        value: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Is {
        value: Box<Expr>,
        pattern: Pattern,
    },
    Loop {
        body: Block,
        charge: Option<ChargeEvent>,
    },
    While {
        condition: Box<Expr>,
        body: Block,
        charge: Option<ChargeEvent>,
    },
    For {
        iterable: Box<Expr>,
        pattern: Pattern,
        body: Block,
        charge: Option<ChargeEvent>,
    },
    Control {
        operation: ControlOperation,
        value: Option<Box<Expr>>,
    },
    Derive {
        base: Box<Expr>,
        recipe: Box<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum RecordMember {
    Field(String, Expr),
    Spread(Expr),
}

#[derive(Debug, Clone)]
pub struct Argument {
    pub label: Option<String>,
    pub value: Expr,
}
#[derive(Debug, Clone)]
pub struct Parameter {
    pub pattern: Pattern,
    pub default: Option<Expr>,
}
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Name(String),
    Wildcard,
    Literal(Literal),
    Value(Box<Expr>),
    Tuple(Vec<Pattern>),
    Array(Vec<Pattern>),
    /// A sequence remainder; named remainders are array slot windows.
    Rest(Option<String>),
    Record(Vec<(String, Pattern)>),
    RecordRest {
        fields: Vec<(String, Pattern)>,
        rest: String,
    },
    Constructor {
        tag: String,
        arguments: Vec<Pattern>,
    },
    Alternative(Vec<Pattern>),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlOperation {
    Return,
    Last,
    Next,
    Resume,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum ChargeEvent {
    FunctionEntry = 0,
    LoopIteration = 1,
    HandlerEntry = 2,
    Resume = 3,
    BudgetEntry = 4,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum FunctionRole {
    #[default]
    Ordinary,
    Handler,
    Synthetic,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Bind {
        pattern: Pattern,
        value: Expr,
        scoped: bool,
    },
    Assign {
        target: Expr,
        operator: String,
        value: Expr,
    },
    Expr {
        expression: Expr,
        terminated: bool,
    },
    Function(Function),
    Handle {
        definition: u64,
        arms: Vec<HandlerArm>,
    },
}

#[derive(Debug, Clone)]
pub struct HandlerArm {
    pub operation: u64,
    pub parameters: Vec<Parameter>,
    pub body: Expr,
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub role: FunctionRole,
    pub definition: DefinitionId,
    pub name: String,
    pub generic_parameters: Vec<crate::metadata::GenericParameter>,
    pub parameters: Vec<Parameter>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub constant_graphs: Vec<crate::constants::ConstGraph>,
    pub external_functions: Vec<crate::foreign::ExternalFunction>,
    pub external_constants: Vec<crate::foreign::ExternalConstant>,
    pub functions: Vec<Function>,
    pub globals: Block,
    pub metadata: crate::metadata::ProgramMetadata,
    pub operations: Vec<Operation>,
    pub constructors: Vec<Constructor>,
    pub call_signatures: Vec<CallSignature>,
}
/// The signature visible at this source call, including callable ascriptions.
/// Runtime target declarations cannot override these argument labels.
#[derive(Debug, Clone)]
pub struct CallSignature {
    pub span: Span,
    pub parameters: Vec<CallParameter>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallParameter {
    pub label: Option<String>,
    pub has_default: bool,
}
#[derive(Debug, Clone)]
pub struct Constructor {
    pub name: String,
    pub tag: String,
    pub nominal: bool,
    pub has_payload: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Operation {
    pub identity: u64,
    pub name: String,
    pub span: Span,
}

impl Program {
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
}
