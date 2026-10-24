//! Native continuation graph after selective CPS conversion. Every block is
//! emitted as machine code; these instructions are never source-interpreted.
use crate::core::{self, Expr, Parameter, Pattern};
use ril_compiler_core::{ids::DefinitionId, source::Span};
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone)]
pub struct Function {
    pub role: core::FunctionRole,
    pub metered: bool,
    pub name: String,
    pub definition: DefinitionId,
    pub generic_parameters: Vec<crate::metadata::GenericParameter>,
    pub span: Span,
    pub parameters: Vec<Parameter>,
    pub entry: BlockId,
    pub locals: BTreeSet<String>,
    /// Callables created under a handler may need its retained context.
    pub retained_lambdas: BTreeSet<(u32, u32, u32)>,
    pub blocks: Vec<Block>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub input: Input,
    /// Source effect operations and suspending calls have been split out.
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Statement(Box<core::Statement>),
    /// Establish a lexical where group's cells before any initializer runs.
    Hoist {
        declarations: BTreeSet<String>,
        functions: Vec<core::Function>,
    },
    /// A later initializer fills the cell already captured by a where function.
    ReuseBindings {
        names: BTreeSet<String>,
    },
    ScopeEnter {
        marker: String,
    },
}

#[derive(Debug, Clone)]
pub enum Input {
    /// Original function arguments followed by its hidden return continuation.
    Function,
    /// A continuation receives exactly one resumed/computed value.
    Continue(Option<Pattern>),
    /// Fork the lexical cell environment and install the delimiter continuation.
    HandlerBody,
    /// Operation arguments, resumption, and the implicit abort continuation.
    HandlerArm(Vec<Parameter>),
}

#[derive(Debug, Clone)]
pub struct Arm {
    pub source: core::HandlerArm,
    pub operation: u64,
    pub entry: BlockId,
}

#[derive(Debug, Clone)]
pub enum Terminator {
    /// Mandatory cleanup can invoke a native CPS callback before resuming next.
    ScopeLeave {
        marker: String,
        value: Expr,
        next: BlockId,
    },
    Charge {
        event: core::ChargeEvent,
        span: Span,
        next: BlockId,
    },
    Budget {
        limit: Expr,
        action: Expr,
        exhaustion_operation: u64,
        coverage: ril_compiler_core::diagnostic::CauseId,
        span: Span,
        next: BlockId,
    },
    Return {
        value: Expr,
        function: bool,
    },
    Jump(BlockId),
    Branch {
        condition: Expr,
        then_block: BlockId,
        else_block: BlockId,
    },
    Call {
        callback_entry: bool,
        callee: Expr,
        arguments: Vec<core::Argument>,
        next: BlockId,
        span: Span,
    },
    Perform {
        operation: u64,
        arguments: Vec<core::Argument>,
        next: BlockId,
        span: Span,
    },
    Handle {
        definition: u64,
        body: BlockId,
        arms: Vec<Arm>,
        next: BlockId,
    },
    Resume {
        value: Expr,
        /// A non-tail resume receives the delimited body's answer here before
        /// continuing the arm. None keeps the tail FinishArm fast path.
        next: Option<BlockId>,
    },
}

/// Environment keys cannot be produced by a source identifier.
pub const CONTINUATION: &str = "\0ril.cps.continuation";
pub const FUNCTION_RETURN: &str = "\0ril.cps.function-return";
pub const RESUMPTION: &str = "\0ril.cps.resumption";
pub const ACTIVATION: &str = "\0ril.cps.activation";
/// Original supplied values followed by the hidden return continuation.
pub const ARGUMENTS: &str = "\0ril.cps.arguments";
