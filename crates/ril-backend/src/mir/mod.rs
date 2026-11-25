mod lower;
mod opt;
mod promote;
mod verify;

use std::sync::Arc;

use ril_base::diag::Diagnostic;
use ril_sema::{access::Analysis, ty::TypedProgram};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct LowerOptions {
    pub stack_promote: bool,
}

pub fn lower(program: &TypedProgram, analysis: &Analysis) -> Result<Program, Diagnostic> {
    lower_with_options(program, analysis, LowerOptions::default())
}

pub fn lower_with_options(
    program: &TypedProgram,
    analysis: &Analysis,
    options: LowerOptions,
) -> Result<Program, Diagnostic> {
    let mut lowered = lower::lower(program, analysis)?;
    opt::optimize(&mut lowered);
    if cfg!(debug_assertions) {
        verify::verify(&lowered)?;
    }
    if options.stack_promote {
        promote::promote_program(&mut lowered);
        opt::optimize(&mut lowered);
        if cfg!(debug_assertions) {
            verify::verify(&lowered)?;
        }
    }
    Ok(lowered)
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct FunctionId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct BlockId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Register(pub usize);

/// Static type of a MIR SSA register, separating GC-managed values from raw/immediate words.
#[allow(
    dead_code,
    reason = "typed MIR variants used progressively across R3 passes"
)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) enum MirTy {
    Unit,
    Bool,
    SmallInt,
    Int,
    F64,
    Never,
    Str,
    Bytes,
    Obj,
    Sum,
    Array,
    Map,
    Closure,
    Evidence,
    Draft,
    Scope,
    Task,
    Sender,
    Receiver,
    PanicInfo,
    Foreign,
    RawFnPtr,
    RawU64,
    #[default]
    Any,
}

impl MirTy {
    /// Returns `true` when values of this MIR type may point to a GC-managed heap object
    /// and therefore require a slot in the stack `RootFrame`.
    pub(crate) const fn is_gc_managed(self) -> bool {
        !matches!(
            self,
            Self::Unit
                | Self::Bool
                | Self::SmallInt
                | Self::Never
                | Self::Foreign
                | Self::RawFnPtr
                | Self::RawU64
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum IntBinOp {
    Add,
    Sub,
    Mul,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl IntBinOp {
    pub(crate) const fn slow_symbol(self) -> &'static str {
        match self {
            Self::Add => "ril_rt_int_add",
            Self::Sub => "ril_rt_int_sub",
            Self::Mul => "ril_rt_int_mul",
            Self::BitAnd => "ril_rt_int_and",
            Self::BitOr => "ril_rt_int_or",
            Self::BitXor => "ril_rt_int_xor",
            Self::Eq => "ril_rt_equal",
            Self::Ne => "ril_rt_not_equal",
            Self::Lt => "ril_rt_lt",
            Self::Le => "ril_rt_le",
            Self::Gt => "ril_rt_gt",
            Self::Ge => "ril_rt_ge",
        }
    }

    pub(crate) fn from_token(token: &str) -> Option<Self> {
        Some(match token {
            "+" => Self::Add,
            "-" => Self::Sub,
            "*" => Self::Mul,
            "&" => Self::BitAnd,
            "|" => Self::BitOr,
            "^" => Self::BitXor,
            "==" => Self::Eq,
            "!=" => Self::Ne,
            "<" => Self::Lt,
            "<=" => Self::Le,
            ">" => Self::Gt,
            ">=" => Self::Ge,
            _ => return None,
        })
    }

    pub(crate) const fn result_ty(self) -> MirTy {
        match self {
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => MirTy::Bool,
            Self::Add | Self::Sub | Self::Mul | Self::BitAnd | Self::BitOr | Self::BitXor => {
                MirTy::Any
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum IntUnaryOp {
    Neg,
    BitNot,
}

impl IntUnaryOp {
    pub(crate) const fn slow_symbol(self) -> &'static str {
        match self {
            Self::Neg => "ril_rt_neg",
            Self::BitNot => "ril_rt_bit_not",
        }
    }
}

#[derive(Debug)]
pub struct Program {
    pub(crate) functions: Vec<Function>,
    pub(crate) entry: FunctionId,
    pub(crate) suspend_at_entry: bool,
}

impl Program {
    /// Returns the deterministic canonical linker symbols of all lowered MIR functions.
    pub fn function_symbols(&self) -> Vec<&str> {
        self.functions.iter().map(|f| f.symbol.as_str()).collect()
    }
}

/// The source declaration and ABI of a host callback used by native code.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ForeignImport {
    pub declaration: String,
    pub signature: String,
    pub symbol: String,
    pub abi: ForeignAbi,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ForeignAbi {
    Function { arity: usize },
    Constant,
}

#[derive(Debug)]
pub(crate) struct Function {
    pub(crate) name: String,
    pub(crate) symbol: String,
    pub(crate) arity: usize,
    pub(crate) registers: usize,
    pub(crate) reg_types: Vec<MirTy>,
    pub(crate) stack_slots: usize,
    pub(crate) blocks: Vec<Block>,
}

#[derive(Debug, Default)]
pub(crate) struct Block {
    pub(crate) params: Vec<Register>,
    pub(crate) instructions: Vec<(Register, Instruction)>,
    pub(crate) terminator: Option<Terminator>,
}

#[derive(Debug)]
pub(crate) enum Instruction {
    Handle(u64),
    ConstSmallInt(i64),
    RawU64(u64),
    Evidence,
    Environment,
    FunctionAddress(FunctionId),
    Integer(Box<[u8]>),
    Float(u64),
    Text(Box<[u8]>),
    Bytes(Box<[u8]>),
    IntBinOp {
        op: IntBinOp,
        left: Register,
        right: Register,
    },
    IntUnaryOp {
        op: IntUnaryOp,
        value: Register,
    },
    BoolNot(Register),
    StackLoad(usize),
    StackStore {
        slot: usize,
        value: Register,
    },
}

impl Instruction {
    pub(crate) fn visit_reads(&self, mut visit: impl FnMut(Register)) {
        match self {
            Self::StackStore { value, .. }
            | Self::IntUnaryOp { value, .. }
            | Self::BoolNot(value) => visit(*value),
            Self::IntBinOp { left, right, .. } => {
                visit(*left);
                visit(*right);
            }
            Self::Handle(_)
            | Self::ConstSmallInt(_)
            | Self::RawU64(_)
            | Self::Evidence
            | Self::Environment
            | Self::FunctionAddress(_)
            | Self::Integer(_)
            | Self::Float(_)
            | Self::Text(_)
            | Self::Bytes(_)
            | Self::StackLoad(_) => {}
        }
    }

    pub(crate) fn remap_reads(&mut self, mut remap: impl FnMut(&mut Register)) {
        match self {
            Self::StackStore { value, .. }
            | Self::IntUnaryOp { value, .. }
            | Self::BoolNot(value) => remap(value),
            Self::IntBinOp { left, right, .. } => {
                remap(left);
                remap(right);
            }
            Self::Handle(_)
            | Self::ConstSmallInt(_)
            | Self::RawU64(_)
            | Self::Evidence
            | Self::Environment
            | Self::FunctionAddress(_)
            | Self::Integer(_)
            | Self::Float(_)
            | Self::Text(_)
            | Self::Bytes(_)
            | Self::StackLoad(_) => {}
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum Target {
    Function(FunctionId),
    FunctionWithEnv {
        function: FunctionId,
        environment: Register,
    },
    Runtime(&'static str),
    Draft(DraftOp),
    Foreign(Arc<ForeignImport>),
    Indirect {
        address: Register,
        evidence: Register,
        environment: Register,
    },
}

#[derive(Debug)]
pub(crate) enum Terminator {
    Unreachable,
    Jump(BlockId, Vec<Register>),
    Branch {
        condition: Register,
        yes: BlockId,
        no: BlockId,
    },
    Invoke {
        target: Target,
        evidence: Register,
        arguments: Vec<Register>,
        normal: BlockId,
        unwind: BlockId,
        cleanup: bool,
        keep_result: bool,
    },
    Return(Register),
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum DraftOp {
    Begin,
    Read,
    Write,
    Commit,
    Abort,
}

impl DraftOp {
    pub(crate) const fn symbol(self) -> &'static str {
        match self {
            Self::Begin => "ril_rt_draft_begin",
            Self::Read => "ril_rt_draft_read",
            Self::Write => "ril_rt_draft_write",
            Self::Commit => "ril_rt_draft_commit",
            Self::Abort => "ril_rt_draft_abort",
        }
    }
}

pub trait IntLowering {
    fn binary(&self, operator: &str) -> Option<&'static str>;
    fn unary(&self, operator: &str) -> Option<&'static str>;
}

pub(crate) struct ManagedInt;

impl IntLowering for ManagedInt {
    fn binary(&self, operator: &str) -> Option<&'static str> {
        Some(match operator {
            "+" => "ril_rt_int_add",
            "-" => "ril_rt_int_sub",
            "*" => "ril_rt_int_mul",
            "/" => "ril_rt_int_div",
            "%" => "ril_rt_int_rem",
            "&" => "ril_rt_int_and",
            "|" => "ril_rt_int_or",
            "^" => "ril_rt_int_xor",
            "<<" => "ril_rt_int_shl",
            ">>" => "ril_rt_int_shr",
            "==" => "ril_rt_equal",
            "!=" => "ril_rt_not_equal",
            "<" => "ril_rt_lt",
            "<=" => "ril_rt_le",
            ">" => "ril_rt_gt",
            ">=" => "ril_rt_ge",
            _ => return None,
        })
    }
    fn unary(&self, operator: &str) -> Option<&'static str> {
        Some(match operator {
            "-" => "ril_rt_neg",
            "!" => "ril_rt_not",
            "~" => "ril_rt_bit_not",
            _ => return None,
        })
    }
}
