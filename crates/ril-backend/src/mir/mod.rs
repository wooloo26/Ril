mod lower;

use ril_base::diag::Diagnostic;
use ril_sema::{access::Analysis, ty::TypedProgram};

pub fn lower(program: &TypedProgram, analysis: &Analysis) -> Result<Program, Diagnostic> {
    lower::lower(program, analysis)
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(pub usize);

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub entry: FunctionId,
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub arity: usize,
    pub registers: usize,
    pub blocks: Vec<Block>,
}

#[derive(Debug, Default)]
pub struct Block {
    pub params: Vec<Register>,
    pub instructions: Vec<(Register, Instruction)>,
    pub terminator: Option<Terminator>,
}

#[derive(Debug)]
pub enum Instruction {
    Handle(u64),
    Evidence,
    Environment,
    FunctionAddress(FunctionId),
    Integer(Box<[u8]>),
    Float(u64),
    Text(Box<[u8]>),
    Bytes(Box<[u8]>),
}

#[derive(Clone, Debug)]
pub enum Target {
    Function(FunctionId),
    FunctionWithEnv {
        function: FunctionId,
        environment: Register,
    },
    Runtime(&'static str),
    Foreign(String),
    Indirect {
        address: Register,
        evidence: Register,
        environment: Register,
    },
}

#[derive(Debug)]
pub enum Terminator {
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
pub enum DraftOp {
    Begin,
    Read,
    Write,
    Commit,
    Abort,
}

impl DraftOp {
    pub const fn symbol(self) -> &'static str {
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

pub struct ManagedInt;

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
