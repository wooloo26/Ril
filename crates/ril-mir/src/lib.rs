#![forbid(unsafe_code)]

mod lower;
mod opt;
mod promote;
mod verify;

use ril_sema::{access::Analysis, ty::TypedProgram};
use ril_source::diag::Diagnostic;

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
pub struct FunctionId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(pub usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(pub usize);

/// Static type of a MIR SSA register, separating GC-managed values from raw/immediate words.
#[allow(
    dead_code,
    reason = "typed MIR classification used by verifier and codegen"
)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum MirTy {
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
    Continuation,
    Draft,
    RawFnPtr,
    RawU64,
    #[default]
    Any,
}

impl MirTy {
    /// Returns `true` when values of this MIR type may point to a GC-managed heap object
    /// and therefore require a slot in the stack `RootFrame`.
    pub const fn is_gc_managed(self) -> bool {
        !matches!(
            self,
            Self::Unit
                | Self::Bool
                | Self::SmallInt
                | Self::Never
                | Self::RawFnPtr
                | Self::RawU64
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IntBinOp {
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
    pub const fn slow_symbol(self) -> &'static str {
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

    pub fn from_token(token: &str) -> Option<Self> {
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

    pub const fn result_ty(self) -> MirTy {
        match self {
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => MirTy::Bool,
            Self::Add | Self::Sub | Self::Mul | Self::BitAnd | Self::BitOr | Self::BitXor => {
                MirTy::Any
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IntUnaryOp {
    Neg,
    BitNot,
}

impl IntUnaryOp {
    pub const fn slow_symbol(self) -> &'static str {
        match self {
            Self::Neg => "ril_rt_neg",
            Self::BitNot => "ril_rt_bit_not",
        }
    }
}

/// Source-location table entry attached to lowered MIR functions for debugger/profiler mapping.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceLocEntry {
    pub id: u32,
    pub file: String,
    pub line: u32,
    pub column: u32,
}

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub entry: FunctionId,
    pub source_locs: Vec<SourceLocEntry>,
}

impl Program {
    /// Returns the deterministic canonical linker symbols of all lowered MIR functions.
    pub fn function_symbols(&self) -> Vec<&str> {
        self.functions.iter().map(|f| f.symbol.as_str()).collect()
    }

    /// Returns the debug source-location table emitted alongside Cranelift `SourceLoc` records.
    pub fn source_locations(&self) -> &[SourceLocEntry] {
        &self.source_locs
    }
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub symbol: String,
    pub source_loc: Option<u32>,
    pub arity: usize,
    pub registers: usize,
    pub reg_types: Vec<MirTy>,
    pub stack_slots: usize,
    pub blocks: Vec<Block>,
}

impl Function {
    /// Returns all blocks reachable from the entry block (`BlockId(0)`) in reverse post-order.
    pub fn rpo(&self) -> Vec<BlockId> {
        let mut order = Vec::new();
        let mut visited = std::collections::BTreeSet::new();
        let mut stack = vec![(BlockId(0), false)];
        while let Some((id, done)) = stack.pop() {
            if done {
                order.push(id);
            } else if visited.insert(id) {
                let Some(block) = self.blocks.get(id.0) else {
                    continue;
                };
                stack.push((id, true));
                if let Some(term) = &block.terminator {
                    for succ in term.successors() {
                        stack.push((succ, false));
                    }
                }
            }
        }
        order.reverse();
        order
    }
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
    ConstSmallInt(i64),
    RawU64(u64),
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
    pub fn visit_reads(&self, mut visit: impl FnMut(Register)) {
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
            | Self::Environment
            | Self::FunctionAddress(_)
            | Self::Integer(_)
            | Self::Float(_)
            | Self::Text(_)
            | Self::Bytes(_)
            | Self::StackLoad(_) => {}
        }
    }

    pub fn remap_reads(&mut self, mut remap: impl FnMut(&mut Register)) {
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
pub enum Target {
    Function(FunctionId),
    FunctionWithEnv {
        function: FunctionId,
        environment: Register,
    },
    Runtime(&'static str),
    Draft(DraftOp),
    Indirect {
        address: Register,
        environment: Register,
    },
}

#[derive(Debug)]
pub enum Terminator {
    Unreachable,
    Jump(BlockId, Vec<Register>),
    Branch {
        condition: Register,
        yes: BlockId,
        no: BlockId,
    },
    Invoke {
        target: Target,
        arguments: Vec<Register>,
        normal: BlockId,
        unwind: BlockId,
        cleanup: bool,
        keep_result: bool,
    },
    Return(Register),
}

impl Terminator {
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Self::Unreachable | Self::Return(_) => Vec::new(),
            Self::Jump(target, _) => vec![*target],
            Self::Branch { yes, no, .. } => vec![*yes, *no],
            Self::Invoke { normal, unwind, .. } => vec![*normal, *unwind],
        }
    }

    pub fn visit_reads(&self, mut visit: impl FnMut(Register)) {
        match self {
            Self::Unreachable => {}
            Self::Return(reg) => visit(*reg),
            Self::Jump(_, args) => {
                for &arg in args {
                    visit(arg);
                }
            }
            Self::Branch { condition, .. } => visit(*condition),
            Self::Invoke {
                target, arguments, ..
            } => {
                match target {
                    Target::FunctionWithEnv { environment, .. } => visit(*environment),
                    Target::Indirect {
                        address,
                        environment,
                    } => {
                        visit(*address);
                        visit(*environment);
                    }
                    Target::Function(_) | Target::Runtime(_) | Target::Draft(_) => {}
                }
                for &arg in arguments {
                    visit(arg);
                }
            }
        }
    }

    pub fn remap_reads(&mut self, mut remap: impl FnMut(&mut Register)) {
        match self {
            Self::Unreachable => {}
            Self::Return(reg) => remap(reg),
            Self::Jump(_, args) => {
                for arg in args {
                    remap(arg);
                }
            }
            Self::Branch { condition, .. } => remap(condition),
            Self::Invoke {
                target, arguments, ..
            } => {
                match target {
                    Target::FunctionWithEnv { environment, .. } => remap(environment),
                    Target::Indirect {
                        address,
                        environment,
                    } => {
                        remap(address);
                        remap(environment);
                    }
                    Target::Function(_) | Target::Runtime(_) | Target::Draft(_) => {}
                }
                for arg in arguments {
                    remap(arg);
                }
            }
        }
    }
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
