//! Versioned, representation-independent operation numbers for the native ABI.
//! Rust collections and enums never cross the exported function boundary.

pub const ABI_VERSION: u32 = 3;
/// Flags passed to ril_rt_callable_with_budget. A synthetic entry requires the
/// caller to supply a normative callback event; ordinary entries emit their own.
pub const CALLABLE_NORMAL_IS_CPS: u32 = 1;
pub const CALLABLE_METERED_ENTRY_EVENT: u32 = 2;

/// Abstract language events, never trampoline implementation steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum BudgetEvent {
    FunctionEntry = 0,
    LoopIteration = 1,
    HandlerEntry = 2,
    Resume = 3,
    BudgetEntry = 4,
}
impl BudgetEvent {
    pub fn from_raw(raw: u32) -> Option<Self> {
        Some(match raw {
            0 => Self::FunctionEntry,
            1 => Self::LoopIteration,
            2 => Self::HandlerEntry,
            3 => Self::Resume,
            4 => Self::BudgetEntry,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum BinaryOp {
    Add = 0,
    Subtract = 1,
    Multiply = 2,
    Divide = 3,
    Remainder = 4,
    Equal = 5,
    NotEqual = 6,
    Less = 7,
    LessEqual = 8,
    Greater = 9,
    GreaterEqual = 10,
    BitAnd = 11,
    BitOr = 12,
    BitXor = 13,
    ShiftLeft = 14,
    ShiftRight = 15,
    WrappingAdd = 16,
    WrappingSubtract = 17,
    WrappingMultiply = 18,
    SafeDivide = 19,
    SafeRemainder = 20,
}

impl BinaryOp {
    pub fn from_raw(raw: u32) -> Option<Self> {
        Some(match raw {
            0 => Self::Add,
            1 => Self::Subtract,
            2 => Self::Multiply,
            3 => Self::Divide,
            4 => Self::Remainder,
            5 => Self::Equal,
            6 => Self::NotEqual,
            7 => Self::Less,
            8 => Self::LessEqual,
            9 => Self::Greater,
            10 => Self::GreaterEqual,
            11 => Self::BitAnd,
            12 => Self::BitOr,
            13 => Self::BitXor,
            14 => Self::ShiftLeft,
            15 => Self::ShiftRight,
            16 => Self::WrappingAdd,
            17 => Self::WrappingSubtract,
            18 => Self::WrappingMultiply,
            19 => Self::SafeDivide,
            20 => Self::SafeRemainder,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum UnaryOp {
    Negate = 0,
    Not = 1,
    BitNot = 2,
}

/// Language outcomes are explicit; a host panic is a distinct runtime fault.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum OutcomeTag {
    Running = 0,
    LanguagePanic = 1,
    Cancelled = 2,
    DoubleFault = 3,
    InternalFault = 4,
    /// Transient unwinding cause; a successfully handled abort does not escape.
    EffectAborted = 5,
}
