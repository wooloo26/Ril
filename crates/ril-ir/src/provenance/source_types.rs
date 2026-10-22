//! Finite complete Source graphs retained independently of runtime types.
//! Edges preserve sharing and recursive declarations instead of expanding them
//! into trees. Inspecting or constructing this evidence grants no authority.
use super::Access;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceTypeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceView {
    pub ty: SourceTypeId,
    pub environment: super::FrozenEnvironmentId,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceTypeGraph {
    pub nodes: Vec<SourceTypeNode>,
}

impl SourceTypeGraph {
    pub fn get(&self, id: SourceTypeId) -> Option<&SourceTypeNode> {
        self.nodes.get(id.0 as usize)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceScalar {
    Unit,
    Bool,
    Str,
    Bytes,
    Never,
    Int,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    BigInt,
    F32,
    F64,
    Intrinsic(ril_compiler_core::builtin_types::AtomicBuiltinType),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceLength {
    Dynamic,
    Fixed(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceContainer {
    Immutable,
    Option,
    Result,
    Set,
    Range,
    Heap,
    Deque,
}

/// Closed declaration identities from the standard data catalog. An arbitrary
/// name with the same spelling cannot introduce one of these identities.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceNominal {
    ProcessInput,
    ProcessOutputMode,
    ProcessExitStatus,
    ProcessError,
    IoErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceTypeField {
    pub label: String,
    pub mutable: bool,
    pub value: SourceTypeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceTypeNode {
    GenericBuiltin(ril_compiler_core::builtin_calls::GenericBuiltin),
    Scalar(SourceScalar),
    Nominal(SourceNominal),
    Binder(String),
    Array {
        length: SourceLength,
        element: SourceTypeId,
    },
    Map {
        key: SourceTypeId,
        value: SourceTypeId,
    },
    Tuple(Vec<SourceTypeId>),
    Record {
        fields: Vec<SourceTypeField>,
        row: Option<SourceTypeId>,
    },
    Callable {
        parameters: Vec<(Access, SourceTypeId)>,
        result: SourceTypeId,
        annotations: Vec<String>,
    },
    Container {
        kind: SourceContainer,
        arguments: Vec<SourceTypeId>,
    },
    Alias {
        declaration: String,
        target: SourceTypeId,
    },
    OpaqueName {
        name: String,
        arguments: Vec<SourceTypeId>,
    },
    /// An independently certified normalized Const argument of a nominal.
    /// It is not a runtime type or an unresolved type computation.
    StaticValue(String),
    OpaqueComputation(String),
    Unresolved {
        description: String,
        arguments: Vec<SourceTypeId>,
    },
}
