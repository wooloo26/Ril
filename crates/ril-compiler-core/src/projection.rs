//! Type-coordinate projections shared by HIR, semantic views and retained IR.
//! These steps identify declared views; they grant no access to heap storage.
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeProjection {
    Field(String),
    Tuple(u32),
    /// Zero denotes the last tuple member.
    TupleFromEnd(u32),
    Element,
    ArrayRemainder {
        prefix: u32,
        suffix: u32,
    },
    MapKey,
    MapValue,
    OptionalPayload,
    ResultSuccess,
    ResultError,
    CallableParameter(u32),
    CallableResult,
    RecordRemainder(BTreeSet<String>),
}
