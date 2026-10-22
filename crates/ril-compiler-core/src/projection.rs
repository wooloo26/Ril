//! Type-coordinate projections shared by HIR, semantic views and retained IR.
//! These steps identify declared views; they grant no access to heap storage.
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeProjection {
    Field(String),
    Tuple(u32),
    Element,
    MapKey,
    MapValue,
    OptionalPayload,
    ResultSuccess,
    ResultError,
    CallableParameter(u32),
    CallableResult,
    RecordRemainder(BTreeSet<String>),
}
