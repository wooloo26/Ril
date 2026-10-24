//! Immutable object identity is independent of source locations and contents.
use ril_compiler_core::ids::{ConstGraphId, ConstNodeId, ConstRef};

#[derive(Debug, Clone)]
pub enum ConstNodeKind {
    Literal(crate::core::Literal),
    Tuple(Vec<ConstRef>),
    Array(Vec<ConstRef>),
    ArrayWindow {
        backing: ConstRef,
        start: u64,
        len: u64,
    },
    Map(Vec<(ConstRef, ConstRef)>),
    Record(Vec<(String, ConstRef)>),
    Variant {
        tag: String,
        payload: Option<ConstRef>,
    },
}

#[derive(Debug, Clone)]
pub struct ConstNode {
    pub id: ConstNodeId,
    pub kind: ConstNodeKind,
    pub span: ril_compiler_core::source::Span,
    pub fixed_array_length: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct ConstGraph {
    pub id: ConstGraphId,
    pub nodes: Vec<ConstNode>,
}
