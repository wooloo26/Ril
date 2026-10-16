//! Host exchange schemas are semantic value contracts, never machine layouts.
//! Schema indices preserve recursive types without recursively expanding them.
use crate::core;
use ril_compiler_core::{ids::DefinitionId, source::Span};
use std::collections::BTreeMap;

pub type TypeRef = u32;
/// Concrete static arguments belong to an invocation descriptor even when
/// they do not occur in the ordinary parameter or result types.
#[derive(Debug, Clone, PartialEq)]
pub struct StaticArgument {
    pub name: String,
    pub value: StaticArgumentValue,
}
#[derive(Debug, Clone, PartialEq)]
pub enum StaticArgumentValue {
    Type {
        identity: String,
        schema: Option<TypeRef>,
    },
    Value {
        identity: String,
        value: StaticValue,
    },
    Effects {
        identities: Vec<String>,
    },
    Capabilities {
        identities: Vec<String>,
    },
}
#[derive(Debug, Clone, PartialEq)]
pub enum StaticValue {
    Unit,
    Bool(bool),
    Integer {
        decimal: String,
        bits: u8,
        signed: bool,
    },
    BigInteger(String),
    Float {
        bits: u8,
        raw: u64,
    },
    String(String),
    Bytes(Vec<u8>),
}
#[derive(Debug, Clone)]
pub struct ProviderConfig {
    pub id: String,
    pub program: std::path::PathBuf,
    pub args: Vec<String>,
    pub max_frame_bytes: u64,
}
#[derive(Debug, Clone)]
pub struct Binding {
    pub declaration: String,
    pub export: String,
    pub provider: ProviderConfig,
}
#[derive(Debug, Clone, PartialEq)]
pub struct Signature {
    pub arena: Vec<TypeNode>,
    pub parameters: Vec<TypeRef>,
    pub result: TypeRef,
    pub callbacks: Vec<CallbackSlot>,
}
#[derive(Debug, Clone, PartialEq)]
pub enum TypeNode {
    Unit,
    Bool,
    Integer {
        bits: u8,
        signed: bool,
    },
    BigInteger,
    Float {
        bits: u8,
    },
    String,
    Bytes,
    Array {
        element: TypeRef,
        length: Option<u64>,
    },
    Map {
        key: TypeRef,
        value: TypeRef,
    },
    Set(TypeRef),
    Range(TypeRef),
    Immutable(TypeRef),
    Tuple(Vec<TypeRef>),
    Record(BTreeMap<String, TypeRef>),
    Variant(Vec<VariantShape>),
    Nominal {
        wire_tag: String,
        runtime_tag: String,
        payload: TypeRef,
    },
    Opaque {
        wire_tag: String,
        runtime_tag: String,
    },
    OpaqueData {
        wire_tag: String,
        runtime_tag: String,
        representation: TypeRef,
    },
    Callback,
    Resource {
        contract: String,
    },
}
#[derive(Debug, Clone, PartialEq)]
pub struct VariantShape {
    pub wire_tag: String,
    pub runtime_tag: String,
    pub fields: Vec<TypeRef>,
}
#[derive(Debug, Clone, PartialEq)]
pub struct CallbackSlot {
    pub argument: u32,
    pub path: Vec<CallbackPath>,
    pub mutable: bool,
    pub parameters: Vec<TypeRef>,
    pub result: TypeRef,
}
#[derive(Debug, Clone, PartialEq)]
pub enum CallbackPath {
    Field(String),
    Tuple(u32),
    Variant { tag: String, field: u32 },
    Array(u32),
}
#[derive(Debug, Clone)]
pub struct ExternalFunction {
    pub definition: DefinitionId,
    pub internal_name: String,
    pub declaration: String,
    pub static_arguments: Vec<StaticArgument>,
    pub span: Span,
    pub parameters: Vec<core::Parameter>,
    pub signature: Signature,
}
#[derive(Debug, Clone)]
pub struct ExternalConstant {
    pub internal_name: String,
    pub declaration: String,
    pub static_arguments: Vec<StaticArgument>,
    pub span: Span,
    /// Constants have no parameters or callback slots.
    pub signature: Signature,
}
