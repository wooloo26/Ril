//! Versioned external-provider protocol. This is an implementation binding
//! contract, not a source-language C ABI or permission to expose host pointers.
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};

pub const PROTOCOL_VERSION: u32 = 1;
pub const DEFAULT_MAX_FRAME_BYTES: u64 = 64 * 1024 * 1024;
pub type NodeId = u32;
pub type CallId = u64;
pub type CallbackToken = u64;
pub type RequestId = u64;
pub type TypeRef = u32;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProviderConfig {
    pub id: String,
    pub program: PathBuf,
    pub args: Vec<String>,
    pub max_frame_bytes: u64,
}
impl From<&Provider> for ProviderConfig {
    fn from(provider: &Provider) -> Self {
        Self {
            id: provider.id.clone(),
            program: provider.program.clone(),
            args: provider.args.clone(),
            max_frame_bytes: provider.max_frame_bytes,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EntryKind {
    Function,
    Constant,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundCall {
    pub declaration: String,
    pub export: String,
    pub provider: ProviderConfig,
    pub kind: EntryKind,
    pub static_arguments: Vec<StaticArgument>,
    pub signature: Signature,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StaticArgument {
    pub name: String,
    pub value: StaticArgumentValue,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Signature {
    pub arena: Vec<TypeNode>,
    pub parameters: Vec<TypeRef>,
    pub result: TypeRef,
    pub callbacks: Vec<CallbackSlot>,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallbackSlot {
    pub argument: u32,
    pub path: Vec<CallbackPath>,
    pub mutable: bool,
    pub parameters: Vec<TypeRef>,
    pub result: TypeRef,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum CallbackPath {
    Field(String),
    Tuple(u32),
    Variant { tag: String, field: u32 },
    Array(u32),
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantShape {
    pub wire_tag: String,
    pub runtime_tag: String,
    pub fields: Vec<TypeRef>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub version: u32,
    pub providers: Vec<Provider>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Provider {
    pub id: String,
    pub program: PathBuf,
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(deserialize_with = "unique_bindings")]
    pub bindings: BTreeMap<String, String>,
    #[serde(default = "default_frame_limit")]
    pub max_frame_bytes: u64,
}
fn default_frame_limit() -> u64 {
    DEFAULT_MAX_FRAME_BYTES
}
fn unique_bindings<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<BTreeMap<String, String>, D::Error> {
    struct Visitor;
    impl<'de> serde::de::Visitor<'de> for Visitor {
        type Value = BTreeMap<String, String>;
        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("a map of unique declaration identities to exports")
        }
        fn visit_map<M: serde::de::MapAccess<'de>>(
            self,
            mut map: M,
        ) -> Result<Self::Value, M::Error> {
            let mut values = BTreeMap::new();
            while let Some((key, value)) = map.next_entry::<String, String>()? {
                if values.insert(key.clone(), value).is_some() {
                    return Err(serde::de::Error::custom(format!(
                        "duplicate external binding {key}"
                    )));
                }
            }
            Ok(values)
        }
    }
    deserializer.deserialize_map(Visitor)
}

impl Manifest {
    pub fn validate(&self) -> Result<(), String> {
        if self.version != PROTOCOL_VERSION {
            return Err("unsupported external binding manifest version".into());
        }
        let mut providers = BTreeSet::new();
        let mut declarations = BTreeSet::new();
        for provider in &self.providers {
            if provider.id.is_empty() || !providers.insert(&provider.id) {
                return Err("provider identities must be nonempty and unique".into());
            }
            if provider.program.as_os_str().is_empty() || provider.max_frame_bytes == 0 {
                return Err("provider program and positive frame limit are required".into());
            }
            if provider.args.iter().any(|argument| argument.contains('\0')) {
                return Err("provider arguments cannot contain NUL".into());
            }
            for (declaration, export) in &provider.bindings {
                if !declarations.insert(declaration)
                    || !valid_declaration(declaration)
                    || export.is_empty()
                    || export.contains('\0')
                {
                    return Err(format!(
                        "invalid or duplicate external binding {declaration}"
                    ));
                }
            }
        }
        Ok(())
    }
}

pub fn valid_declaration(value: &str) -> bool {
    let Some((module, member)) = value.rsplit_once("::") else {
        return false;
    };
    !module.is_empty()
        && !member.is_empty()
        && !value.contains('\0')
        && !value.contains('\\')
        && !module.starts_with('/')
        && !module.contains(':')
        && module
            .split('/')
            .all(|part| !part.is_empty() && part != "." && part != "..")
        && !member.contains('/')
        && !member.contains(':')
}

/// An explicit node table preserves aliases and cycles. It contains ordinary
/// immutable values only: callback/resource/host-pointer variants do not exist.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Graph {
    pub nodes: Vec<Node>,
    pub roots: Vec<NodeId>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum Node {
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
    Array(Vec<NodeId>),
    Map(Vec<(NodeId, NodeId)>),
    Set(Vec<NodeId>),
    Range {
        lower: Option<NodeId>,
        upper: Option<NodeId>,
        inclusive: bool,
    },
    Tuple(Vec<NodeId>),
    Record(Vec<Field>),
    Variant {
        tag: String,
        fields: Vec<NodeId>,
    },
    Nominal {
        tag: String,
        payload: NodeId,
    },
    Opaque {
        tag: String,
        data: Vec<u8>,
    },
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Field {
    pub name: String,
    pub node: NodeId,
}

impl Graph {
    /// Structural validation is independent of declared-type validation. A
    /// valid wire graph alone never certifies a foreign exchange contract.
    pub fn validate(&self) -> Result<(), String> {
        if self.nodes.len() > u32::MAX as usize {
            return Err("external graph has too many nodes".into());
        }
        let valid_ref = |id: NodeId| (id as usize) < self.nodes.len();
        if !self.roots.iter().copied().all(valid_ref) {
            return Err("external graph root is out of range".into());
        }
        for node in &self.nodes {
            let references: Vec<_> = match node {
                Node::Integer {
                    decimal,
                    bits,
                    signed,
                } => {
                    if !matches!(bits, 8 | 16 | 32 | 64) {
                        return Err("invalid external integer width".into());
                    }
                    if *signed {
                        let value = decimal
                            .parse::<i128>()
                            .map_err(|_| "invalid external signed integer")?;
                        if value < -(1i128 << (bits - 1)) || value >= (1i128 << (bits - 1)) {
                            return Err("external signed integer exceeds its width".into());
                        }
                    } else {
                        let value = decimal
                            .parse::<u128>()
                            .map_err(|_| "invalid external unsigned integer")?;
                        if value >= (1u128 << bits) {
                            return Err("external unsigned integer exceeds its width".into());
                        }
                    }
                    vec![]
                }
                Node::BigInteger(decimal) => {
                    let digits = decimal.strip_prefix('-').unwrap_or(decimal);
                    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
                        return Err("invalid external arbitrary integer".into());
                    }
                    vec![]
                }
                Node::Float { bits, raw } => {
                    if !matches!(bits, 32 | 64) || (*bits == 32 && *raw > u32::MAX as u64) {
                        return Err("invalid external float representation".into());
                    }
                    vec![]
                }
                Node::Array(values) | Node::Set(values) | Node::Tuple(values) => values.clone(),
                Node::Map(values) => values
                    .iter()
                    .flat_map(|&(key, value)| [key, value])
                    .collect(),
                Node::Range { lower, upper, .. } => lower.iter().chain(upper).copied().collect(),
                Node::Record(fields) => {
                    let mut names = BTreeSet::new();
                    if fields
                        .iter()
                        .any(|field| !names.insert(&field.name) || field.name.contains('\0'))
                    {
                        return Err("duplicate or invalid external record field".into());
                    }
                    fields.iter().map(|field| field.node).collect()
                }
                Node::Variant { tag, fields } => {
                    if tag.is_empty() || tag.contains('\0') {
                        return Err("invalid external constructor tag".into());
                    }
                    fields.clone()
                }
                Node::Nominal { tag, payload } => {
                    if tag.is_empty() || tag.contains('\0') {
                        return Err("invalid external nominal tag".into());
                    }
                    vec![*payload]
                }
                Node::Opaque { tag, .. } => {
                    if tag.is_empty() || tag.contains('\0') {
                        return Err("invalid external opaque type tag".into());
                    }
                    vec![]
                }
                Node::Unit | Node::Bool(_) | Node::String(_) | Node::Bytes(_) => vec![],
            };
            if !references.into_iter().all(valid_ref) {
                return Err("external graph edge is out of range".into());
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum Argument {
    Value(NodeId),
    Callback(CallbackToken),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ClientMessage {
    Invoke {
        version: u32,
        call: CallId,
        entry: EntryKind,
        declaration: String,
        export: String,
        static_arguments: Vec<StaticArgument>,
        signature: Signature,
        values: Graph,
        arguments: Vec<Argument>,
    },
    CallbackReturn {
        call: CallId,
        request: RequestId,
        values: Graph,
    },
    Abort {
        call: CallId,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProviderMessage {
    Ready {
        version: u32,
    },
    Callback {
        call: CallId,
        request: RequestId,
        token: CallbackToken,
        arguments: Graph,
    },
    Return {
        call: CallId,
        values: Graph,
    },
    Panic {
        call: CallId,
        message: String,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn graphs_preserve_shared_nodes_and_cycles_without_recursive_validation() {
        let graph = Graph {
            roots: vec![0, 0],
            nodes: vec![
                Node::Record(vec![
                    Field {
                        name: "self".into(),
                        node: 0,
                    },
                    Field {
                        name: "value".into(),
                        node: 1,
                    },
                ]),
                Node::Integer {
                    decimal: "42".into(),
                    bits: 64,
                    signed: true,
                },
            ],
        };
        assert!(graph.validate().is_ok());
        let invalid = Graph {
            roots: vec![0],
            nodes: vec![Node::Tuple(vec![1])],
        };
        assert!(invalid.validate().is_err());
    }
    #[test]
    fn wire_scalars_do_not_silently_truncate_or_duplicate_record_fields() {
        for node in [
            Node::Integer {
                decimal: "256".into(),
                bits: 8,
                signed: false,
            },
            Node::Integer {
                decimal: "128".into(),
                bits: 8,
                signed: true,
            },
            Node::Float {
                bits: 32,
                raw: 1u64 << 40,
            },
            Node::Record(vec![
                Field {
                    name: "a".into(),
                    node: 0,
                },
                Field {
                    name: "a".into(),
                    node: 0,
                },
            ]),
        ] {
            assert!(
                Graph {
                    roots: vec![0],
                    nodes: vec![node]
                }
                .validate()
                .is_err()
            );
        }
    }
    #[test]
    fn declaration_identities_are_module_relative_and_independent_of_aliases() {
        assert!(valid_declaration("platform/text::transform_text"));
        for invalid in [
            "ril__module_1_value",
            "../foreign::value",
            "/foreign::value",
            "C:/foreign::value",
            "foreign::",
            "foreign\\text::value",
        ] {
            assert!(!valid_declaration(invalid));
        }
    }
}
