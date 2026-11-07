//! Compiler-owned library declarations, bodies, and operation identities.

use crate::ast::{Program, StmtKind, Visibility};
use std::path::Path;

/// Stable semantic identities assigned only to compiler-owned declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveId {
    Len,
    Inner,
    Clone,
    Derive,
    ByteSize,
    TypeName,
    Panic,
    Assert,
    Print,
    Println,
    NumericConvert,
    NumericTrunc,
    NumericWrap,
    NumericReinterpret,
    StringScalars,
    StringAt,
    StringFromScalars,
    StringEncodeUtf8,
    StringDecodeUtf8,
    BytesAt,
    BytesToArray,
    BytesFromArray,
    DivBudget,
    ArrayPush,
    ArrayInsert,
    ArrayPop,
    ArrayTruncate,
    SetEmpty,
    SetInsert,
    SetContains,
    SetRemove,
    SetToArray,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationPhase {
    Static,
    Runtime,
    Dual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LibraryTypeId {
    Option,
    Result,
    Set,
}

impl PrimitiveId {
    pub const fn phase(self) -> OperationPhase {
        match self {
            Self::ByteSize | Self::TypeName => OperationPhase::Static,
            Self::Inner
            | Self::Clone
            | Self::Derive
            | Self::Print
            | Self::Println
            | Self::DivBudget => OperationPhase::Runtime,
            Self::Len
            | Self::Panic
            | Self::Assert
            | Self::NumericConvert
            | Self::NumericTrunc
            | Self::NumericWrap
            | Self::NumericReinterpret
            | Self::StringScalars
            | Self::StringAt
            | Self::StringFromScalars
            | Self::StringEncodeUtf8
            | Self::StringDecodeUtf8
            | Self::BytesAt
            | Self::BytesToArray
            | Self::BytesFromArray
            | Self::ArrayPush
            | Self::ArrayInsert
            | Self::ArrayPop
            | Self::ArrayTruncate
            | Self::SetEmpty
            | Self::SetInsert
            | Self::SetContains
            | Self::SetRemove
            | Self::SetToArray => OperationPhase::Dual,
        }
    }
}

/// These identities grant phase admission; execution still uses the Ril body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LibraryBodyId {
    ArrayFirst,
    ArrayContains,
    ArrayMap,
    ArrayFilter,
    ArrayFold,
    ArrayReverse,
    MapGet,
    MapSet,
    MapKeys,
    MapValues,
    SetFrom,
}

impl LibraryBodyId {
    pub const fn phase(self) -> OperationPhase {
        match self {
            Self::ArrayFirst
            | Self::ArrayContains
            | Self::ArrayMap
            | Self::ArrayFilter
            | Self::ArrayFold
            | Self::ArrayReverse
            | Self::MapGet
            | Self::MapSet
            | Self::MapKeys
            | Self::MapValues
            | Self::SetFrom => OperationPhase::Dual,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Placement {
    Prelude,
    AmbientModule(&'static str),
    ExistingNamespace {
        name: &'static str,
        module: Option<&'static str>,
    },
}

pub(crate) struct PrimitiveSource {
    pub display_path: &'static str,
    pub source: &'static str,
    pub placement: Placement,
    entries: &'static [(&'static str, PrimitiveId)],
    bodies: &'static [(&'static str, LibraryBodyId)],
    types: &'static [(&'static str, LibraryTypeId)],
}

pub(crate) const REFLECT_PATH: &str = "ril/reflect";

impl PrimitiveSource {
    pub fn primitive(&self, name: &str) -> Option<PrimitiveId> {
        self.entries
            .iter()
            .find_map(|(spelling, id)| (*spelling == name).then_some(*id))
    }

    pub fn body(&self, name: &str) -> Option<LibraryBodyId> {
        self.bodies
            .iter()
            .find_map(|(spelling, id)| (*spelling == name).then_some(*id))
    }

    pub fn type_id(&self, name: &str) -> Option<LibraryTypeId> {
        self.types
            .iter()
            .find_map(|(spelling, id)| (*spelling == name).then_some(*id))
    }

    pub fn matches_manifest(&self, program: &Program) -> bool {
        let mut seen = std::collections::BTreeSet::new();
        let mut bodies = std::collections::BTreeSet::new();
        let mut types = std::collections::BTreeSet::new();
        for statement in &program.statements {
            if let StmtKind::Function(function) = &statement.kind {
                if let Some(id) = self.primitive(&function.name) {
                    if function.body.is_some()
                        || function.visibility != Visibility::Public
                        || function.is_meta != (id.phase() == OperationPhase::Static)
                        || !seen.insert(id)
                    {
                        return false;
                    }
                } else if let Some(id) = self.body(&function.name) {
                    if function.body.is_none()
                        || function.visibility != Visibility::Public
                        || function.is_meta
                        || !bodies.insert(id)
                    {
                        return false;
                    }
                } else if function.body.is_none() || function.visibility == Visibility::Public {
                    return false;
                }
            }
            if let StmtKind::Type(ty) = &statement.kind
                && let Some(id) = self.type_id(&ty.name)
                && (ty.visibility != Visibility::Public || !types.insert(id))
            {
                return false;
            }
        }
        seen.len() == self.entries.len()
            && bodies.len() == self.bodies.len()
            && types.len() == self.types.len()
    }
}

pub(crate) fn bundled_module(path: &Path) -> bool {
    path == Path::new(REFLECT_PATH)
        || SOURCES.iter().any(|source| {
            let module = match source.placement {
                Placement::AmbientModule(module) => Some(module),
                Placement::ExistingNamespace { module, .. } => module,
                Placement::Prelude => None,
            };
            module.is_some_and(|module| path == Path::new(module))
        })
}

pub(crate) const SOURCES: &[PrimitiveSource] = &[
    PrimitiveSource {
        display_path: "@prelude.ril",
        source: include_str!("../library/prelude.ril"),
        placement: Placement::Prelude,
        entries: &[
            ("len", PrimitiveId::Len),
            ("inner", PrimitiveId::Inner),
            ("clone", PrimitiveId::Clone),
            ("derive", PrimitiveId::Derive),
            ("byte_size", PrimitiveId::ByteSize),
            ("type_name", PrimitiveId::TypeName),
            ("panic", PrimitiveId::Panic),
            ("assert", PrimitiveId::Assert),
            ("print", PrimitiveId::Print),
            ("println", PrimitiveId::Println),
        ],
        bodies: &[],
        types: &[
            ("Option", LibraryTypeId::Option),
            ("Result", LibraryTypeId::Result),
            ("Set", LibraryTypeId::Set),
        ],
    },
    PrimitiveSource {
        display_path: "ril/array.ril",
        source: include_str!("../library/array.ril"),
        placement: Placement::AmbientModule("ril/array"),
        entries: &[
            ("push", PrimitiveId::ArrayPush),
            ("insert", PrimitiveId::ArrayInsert),
            ("pop", PrimitiveId::ArrayPop),
            ("truncate", PrimitiveId::ArrayTruncate),
        ],
        bodies: &[
            ("first", LibraryBodyId::ArrayFirst),
            ("contains", LibraryBodyId::ArrayContains),
            ("map", LibraryBodyId::ArrayMap),
            ("filter", LibraryBodyId::ArrayFilter),
            ("fold", LibraryBodyId::ArrayFold),
            ("reverse", LibraryBodyId::ArrayReverse),
        ],
        types: &[],
    },
    PrimitiveSource {
        display_path: "ril/map.ril",
        source: include_str!("../library/map.ril"),
        placement: Placement::AmbientModule("ril/map"),
        entries: &[],
        bodies: &[
            ("get", LibraryBodyId::MapGet),
            ("set", LibraryBodyId::MapSet),
            ("keys", LibraryBodyId::MapKeys),
            ("values", LibraryBodyId::MapValues),
        ],
        types: &[],
    },
    PrimitiveSource {
        display_path: "ril/set.ril",
        source: include_str!("../library/set.ril"),
        placement: Placement::ExistingNamespace {
            name: "Set",
            module: Some("ril/set"),
        },
        entries: &[
            ("empty", PrimitiveId::SetEmpty),
            ("insert", PrimitiveId::SetInsert),
            ("contains", PrimitiveId::SetContains),
            ("remove", PrimitiveId::SetRemove),
            ("to_array", PrimitiveId::SetToArray),
        ],
        bodies: &[("from", LibraryBodyId::SetFrom)],
        types: &[],
    },
    PrimitiveSource {
        display_path: "ril/numeric.ril",
        source: include_str!("../library/numeric.ril"),
        placement: Placement::AmbientModule("ril/numeric"),
        entries: &[
            ("convert", PrimitiveId::NumericConvert),
            ("trunc", PrimitiveId::NumericTrunc),
            ("wrap", PrimitiveId::NumericWrap),
            ("reinterpret", PrimitiveId::NumericReinterpret),
        ],
        bodies: &[],
        types: &[],
    },
    PrimitiveSource {
        display_path: "ril/string.ril",
        source: include_str!("../library/string.ril"),
        placement: Placement::AmbientModule("ril/string"),
        entries: &[
            ("scalars", PrimitiveId::StringScalars),
            ("at", PrimitiveId::StringAt),
            ("from_scalars", PrimitiveId::StringFromScalars),
            ("encode_utf8", PrimitiveId::StringEncodeUtf8),
            ("decode_utf8", PrimitiveId::StringDecodeUtf8),
        ],
        bodies: &[],
        types: &[],
    },
    PrimitiveSource {
        display_path: "ril/bytes.ril",
        source: include_str!("../library/bytes.ril"),
        placement: Placement::AmbientModule("ril/bytes"),
        entries: &[
            ("at", PrimitiveId::BytesAt),
            ("to_array", PrimitiveId::BytesToArray),
            ("from_array", PrimitiveId::BytesFromArray),
        ],
        bodies: &[],
        types: &[],
    },
    PrimitiveSource {
        display_path: "@div.ril",
        source: include_str!("../library/div.ril"),
        placement: Placement::ExistingNamespace {
            name: "Div",
            module: None,
        },
        entries: &[("budget", PrimitiveId::DivBudget)],
        bodies: &[],
        types: &[],
    },
];
