//! Compiler-owned source declarations for language primitives.

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
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Placement {
    Prelude,
    AmbientModule(&'static str),
    ExistingNamespace(&'static str),
}

pub(crate) struct PrimitiveSource {
    pub display_path: &'static str,
    pub source: &'static str,
    pub placement: Placement,
    entries: &'static [(&'static str, PrimitiveId)],
}

pub(crate) const REFLECT_PATH: &str = "ril/reflect";

impl PrimitiveSource {
    pub fn primitive(&self, name: &str) -> Option<PrimitiveId> {
        self.entries
            .iter()
            .find_map(|(spelling, id)| (*spelling == name).then_some(*id))
    }

    pub fn matches_manifest(&self, program: &Program) -> bool {
        let mut seen = std::collections::BTreeSet::new();
        for statement in &program.statements {
            if let StmtKind::Function(function) = &statement.kind
                && (function.body.is_some()
                    || function.visibility != Visibility::Public
                    || self
                        .primitive(&function.name)
                        .is_none_or(|id| !seen.insert(id)))
            {
                return false;
            }
        }
        seen.len() == self.entries.len()
    }
}

pub(crate) fn bundled_module(path: &Path) -> bool {
    path == Path::new(REFLECT_PATH)
        || SOURCES.iter().any(|source| {
            matches!(source.placement, Placement::AmbientModule(module) if path == Path::new(module))
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
    },
    PrimitiveSource {
        display_path: "@div.ril",
        source: include_str!("../library/div.ril"),
        placement: Placement::ExistingNamespace("Div"),
        entries: &[("budget", PrimitiveId::DivBudget)],
    },
];
