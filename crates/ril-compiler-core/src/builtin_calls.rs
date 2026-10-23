//! Closed identities of polymorphic primitive declarations. Their Source
//! schemes live in the semantic kernel; no user spelling introduces an ID.
/// Sealed nullary language-item constructors. A template is instantiated at a
/// receiving boundary; it is not a callable or an unknown payload value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NullaryConstructor {
    None,
}

impl NullaryConstructor {
    pub const fn name(self) -> &'static str {
        match self {
            Self::None => "None",
        }
    }

    pub fn lookup(name: &str) -> Option<Self> {
        match name.strip_prefix("Prelude::").unwrap_or(name) {
            "None" => Some(Self::None),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GenericBuiltin {
    ArrayPush,
    ArrayInsert,
    ArrayTruncate,
    MapSet,
}

impl GenericBuiltin {
    pub const fn name(self) -> &'static str {
        match self {
            Self::ArrayPush => "Array::push",
            Self::ArrayInsert => "Array::insert",
            Self::ArrayTruncate => "Array::truncate",
            Self::MapSet => "Map::set",
        }
    }

    pub fn lookup(name: &str) -> Option<Self> {
        Some(match name {
            "Array::push" => Self::ArrayPush,
            "Array::insert" => Self::ArrayInsert,
            "Array::truncate" => Self::ArrayTruncate,
            "Map::set" => Self::MapSet,
            _ => return None,
        })
    }
}
