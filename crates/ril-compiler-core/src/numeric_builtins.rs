//! Canonical identities of the numeric SDK declarations. Instance types are
//! supplied by their original static arguments, never by a runtime descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericPrimitive {
    Int,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    BigInt,
    F32,
    F64,
}

impl NumericPrimitive {
    pub const ALL: [Self; 12] = [
        Self::Int,
        Self::I8,
        Self::I16,
        Self::I32,
        Self::I64,
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
        Self::BigInt,
        Self::F32,
        Self::F64,
    ];

    pub const fn name(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::BigInt => "bigint",
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }

    pub const fn floating(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericBuiltin {
    Parse(NumericPrimitive),
    Format(NumericPrimitive),
    Convert,
}

impl NumericBuiltin {
    pub fn lookup(name: &str) -> Option<Self> {
        if name == "Num::convert" {
            return Some(Self::Convert);
        }
        for primitive in NumericPrimitive::ALL {
            for id in [Self::Parse(primitive), Self::Format(primitive)] {
                if id.name() == name {
                    return Some(id);
                }
            }
        }
        None
    }

    pub const fn name(self) -> &'static str {
        use NumericPrimitive::*;
        match self {
            Self::Convert => "Num::convert",
            Self::Parse(Int) => "Num::parse_int",
            Self::Parse(I8) => "Num::parse_i8",
            Self::Parse(I16) => "Num::parse_i16",
            Self::Parse(I32) => "Num::parse_i32",
            Self::Parse(I64) => "Num::parse_i64",
            Self::Parse(U8) => "Num::parse_u8",
            Self::Parse(U16) => "Num::parse_u16",
            Self::Parse(U32) => "Num::parse_u32",
            Self::Parse(U64) => "Num::parse_u64",
            Self::Parse(BigInt) => "Num::parse_bigint",
            Self::Parse(F32) => "Num::parse_f32",
            Self::Parse(F64) => "Num::parse_f64",
            Self::Format(Int) => "Num::format_int",
            Self::Format(I8) => "Num::format_i8",
            Self::Format(I16) => "Num::format_i16",
            Self::Format(I32) => "Num::format_i32",
            Self::Format(I64) => "Num::format_i64",
            Self::Format(U8) => "Num::format_u8",
            Self::Format(U16) => "Num::format_u16",
            Self::Format(U32) => "Num::format_u32",
            Self::Format(U64) => "Num::format_u64",
            Self::Format(BigInt) => "Num::format_bigint",
            Self::Format(F32) => "Num::format_f32",
            Self::Format(F64) => "Num::format_f64",
        }
    }

    pub const fn lexical_bit(self) -> u128 {
        let offset = match self {
            Self::Parse(primitive) => primitive as u32,
            Self::Format(primitive) => 12 + primitive as u32,
            Self::Convert => 24,
        };
        1 << (64 + offset)
    }
}
