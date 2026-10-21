//! Canonical identities of intrinsic atomic types shared by semantic and
//! static/type-domain checking. These identities carry no runtime authority.
use crate::target::TargetLayout;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomicBuiltinType {
    ReadPosition,
    NativeString,
    Path,
    NativeError,
    Platform,
    Ordering,
}

impl AtomicBuiltinType {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Io::ReadPosition" => Some(Self::ReadPosition),
            "Os::NativeString" => Some(Self::NativeString),
            "Path::Path" => Some(Self::Path),
            "Os::NativeError" => Some(Self::NativeError),
            "Os::Platform" => Some(Self::Platform),
            "Order::Ordering" => Some(Self::Ordering),
            _ => None,
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::ReadPosition => "Io::ReadPosition",
            Self::NativeString => "Os::NativeString",
            Self::Path => "Path::Path",
            Self::NativeError => "Os::NativeError",
            Self::Platform => "Os::Platform",
            Self::Ordering => "Order::Ordering",
        }
    }

    pub fn byte_size(self, target: TargetLayout) -> u8 {
        match self {
            Self::ReadPosition
            | Self::NativeString
            | Self::Path
            | Self::NativeError
            | Self::Platform
            | Self::Ordering => target.pointer_bytes(),
        }
    }
}
