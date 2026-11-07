//! Target contracts shared by static layout queries and runtime lowering.

pub mod float;
pub mod layout;

/// An abstract evaluation target or a native target supported by the architecture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetSpec {
    Pointer32,
    Pointer64,
    LinuxX86_64,
    WindowsX86_64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectFormat {
    Elf,
    Coff,
}

impl TargetSpec {
    pub const ABSTRACT: [Self; 2] = [Self::Pointer32, Self::Pointer64];
    pub const NATIVE: [Self; 2] = [Self::LinuxX86_64, Self::WindowsX86_64];

    pub fn parse(name: &str) -> Option<Self> {
        Self::ABSTRACT
            .into_iter()
            .chain(Self::NATIVE)
            .find(|target| target.name() == name)
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::Pointer32 => "pointer32",
            Self::Pointer64 => "pointer64",
            Self::LinuxX86_64 => "x86_64-unknown-linux-gnu",
            Self::WindowsX86_64 => "x86_64-pc-windows-msvc",
        }
    }

    pub const fn pointer_bytes(self) -> u8 {
        match self {
            Self::Pointer32 => 4,
            _ => 8,
        }
    }

    pub const fn max_object_bytes(self) -> u64 {
        match self {
            Self::Pointer32 => u32::MAX as u64,
            Self::Pointer64 | Self::LinuxX86_64 | Self::WindowsX86_64 => i64::MAX as u64,
        }
    }

    pub const fn object_format(self) -> Option<ObjectFormat> {
        match self {
            Self::LinuxX86_64 => Some(ObjectFormat::Elf),
            Self::WindowsX86_64 => Some(ObjectFormat::Coff),
            Self::Pointer32 | Self::Pointer64 => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ObjectFormat, TargetSpec};

    #[test]
    fn abstract_layouts_are_independent_of_the_host() {
        assert_eq!(TargetSpec::Pointer32.pointer_bytes(), 4);
        assert_eq!(TargetSpec::Pointer64.pointer_bytes(), 8);
        assert_eq!(TargetSpec::Pointer32.object_format(), None);
        assert_eq!(TargetSpec::Pointer64.object_format(), None);
    }

    #[test]
    fn native_targets_pair_the_abi_name_and_object_format() {
        for (target, format) in TargetSpec::NATIVE
            .into_iter()
            .zip([ObjectFormat::Elf, ObjectFormat::Coff])
        {
            assert_eq!(TargetSpec::parse(target.name()), Some(target));
            assert_eq!(target.pointer_bytes(), 8);
            assert_eq!(target.object_format(), Some(format));
        }
        assert_eq!(TargetSpec::parse("x86_64-apple-darwin"), None);
    }
}
