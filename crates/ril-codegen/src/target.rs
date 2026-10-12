//! Target properties are separate from compiler implementation status.
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ObjectFormat {
    Coff,
    Elf,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Endianness {
    Little,
    Big,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetSpec {
    pub triple: String,
    pub pointer_bits: u8,
    pub endianness: Endianness,
    pub object_format: ObjectFormat,
    pub capabilities: Vec<String>,
}

pub const NATIVE_TARGETS: [&str; 2] = ["x86_64-pc-windows-msvc", "x86_64-unknown-linux-gnu"];

#[derive(Debug, thiserror::Error)]
#[error("unsupported target: {0}")]
pub struct UnsupportedTarget(pub String);

impl TargetSpec {
    pub fn native(triple: &str) -> Result<Self, UnsupportedTarget> {
        let (object_format, platform) = match triple {
            "x86_64-pc-windows-msvc" => (ObjectFormat::Coff, "windows"),
            "x86_64-unknown-linux-gnu" => (ObjectFormat::Elf, "posix"),
            _ => return Err(UnsupportedTarget(triple.into())),
        };
        Ok(Self {
            triple: triple.into(),
            pointer_bits: 64,
            endianness: Endianness::Little,
            object_format,
            capabilities: [platform, "filesystem", "process", "clock", "entropy"]
                .into_iter()
                .map(str::to_owned)
                .collect(),
        })
    }
    /// Reject internally inconsistent user-provided target descriptions.
    pub fn validate(&self) -> Result<(), UnsupportedTarget> {
        if *self == Self::native(&self.triple)? {
            Ok(())
        } else {
            Err(UnsupportedTarget(self.triple.clone()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rejects_unknown_and_inconsistent_targets() {
        assert!(TargetSpec::native("pointer32").is_err());
        let mut target = TargetSpec::native(NATIVE_TARGETS[0]).unwrap();
        target.pointer_bits = 32;
        assert!(target.validate().is_err());
    }
}
