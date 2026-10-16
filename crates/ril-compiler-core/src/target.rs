//! Abstract layout facts used by checking and static evaluation.
//! A layout does not imply that an object emitter exists for it.
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TargetLayout {
    pub pointer_bits: u8,
}

impl TargetLayout {
    pub const POINTER32: Self = Self { pointer_bits: 32 };
    pub const POINTER64: Self = Self { pointer_bits: 64 };

    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "pointer32" => Some(Self::POINTER32),
            "pointer64" | "x86_64-pc-windows-msvc" | "x86_64-unknown-linux-gnu" => {
                Some(Self::POINTER64)
            }
            _ => None,
        }
    }

    pub fn pointer_bytes(self) -> u8 {
        self.pointer_bits / 8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abstract_layout_does_not_follow_the_host() {
        assert_eq!(
            TargetLayout::from_name("pointer32")
                .unwrap()
                .pointer_bytes(),
            4
        );
        assert_eq!(
            TargetLayout::from_name("pointer64")
                .unwrap()
                .pointer_bytes(),
            8
        );
        assert_eq!(TargetLayout::from_name("unrecognized"), None);
    }
}
