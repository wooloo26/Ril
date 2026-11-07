//! Canonical IEEE values. Runtime comparisons and static identity are distinct.
use crate::layout::FloatType;
use std::{
    cmp::Ordering,
    ops::{Add, Div, Mul, Neg, Rem, Sub},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FloatKey {
    format: FloatType,
    bits: u64,
}

impl FloatKey {
    pub const fn format(self) -> FloatType {
        self.format
    }
    pub const fn bits(self) -> u64 {
        self.bits
    }
}

macro_rules! float_value {
    ($name:ident, $float:ty, $bits:ty, $format:ident, $nan:expr) => {
        /// Intentionally lacks Rust equality: use IEEE comparison or an explicit static key.
        #[derive(Debug, Clone, Copy)]
        pub struct $name {
            bits: $bits,
        }

        impl $name {
            pub const NAN_BITS: $bits = $nan;

            pub fn from_bits(bits: $bits) -> Self {
                Self {
                    bits: if <$float>::from_bits(bits).is_nan() {
                        Self::NAN_BITS
                    } else {
                        bits
                    },
                }
            }

            pub fn from_float(value: $float) -> Self {
                Self::from_bits(value.to_bits())
            }
            pub fn get(self) -> $float {
                <$float>::from_bits(self.bits)
            }
            pub const fn to_bits(self) -> $bits {
                self.bits
            }
            pub const fn key(self) -> FloatKey {
                FloatKey {
                    format: FloatType::$format,
                    bits: self.bits as u64,
                }
            }

            pub fn ieee_eq(self, other: Self) -> bool {
                self.get() == other.get()
            }
            pub fn ieee_cmp(self, other: Self) -> Option<Ordering> {
                self.get().partial_cmp(&other.get())
            }

            pub fn safe_div(self, divisor: Self) -> Option<Self> {
                (divisor.get() != 0.0).then(|| self / divisor)
            }

            pub fn safe_rem(self, divisor: Self) -> Option<Self> {
                (divisor.get() != 0.0).then(|| self % divisor)
            }
        }

        impl Add for $name {
            type Output = Self;
            fn add(self, other: Self) -> Self {
                Self::from_float(self.get() + other.get())
            }
        }
        impl Sub for $name {
            type Output = Self;
            fn sub(self, other: Self) -> Self {
                Self::from_float(self.get() - other.get())
            }
        }
        impl Mul for $name {
            type Output = Self;
            fn mul(self, other: Self) -> Self {
                Self::from_float(self.get() * other.get())
            }
        }
        impl Div for $name {
            type Output = Self;
            fn div(self, other: Self) -> Self {
                Self::from_float(self.get() / other.get())
            }
        }
        impl Rem for $name {
            type Output = Self;
            fn rem(self, other: Self) -> Self {
                Self::from_float(self.get() % other.get())
            }
        }
        impl Neg for $name {
            type Output = Self;
            fn neg(self) -> Self {
                Self::from_float(-self.get())
            }
        }
    };
}

float_value!(F32Value, f32, u32, F32, 0x7fc0_0000);
float_value!(F64Value, f64, u64, F64, 0x7ff8_0000_0000_0000);

impl From<F32Value> for F64Value {
    fn from(value: F32Value) -> Self {
        Self::from_float(f64::from(value.get()))
    }
}

impl F64Value {
    /// One explicit IEEE rounding step; eligibility of a Ril conversion is checked separately.
    pub fn round_to_f32(self) -> F32Value {
        F32Value::from_float(self.get() as f32)
    }
}
