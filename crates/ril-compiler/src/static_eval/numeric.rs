use super::*;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

impl Evaluator {
    pub(super) fn shift(
        &self,
        left: StaticValue,
        right: StaticValue,
        leftward: bool,
    ) -> Result<StaticValue> {
        let count = match right {
            StaticValue::Integer(value) | StaticValue::TypedInteger(value, ..) => {
                BigInt::from(value)
            }
            StaticValue::BigInteger(value) => value,
            _ => {
                return Err(Failure::Diagnostic(
                    "E0327",
                    "shift count must be an integer".into(),
                ));
            }
        };
        if count.is_negative() {
            return Err(Failure::Diagnostic(
                "E0831",
                "negative static shift count".into(),
            ));
        }
        let fixed = |value: i128, bits: u8, signed: bool| -> Result<i128> {
            let count = count
                .to_u32()
                .filter(|&count| count < u32::from(bits))
                .ok_or_else(|| {
                    Failure::Diagnostic(
                        "E0831",
                        "static shift count reaches the left operand width".into(),
                    )
                })?;
            if !leftward {
                return Ok(value >> count);
            }
            let raw = (value << count) & ((1i128 << bits) - 1);
            Ok(if signed && raw >= (1i128 << (bits - 1)) {
                raw - (1i128 << bits)
            } else {
                raw
            })
        };
        match left {
            StaticValue::Integer(value) => Ok(StaticValue::Integer(fixed(
                value,
                self.layout.pointer_bits,
                true,
            )?)),
            StaticValue::TypedInteger(value, bits, signed) => Ok(StaticValue::TypedInteger(
                fixed(value, bits, signed)?,
                bits,
                signed,
            )),
            StaticValue::BigInteger(value) => {
                let shifted = if value.is_zero() {
                    value
                } else if !leftward && count > BigInt::from(value.bits()) {
                    BigInt::from(if value.is_negative() { -1 } else { 0 })
                } else {
                    // A host-independent implementation resource bound. This
                    // cannot reject a program as invalid or certify its result.
                    const MAX_STATIC_INTEGER_BITS: u64 = 1_048_576;
                    let Some(count) = count.to_u64() else {
                        return Err(Failure::Unsupported(
                            "static bigint shift exceeds the allocation budget".into(),
                        ));
                    };
                    if count > MAX_STATIC_INTEGER_BITS
                        || (leftward
                            && value.bits().saturating_add(count) > MAX_STATIC_INTEGER_BITS)
                    {
                        return Err(Failure::Unsupported(
                            "static bigint shift exceeds the allocation budget".into(),
                        ));
                    }
                    if leftward {
                        value << count as usize
                    } else {
                        value >> count as usize
                    }
                };
                Ok(StaticValue::BigInteger(shifted))
            }
            _ => Err(Failure::Diagnostic(
                "E0327",
                "shift value must be an integer".into(),
            )),
        }
    }
}
