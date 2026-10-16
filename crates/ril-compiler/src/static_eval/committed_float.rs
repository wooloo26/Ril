//! Temporary normalized-AST carrier for a committed IEEE value.
//! Public syntax rejects NUL; this is data, never a parsing or evaluation request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CommittedFloat {
    pub width: u8,
    pub bits: u64,
}

impl CommittedFloat {
    pub(crate) fn value(self) -> f64 {
        if self.width == 32 {
            f64::from(f32::from_bits(self.bits as u32))
        } else {
            f64::from_bits(self.bits)
        }
    }
}

pub(crate) fn encode(value: f64, narrow: bool) -> String {
    if narrow {
        format!("\0ril.float32:{:08x}", (value as f32).to_bits())
    } else {
        format!("\0ril.float64:{:016x}", value.to_bits())
    }
}

pub(crate) fn decode(text: &str) -> Result<Option<CommittedFloat>, ()> {
    if !text.contains('\0') {
        return Ok(None);
    }
    let (width, hex) = if let Some(hex) = text.strip_prefix("\0ril.float32:") {
        (32, hex)
    } else if let Some(hex) = text.strip_prefix("\0ril.float64:") {
        (64, hex)
    } else {
        return Err(());
    };
    if hex.len() != usize::from(width / 4) || !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(());
    }
    let bits = u64::from_str_radix(hex, 16).map_err(|_| ())?;
    Ok(Some(CommittedFloat { width, bits }))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn portable_values_preserve_width_bits_and_reject_malformed_private_payloads() {
        for (value, narrow) in [
            (0.0, true),
            (-0.0, true),
            (f64::INFINITY, false),
            (f64::NAN, false),
            (f64::from(f32::from_bits(0x5a800001)), true),
        ] {
            let actual = decode(&encode(value, narrow)).unwrap().unwrap();
            assert_eq!(actual.width, if narrow { 32 } else { 64 });
            assert_eq!(
                actual.bits,
                if narrow {
                    u64::from((value as f32).to_bits())
                } else {
                    value.to_bits()
                }
            );
        }
        for text in [
            "\0ril.float16:0000",
            "\0ril.float32:000000000",
            "\0ril.float64:0",
            "\0ril.float32:garbage!",
            "prefix\0ril.float32:00000000",
        ] {
            assert!(decode(text).is_err(), "{text:?}");
        }
        assert_eq!(decode("1.0f32"), Ok(None));
    }
}
