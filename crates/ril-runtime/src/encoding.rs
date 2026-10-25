//! Byte storage and IEEE scalar representation primitives.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
impl Runtime {
    pub fn as_bytes(&self, value: Handle) -> Result<&[u8]> {
        match self.heap.get(value)? {
            Object::Bytes(value) => Ok(value),
            _ => Err(RuntimeError::internal("expected bytes")),
        }
    }
    pub(crate) fn scalar_storage(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let input = *args
            .first()
            .ok_or_else(|| RuntimeError::internal("missing scalar storage input"))?;
        match name {
            "\0ril.storage.sqrt_f32" | "\0ril.storage.sqrt_f64" => {
                let width = if name.ends_with("f32") { 32 } else { 64 };
                let Object::Float { value, bits } = self.heap.get(input)? else {
                    return Err(RuntimeError::internal("expected sqrt input"));
                };
                if *bits != width {
                    return Err(RuntimeError::internal("sqrt input width differs"));
                }
                let result = if width == 32 {
                    f64::from((*value as f32).sqrt())
                } else {
                    value.sqrt()
                };
                self.float(result, width)
            }
            "\0ril.storage.bytes_from_array" => {
                let data = self
                    .sequence(input)?
                    .iter()
                    .map(|&value| {
                        u8::try_from(self.as_integer(value)?)
                            .map_err(|_| RuntimeError::internal("byte array contains non-byte"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                self.allocate(Object::Bytes(data.into()))
            }
            "\0ril.storage.bytes_to_array" => {
                let bytes = self.as_bytes(input)?.to_vec();
                let values = bytes
                    .into_iter()
                    .map(|value| self.integer(i128::from(value), 8, false))
                    .collect::<Result<_>>()?;
                self.allocate(Object::Array(values))
            }
            "\0ril.storage.f32_bits" | "\0ril.storage.f64_bits" => {
                let width = if name.contains("f32") { 32 } else { 64 };
                let Object::Float { value, bits } = self.heap.get(input)? else {
                    return Err(RuntimeError::internal("expected float bits input"));
                };
                if *bits != width {
                    return Err(RuntimeError::internal("float bits input width differs"));
                }
                let raw = if width == 32 {
                    u64::from(if value.is_nan() {
                        0x7fc00000
                    } else {
                        (*value as f32).to_bits()
                    })
                } else if value.is_nan() {
                    0x7ff8000000000000
                } else {
                    value.to_bits()
                };
                self.integer(i128::from(raw), width, false)
            }
            "\0ril.storage.f32_from_bits" => {
                let raw = u32::try_from(self.as_integer(input)?)
                    .map_err(|_| RuntimeError::internal("expected u32 float bits"))?;
                self.float(f64::from(f32::from_bits(raw)), 32)
            }
            "\0ril.storage.f64_from_bits" => {
                let raw = u64::try_from(self.as_integer(input)?)
                    .map_err(|_| RuntimeError::internal("expected u64 float bits"))?;
                self.float(f64::from_bits(raw), 64)
            }
            _ => Err(RuntimeError::internal("unknown scalar storage operation")),
        }
    }
}
