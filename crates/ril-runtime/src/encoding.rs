//! Immutable bytes, hexadecimal encoding, and transactional binary cursors.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};

fn width(name: &str) -> Option<(usize, bool, bool)> {
    Some(match name {
        "u8" => (1, false, false),
        "i8" => (1, true, false),
        "u16" => (2, false, false),
        "i16" => (2, true, false),
        "u32" => (4, false, false),
        "i32" => (4, true, false),
        "u64" => (8, false, false),
        "i64" => (8, true, false),
        "f32" => (4, false, true),
        "f64" => (8, false, true),
        _ => return None,
    })
}
impl Runtime {
    pub fn as_bytes(&self, value: Handle) -> Result<&[u8]> {
        match self.heap.get(value)? {
            Object::Bytes(data) => Ok(data),
            _ => Err(RuntimeError::internal("expected bytes")),
        }
    }
    fn binary_error(&mut self, name: &str) -> Result<Handle> {
        let error = self.variant(&format!("Binary::BinaryError::{name}"), vec![])?;
        self.variant("Err", vec![error])
    }
    fn cursor_data(&mut self, cursor: Handle) -> Result<(Handle, usize)> {
        let data = self.field(cursor, "data")?;
        let offset = self.field(cursor, "offset")?;
        let offset = usize::try_from(self.as_integer(offset)?)
            .ok()
            .filter(|offset| *offset <= self.as_bytes(data).map_or(0, |data| data.len()))
            .ok_or_else(|| RuntimeError::panic("binary cursor offset out of bounds"))?;
        self.as_bytes(data)?;
        Ok((data, offset))
    }
    fn byte_order(&self, order: Handle) -> Result<bool> {
        match self.heap.get(order)? {
            Object::Variant { tag, fields } if fields.is_empty() => match tag.as_str() {
                "Binary::ByteOrder::Little" => Ok(true),
                "Binary::ByteOrder::Big" => Ok(false),
                _ => Err(RuntimeError::internal("invalid byte order")),
            },
            _ => Err(RuntimeError::internal("invalid byte order")),
        }
    }
    fn advance_cursor(&mut self, cursor: Handle, offset: usize, value: Handle) -> Result<Handle> {
        let offset = self.int(offset as i128)?;
        self.set_field(cursor, "offset".into(), offset)?;
        self.variant("Ok", vec![value])
    }
    fn append_bytes(&mut self, output: Handle, data: &[u8]) -> Result<Handle> {
        let values = data
            .iter()
            .map(|byte| self.integer(i128::from(*byte), 8, false))
            .collect::<Result<Vec<_>>>()?;
        match self.heap.get_mut(output)? {
            Object::Array(output) => output.extend(values),
            _ => return Err(RuntimeError::internal("expected byte output array")),
        }
        self.unit()
    }
    pub(crate) fn encoding_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index: usize| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing encoding argument"))
        };
        match name {
            "Bytes::from_array" => {
                let bytes = self
                    .sequence(arg(0)?)?
                    .iter()
                    .map(|&value| {
                        u8::try_from(self.as_integer(value)?)
                            .map_err(|_| RuntimeError::internal("byte array contains non-byte"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                self.allocate(Object::Bytes(bytes.into()))
            }
            "Bytes::to_array" => {
                let bytes = self.as_bytes(arg(0)?)?.to_vec();
                let values = bytes
                    .into_iter()
                    .map(|byte| self.integer(i128::from(byte), 8, false))
                    .collect::<Result<_>>()?;
                self.allocate(Object::Array(values))
            }
            "Bytes::slice" => {
                let (start, end) = (self.as_integer(arg(1)?)?, self.as_integer(arg(2)?)?);
                let Object::Bytes(data) = self.heap.get(arg(0)?)? else {
                    return Err(RuntimeError::internal("expected byte slice input"));
                };
                if start < 0 || end < start || end > data.len() as i128 {
                    return self.variant("None", vec![]);
                }
                let view = data
                    .slice(start as usize..end as usize)
                    .expect("validated byte slice");
                let value = self.allocate(Object::Bytes(view))?;
                self.variant("Some", vec![value])
            }
            "Bytes::concat" => {
                let mut bytes = self.as_bytes(arg(0)?)?.to_vec();
                bytes.extend_from_slice(self.as_bytes(arg(1)?)?);
                self.allocate(Object::Bytes(bytes.into()))
            }
            "Bytes::find" => {
                let (data, needle) = (self.as_bytes(arg(0)?)?, self.as_bytes(arg(1)?)?);
                let position = if needle.is_empty() {
                    Some(0)
                } else {
                    data.windows(needle.len())
                        .position(|window| window == needle)
                };
                if let Some(position) = position {
                    let index = self.int(position as i128)?;
                    self.variant("Some", vec![index])
                } else {
                    self.variant("None", vec![])
                }
            }
            "Bytes::at" => self.index(arg(0)?, arg(1)?, true),
            "Hex::encode" => {
                const DIGITS: &[u8] = b"0123456789abcdef";
                let mut result = String::new();
                for &byte in self.as_bytes(arg(0)?)? {
                    result.push(DIGITS[(byte >> 4) as usize] as char);
                    result.push(DIGITS[(byte & 15) as usize] as char);
                }
                self.string(result)
            }
            "Hex::decode" => {
                let mut digits = Vec::new();
                let mut error = None;
                for (index, c) in self.as_string(arg(0)?)?.chars().enumerate() {
                    if c.is_ascii_hexdigit() {
                        digits.push(c.to_digit(16).unwrap() as u8);
                    } else {
                        error = Some(index);
                        break;
                    }
                }
                if error.is_none() && digits.len() % 2 != 0 {
                    error = Some(digits.len() - 1);
                }
                if let Some(index) = error {
                    let offset = self.int(index as i128)?;
                    let error =
                        self.allocate(Object::Record([("offset".into(), offset)].into()))?;
                    return self.variant("Err", vec![error]);
                }
                let bytes: Vec<u8> = digits
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| (pair[0] << 4) | pair[1])
                    .collect();
                let value = self.allocate(Object::Bytes(bytes.into()))?;
                self.variant("Ok", vec![value])
            }
            "Binary::cursor" => {
                self.as_bytes(arg(0)?)?;
                let offset = self.int(0)?;
                self.allocate(Object::Record(
                    [("data".into(), arg(0)?), ("offset".into(), offset)].into(),
                ))
            }
            "Binary::remaining" => {
                let (data, offset) = self.cursor_data(arg(0)?)?;
                self.int((self.as_bytes(data)?.len() - offset) as i128)
            }
            _ if name.starts_with("Binary::read_") => {
                let operation = &name[13..];
                let cursor = arg(0)?;
                let (data, offset) = self.cursor_data(cursor)?;
                if operation == "uleb128" {
                    let mut result = 0u64;
                    for index in 0..10 {
                        let Some(&byte) = self.as_bytes(data)?.get(offset + index) else {
                            return self.binary_error("UnexpectedEnd");
                        };
                        if index == 9 && (byte & 0xfe) != 0 {
                            return self.binary_error("Overflow");
                        }
                        result |= u64::from(byte & 0x7f) << (index * 7);
                        if byte & 0x80 == 0 {
                            if index != 0 && byte == 0 {
                                return self.binary_error("NonCanonical");
                            }
                            let value = self.integer(i128::from(result), 64, false)?;
                            return self.advance_cursor(cursor, offset + index + 1, value);
                        }
                    }
                    return self.binary_error("Overflow");
                }
                if operation == "bytes" {
                    let count = usize::try_from(self.as_integer(arg(1)?)?)
                        .map_err(|_| RuntimeError::panic("negative byte count"))?;
                    let Some(end) = offset
                        .checked_add(count)
                        .filter(|&end| end <= self.as_bytes(data).map_or(0, |data| data.len()))
                    else {
                        return self.binary_error("UnexpectedEnd");
                    };
                    let value = self.allocate(Object::Bytes(
                        self.as_bytes(data)?[offset..end].to_vec().into(),
                    ))?;
                    return self.advance_cursor(cursor, end, value);
                }
                let (count, signed, float) = width(operation)
                    .ok_or_else(|| RuntimeError::internal("unknown binary read"))?;
                let little = count == 1 || self.byte_order(arg(1)?)?;
                if self.as_bytes(data)?.len() - offset < count {
                    return self.binary_error("UnexpectedEnd");
                }
                let mut bits = 0u64;
                for (index, &byte) in self.as_bytes(data)?[offset..offset + count]
                    .iter()
                    .enumerate()
                {
                    bits |=
                        u64::from(byte) << ((if little { index } else { count - 1 - index }) * 8);
                }
                let value = if float {
                    self.float(
                        if count == 4 {
                            f64::from(f32::from_bits(bits as u32))
                        } else {
                            f64::from_bits(bits)
                        },
                        (count * 8) as u8,
                    )?
                } else {
                    let value = if signed {
                        (i128::from(bits) << (128 - count * 8)) >> (128 - count * 8)
                    } else {
                        i128::from(bits)
                    };
                    self.integer(value, (count * 8) as u8, signed)?
                };
                self.advance_cursor(cursor, offset + count, value)
            }
            _ if name.starts_with("Binary::write_") => {
                let operation = &name[14..];
                let output = arg(0)?;
                if operation == "bytes" {
                    let data = self.as_bytes(arg(1)?)?.to_vec();
                    return self.append_bytes(output, &data);
                }
                if operation == "uleb128" {
                    let mut value = u64::try_from(self.as_integer(arg(1)?)?)
                        .map_err(|_| RuntimeError::internal("expected u64"))?;
                    let mut data = Vec::new();
                    loop {
                        let byte = (value & 127) as u8;
                        value >>= 7;
                        data.push(byte | if value == 0 { 0 } else { 128 });
                        if value == 0 {
                            break;
                        }
                    }
                    return self.append_bytes(output, &data);
                }
                let (count, _, float) = width(operation)
                    .ok_or_else(|| RuntimeError::internal("unknown binary write"))?;
                let little = count == 1 || self.byte_order(arg(2)?)?;
                let bits = if float {
                    let Object::Float { value, .. } = self.heap.get(arg(1)?)? else {
                        return Err(RuntimeError::internal("expected float"));
                    };
                    if count == 4 {
                        u64::from(if value.is_nan() {
                            0x7fc00000
                        } else {
                            (*value as f32).to_bits()
                        })
                    } else if value.is_nan() {
                        0x7ff8000000000000
                    } else {
                        value.to_bits()
                    }
                } else {
                    self.as_integer(arg(1)?)? as u64
                };
                let data = (0..count)
                    .map(|index| {
                        (bits >> ((if little { index } else { count - 1 - index }) * 8)) as u8
                    })
                    .collect::<Vec<_>>();
                self.append_bytes(output, &data)
            }
            _ => Err(RuntimeError::internal("unknown encoding operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn result(rt: &Runtime, h: Handle, tag: &str) -> Handle {
        let Object::Variant {
            tag: actual,
            fields,
        } = rt.heap.get(h).unwrap()
        else {
            panic!("variant")
        };
        assert_eq!(actual, tag);
        fields[0]
    }
    fn cursor(rt: &mut Runtime, data: &[u8]) -> Handle {
        let data = rt.allocate(Object::Bytes(data.to_vec().into())).unwrap();
        rt.encoding_builtin("Binary::cursor", &[data]).unwrap()
    }
    #[test]
    fn leb_errors_preserve_offsets_and_inspect_no_more_than_ten_bytes() {
        let mut rt = Runtime::default();
        for (data, expected) in [
            (vec![0x80], "UnexpectedEnd"),
            (vec![0x80, 0], "NonCanonical"),
            (vec![0xff; 10], "Overflow"),
            (vec![0x80; 10], "Overflow"),
            (vec![0xff; 9].into_iter().chain([2]).collect(), "Overflow"),
        ] {
            let cursor = cursor(&mut rt, &data);
            let outcome = rt
                .encoding_builtin("Binary::read_uleb128", &[cursor])
                .unwrap();
            let error = result(&rt, outcome, "Err");
            assert!(
                matches!(rt.heap.get(error).unwrap(),Object::Variant{tag,..}if tag==&format!("Binary::BinaryError::{expected}"))
            );
            let offset = rt.field(cursor, "offset").unwrap();
            assert_eq!(rt.as_integer(offset).unwrap(), 0);
        }
        for value in [0u64, 127, 128, u64::MAX] {
            let output = rt.allocate(Object::Array(vec![])).unwrap();
            let input = rt.integer(i128::from(value), 64, false).unwrap();
            rt.encoding_builtin("Binary::write_uleb128", &[output, input])
                .unwrap();
            let bytes = rt.encoding_builtin("Bytes::from_array", &[output]).unwrap();
            let cursor = rt.encoding_builtin("Binary::cursor", &[bytes]).unwrap();
            let outcome = rt
                .encoding_builtin("Binary::read_uleb128", &[cursor])
                .unwrap();
            assert_eq!(
                rt.as_integer(result(&rt, outcome, "Ok")).unwrap(),
                i128::from(value)
            );
        }
    }
    #[test]
    fn fixed_width_encoding_is_explicit_endian_and_canonicalizes_nan() {
        let mut rt = Runtime::default();
        let output = rt.allocate(Object::Array(vec![])).unwrap();
        let nan = rt.float(f64::NAN, 64).unwrap();
        let big = rt.variant("Binary::ByteOrder::Big", vec![]).unwrap();
        rt.encoding_builtin("Binary::write_f64", &[output, nan, big])
            .unwrap();
        let bytes = rt.encoding_builtin("Bytes::from_array", &[output]).unwrap();
        assert_eq!(rt.as_bytes(bytes).unwrap(), [0x7f, 0xf8, 0, 0, 0, 0, 0, 0]);
        let cursor = cursor(&mut rt, &[0xff, 0xfe]);
        let outcome = rt
            .encoding_builtin("Binary::read_i16", &[cursor, big])
            .unwrap();
        assert_eq!(rt.as_integer(result(&rt, outcome, "Ok")).unwrap(), -2);
        let outcome = rt.encoding_builtin("Binary::read_u8", &[cursor]).unwrap();
        result(&rt, outcome, "Err");
        let offset = rt.field(cursor, "offset").unwrap();
        assert_eq!(rt.as_integer(offset).unwrap(), 2);
    }
    #[test]
    fn hex_reports_scalar_offsets_and_byte_snapshots_are_independent() {
        let mut rt = Runtime::default();
        for (text, index) in [("aé", 1), ("abc", 2), ("😀", 0)] {
            let text = rt.string(text.into()).unwrap();
            let outcome = rt.encoding_builtin("Hex::decode", &[text]).unwrap();
            let error = result(&rt, outcome, "Err");
            let offset = rt.field(error, "offset").unwrap();
            assert_eq!(rt.as_integer(offset).unwrap(), index);
        }
        let byte = rt.integer(10, 8, false).unwrap();
        let input = rt.allocate(Object::Array(vec![byte])).unwrap();
        let bytes = rt.encoding_builtin("Bytes::from_array", &[input]).unwrap();
        let replacement = rt.integer(20, 8, false).unwrap();
        let index = rt.int(0).unwrap();
        rt.set_index(input, index, replacement).unwrap();
        assert_eq!(rt.as_bytes(bytes).unwrap(), [10]);
    }
}
