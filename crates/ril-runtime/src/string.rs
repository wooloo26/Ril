//! Strings remain UTF-8; source positions and counts are Unicode scalars.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
impl Runtime {
    fn string_array(&mut self, parts: Vec<String>) -> Result<Handle> {
        let values = parts
            .into_iter()
            .map(|text| self.string(text))
            .collect::<Result<_>>()?;
        self.allocate(Object::Array(values))
    }
    fn optional_int(&mut self, value: Option<usize>) -> Result<Handle> {
        if let Some(value) = value {
            let value = self.int(value as i128)?;
            self.variant("Some", vec![value])
        } else {
            self.variant("None", vec![])
        }
    }
    pub(crate) fn string_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index: usize| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing string argument"))
        };
        match name {
            "String::split" => {
                let (text, separator) = (self.as_string(arg(0)?)?, self.as_string(arg(1)?)?);
                let parts = if separator.is_empty() {
                    text.chars().map(|c| c.to_string()).collect()
                } else {
                    text.split(separator).map(str::to_owned).collect()
                };
                self.string_array(parts)
            }
            "String::trim" => {
                let text = self
                    .as_string(arg(0)?)?
                    .trim_matches(|c: char| crate::unicode::is_white_space(c as u32))
                    .to_owned();
                self.string(text)
            }
            "String::contains" => {
                self.boolean(self.as_string(arg(0)?)?.contains(self.as_string(arg(1)?)?))
            }
            "String::starts_with" => self.boolean(
                self.as_string(arg(0)?)?
                    .starts_with(self.as_string(arg(1)?)?),
            ),
            "String::ends_with" => {
                self.boolean(self.as_string(arg(0)?)?.ends_with(self.as_string(arg(1)?)?))
            }
            "String::replace" => {
                let text = self
                    .as_string(arg(0)?)?
                    .replace(self.as_string(arg(1)?)?, self.as_string(arg(2)?)?);
                self.string(text)
            }
            "String::find" => {
                let text = self.as_string(arg(0)?)?;
                let position = text
                    .find(self.as_string(arg(1)?)?)
                    .map(|byte| text[..byte].chars().count());
                self.optional_int(position)
            }
            "String::slice" => {
                let (start, end) = (self.as_integer(arg(1)?)?, self.as_integer(arg(2)?)?);
                let text = self.as_string(arg(0)?)?;
                let boundaries = text
                    .char_indices()
                    .map(|(byte, _)| byte)
                    .chain([text.len()])
                    .collect::<Vec<_>>();
                if start < 0 || end < start || end >= boundaries.len() as i128 {
                    return self.variant("None", vec![]);
                }
                let value = self.string(
                    text[boundaries[start as usize]..boundaries[end as usize]].to_owned(),
                )?;
                self.variant("Some", vec![value])
            }
            "String::concat" => {
                let text = self.as_string(arg(0)?)?.to_owned() + self.as_string(arg(1)?)?;
                self.string(text)
            }
            "String::join" => {
                let parts = self.sequence(arg(0)?)?;
                let parts = parts
                    .iter()
                    .map(|&part| self.as_string(part))
                    .collect::<Result<Vec<_>>>()?;
                let text = parts.join(self.as_string(arg(1)?)?);
                self.string(text)
            }
            "String::lines" => {
                let parts = self
                    .as_string(arg(0)?)?
                    .split_inclusive('\n')
                    .map(|line| {
                        if let Some(line) = line.strip_suffix('\n') {
                            line.strip_suffix('\r').unwrap_or(line)
                        } else {
                            line
                        }
                    })
                    .map(str::to_owned)
                    .collect();
                self.string_array(parts)
            }
            "String::scalar_at" => {
                let index = usize::try_from(self.as_integer(arg(1)?)?).ok();
                let text = self.as_string(arg(0)?)?;
                let scalar = index
                    .and_then(|index| text.chars().nth(index))
                    .map(|c| c as u32);
                if let Some(scalar) = scalar {
                    let scalar = self.integer(i128::from(scalar), 32, false)?;
                    self.variant("Some", vec![scalar])
                } else {
                    self.variant("None", vec![])
                }
            }
            "String::scalars" => {
                let scalars = self
                    .as_string(arg(0)?)?
                    .chars()
                    .map(|c| c as u32)
                    .collect::<Vec<_>>();
                let values = scalars
                    .into_iter()
                    .map(|scalar| self.integer(i128::from(scalar), 32, false))
                    .collect::<Result<_>>()?;
                self.allocate(Object::Array(values))
            }
            "String::utf8" => {
                let bytes = self.as_string(arg(0)?)?.as_bytes().to_vec();
                self.allocate(Object::Bytes(bytes.into()))
            }
            "String::byte_len" => self.int(self.as_string(arg(0)?)?.len() as i128),
            "String::byte_offset" => {
                let index = usize::try_from(self.as_integer(arg(1)?)?).ok();
                let text = self.as_string(arg(0)?)?;
                let offset = index.and_then(|index| {
                    text.char_indices()
                        .map(|(byte, _)| byte)
                        .chain([text.len()])
                        .nth(index)
                });
                self.optional_int(offset)
            }
            "String::scalar_offset" => {
                let index = usize::try_from(self.as_integer(arg(1)?)?).ok();
                let text = self.as_string(arg(0)?)?;
                let offset = index
                    .filter(|&byte| byte <= text.len() && text.is_char_boundary(byte))
                    .map(|byte| text[..byte].chars().count());
                self.optional_int(offset)
            }
            _ => Err(RuntimeError::internal("unknown string operation")),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    fn texts(rt: &Runtime, value: Handle) -> Vec<String> {
        rt.sequence(value)
            .unwrap()
            .iter()
            .map(|&value| rt.as_string(value).unwrap().to_owned())
            .collect()
    }
    #[test]
    fn empty_split_has_no_artificial_fields_and_lines_only_remove_cr_before_lf() {
        let mut rt = Runtime::default();
        let empty = rt.string("".into()).unwrap();
        let word = rt.string("é🙂".into()).unwrap();
        let result = rt.string_builtin("String::split", &[word, empty]).unwrap();
        assert_eq!(texts(&rt, result), ["é", "🙂"]);
        let result = rt.string_builtin("String::split", &[empty, empty]).unwrap();
        assert!(texts(&rt, result).is_empty());
        let text = rt.string("a\r\nb\n\n\r".into()).unwrap();
        let result = rt.string_builtin("String::lines", &[text]).unwrap();
        assert_eq!(texts(&rt, result), ["a", "b", "", "\r"]);
        let result = rt.string_builtin("String::lines", &[empty]).unwrap();
        assert!(texts(&rt, result).is_empty());
    }
    #[test]
    fn scalar_offsets_and_byte_offsets_are_distinct_and_allow_end_boundaries() {
        let mut rt = Runtime::default();
        let text = rt.string("Aé🙂".into()).unwrap();
        for (operation, index, expected) in [
            ("String::byte_offset", 2, Some(3)),
            ("String::byte_offset", 3, Some(7)),
            ("String::byte_offset", 4, None),
            ("String::scalar_offset", 2, None),
            ("String::scalar_offset", 7, Some(3)),
        ] {
            let index = rt.int(index).unwrap();
            let result = rt.string_builtin(operation, &[text, index]).unwrap();
            let Object::Variant { tag, fields } = rt.heap.get(result).unwrap() else {
                panic!("option")
            };
            assert_eq!(tag, if expected.is_some() { "Some" } else { "None" });
            if let Some(value) = expected {
                assert_eq!(rt.as_integer(fields[0]).unwrap(), value);
            }
        }
    }
}
