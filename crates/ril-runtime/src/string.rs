//! Immutable string storage and checked scalar representation conversion.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
impl Runtime {
    pub(crate) fn string_storage(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let input = *args
            .first()
            .ok_or_else(|| RuntimeError::internal("missing string storage input"))?;
        match name {
            "\0ril.storage.string_scalars" => {
                let scalars = self
                    .as_string(input)?
                    .chars()
                    .map(|value| value as u32)
                    .collect::<Vec<_>>();
                let values = scalars
                    .into_iter()
                    .map(|value| self.integer(i128::from(value), 32, false))
                    .collect::<Result<_>>()?;
                self.allocate(Object::Array(values))
            }
            "\0ril.storage.string_utf8" => {
                let bytes = self.as_string(input)?.as_bytes().to_vec();
                self.allocate(Object::Bytes(bytes.into()))
            }
            "\0ril.storage.string_from_scalars" => {
                let mut text = String::new();
                for value in self.sequence(input)? {
                    let scalar = u32::try_from(self.as_integer(value)?)
                        .ok()
                        .and_then(char::from_u32)
                        .ok_or_else(|| {
                            RuntimeError::panic("string construction received a nonscalar")
                        })?;
                    text.push(scalar);
                }
                self.string(text)
            }
            _ => Err(RuntimeError::internal("unknown string storage operation")),
        }
    }
}
