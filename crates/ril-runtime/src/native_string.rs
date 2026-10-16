//! Lossless target-native value data. No OS observation or Unicode replacement.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use std::ffi::{OsStr, OsString};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NativeString {
    Posix(Vec<u8>),
    Windows(Vec<u16>),
}
impl NativeString {
    pub fn from_text(text: &str) -> Self {
        if cfg!(windows) {
            Self::Windows(text.encode_utf16().collect())
        } else {
            Self::Posix(text.as_bytes().to_vec())
        }
    }
    pub fn text(&self) -> std::result::Result<String, &'static str> {
        match self {
            Self::Posix(bytes) => String::from_utf8(bytes.clone()).map_err(|_| "InvalidEncoding"),
            Self::Windows(units) => String::from_utf16(units).map_err(|_| "InvalidEncoding"),
        }
    }
    pub(crate) fn units(&self) -> Vec<u16> {
        match self {
            Self::Posix(bytes) => bytes.iter().map(|&byte| u16::from(byte)).collect(),
            Self::Windows(units) => units.clone(),
        }
    }
    pub(crate) fn with_units(&self, units: Vec<u16>) -> Self {
        match self {
            Self::Posix(_) => Self::Posix(units.into_iter().map(|unit| unit as u8).collect()),
            Self::Windows(_) => Self::Windows(units),
        }
    }
    pub(crate) fn windows(&self) -> bool {
        matches!(self, Self::Windows(_))
    }
    pub fn contains_nul(&self) -> bool {
        match self {
            Self::Posix(bytes) => bytes.contains(&0),
            Self::Windows(units) => units.contains(&0),
        }
    }
    pub fn from_os(value: &OsStr) -> Self {
        #[cfg(windows)]
        {
            use std::os::windows::ffi::OsStrExt;
            Self::Windows(value.encode_wide().collect())
        }
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            Self::Posix(value.as_bytes().to_vec())
        }
    }
    pub fn to_os(&self) -> std::result::Result<OsString, &'static str> {
        match self {
            #[cfg(windows)]
            Self::Windows(units) => {
                use std::os::windows::ffi::OsStringExt;
                Ok(OsString::from_wide(units))
            }
            #[cfg(unix)]
            Self::Posix(bytes) => {
                use std::os::unix::ffi::OsStringExt;
                Ok(OsString::from_vec(bytes.clone()))
            }
            _ => Err("WrongPlatform"),
        }
    }
}

impl Runtime {
    pub(crate) fn as_native(&self, handle: Handle) -> Result<NativeString> {
        match self.heap.get(handle)? {
            Object::NativeString(value) => Ok(value.clone()),
            _ => Err(RuntimeError::internal("expected native string")),
        }
    }
    pub(crate) fn as_path(&self, handle: Handle) -> Result<NativeString> {
        match self.heap.get(handle)? {
            Object::Path(value) => Ok(value.clone()),
            _ => Err(RuntimeError::internal("expected path")),
        }
    }
    fn native_error(&mut self, kind: &str) -> Result<Handle> {
        let error = self.variant(&format!("Os::NativeError::{kind}"), vec![])?;
        self.variant("Err", vec![error])
    }
    pub(crate) fn native_text_result(&mut self, value: &NativeString) -> Result<Handle> {
        match value.text() {
            Ok(text) => {
                let text = self.string(text)?;
                self.variant("Ok", vec![text])
            }
            Err(kind) => self.native_error(kind),
        }
    }
    pub(crate) fn native_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing native string argument"))
        };
        match name {
            "Os::platform" => self.variant(
                if cfg!(windows) {
                    "Os::Platform::Windows"
                } else {
                    "Os::Platform::Posix"
                },
                vec![],
            ),
            "Os::from_string" => {
                let value = NativeString::from_text(self.as_string(arg(0)?)?);
                self.allocate(Object::NativeString(value))
            }
            "Os::to_string" => self.native_text_result(&self.as_native(arg(0)?)?),
            "Os::from_posix_bytes" => {
                let Object::Bytes(data) = self.heap.get(arg(0)?)? else {
                    return Err(RuntimeError::internal("expected POSIX byte array"));
                };
                if cfg!(windows) {
                    self.native_error("WrongPlatform")
                } else {
                    let value =
                        self.allocate(Object::NativeString(NativeString::Posix(data.to_vec())))?;
                    self.variant("Ok", vec![value])
                }
            }
            "Os::from_windows_units" => {
                let units = self
                    .sequence(arg(0)?)?
                    .into_iter()
                    .map(|unit| {
                        u16::try_from(self.as_integer(unit)?)
                            .map_err(|_| RuntimeError::internal("expected UTF-16 unit"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                if cfg!(windows) {
                    let value =
                        self.allocate(Object::NativeString(NativeString::Windows(units)))?;
                    self.variant("Ok", vec![value])
                } else {
                    self.native_error("WrongPlatform")
                }
            }
            "Os::posix_bytes" => match self.as_native(arg(0)?)? {
                NativeString::Posix(data) => {
                    let data = self.allocate(Object::Bytes(data.into()))?;
                    self.variant("Ok", vec![data])
                }
                _ => self.native_error("WrongPlatform"),
            },
            "Os::windows_units" => match self.as_native(arg(0)?)? {
                NativeString::Windows(units) => {
                    let units = units
                        .into_iter()
                        .map(|unit| self.integer(i128::from(unit), 16, false))
                        .collect::<Result<Vec<_>>>()?;
                    let array = self.allocate(Object::Array(units))?;
                    self.variant("Ok", vec![array])
                }
                _ => self.native_error("WrongPlatform"),
            },
            "Os::compare" => {
                let order = self.as_native(arg(0)?)?.cmp(&self.as_native(arg(1)?)?);
                self.ordering_value(order)
            }
            _ => Err(RuntimeError::internal("unknown native string operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn strict_decoding_and_exact_units_do_not_replace_invalid_unicode() {
        let posix = NativeString::Posix(vec![b'a', 255, 0]);
        let windows = NativeString::Windows(vec![0xd800, 0, b'a' as u16]);
        assert_eq!(posix.text(), Err("InvalidEncoding"));
        assert_eq!(windows.text(), Err("InvalidEncoding"));
        assert!(posix.contains_nul() && windows.contains_nul());
        let text = NativeString::from_text("Aé🙂");
        assert_eq!(text.text().unwrap(), "Aé🙂");
        assert_eq!(NativeString::from_os(&text.to_os().unwrap()), text);
    }
}
