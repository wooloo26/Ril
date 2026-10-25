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
    pub(crate) fn units(&self) -> Vec<u16> {
        match self {
            Self::Posix(bytes) => bytes.iter().map(|&byte| u16::from(byte)).collect(),
            Self::Windows(units) => units.clone(),
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
    pub(crate) fn native_storage(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let input = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing native storage input"))
        };
        match name {
            "\0ril.storage.platform_windows" => self.boolean(cfg!(windows)),
            "\0ril.storage.native_from_units" => {
                let units = self
                    .sequence(input(0)?)?
                    .into_iter()
                    .map(|value| {
                        u16::try_from(self.as_integer(value)?)
                            .map_err(|_| RuntimeError::internal("native unit outside u16"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let value = if self.truth(input(1)?)? {
                    NativeString::Windows(units)
                } else {
                    NativeString::Posix(
                        units
                            .into_iter()
                            .map(|value| {
                                u8::try_from(value)
                                    .map_err(|_| RuntimeError::internal("native byte outside u8"))
                            })
                            .collect::<Result<Vec<_>>>()?,
                    )
                };
                self.allocate(Object::NativeString(value))
            }
            "\0ril.storage.native_units" => {
                let units = self
                    .as_native(input(0)?)?
                    .units()
                    .into_iter()
                    .map(|value| self.integer(i128::from(value), 16, false))
                    .collect::<Result<_>>()?;
                self.allocate(Object::Array(units))
            }
            "\0ril.storage.native_windows" => self.boolean(self.as_native(input(0)?)?.windows()),
            "\0ril.storage.path_from_native" => {
                let value = self.as_native(input(0)?)?;
                self.allocate(Object::Path(value))
            }
            "\0ril.storage.path_native" => {
                let value = self.as_path(input(0)?)?;
                self.allocate(Object::NativeString(value))
            }
            _ => Err(RuntimeError::internal("unknown native storage operation")),
        }
    }
}
