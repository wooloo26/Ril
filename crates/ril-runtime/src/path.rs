//! Target lexical paths operate on unsigned native units, without filesystem IO.
use crate::{
    heap::{Handle, Object},
    native_string::NativeString,
    value::{Result, Runtime, RuntimeError},
};

const SLASH: u16 = b'/' as u16;
const BACKSLASH: u16 = b'\\' as u16;
fn separator(unit: u16, windows: bool) -> bool {
    unit == SLASH || windows && unit == BACKSLASH
}
#[derive(Debug, Clone, Copy)]
struct Prefix {
    /// Drive or complete UNC share, excluding its following separators.
    name_end: usize,
    root_end: usize,
    rooted: bool,
    absolute: bool,
    verbatim: bool,
}
fn prefix(units: &[u16], windows: bool) -> Prefix {
    let mut result = Prefix {
        name_end: 0,
        root_end: 0,
        rooted: false,
        absolute: false,
        verbatim: false,
    };
    if windows {
        if units.len() >= 4
            && units[0..2] == [BACKSLASH, BACKSLASH]
            && matches!(units[2], 46 | 63)
            && units[3] == BACKSLASH
        {
            result.verbatim = true;
            result.absolute = true;
            result.rooted = true;
            result.name_end = 4;
            result.root_end = 4;
            if units.len() >= 6 && matches!(units[4], 65..=90 | 97..=122) && units[5] == 58 {
                result.name_end = 6;
                result.root_end = 6;
            } else {
                let mut end = 4;
                // Verbatim UNC has a share root; device paths keep their first
                // namespace component as the root rather than a file name.
                let unc = units
                    .get(4..8)
                    .is_some_and(|part| part == [85, 78, 67, BACKSLASH]);
                if unc {
                    end = 8;
                }
                let components = if unc { 2 } else { 1 };
                for _ in 0..components {
                    while end < units.len() && units[end] == BACKSLASH {
                        end += 1;
                    }
                    while end < units.len() && units[end] != BACKSLASH {
                        end += 1;
                    }
                }
                result.name_end = end;
                result.root_end = end;
            }
            while result.root_end < units.len() && units[result.root_end] == BACKSLASH {
                result.root_end += 1;
            }
            return result;
        }
        if units.len() >= 2 && matches!(units[0], 65..=90 | 97..=122) && units[1] == b':' as u16 {
            result.name_end = 2;
            result.root_end = 2;
        } else if units.len() >= 2 && separator(units[0], true) && separator(units[1], true) {
            let mut end = 2;
            let server = end;
            while end < units.len() && !separator(units[end], true) {
                end += 1;
            }
            if end > server {
                while end < units.len() && separator(units[end], true) {
                    end += 1;
                }
                let share = end;
                while end < units.len() && !separator(units[end], true) {
                    end += 1;
                }
                if end > share {
                    result.name_end = end;
                    result.root_end = end;
                    result.rooted = true;
                    result.absolute = true;
                }
            }
        }
    }
    while result.root_end < units.len() && separator(units[result.root_end], windows) {
        result.rooted = true;
        result.root_end += 1;
    }
    result.absolute |= result.rooted && (!windows || result.name_end != 0);
    result
}

pub(crate) fn join(base: &NativeString, child: &NativeString) -> NativeString {
    let windows = base.windows();
    let mut base_units = base.units();
    let child_units = child.units();
    if child_units.is_empty() {
        return base.clone();
    }
    if base_units.is_empty() {
        return child.clone();
    }
    let base_prefix = prefix(&base_units, windows);
    let child_prefix = prefix(&child_units, windows);
    if child_prefix.absolute || child_prefix.name_end != 0 {
        return child.clone();
    }
    if base_prefix.verbatim {
        if child_prefix.rooted {
            return child.clone();
        }
        if base_units.last() != Some(&BACKSLASH) {
            base_units.push(BACKSLASH);
        }
    } else if child_prefix.rooted {
        base_units.truncate(base_prefix.name_end);
        base_units.extend(child_units);
        return base.with_units(base_units);
    } else if !base_units
        .last()
        .is_some_and(|&unit| separator(unit, windows))
        && !(windows && base_units.len() == 2 && base_prefix.name_end == 2)
    {
        base_units.push(if windows { BACKSLASH } else { SLASH });
    }
    base_units.extend(child_units);
    base.with_units(base_units)
}

fn last_component(path: &NativeString) -> Option<(Vec<u16>, Prefix, usize, usize)> {
    let units = path.units();
    let root = prefix(&units, path.windows());
    let is_separator = |unit| {
        if root.verbatim {
            unit == BACKSLASH
        } else {
            separator(unit, path.windows())
        }
    };
    let mut end = units.len();
    while end > root.root_end && is_separator(units[end - 1]) {
        end -= 1;
    }
    if end <= root.root_end {
        return None;
    }
    let mut start = end;
    while start > root.root_end && !is_separator(units[start - 1]) {
        start -= 1;
    }
    Some((units, root, start, end))
}
pub(crate) fn parent(path: &NativeString) -> Option<NativeString> {
    let (mut units, root, start, _) = last_component(path)?;
    let mut end = start;
    while end > root.root_end
        && if root.verbatim {
            units[end - 1] == BACKSLASH
        } else {
            separator(units[end - 1], path.windows())
        }
    {
        end -= 1;
    }
    units.truncate(end);
    Some(path.with_units(units))
}
fn file_name(path: &NativeString) -> Option<NativeString> {
    let (units, _, start, end) = last_component(path)?;
    Some(path.with_units(units[start..end].to_vec()))
}
fn extension(path: &NativeString) -> Option<NativeString> {
    let file = file_name(path)?;
    let units = file.units();
    let dot = units.iter().rposition(|&unit| unit == b'.' as u16)?;
    (dot != 0).then(|| file.with_units(units[dot + 1..].to_vec()))
}
pub(crate) fn normalize(path: &NativeString) -> NativeString {
    let windows = path.windows();
    let units = path.units();
    let root = prefix(&units, windows);
    if root.verbatim {
        return path.clone();
    }
    let mut components: Vec<&[u16]> = Vec::new();
    for part in units[root.root_end..].split(|&unit| separator(unit, windows)) {
        if part.is_empty() || part == [46] {
            continue;
        }
        if part == [46, 46] {
            if components.last().is_some_and(|part| *part != [46, 46]) {
                components.pop();
            } else if !root.rooted {
                components.push(part);
            }
        } else {
            components.push(part);
        }
    }
    let sep = if windows { BACKSLASH } else { SLASH };
    let mut output = units[..root.name_end].to_vec();
    if windows {
        // UNC prefix separators also use the native separator in normalized paths.
        for unit in &mut output {
            if *unit == SLASH {
                *unit = BACKSLASH;
            }
        }
    }
    if root.rooted {
        output.push(sep);
    }
    for (index, component) in components.iter().enumerate() {
        if index != 0 {
            output.push(sep);
        }
        output.extend(*component);
    }
    if components.is_empty() && !root.rooted {
        output.push(b'.' as u16);
    }
    path.with_units(output)
}

impl Runtime {
    pub(crate) fn ordering_value(&mut self, order: std::cmp::Ordering) -> Result<Handle> {
        self.variant(
            match order {
                std::cmp::Ordering::Less => "Order::Ordering::Less",
                std::cmp::Ordering::Equal => "Order::Ordering::Equal",
                std::cmp::Ordering::Greater => "Order::Ordering::Greater",
            },
            vec![],
        )
    }
    pub(crate) fn path_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing path argument"))
        };
        match name {
            "Path::from_string" => {
                let value = NativeString::from_text(self.as_string(arg(0)?)?);
                self.allocate(Object::Path(value))
            }
            "Path::from_native" => {
                let value = self.as_native(arg(0)?)?;
                self.allocate(Object::Path(value))
            }
            "Path::native" => {
                let value = self.as_path(arg(0)?)?;
                self.allocate(Object::NativeString(value))
            }
            "Path::to_string" => self.native_text_result(&self.as_path(arg(0)?)?),
            "Path::join" => {
                let value = join(&self.as_path(arg(0)?)?, &self.as_path(arg(1)?)?);
                self.allocate(Object::Path(value))
            }
            "Path::parent" | "Path::file_name" | "Path::extension" => {
                let value = self.as_path(arg(0)?)?;
                let result = match name {
                    "Path::parent" => parent(&value).map(Object::Path),
                    "Path::file_name" => file_name(&value).map(Object::NativeString),
                    _ => extension(&value).map(Object::NativeString),
                };
                if let Some(value) = result {
                    let value = self.allocate(value)?;
                    self.variant("Some", vec![value])
                } else {
                    self.variant("None", vec![])
                }
            }
            "Path::is_absolute" => {
                let path = self.as_path(arg(0)?)?;
                self.boolean(prefix(&path.units(), path.windows()).absolute)
            }
            "Path::normalize_lexical" => {
                let value = normalize(&self.as_path(arg(0)?)?);
                self.allocate(Object::Path(value))
            }
            "Path::compare" => {
                let order = self.as_path(arg(0)?)?.cmp(&self.as_path(arg(1)?)?);
                self.ordering_value(order)
            }
            _ => Err(RuntimeError::internal("unknown path operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn p(text: &str, windows: bool) -> NativeString {
        if windows {
            NativeString::Windows(text.encode_utf16().collect())
        } else {
            NativeString::Posix(text.as_bytes().to_vec())
        }
    }
    #[test]
    fn lexical_roots_drive_relative_unc_and_verbatim_are_target_specific() {
        for (windows, base, child, expected) in [
            (false, "/a", "/b", "/b"),
            (false, "/a", "b\\c", "/a/b\\c"),
            (true, "C:\\a", "\\b", "C:\\b"),
            (true, "C:\\a", "D:b", "D:b"),
            (true, "C:", "b", "C:b"),
            (true, "\\\\host\\share\\a", "/b", "\\\\host\\share/b"),
            (true, "\\\\?\\C:\\a\\..\\b", "x", "\\\\?\\C:\\a\\..\\b\\x"),
        ] {
            assert_eq!(
                join(&p(base, windows), &p(child, windows)),
                p(expected, windows)
            );
        }
        for (windows, input, expected) in [
            (false, "/a/../../b", "/b"),
            (false, "a/..", "."),
            (false, "../../a", "../../a"),
            (true, "C:/a/../b", "C:\\b"),
            (true, "C:a/..", "C:."),
            (true, "\\\\server/share/a/../../b", "\\\\server\\share\\b"),
            (true, "\\\\?\\C:\\a\\..\\b", "\\\\?\\C:\\a\\..\\b"),
        ] {
            assert_eq!(normalize(&p(input, windows)), p(expected, windows));
        }
        assert!(!prefix(&p("C:a", true).units(), true).absolute);
        assert!(prefix(&p("\\\\server\\share", true).units(), true).absolute);
        assert!(!prefix(&p("\\a", true).units(), true).absolute);
    }
    #[test]
    fn parents_and_extensions_preserve_spelling_and_native_invalid_data() {
        for windows in [false, true] {
            assert_eq!(parent(&p("one", windows)), Some(p("", windows)));
            assert_eq!(parent(&p("a//b///", windows)), Some(p("a", windows)));
            assert_eq!(parent(&p("/", windows)), None);
            assert_eq!(file_name(&p("", windows)), None);
            assert_eq!(extension(&p(".profile", windows)), None);
            assert_eq!(extension(&p("a.", windows)), Some(p("", windows)));
            assert_eq!(extension(&p("a.tar.gz", windows)), Some(p("gz", windows)));
        }
        let bad = NativeString::Posix(vec![47, 255, 47, 46, 46, 47, 254]);
        assert_eq!(normalize(&bad), NativeString::Posix(vec![47, 254]));
        assert_eq!(parent(&p("C:\\a\\", true)), Some(p("C:\\", true)));
        assert_eq!(file_name(&p("\\\\server\\share", true)), None);
        assert_eq!(file_name(&p("\\\\?\\C:\\", true)), None);
        assert_eq!(
            parent(&p("\\\\?\\C:\\a", true)),
            Some(p("\\\\?\\C:\\", true))
        );
        assert_eq!(file_name(&p("\\\\?\\UNC\\server\\share\\", true)), None);
        assert_eq!(
            parent(&p("\\\\?\\UNC\\server\\share\\a", true)),
            Some(p("\\\\?\\UNC\\server\\share\\", true))
        );
        assert_eq!(file_name(&p("\\\\?\\C:\\a/b", true)), Some(p("a/b", true)));
    }
}
