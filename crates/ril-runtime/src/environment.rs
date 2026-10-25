//! Environmental snapshots preserve native strings and never mutate the parent.
use crate::{
    heap::{Handle, Object},
    native_string::NativeString,
    value::{Result, Runtime, RuntimeError},
};

/// STD's command-line grammar applies equally to the program-name element.
pub fn parse_windows_command_line(line: &[u16]) -> Vec<Vec<u16>> {
    let line = &line[..line
        .iter()
        .position(|&unit| unit == 0)
        .unwrap_or(line.len())];
    let mut output = Vec::new();
    let mut index = 0;
    while index < line.len() {
        while index < line.len() && matches!(line[index], 9 | 32) {
            index += 1;
        }
        if index == line.len() {
            break;
        }
        let mut argument = Vec::new();
        let mut quoted = false;
        while index < line.len() && (quoted || !matches!(line[index], 9 | 32)) {
            let mut backslashes = 0;
            while index < line.len() && line[index] == 92 {
                backslashes += 1;
                index += 1;
            }
            if index < line.len() && line[index] == 34 {
                argument.extend(std::iter::repeat_n(92, backslashes / 2));
                if backslashes % 2 == 0 {
                    quoted = !quoted;
                } else {
                    argument.push(34);
                }
                index += 1;
            } else {
                argument.extend(std::iter::repeat_n(92, backslashes));
                if index < line.len() {
                    if !quoted && matches!(line[index], 9 | 32) {
                        break;
                    }
                    argument.push(line[index]);
                    index += 1;
                }
            }
        }
        output.push(argument);
    }
    output
}
pub fn quote_windows_argument(argument: &[u16]) -> Vec<u16> {
    let mut output = vec![34];
    let mut backslashes = 0;
    for &unit in argument {
        if unit == 92 {
            backslashes += 1;
            continue;
        }
        output.extend(std::iter::repeat_n(
            92,
            if unit == 34 {
                backslashes * 2 + 1
            } else {
                backslashes
            },
        ));
        output.push(unit);
        backslashes = 0;
    }
    output.extend(std::iter::repeat_n(92, backslashes * 2));
    output.push(34);
    output
}
pub(crate) fn valid_environment_name(name: &NativeString) -> bool {
    let units = name.units();
    !units.is_empty() && !units.contains(&0) && !units.contains(&61)
}

impl Runtime {
    pub(crate) fn environment_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        match name {
            "Env::args" => {
                let arguments = {
                    #[cfg(windows)]
                    {
                        parse_windows_command_line(&crate::platform_environment::command_line())
                            .into_iter()
                            .skip(1)
                            .map(NativeString::Windows)
                            .collect::<Vec<_>>()
                    }
                    #[cfg(unix)]
                    {
                        std::env::args_os()
                            .skip(1)
                            .map(|argument| NativeString::from_os(&argument))
                            .collect::<Vec<_>>()
                    }
                };
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.allocate(Object::NativeString(argument)))
                    .collect::<Result<Vec<_>>>()?;
                self.allocate(Object::Array(arguments))
            }
            "Env::get" => {
                let argument = *args
                    .first()
                    .ok_or_else(|| RuntimeError::internal("missing environment name"))?;
                let name = self.as_native(argument)?;
                if !valid_environment_name(&name) {
                    return self.io_failure("InvalidInput", "invalid environment name");
                }
                let name = match name.to_os() {
                    Ok(name) => name,
                    Err(kind) => return self.io_failure("InvalidInput", kind),
                };
                let value = if let Some(value) = std::env::var_os(name) {
                    let value =
                        self.allocate(Object::NativeString(NativeString::from_os(&value)))?;
                    self.variant("Some", vec![value])?
                } else {
                    self.variant("None", vec![])?
                };
                self.variant("Ok", vec![value])
            }
            "\0ril.host.environment_all" => {
                let entries = std::env::vars_os()
                    .map(|(name, value)| {
                        (NativeString::from_os(&name), NativeString::from_os(&value))
                    })
                    .filter(|(name, _)| valid_environment_name(name))
                    .collect::<Vec<_>>();
                #[cfg(windows)]
                let entries = {
                    let mut entries = entries;
                    entries.sort_by(|a, b| {
                        crate::platform_environment::compare_environment_names(
                            &a.0.units(),
                            &b.0.units(),
                        )
                    });
                    entries.dedup_by(|a, b| {
                        crate::platform_environment::compare_environment_names(
                            &a.0.units(),
                            &b.0.units(),
                        )
                        .is_eq()
                    });
                    entries
                };
                let mut values = Vec::with_capacity(entries.len());
                for (name, value) in entries {
                    let name = self.allocate(Object::NativeString(name))?;
                    let value = self.allocate(Object::NativeString(value))?;
                    values.push(self.allocate(Object::Tuple(vec![name, value]))?);
                }
                self.allocate(Object::Array(values))
            }
            "Env::current_dir" | "Env::temp_dir" => {
                let path = if name == "Env::current_dir" {
                    std::env::current_dir()
                } else {
                    let path = std::env::temp_dir();
                    if path.is_absolute() {
                        Ok(path)
                    } else {
                        std::env::current_dir().map(|cwd| cwd.join(path))
                    }
                };
                match path {
                    Ok(path) => {
                        let value =
                            self.allocate(Object::Path(NativeString::from_os(path.as_os_str())))?;
                        self.variant("Ok", vec![value])
                    }
                    Err(error) => self.io_result(Err(error)),
                }
            }
            _ => Err(RuntimeError::internal("unknown environment operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn command_line_grammar_matches_the_spec_and_preserves_unpaired_units() {
        for (line, expected) in [
            ("app.exe a b", vec!["app.exe", "a", "b"]),
            ("app.exe a\" b\"c", vec!["app.exe", "a bc"]),
            ("app.exe \"\"", vec!["app.exe", ""]),
            ("app.exe \"unfinished", vec!["app.exe", "unfinished"]),
            ("app.exe \"a\"\"b\"", vec!["app.exe", "ab"]),
            ("app.exe a\\\"b", vec!["app.exe", "a\"b"]),
            ("  \t\"ex e\" a\r\nb\t", vec!["ex e", "a\r\nb"]),
        ] {
            let units = line.encode_utf16().collect::<Vec<_>>();
            assert_eq!(
                parse_windows_command_line(&units),
                expected
                    .into_iter()
                    .map(|text| text.encode_utf16().collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            );
        }
        // Exhaustively round-trip short native-unit sequences, including NUL-free
        // invalid Unicode, separators, quotes, and runs of backslashes.
        let alphabet = [9, 10, 32, 34, 92, 97, 0xd800];
        let mut words = vec![vec![]];
        for _ in 0..4 {
            let previous = words.clone();
            words.extend(previous.iter().flat_map(|prefix| {
                alphabet.into_iter().map(move |unit| {
                    let mut word = prefix.clone();
                    word.push(unit);
                    word
                })
            }));
        }
        for word in words {
            assert_eq!(
                parse_windows_command_line(&quote_windows_argument(&word)),
                vec![word]
            );
        }
        assert_eq!(parse_windows_command_line(&[97, 0, 98]), vec![vec![97]]);
    }
}
