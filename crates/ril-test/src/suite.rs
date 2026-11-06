//! Extract byte-exact virtual source files with coordinates back into the suite.
use ril_compiler::frontend::UnitKind;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Component, Path, PathBuf},
};

#[derive(Debug)]
pub enum Mode {
    FrontPass,
    FrontFail,
    Later(String),
}

#[derive(Debug)]
pub struct Expected {
    pub code: String,
    pub line: Option<usize>,
}

#[derive(Debug, Default)]
pub struct File {
    pub bytes: Vec<u8>,
    lines: Vec<(usize, usize)>,
}

impl File {
    pub fn suite_line(&self, offset: usize) -> Option<usize> {
        let count = self.lines.partition_point(|(start, _)| *start <= offset);
        count.checked_sub(1).map(|index| self.lines[index].1)
    }
}

#[derive(Debug)]
pub struct Case {
    pub name: String,
    pub mode: Mode,
    pub kind: UnitKind,
    pub line: usize,
    pub files: BTreeMap<PathBuf, File>,
    pub errors: Vec<Expected>,
}

impl Case {
    fn new(name: &str, mode: Mode, line: usize) -> Self {
        Self {
            name: name.into(),
            mode,
            kind: UnitKind::Library,
            line,
            files: BTreeMap::new(),
            errors: vec![],
        }
    }
}

pub fn parse_suite(bytes: &[u8]) -> Result<Vec<Case>, String> {
    let mut cases = vec![];
    let mut case = None;
    let mut pair = None;
    let mut path = PathBuf::from("root.ril");
    let mut hexadecimal = false;
    let mut last_source_line = None;
    let mut names = BTreeSet::new();
    let mut header_open = false;

    for (index, bytes) in bytes.split_inclusive(|byte| *byte == b'\n').enumerate() {
        let line = index + 1;
        let fail = |message: &str| format!("{line}: {message}");
        let text = std::str::from_utf8(bytes)
            .ok()
            .map(|text| text.trim_end_matches(['\r', '\n']));
        if let Some(text) = text {
            if let Some(header) = text
                .strip_prefix("-- [case: ")
                .and_then(|text| text.strip_suffix(']'))
            {
                finish(&mut case, &mut cases, &mut names)?;
                let (name, mode) = header
                    .rsplit_once(',')
                    .ok_or_else(|| fail("case requires a name and mode"))?;
                let mode = match mode.trim() {
                    "front-pass" => Mode::FrontPass,
                    "front-fail" => Mode::FrontFail,
                    mode @ ("check-pass" | "check-fail" | "run-pass" | "run-panic"
                    | "run-program") => Mode::Later(mode.into()),
                    _ => return Err(fail("unknown case mode")),
                };
                case = Some(Case::new(name.trim(), mode, line));
                pair = None;
                path = PathBuf::from("root.ril");
                hexadecimal = false;
                last_source_line = None;
                header_open = true;
                continue;
            }
            if let Some(name) = text
                .strip_prefix("-- [pair: ")
                .and_then(|text| text.strip_suffix(']'))
            {
                finish(&mut case, &mut cases, &mut names)?;
                pair = Some((name, UnitKind::Library, false));
                continue;
            }
            if matches!(text, "-- accept" | "-- reject") {
                finish(&mut case, &mut cases, &mut names)?;
                let (name, kind, accepted) = pair
                    .as_mut()
                    .ok_or_else(|| fail("pair side without pair"))?;
                let accept = text == "-- accept";
                if accept == *accepted {
                    return Err(fail("pair requires accept followed by reject"));
                }
                *accepted = accept;
                let side = if accept { "accept" } else { "reject" };
                let mut side_case = Case::new(
                    &format!("{name}/{side}"),
                    Mode::Later(format!("check-{}", if accept { "pass" } else { "fail" })),
                    line,
                );
                side_case.kind = *kind;
                case = Some(side_case);
                if !accept {
                    pair = None;
                }
                path = PathBuf::from("root.ril");
                hexadecimal = false;
                last_source_line = None;
                header_open = true;
                continue;
            }
            if let Some(unit) = text.strip_prefix("-- unit: ")
                && (header_open || case.is_none())
            {
                let kind = match unit {
                    "executable" => UnitKind::Executable,
                    _ => return Err(fail("unknown unit kind")),
                };
                if let Some(case) = &mut case {
                    case.kind = kind;
                } else if let Some((_, current, _)) = &mut pair {
                    *current = kind;
                } else {
                    return Err(fail("unit directive outside a case"));
                }
                continue;
            }
            if header_open && text.starts_with("-- spec: ") {
                continue;
            }
            if let Some(file) = text.strip_prefix("-- file: ") {
                let case = case.as_mut().ok_or_else(|| fail("file outside a case"))?;
                let (file, hex) = file
                    .strip_suffix(" hex")
                    .map_or((file, false), |file| (file, true));
                if file.contains('\\')
                    || file.contains(':')
                    || file.is_empty()
                    || Path::new(file)
                        .components()
                        .any(|part| !matches!(part, Component::Normal(_)))
                {
                    return Err(fail("virtual file must be a relative path within the case"));
                }
                path = file.into();
                if case.files.insert(path.clone(), File::default()).is_some() {
                    return Err(fail("duplicate virtual file"));
                }
                hexadecimal = hex;
                last_source_line = None;
                header_open = false;
                continue;
            }
            if let Some(code) = text
                .strip_prefix("-- Error [")
                .and_then(|text| text.split_once(']'))
                .map(|(code, _)| code)
            {
                let case = case
                    .as_mut()
                    .ok_or_else(|| fail("diagnostic outside a case"))?;
                case.errors.push(Expected {
                    code: code.into(),
                    line: None,
                });
                continue;
            }
            if !hexadecimal
                && let Some((prefix, suffix)) = text.split_once("--~ ERROR [")
                && let Some((code, _)) = suffix.split_once(']')
            {
                let case = case
                    .as_mut()
                    .ok_or_else(|| fail("diagnostic outside a case"))?;
                let target = if prefix.trim().is_empty() {
                    last_source_line
                        .ok_or_else(|| fail("diagnostic marker has no preceding source line"))?
                } else {
                    line
                };
                case.errors.push(Expected {
                    code: code.into(),
                    line: Some(target),
                });
            }
        }
        let Some(case) = &mut case else {
            if text.is_some_and(|text| text.trim().is_empty() || text.starts_with("--")) {
                continue;
            }
            return Err(fail("source outside a case"));
        };
        // A framing header may include blank lines before an explicit file marker.
        if header_open && text.is_some_and(|text| text.trim().is_empty()) {
            continue;
        }
        header_open = false;
        let file = case.files.entry(path.clone()).or_default();
        if hexadecimal {
            let text = text.ok_or_else(|| fail("invalid UTF-8 in hex fixture"))?;
            for word in text.split_ascii_whitespace() {
                if word.len() % 2 != 0 || !word.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                    return Err(fail("invalid hexadecimal fixture"));
                }
                for offset in (0..word.len()).step_by(2) {
                    file.lines.push((file.bytes.len(), line));
                    file.bytes.push(
                        u8::from_str_radix(&word[offset..offset + 2], 16)
                            .map_err(|_| fail("invalid hexadecimal byte"))?,
                    );
                }
            }
        } else {
            file.lines.push((file.bytes.len(), line));
            file.bytes.extend_from_slice(bytes);
            if text
                .is_none_or(|text| !text.trim().is_empty() && !text.trim_start().starts_with("--"))
            {
                last_source_line = Some(line);
            }
        }
    }
    finish(&mut case, &mut cases, &mut names)?;
    Ok(cases)
}

fn finish(
    case: &mut Option<Case>,
    cases: &mut Vec<Case>,
    names: &mut BTreeSet<String>,
) -> Result<(), String> {
    if let Some(case) = case.take() {
        if case.name.is_empty() || !names.insert(case.name.clone()) {
            return Err(format!("{}: empty or duplicate case name", case.line));
        }
        if !case.files.contains_key(Path::new("root.ril")) {
            return Err(format!("{}: case requires root.ril", case.line));
        }
        if matches!(case.mode, Mode::FrontFail) && case.errors.is_empty() {
            return Err(format!(
                "{}: front-fail requires a diagnostic code",
                case.line
            ));
        }
        cases.push(case);
    }
    Ok(())
}
