use crate::{Error, Result, annotations::line_comments, require};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::{
    collections::{HashMap, HashSet},
    sync::LazyLock,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Mode {
    CheckPass,
    CheckFail,
    RunPass,
    RunPanic,
    RunProgram,
}

impl Mode {
    pub const ALL: [Self; 5] = [
        Self::CheckPass,
        Self::CheckFail,
        Self::RunPass,
        Self::RunPanic,
        Self::RunProgram,
    ];
    pub fn is_run(self) -> bool {
        matches!(self, Self::RunPass | Self::RunPanic | Self::RunProgram)
    }
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::CheckPass => "check-pass",
            Self::CheckFail => "check-fail",
            Self::RunPass => "run-pass",
            Self::RunPanic => "run-panic",
            Self::RunProgram => "run-program",
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Unit {
    Library,
    Executable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PointerTarget {
    Pointer32,
    Pointer64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Capability {
    Windows,
    Posix,
    Filesystem,
    Process,
    Clock,
    Entropy,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HelperBuild {
    pub source: String,
    pub output: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Metadata {
    pub mode: Mode,
    pub spec: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub entry: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unit: Option<Unit>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub companion: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<PointerTarget>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requires: Option<Vec<Capability>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seed: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exit: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stderr: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdin: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub args: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub env: Option<Vec<String>>,
    #[serde(rename = "unset-env", skip_serializing_if = "Option::is_none")]
    pub unset_env: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build: Option<Vec<HelperBuild>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VirtualFile {
    pub name: String,
    pub bytes: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Case {
    pub id: String,
    pub bundle: String,
    pub name: String,
    pub line: usize,
    pub meta: Metadata,
    pub annotations: Vec<String>,
    pub files: Vec<VirtualFile>,
    pub root: String,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

fn regex(pattern: &'static str) -> Regex {
    Regex::new(pattern).expect("constant regex")
}

static NAME: LazyLock<Regex> = LazyLock::new(|| regex(r"^[a-z0-9]+(?:-[a-z0-9]+)*$"));
static SPEC: LazyLock<Regex> = LazyLock::new(|| regex(r"^(SPEC|STD)#[a-z0-9-]+$"));
static ERRORS: LazyLock<Regex> = LazyLock::new(|| regex(r"-- Error \[(E[0-9]{4})\]"));
static WARNINGS: LazyLock<Regex> = LazyLock::new(|| regex(r"-- Warning \[(W[0-9]{4})\]"));
static PANIC: LazyLock<Regex> = LazyLock::new(|| regex(r"-- Panics\b"));
static ENTRY: LazyLock<Regex> = LazyLock::new(|| regex(r"^test_[a-z0-9_]+$"));

pub fn portable_path(name: &str) -> Result<()> {
    require(!name.is_empty(), "invalid file path")?;
    for part in name.split('/') {
        require(
            !part.is_empty()
                && part
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || "_.-".contains(c))
                && part != "."
                && part != ".."
                && !part.ends_with('.'),
            format!("invalid file path: {name}"),
        )?;
        let stem = part.split('.').next().unwrap().to_ascii_lowercase();
        let reserved = ["con", "prn", "aux", "nul"].contains(&stem.as_str())
            || ((stem.starts_with("com") || stem.starts_with("lpt"))
                && stem.len() == 4
                && matches!(stem.as_bytes()[3], b'1'..=b'9'));
        require(!reserved, format!("nonportable file path: {name}"))?;
    }
    Ok(())
}

fn claim_path(claims: &mut HashSet<String>, name: &str) -> Result<()> {
    portable_path(name)?;
    let folded = name.to_ascii_lowercase();
    require(
        !claims.iter().any(|old| {
            old == &folded
                || old.starts_with(&format!("{folded}/"))
                || folded.starts_with(&format!("{old}/"))
        }),
        format!("conflicting file path: {name}"),
    )?;
    claims.insert(folded);
    Ok(())
}

pub fn validate_case(item: &mut Case) -> Result<()> {
    require(
        item.files
            .first()
            .is_some_and(|file| file.name.ends_with(".ril")),
        "first file must be a Ril compilation root",
    )?;
    let source = String::from_utf8_lossy(&item.files[0].bytes);
    item.root = item.files[0].name.clone();

    if matches!(item.meta.mode, Mode::RunPass | Mode::RunPanic) && item.meta.entry.is_none() {
        let candidate = format!("test_{}", item.name.replace('-', "_"));
        if source
            .lines()
            .any(|line| line.starts_with(&format!("pub fn {candidate}()")))
        {
            item.meta.entry = Some(candidate);
        } else {
            let matches: Vec<_> = source
                .lines()
                .filter_map(|line| {
                    line.strip_prefix("pub fn ")
                        .and_then(|rest| rest.split('(').next())
                        .filter(|name| ENTRY.is_match(name))
                })
                .collect();
            if matches.len() == 1 {
                item.meta.entry = Some(matches[0].to_owned());
            }
        }
    }

    let meta = &item.meta;
    require(
        !meta.spec.is_empty() && meta.spec.iter().all(|value| SPEC.is_match(value)),
        "missing or invalid spec",
    )?;
    let mut claims = HashSet::new();
    for file in &item.files {
        claim_path(&mut claims, &file.name)?;
    }
    let need_file = |name: &str| -> Result<()> {
        portable_path(name)?;
        require(
            item.files.iter().any(|file| file.name == name),
            format!("missing virtual file: {name}"),
        )
    };
    let comments = item
        .annotations
        .iter()
        .cloned()
        .chain(line_comments(&source))
        .collect::<Vec<_>>()
        .join("\n");
    item.errors = ERRORS
        .captures_iter(&comments)
        .map(|c| c[1].to_owned())
        .collect();
    item.warnings = WARNINGS
        .captures_iter(&comments)
        .map(|c| c[1].to_owned())
        .collect();
    if meta.mode == Mode::CheckFail {
        require(
            item.errors.len() == 1,
            "check-fail requires one diagnostic expectation",
        )?;
    } else {
        require(
            item.errors.is_empty(),
            "error expectation on an accepting case",
        )?;
    }
    if meta.mode == Mode::RunPanic {
        require(PANIC.is_match(&comments), "missing panic expectation")?;
    }
    if matches!(meta.mode, Mode::RunPass | Mode::RunPanic) {
        let entry = meta.entry.as_deref().unwrap_or("");
        require(ENTRY.is_match(entry), "missing or invalid entry")?;
        require(
            source
                .lines()
                .any(|line| line.starts_with(&format!("pub fn {entry}()"))),
            "selected zero-argument function missing",
        )?;
        require(
            meta.unit.is_none_or(|unit| unit == Unit::Library),
            "test functions require library input",
        )?;
    } else {
        require(
            meta.entry.is_none(),
            "entry only applies to test-function modes",
        )?;
    }
    if meta.mode == Mode::RunProgram {
        require(
            meta.exit
                .is_some_and(|value| value.unsigned_abs() <= 9_007_199_254_740_991),
            "missing or invalid exit status",
        )?;
        require(
            source.lines().any(|line| line.starts_with("pub fn main()")),
            "program main missing",
        )?;
        require(
            meta.unit.is_none_or(|unit| unit == Unit::Executable),
            "program requires executable input",
        )?;
    } else {
        require(
            meta.exit.is_none() && meta.stdout.is_none() && meta.stderr.is_none(),
            "program expectations on non-program mode",
        )?;
    }
    for name in [&meta.stdout, &meta.stderr].into_iter().flatten() {
        if name != "empty" {
            need_file(name)?;
        }
    }
    if let Some(name) = &meta.stdin {
        need_file(name)?;
    }
    if let Some(requires) = &meta.requires {
        require(!requires.is_empty(), "unknown external capability")?;
        require(
            !(requires.contains(&Capability::Windows) && requires.contains(&Capability::Posix)),
            "contradictory platforms",
        )?;
    }
    if let Some(seed) = &meta.seed {
        require(
            !seed.is_empty() && seed.bytes().all(|c| c.is_ascii_digit()),
            "invalid seed",
        )?;
    }
    if let Some(companion) = &meta.companion {
        require(NAME.is_match(companion), "invalid companion name")?;
    }
    if let Some(args) = &meta.args {
        require(
            args.iter().all(|arg| !arg.contains('\0')),
            "args must be strings without NUL",
        )?;
    }
    let mut environment = HashSet::new();
    for assignment in meta.env.iter().flatten() {
        let (name, _) = assignment
            .split_once('=')
            .ok_or_else(|| Error::Invalid("invalid environment assignment".into()))?;
        require(
            !name.is_empty() && !assignment.contains('\0'),
            "invalid environment assignment",
        )?;
        require(
            environment.insert(name.to_lowercase()),
            "duplicate environment name",
        )?;
    }
    for name in meta.unset_env.iter().flatten() {
        require(
            !name.is_empty() && !name.contains(['=', '\0']),
            "invalid environment name",
        )?;
        require(
            environment.insert(name.to_lowercase()),
            "conflicting environment name",
        )?;
    }
    for build in meta.build.iter().flatten() {
        need_file(&build.source)?;
        require(
            build.source.ends_with(".ril") && !build.source.ends_with(".d.ril"),
            "helper build requires implementation source",
        )?;
        claim_path(&mut claims, &build.output)?;
    }
    if !meta.mode.is_run() {
        require(
            meta.build.is_none()
                && meta.args.is_none()
                && meta.env.is_none()
                && meta.unset_env.is_none()
                && meta.stdin.is_none(),
            "execution setup requires a run mode",
        )?;
    }
    Ok(())
}

struct CaseBuilder {
    name: String,
    line: usize,
    meta: Map<String, Value>,
    annotations: Vec<String>,
    files: Vec<VirtualFile>,
}

struct FileBuilder {
    name: String,
    hex: bool,
    final_newline: bool,
    lines: Vec<String>,
}

struct SourceBuilder {
    name: String,
    files: Vec<VirtualFile>,
}

fn decode_metadata(mut raw: Map<String, Value>) -> Result<Metadata> {
    if let Some(Value::String(args)) = raw.remove("args") {
        let args: Value = serde_json::from_str(&args)?;
        require(
            args.as_array().is_some_and(|values| {
                values
                    .iter()
                    .all(|value| value.as_str().is_some_and(|arg| !arg.contains('\0')))
            }),
            "args must be an array of strings without NUL",
        )?;
        raw.insert("args".into(), args);
    }
    if let Some(Value::String(requires)) = raw.remove("requires") {
        raw.insert(
            "requires".into(),
            serde_json::to_value(requires.split(',').map(str::trim).collect::<Vec<_>>())?,
        );
    }
    if let Some(Value::String(exit)) = raw.remove("exit") {
        let digits = exit.strip_prefix('-').unwrap_or(&exit);
        require(
            !digits.is_empty() && digits.bytes().all(|c| c.is_ascii_digit()),
            "invalid exit status",
        )?;
        let number = exit
            .parse::<i64>()
            .map_err(|_| Error::Invalid("invalid exit status".into()))?;
        raw.insert("exit".into(), number.into());
    }
    if let Some(Value::Array(builds)) = raw.remove("build") {
        let mut decoded = Vec::new();
        for build in builds {
            let build = build.as_str().unwrap();
            let (source, output) = build
                .split_once(" -> ")
                .ok_or_else(|| Error::Invalid("build must be source -> output".into()))?;
            require(
                !source.is_empty()
                    && !output.is_empty()
                    && !source.chars().any(char::is_whitespace)
                    && !output.chars().any(char::is_whitespace),
                "build must be source -> output",
            )?;
            decoded.push(HelperBuild {
                source: source.into(),
                output: output.into(),
            });
        }
        raw.insert("build".into(), serde_json::to_value(decoded)?);
    }
    Ok(serde_json::from_value(Value::Object(raw))?)
}

const DIRECTIVE_KEYS: &[&str] = &[
    "mode",
    "spec",
    "entry",
    "unit",
    "companion",
    "target",
    "requires",
    "seed",
    "exit",
    "stdout",
    "stderr",
    "stdin",
    "args",
    "env",
    "unset-env",
    "build",
];

fn split_bracket_items(s: &str) -> Vec<String> {
    let mut items = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;
    let mut bracket_depth: usize = 0;
    for c in s.chars() {
        match c {
            '"' => {
                in_quote = !in_quote;
                current.push(c);
            }
            '[' | '{' if !in_quote => {
                bracket_depth += 1;
                current.push(c);
            }
            ']' | '}' if !in_quote => {
                bracket_depth = bracket_depth.saturating_sub(1);
                current.push(c);
            }
            ',' if !in_quote && bracket_depth == 0 => {
                let trimmed = current.trim();
                if !trimmed.is_empty() {
                    items.push(trimmed.to_string());
                }
                current.clear();
            }
            _ => current.push(c),
        }
    }
    let trimmed = current.trim();
    if !trimmed.is_empty() {
        items.push(trimmed.to_string());
    }
    items
}

fn apply_directive(meta: &mut Map<String, Value>, key: &str, value: &str) -> Result<()> {
    require(
        DIRECTIVE_KEYS.contains(&key),
        format!("unknown or malformed directive: {key}"),
    )?;
    if ["spec", "build", "env", "unset-env"].contains(&key) {
        meta.entry(key.to_owned())
            .or_insert_with(|| Value::Array(Vec::new()))
            .as_array_mut()
            .unwrap()
            .push(value.into());
    } else {
        require(!meta.contains_key(key), format!("duplicate {key}"))?;
        meta.insert(key.into(), value.into());
    }
    Ok(())
}

fn apply_item_to_meta(meta: &mut Map<String, Value>, item: &str) -> Result<()> {
    let item = item.trim();
    if item.is_empty() {
        return Ok(());
    }
    if Mode::ALL.iter().any(|m| m.to_string() == item) {
        apply_directive(meta, "mode", item)
    } else if SPEC.is_match(item) {
        apply_directive(meta, "spec", item)
    } else if let Some((k, v)) = item.split_once(": ") {
        apply_directive(meta, k.trim(), v.trim())
    } else if let Some((k, v)) = item.split_once(':') {
        apply_directive(meta, k.trim(), v.trim())
    } else {
        Err(Error::Invalid(format!("unknown directive in bracket: {item}")))
    }
}

fn parse_file_directive(line: &str) -> Option<(String, bool, bool)> {
    static FILE_REGEX: LazyLock<Regex> = LazyLock::new(|| {
        regex(r"^--(?:@\s*|\s*|\s*\[)file:\s*(\S+?)(?:\s+(hex|no-final-newline))?\]?$")
    });
    let cap = FILE_REGEX.captures(line)?;
    let name = cap[1].to_string();
    let flag = cap.get(2).map(|m| m.as_str());
    let hex = flag == Some("hex");
    let final_newline = flag != Some("no-final-newline");
    Some((name, hex, final_newline))
}

fn finish_file(open: FileBuilder) -> Result<VirtualFile> {
    let bytes = if open.hex {
        let hex: String = open
            .lines
            .join("")
            .chars()
            .filter(|c| !c.is_whitespace() && *c != '\u{feff}')
            .collect();
        require(
            hex.len().is_multiple_of(2) && hex.bytes().all(|b| b.is_ascii_hexdigit()),
            "invalid hex bytes",
        )?;
        hex.as_bytes()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|chunk| u8::from_str_radix(std::str::from_utf8(chunk).unwrap(), 16).unwrap())
            .collect()
    } else {
        let mut lines = open.lines;
        while lines.last().is_some_and(|l| l.trim().is_empty()) {
            lines.pop();
        }
        let mut bytes: Vec<_> = lines
            .iter()
            .flat_map(|line| line.bytes().chain(*b"\n"))
            .collect();
        if !open.final_newline && !bytes.is_empty() {
            bytes.pop();
        }
        bytes
    };
    Ok(VirtualFile {
        name: open.name,
        bytes,
    })
}

fn flush_file(
    file: &mut Option<FileBuilder>,
    current: &mut Option<CaseBuilder>,
    source: &mut Option<SourceBuilder>,
) -> Result<()> {
    if let Some(open) = file.take() {
        let vf = finish_file(open)?;
        if let Some(source) = source {
            source.files.push(vf);
        } else if let Some(current) = current {
            current.files.push(vf);
        }
    }
    Ok(())
}

fn flush_case(
    file: &mut Option<FileBuilder>,
    current: &mut Option<CaseBuilder>,
    source: &mut Option<SourceBuilder>,
    cases: &mut Vec<Case>,
    bundle: &str,
) -> Result<()> {
    flush_file(file, current, source)?;
    if let Some(mut open) = current.take() {
        if open.files.is_empty() {
            open.files.push(VirtualFile {
                name: format!("{}.ril", open.name),
                bytes: Vec::new(),
            });
        }
        let mut item = Case {
            id: format!("{bundle}::{}", open.name),
            bundle: bundle.into(),
            name: open.name,
            line: open.line,
            meta: decode_metadata(open.meta)?,
            annotations: open.annotations,
            files: open.files,
            root: String::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
        };
        validate_case(&mut item)?;
        cases.push(item);
    }
    Ok(())
}

fn flush_source(
    file: &mut Option<FileBuilder>,
    current: &mut Option<CaseBuilder>,
    source: &mut Option<SourceBuilder>,
    sources: &mut HashMap<String, Vec<VirtualFile>>,
) -> Result<()> {
    flush_file(file, current, source)?;
    if let Some(open) = source.take() {
        require(!open.files.is_empty(), "empty shared source")?;
        sources.insert(open.name, open.files);
    }
    Ok(())
}

/// Framing is independent from the embedded program's lexical validity.
pub fn parse_bundle(text: &str, bundle: &str) -> Result<Vec<Case>> {
    let mut cases = Vec::new();
    let mut names = HashSet::new();
    let mut current: Option<CaseBuilder> = None;
    let mut source: Option<SourceBuilder> = None;
    let mut sources: HashMap<String, Vec<VirtualFile>> = HashMap::new();
    let mut used_sources = HashSet::new();
    let mut file: Option<FileBuilder> = None;
    let lines: Vec<_> = text.split('\n').collect();
    for (index, raw_line) in lines.iter().enumerate() {
        let line = if index + 1 < lines.len() {
            raw_line.strip_suffix('\r').unwrap_or(raw_line)
        } else {
            raw_line
        };
        let result = (|| -> Result<()> {
            require(
                !line.contains('\r'),
                "bare CR in container; use hex for exact bytes",
            )?;
            if let Some(open) = &mut file {
                if line == "--@ end-file" || line == "-- end-file" || line == "-- [end-file]" {
                    flush_file(&mut file, &mut current, &mut source)?;
                    return Ok(());
                }
                if line == "--@ end-case" || line == "-- end-case" || line == "-- [end-case]" {
                    flush_case(&mut file, &mut current, &mut source, &mut cases, bundle)?;
                    return Ok(());
                }
                if line == "--@ end-source" || line == "-- end-source" || line == "-- [end-source]" {
                    flush_source(&mut file, &mut current, &mut source, &mut sources)?;
                    return Ok(());
                }
                let is_new_case = line.starts_with("--@ case: ")
                    || line.starts_with("-- case: ")
                    || line.starts_with("-- [case: ");
                let is_new_source = line.starts_with("--@ source: ")
                    || line.starts_with("-- source: ")
                    || line.starts_with("-- [source: ");
                let is_new_file = parse_file_directive(line).is_some();

                if is_new_case || is_new_source || is_new_file {
                    flush_file(&mut file, &mut current, &mut source)?;
                    if is_new_case {
                        flush_case(&mut file, &mut current, &mut source, &mut cases, bundle)?;
                    }
                    if is_new_source {
                        flush_source(&mut file, &mut current, &mut source, &mut sources)?;
                    }
                } else if !open.hex && line.starts_with("--@@") {
                    open.lines.push(line.replacen("--@@", "--@", 1));
                    return Ok(());
                } else if !open.hex && line.starts_with("--[[") {
                    open.lines.push(line.replacen("--[[", "--[", 1));
                    return Ok(());
                } else {
                    require(
                        !line.starts_with("--@"),
                        "unexpected nested delimiter; escape source lines with --@@",
                    )?;
                    open.lines.push(line.into());
                    return Ok(());
                }
            }

            if line == "--@ end-case" || line == "-- end-case" || line == "-- [end-case]" {
                flush_case(&mut file, &mut current, &mut source, &mut cases, bundle)?;
                return Ok(());
            }
            if line == "--@ end-source" || line == "-- end-source" || line == "-- [end-source]" {
                flush_source(&mut file, &mut current, &mut source, &mut sources)?;
                return Ok(());
            }
            if line == "--@ end-file" || line == "-- end-file" || line == "-- [end-file]" {
                return Ok(());
            }

            let new_source_name = if let Some(rest) = line.strip_prefix("--@ source: ") {
                Some(rest.trim())
            } else if let Some(rest) = line.strip_prefix("-- source: ") {
                Some(rest.trim())
            } else {
                line.strip_prefix("-- [source: ")
                    .and_then(|s| s.strip_suffix(']'))
                    .map(str::trim)
            };
            if let Some(name) = new_source_name {
                flush_case(&mut file, &mut current, &mut source, &mut cases, bundle)?;
                flush_source(&mut file, &mut current, &mut source, &mut sources)?;
                require(NAME.is_match(name), "invalid shared source name")?;
                require(!sources.contains_key(name), "duplicate shared source")?;
                source = Some(SourceBuilder {
                    name: name.into(),
                    files: Vec::new(),
                });
                return Ok(());
            }

            let new_case_data = if let Some(rest) = line.strip_prefix("--@ case: ") {
                Some((rest.trim().to_string(), Vec::new()))
            } else if let Some(rest) = line.strip_prefix("-- case: ") {
                Some((rest.trim().to_string(), Vec::new()))
            } else if let Some(inner) = line.strip_prefix("-- [case: ").and_then(|s| s.strip_suffix(']')) {
                let mut items = split_bracket_items(inner);
                let name = items.remove(0);
                Some((name, items))
            } else {
                None
            };
            if let Some((name, remaining_items)) = new_case_data {
                flush_case(&mut file, &mut current, &mut source, &mut cases, bundle)?;
                flush_source(&mut file, &mut current, &mut source, &mut sources)?;
                require(NAME.is_match(&name), format!("invalid case name: {name}"))?;
                require(
                    names.insert(name.clone()),
                    format!("duplicate case: {name}"),
                )?;
                let mut builder = CaseBuilder {
                    name,
                    line: index + 1,
                    meta: Map::new(),
                    annotations: Vec::new(),
                    files: Vec::new(),
                };
                for item in remaining_items {
                    apply_item_to_meta(&mut builder.meta, &item)?;
                }
                current = Some(builder);
                return Ok(());
            }

            if source.is_some() {
                if let Some((name, hex, final_newline)) = parse_file_directive(line) {
                    portable_path(&name)?;
                    file = Some(FileBuilder {
                        name,
                        hex,
                        final_newline,
                        lines: Vec::new(),
                    });
                    return Ok(());
                }
                return require(
                    line.trim().is_empty() || (line.starts_with("--") && !line.starts_with("--@")),
                    "shared source accepts only file blocks",
                );
            }

            let Some(open_case) = &mut current else {
                return require(
                    line.trim().is_empty() || (line.starts_with("--") && !line.starts_with("--@")),
                    "expected case delimiter",
                );
            };

            let use_source_name = if let Some(rest) = line.strip_prefix("--@ use-source: ") {
                Some(rest.trim())
            } else if let Some(rest) = line.strip_prefix("-- use-source: ") {
                Some(rest.trim())
            } else {
                line.strip_prefix("-- [use-source: ")
                    .and_then(|s| s.strip_suffix(']'))
                    .map(str::trim)
            };
            if let Some(name) = use_source_name {
                require(
                    open_case.files.is_empty(),
                    "a case has exactly one shared source or explicit file set",
                )?;
                open_case.files = sources
                    .get(name)
                    .cloned()
                    .ok_or_else(|| Error::Invalid(format!("unknown shared source: {name}")))?;
                used_sources.insert(name.to_owned());
                return Ok(());
            }

            if let Some((name, hex, final_newline)) = parse_file_directive(line) {
                portable_path(&name)?;
                file = Some(FileBuilder {
                    name,
                    hex,
                    final_newline,
                    lines: Vec::new(),
                });
                return Ok(());
            }

            if let Some(inner) = line.strip_prefix("-- [").and_then(|s| s.strip_suffix(']')) {
                require(open_case.files.is_empty(), "metadata must precede file blocks")?;
                for item in split_bracket_items(inner) {
                    apply_item_to_meta(&mut open_case.meta, &item)?;
                }
                return Ok(());
            }

            let directive_opt = if let Some(rest) = line.strip_prefix("--@ ") {
                rest.split_once(": ")
            } else if let Some(rest) = line.strip_prefix("-- ") {
                rest.split_once(": ")
            } else {
                None
            };
            if let Some((key, value)) = directive_opt {
                let key = key.trim();
                if DIRECTIVE_KEYS.contains(&key) {
                    require(open_case.files.is_empty(), "metadata must precede file blocks")?;
                    apply_directive(&mut open_case.meta, key, value.trim())?;
                    return Ok(());
                }
            }

            if line.trim().is_empty() {
                return Ok(());
            }

            if line.starts_with("--") {
                open_case.annotations.push(line.into());
                return Ok(());
            }

            let implicit_name = format!("{}.ril", open_case.name);
            portable_path(&implicit_name)?;
            file = Some(FileBuilder {
                name: implicit_name,
                hex: false,
                final_newline: true,
                lines: vec![line.into()],
            });
            Ok(())
        })();
        result.map_err(|error| Error::Invalid(format!("{bundle}:{}: {error}", index + 1)))?;
    }

    flush_case(&mut file, &mut current, &mut source, &mut cases, bundle)?;
    flush_source(&mut file, &mut current, &mut source, &mut sources)?;

    require(
        file.is_none() && current.is_none() && source.is_none(),
        format!("{bundle}: unclosed file or case"),
    )?;
    require(
        sources.keys().all(|name| used_sources.contains(name)),
        format!("{bundle}: unused shared source"),
    )?;
    require(!cases.is_empty(), format!("{bundle}: empty bundle"))?;
    Ok(cases)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_valid_case_bundle() {
        let text = r#"--@ case: simple
--@ mode: check-pass
--@ spec: SPEC#advisory-warnings
--@ file: root.ril
pub fn test_hello() {}
--@ end-file
--@ end-case
"#;
        let cases = parse_bundle(text, "tests/example.ril").unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].id, "tests/example.ril::simple");
        assert_eq!(cases[0].meta.mode, Mode::CheckPass);
        assert_eq!(cases[0].root, "root.ril");
    }

    #[test]
    fn reject_invalid_cases() {
        let text = r#"--@ case: simple
--@ mode: check-pass
-- missing spec
--@ file: root.ril
pub fn test_hello() {}
--@ end-file
--@ end-case
"#;
        assert!(parse_bundle(text, "tests/example.ril").is_err());
    }

    #[test]
    fn parse_compact_bracket_case() {
        let text = r#"-- [case: simple, check-pass]
-- spec: SPEC#advisory-warnings
pub fn test_hello() {}
"#;
        let cases = parse_bundle(text, "tests/example.ril").unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].id, "tests/example.ril::simple");
        assert_eq!(cases[0].meta.mode, Mode::CheckPass);
        assert_eq!(cases[0].root, "simple.ril");
        assert_eq!(
            std::str::from_utf8(&cases[0].files[0].bytes).unwrap(),
            "pub fn test_hello() {}\n"
        );
    }

    #[test]
    fn parse_compact_with_inferred_entry() {
        let text = r#"-- [case: feature-test, run-pass]
-- spec: SPEC#advisory-warnings
pub fn test_feature_test() {}
"#;
        let cases = parse_bundle(text, "tests/example.ril").unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].meta.entry.as_deref(), Some("test_feature_test"));
    }

    #[test]
    fn parse_compact_multiple_cases_with_diagnostics() {
        let text = r#"-- [case: accept-test, check-pass]
-- spec: SPEC#advisory-warnings
-- companion: reject-test
fn accept() {}

-- [case: reject-test, check-fail]
-- spec: SPEC#advisory-warnings
-- companion: accept-test
-- Error [E0501]: immutable reassignment
fn reject() {}
"#;
        let cases = parse_bundle(text, "tests/example.ril").unwrap();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].name, "accept-test");
        assert_eq!(cases[0].meta.mode, Mode::CheckPass);
        assert_eq!(cases[0].root, "accept-test.ril");
        assert_eq!(cases[1].name, "reject-test");
        assert_eq!(cases[1].meta.mode, Mode::CheckFail);
        assert_eq!(cases[1].errors, vec!["E0501"]);
        assert_eq!(cases[1].root, "reject-test.ril");
    }

    #[test]
    fn parse_compact_inline_metadata() {
        let text = r#"-- [case: inline-test, check-pass, spec: SPEC#advisory-warnings]
fn sample() {}
"#;
        let cases = parse_bundle(text, "tests/example.ril").unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].meta.mode, Mode::CheckPass);
        assert_eq!(cases[0].meta.spec, vec!["SPEC#advisory-warnings"]);
        assert_eq!(cases[0].root, "inline-test.ril");
    }
}
