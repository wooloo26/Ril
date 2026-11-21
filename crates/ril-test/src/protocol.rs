use std::{
    fmt,
    path::{Component, Path, PathBuf},
};

use ril_base::diag::Code;

use crate::{Milestone, Stage, Unit, VirtualFile, VirtualPackage, shield::Shield};

#[derive(Clone, Debug)]
pub enum CaseMode {
    CompilePass,
    CompileFail(Code),
    CompatPass,
    CompatFail(Code),
    RunPass,
    RunPanic(Option<String>),
    RunAbort,
}

impl CaseMode {
    const fn milestone(&self) -> Milestone {
        match self {
            Self::CompilePass | Self::CompileFail(_) => Milestone::M0,
            Self::CompatPass | Self::CompatFail(_) => Milestone::M3,
            Self::RunPass | Self::RunPanic(_) | Self::RunAbort => Milestone::M4,
        }
    }

    const fn is_compat(&self) -> bool {
        matches!(self, Self::CompatPass | Self::CompatFail(_))
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) enum Backend {
    #[default]
    Both,
    Jit,
    Aot,
}

#[derive(Clone, Debug)]
pub struct Case {
    pub id: String,
    pub line: usize,
    pub mode: CaseMode,
    pub stage: Stage,
    pub pkg: VirtualPackage,
    pub baseline: Option<VirtualPackage>,
    pub(super) primary: Option<Code>,
    pub(super) forbidden: Vec<Code>,
    pub(super) markers: Vec<(usize, Code)>,
    pub(super) signatures: Vec<(String, String)>,
    pub(super) backend: Backend,
    pub(super) stdout: Option<Vec<u8>>,
    pub(super) exit: Option<i32>,
    required: Milestone,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Activation {
    Ready,
    KnownPending(Milestone),
}

impl Case {
    pub fn activation(&self, enabled: Milestone) -> Activation {
        if self.required <= enabled {
            Activation::Ready
        } else {
            Activation::KnownPending(self.required)
        }
    }
}

#[derive(Clone, Debug)]
pub struct Suite {
    pub name: String,
    pub path: PathBuf,
    pub cases: Vec<Case>,
}

#[derive(Debug)]
pub struct SuiteError {
    path: PathBuf,
    line: usize,
    message: String,
}

impl fmt::Display for SuiteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.path.display(), self.line, self.message)
    }
}

impl std::error::Error for SuiteError {}

#[derive(Default)]
struct FileSet {
    package: Option<VirtualPackage>,
    active: PathBuf,
    explicit: bool,
    started: bool,
}

impl FileSet {
    fn new(unit: Unit, budget: Option<u64>) -> Self {
        let mut package = VirtualPackage::new(unit);
        package.budget = budget;
        Self {
            active: package.entry.clone(),
            package: Some(package),
            ..Self::default()
        }
    }

    fn file(&mut self, path: PathBuf) -> Result<(), String> {
        let files = &mut self.package.as_mut().ok_or("internal suite state")?.files;
        if files.contains_key(&path) {
            return Err(format!("duplicate virtual file {}", path.display()));
        }
        files.insert(path.clone(), VirtualFile::default());
        self.active = path;
        self.explicit = true;
        self.started = false;
        Ok(())
    }

    fn source(&mut self, line: &str, number: usize) {
        if !self.started && !self.explicit && line.trim().is_empty() {
            return;
        }
        if let Some(package) = &mut self.package {
            package
                .files
                .entry(self.active.clone())
                .or_default()
                .push(line, number);
            self.started = true;
        }
    }

    fn bytes(&mut self, hex: &str, line: usize) -> Result<(), String> {
        if self.started {
            return Err("@bytes-hex must supply the entire active file".into());
        }
        let output = hex
            .split_ascii_whitespace()
            .map(|byte| {
                if byte.len() != 2 {
                    return Err(format!("invalid hexadecimal byte {byte:?}"));
                }
                u8::from_str_radix(byte, 16)
                    .map_err(|_| format!("invalid hexadecimal byte {byte:?}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if output.is_empty() {
            return Err("@bytes-hex requires at least one byte".into());
        }
        let package = self.package.as_mut().ok_or("internal suite state")?;
        let file = package.files.entry(self.active.clone()).or_default();
        file.suite_lines = vec![line; output.iter().filter(|&&b| b == b'\n').count() + 1];
        file.bytes = output;
        self.started = true;
        Ok(())
    }

    fn finish(self, prelude: Option<&VirtualFile>) -> Result<VirtualPackage, String> {
        let mut pkg = self.package.ok_or("missing test source")?;
        if !pkg.files.contains_key(&pkg.entry) {
            if pkg.files.len() == 1
                && let Some(path) = pkg.files.keys().next()
            {
                pkg.entry = path.clone();
            } else if !pkg.files.is_empty() {
                return Err(format!("multi-file case needs {}", pkg.entry.display()));
            }
        }
        let file = pkg.files.entry(pkg.entry.clone()).or_default();
        if let Some(prelude) = prelude {
            let mut combined = prelude.clone();
            combined.append(std::mem::take(file));
            *file = combined;
        }
        Ok(pkg)
    }
}

struct CaseBuilder {
    case: Case,
    current: FileSet,
    no_prelude: bool,
    raw: bool,
    whole_bytes: bool,
    previous_line: Option<usize>,
    compat: CompatSection,
}

#[derive(PartialEq)]
enum CompatSection {
    None,
    AwaitBaseline,
    Baseline,
    Revision,
}

impl CaseBuilder {
    fn new(text: &str, line: usize, default_stage: Stage) -> Result<Self, String> {
        let mut fields = text.split_whitespace().peekable();
        let id = fields.next().ok_or("missing case id")?;
        valid_name(id)?;
        let mode = match fields.next().ok_or("missing case mode")? {
            "compile-pass" => CaseMode::CompilePass,
            "compile-fail" => {
                CaseMode::CompileFail(parse_code(fields.next().ok_or("missing expected code")?)?)
            }
            "compat-pass" => CaseMode::CompatPass,
            "compat-fail" => {
                CaseMode::CompatFail(parse_code(fields.next().ok_or("missing expected code")?)?)
            }
            "run-pass" => CaseMode::RunPass,
            "run-panic" => {
                let mut message = Vec::new();
                while fields
                    .peek()
                    .is_some_and(|s| !s.contains('=') && !matches!(*s, "no-prelude" | "raw-slice"))
                {
                    message.extend(fields.next());
                }
                CaseMode::RunPanic(
                    (!message.is_empty()).then(|| unquote(&message.join(" ")).to_owned()),
                )
            }
            "run-abort" => CaseMode::RunAbort,
            mode => return Err(format!("unknown case mode {mode:?}")),
        };
        let mut stage = if mode.milestone() == Milestone::M4 {
            Stage::Run
        } else {
            default_stage
        };
        let mut unit = if stage == Stage::Run {
            Unit::Bin
        } else {
            Unit::Snippet
        };
        let mut no_prelude = false;
        let mut raw = false;
        let mut budget = None;
        let mut backend = Backend::default();
        let mut required = mode.milestone();
        let mut seen = std::collections::HashSet::new();
        for field in fields {
            let (key, value) = field.split_once('=').unwrap_or((field, ""));
            if !seen.insert(key) {
                return Err(format!("duplicate case option {key:?}"));
            }
            match (key, value) {
                ("no-prelude", "") => no_prelude = true,
                ("raw-slice", "") => {
                    raw = true;
                    required = required.max(Milestone::M1);
                }
                ("stage", value) => stage = value.parse()?,
                ("unit", value) => unit = value.parse()?,
                ("budget", value) => {
                    budget = Some(value.parse().map_err(|_| "invalid step budget")?);
                    required = required.max(Milestone::M2);
                }
                ("backend", value) => {
                    backend = match value {
                        "both" => Backend::Both,
                        "jit" => Backend::Jit,
                        "aot" => Backend::Aot,
                        _ => return Err(format!("unknown backend {value:?}")),
                    };
                    required = required.max(Milestone::M4);
                }
                _ => return Err(format!("unknown case option {field:?}")),
            }
        }
        let compat = if mode.is_compat() {
            CompatSection::AwaitBaseline
        } else {
            CompatSection::None
        };
        Ok(Self {
            case: Case {
                id: id.into(),
                line,
                mode,
                stage,
                pkg: VirtualPackage::new(unit),
                baseline: None,
                forbidden: Vec::new(),
                markers: Vec::new(),
                signatures: Vec::new(),
                primary: None,
                backend,
                stdout: None,
                exit: None,
                required: required.max(stage.milestone()),
            },
            current: FileSet::new(unit, budget),
            no_prelude,
            raw,
            whole_bytes: false,
            previous_line: None,
            compat,
        })
    }

    fn directive(
        &mut self,
        key: &str,
        value: &str,
        line: usize,
        prelude: Option<&VirtualFile>,
    ) -> Result<(), String> {
        match key {
            "file" => {
                self.require_source()?;
                self.current.file(virtual_path(value)?)?;
                self.previous_line = None;
                self.whole_bytes = false;
            }
            "forbid" => {
                let codes = value
                    .split(|c: char| c.is_ascii_whitespace() || c == ',')
                    .filter(|code| !code.is_empty())
                    .map(parse_code)
                    .collect::<Result<Vec<_>, _>>()?;
                if codes.is_empty() {
                    return Err("@forbid requires at least one code".into());
                }
                self.case.forbidden.extend(codes);
            }
            "bytes-hex" => {
                self.require_source()?;
                self.case.required = self.case.required.max(Milestone::M1);
                self.current.bytes(value, line)?;
                self.previous_line = Some(line);
                self.whole_bytes = true;
            }
            "expect-primary" => {
                self.case.required = self.case.required.max(Milestone::M1);
                set_once(&mut self.case.primary, parse_code(value)?, key)?;
            }
            "expect-sig" => {
                self.case.required = self.case.required.max(Milestone::M3);
                let (name, sig) = split_word(value);
                let quoted = sig
                    .strip_prefix('"')
                    .and_then(|s| s.strip_suffix('"'))
                    .ok_or("expected a quoted signature")?;
                if name.is_empty() || quoted.is_empty() {
                    return Err("@expect-sig requires a function and its signature".into());
                }
                self.case.signatures.push((name.into(), quoted.into()));
            }
            "expect-stdout" => {
                self.case.required = self.case.required.max(Milestone::M4);
                let output = self.case.stdout.get_or_insert_with(Vec::new);
                output.extend_from_slice(unquote(value).as_bytes());
                output.push(b'\n');
            }
            "expect-exit" => {
                self.case.required = self.case.required.max(Milestone::M4);
                set_once(
                    &mut self.case.exit,
                    value.parse().map_err(|_| "invalid exit status")?,
                    key,
                )?;
            }
            "baseline" if value.is_empty() && self.compat == CompatSection::AwaitBaseline => {
                self.compat = CompatSection::Baseline;
            }
            "revision" if value.is_empty() && self.compat == CompatSection::Baseline => {
                let budget = self.current.package.as_ref().and_then(|pkg| pkg.budget);
                let base =
                    std::mem::replace(&mut self.current, FileSet::new(self.case.pkg.unit, budget));
                self.case.baseline = Some(base.finish(prelude.filter(|_| !self.no_prelude))?);
                self.compat = CompatSection::Revision;
                self.previous_line = None;
                self.whole_bytes = false;
            }
            "baseline" | "revision" => {
                return Err("compat cases require @baseline followed by @revision".into());
            }
            _ => return Err(format!("unknown case directive @{key}")),
        }
        Ok(())
    }

    fn source(&mut self, text: &str, line: usize) -> Result<(), String> {
        if !text.trim().is_empty() {
            self.require_source()?;
            if self.whole_bytes {
                return Err("@bytes-hex cannot be mixed with textual source".into());
            }
            self.previous_line = Some(line);
        }
        if !self.whole_bytes {
            self.current.source(text, line);
        }
        Ok(())
    }

    fn require_source(&self) -> Result<(), String> {
        if self.compat == CompatSection::AwaitBaseline {
            return Err("expected @baseline before source".into());
        }
        Ok(())
    }

    fn finish(mut self, prelude: Option<&VirtualFile>) -> Result<Case, String> {
        if self.case.mode.is_compat() && self.compat != CompatSection::Revision {
            return Err("compat case missing baseline or revision".into());
        }
        self.case.pkg = self.current.finish(prelude.filter(|_| !self.no_prelude))?;
        Ok(self.case)
    }
}

fn set_once<T>(slot: &mut Option<T>, value: T, key: &str) -> Result<(), String> {
    if slot.is_some() {
        return Err(format!("duplicate @{key} directive"));
    }
    *slot = Some(value);
    Ok(())
}

fn split_word(text: &str) -> (&str, &str) {
    text.split_once(char::is_whitespace)
        .map_or((text, ""), |(word, rest)| (word, rest.trim()))
}

fn unquote(text: &str) -> &str {
    text.strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or(text)
}

fn valid_name(name: &str) -> Result<(), String> {
    if name.is_empty()
        || !name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-'))
    {
        return Err(format!("invalid suite or case name {name:?}"));
    }
    Ok(())
}

fn parse_code(text: &str) -> Result<Code, String> {
    text.parse::<Code>().map_err(|err| err.to_string())
}

fn virtual_path(text: &str) -> Result<PathBuf, String> {
    let path = Path::new(text);
    if path.extension().is_some_and(|ext| ext == "ril")
        && path.components().all(|c| matches!(c, Component::Normal(_)))
        && !text
            .split('/')
            .any(|c| c.is_empty() || c == "." || c == ".." || c.contains(['\\', ':']))
        && !text.chars().any(char::is_whitespace)
    {
        Ok(path.into())
    } else {
        Err(format!("invalid virtual path {text:?}"))
    }
}

pub fn parse_suite(path: &Path, source: &str) -> Result<Suite, SuiteError> {
    let mut name = None;
    let mut default_stage = None;
    let mut prelude: Option<VirtualFile> = None;
    let mut case: Option<CaseBuilder> = None;
    let mut cases = Vec::new();
    let mut shield = Shield::default();
    let mut ids = std::collections::HashSet::new();
    let error = |line, message| SuiteError {
        path: path.into(),
        line,
        message,
    };

    for (index, text) in source.split_inclusive('\n').enumerate() {
        let line = index + 1;
        let visible = shield.exposed();
        let heading = text.trim_end_matches(['\r', '\n']);
        let mark = text.trim().strip_prefix("-- ^ ");
        let result = if let Some((key, arg)) = visible
            .then(|| heading.strip_prefix("-- @"))
            .flatten()
            .map(split_word)
        {
            match key {
                "suite" if cases.is_empty() && case.is_none() && prelude.is_none() => {
                    valid_name(arg).and_then(|()| set_once(&mut name, arg.to_owned(), key))
                }
                "default_stage" if case.is_none() => arg
                    .parse()
                    .and_then(|stage| set_once(&mut default_stage, stage, key)),
                "prelude" if case.is_none() && arg.is_empty() => {
                    set_once(&mut prelude, VirtualFile::default(), key)
                }
                "case" => {
                    if let Some(previous) = case.take() {
                        let previous_line = previous.case.line;
                        cases.push(
                            previous
                                .finish(prelude.as_ref())
                                .map_err(|msg| error(previous_line, msg))?,
                        );
                    }
                    CaseBuilder::new(arg, line, default_stage.unwrap_or(Stage::Access)).and_then(
                        |new| {
                            if !ids.insert(new.case.id.clone()) {
                                return Err(format!("duplicate case id {:?}", new.case.id));
                            }
                            case = Some(new);
                            Ok(())
                        },
                    )
                }
                _ => case
                    .as_mut()
                    .ok_or_else(|| format!("unexpected @{key} outside a case"))
                    .and_then(|current| current.directive(key, arg, line, prelude.as_ref())),
            }
        } else if let Some(current) = &mut case {
            if let (true, Some(mark)) = (visible, mark) {
                parse_code(mark).and_then(|code| {
                    let previous = current
                        .previous_line
                        .ok_or("diagnostic marker has no preceding source")?;
                    current.case.markers.push((previous, code));
                    Ok(())
                })
            } else {
                if !current.raw {
                    shield.scan(text);
                }
                current.source(text, line)
            }
        } else if let Some(prelude) = &mut prelude {
            shield.scan(text);
            prelude.push(text, line);
            Ok(())
        } else if text.trim().is_empty() || text.trim_start().starts_with("--") {
            Ok(())
        } else {
            Err("source outside @prelude or @case".into())
        };
        result.map_err(|message| error(line, message))?;
    }
    if let Some(last) = case {
        let line = last.case.line;
        cases.push(
            last.finish(prelude.as_ref())
                .map_err(|msg| error(line, msg))?,
        );
    }
    if cases.is_empty() {
        return Err(error(1, "suite has no cases".into()));
    }
    Ok(Suite {
        name: name.ok_or_else(|| error(1, "missing @suite".into()))?,
        path: path.into(),
        cases,
    })
}
