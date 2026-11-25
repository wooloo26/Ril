use std::{collections::HashMap, fmt, io, str::FromStr};

use ariadne::{Cache, Config, IndexType, Label, Report, ReportKind, Source};

use crate::span::{FileId, SourceMap, Span};

macro_rules! diagnostic_codes {
    ($(($code:ident, $name:ident)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Code { $($code),+ }

        impl Code {
            pub const ALL: &'static [Self] = &[$(Self::$code),+];

            pub const fn as_str(self) -> &'static str {
                match self { $(Self::$code => stringify!($code)),+ }
            }

            pub const fn name(self) -> &'static str {
                match self { $(Self::$code => stringify!($name)),+ }
            }
        }

        impl FromStr for Code {
            type Err = UnknownCode;

            fn from_str(text: &str) -> Result<Self, Self::Err> {
                match text {
                    $(stringify!($code) => Ok(Self::$code)),+,
                    _ => Err(UnknownCode(text.into())),
                }
            }
        }
    };
}

include!("codes.rs");

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug)]
pub struct UnknownCode(String);

impl fmt::Display for UnknownCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown diagnostic code {}", self.0)
    }
}

impl std::error::Error for UnknownCode {}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum Severity {
    #[default]
    Error,
    Warning,
}

impl Severity {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SecondaryLabel {
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct DiagnosticExtra {
    labels: Vec<SecondaryLabel>,
    notes: Vec<String>,
    help: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: Option<Code>,
    pub primary: Option<Span>,
    pub message: String,
    extra: Option<Box<DiagnosticExtra>>,
}

impl Diagnostic {
    pub fn error(code: Code, span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            code: Some(code),
            primary: Some(span),
            message: message.into(),
            extra: None,
        }
    }

    pub fn warning(code: Code, span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            code: Some(code),
            primary: Some(span),
            message: message.into(),
            extra: None,
        }
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            code: None,
            primary: None,
            message: message.into(),
            extra: None,
        }
    }

    pub fn unsupported_at(span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            code: None,
            primary: Some(span),
            message: message.into(),
            extra: None,
        }
    }

    pub fn labels(&self) -> &[SecondaryLabel] {
        self.extra.as_deref().map_or(&[], |e| &e.labels)
    }

    pub fn notes(&self) -> &[String] {
        self.extra.as_deref().map_or(&[], |e| &e.notes)
    }

    pub fn help(&self) -> &[String] {
        self.extra.as_deref().map_or(&[], |e| &e.help)
    }

    #[must_use]
    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.extra
            .get_or_insert_with(Box::default)
            .labels
            .push(SecondaryLabel {
                span,
                message: message.into(),
            });
        self
    }

    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.extra
            .get_or_insert_with(Box::default)
            .notes
            .push(note.into());
        self
    }

    #[must_use]
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.extra
            .get_or_insert_with(Box::default)
            .help
            .push(help.into());
        self
    }

    pub fn render(&self, sources: &SourceMap, out: impl io::Write) -> io::Result<()> {
        self.render_with_color(sources, false, out)
    }

    pub fn render_with_color(
        &self,
        sources: &SourceMap,
        color: bool,
        mut out: impl io::Write,
    ) -> io::Result<()> {
        if let Some(span) = self.primary
            && sources.get(span.file).is_some()
        {
            let kind = match self.severity {
                Severity::Error => ReportKind::Error,
                Severity::Warning => ReportKind::Warning,
            };
            let range = span.start..span.end;
            let mut report = Report::build(kind, (span.file, range.clone()))
                .with_config(
                    Config::new()
                        .with_index_type(IndexType::Byte)
                        .with_color(color),
                )
                .with_message(&self.message)
                .with_label(Label::new((span.file, range)).with_message(&self.message));
            if let Some(code) = self.code {
                report = report.with_code(code.as_str());
            }
            for secondary in self.labels() {
                if sources.get(secondary.span.file).is_some() {
                    report = report.with_label(
                        Label::new((
                            secondary.span.file,
                            secondary.span.start..secondary.span.end,
                        ))
                        .with_message(&secondary.message),
                    );
                }
            }
            for note in self.notes() {
                report = report.with_note(note);
            }
            for help in self.help() {
                report = report.with_help(help);
            }
            let cache = SourceMapCache::new(sources);
            return report.finish().write(cache, out);
        }
        writeln!(out, "{self}")
    }

    /// Serialize this diagnostic into a single-line JSON object suitable for `--message-format=json`.
    pub fn to_json_line(&self, sources: &SourceMap) -> String {
        let mut out = String::from("{\"severity\":\"");
        out.push_str(self.severity.as_str());
        out.push('"');
        if let Some(code) = self.code {
            out.push_str(",\"code\":\"");
            out.push_str(code.as_str());
            out.push('"');
        } else {
            out.push_str(",\"code\":null");
        }
        out.push_str(",\"message\":");
        push_json_str(&mut out, &self.message);
        out.push_str(",\"primary\":");
        if let Some(span) = self.primary {
            push_span_json(&mut out, sources, span);
        } else {
            out.push_str("null");
        }
        out.push_str(",\"labels\":[");
        for (idx, label) in self.labels().iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            out.push_str("{\"span\":");
            push_span_json(&mut out, sources, label.span);
            out.push_str(",\"message\":");
            push_json_str(&mut out, &label.message);
            out.push('}');
        }
        out.push_str("],\"notes\":[");
        for (idx, note) in self.notes().iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            push_json_str(&mut out, note);
        }
        out.push_str("],\"help\":[");
        for (idx, item) in self.help().iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            push_json_str(&mut out, item);
        }
        out.push_str("]}");
        out
    }
}

fn push_span_json(out: &mut String, sources: &SourceMap, span: Span) {
    out.push('{');
    out.push_str("\"file\":");
    if let Some(path) = sources.path(span.file) {
        push_json_str(out, &path.to_string_lossy());
    } else {
        out.push_str("null");
    }
    let (line, column) = sources
        .get(span.file)
        .and_then(|file| file.location(span.start))
        .map_or((None, None), |loc| (Some(loc.line), Some(loc.column)));
    out.push_str(&format!(",\"start\":{},\"end\":{}", span.start, span.end));
    if let (Some(line), Some(column)) = (line, column) {
        out.push_str(&format!(",\"line\":{line},\"column\":{column}"));
    }
    out.push('}');
}

fn push_json_str(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

struct SourceMapCache<'a> {
    sources: &'a SourceMap,
    cached: HashMap<FileId, Source<&'a str>>,
}

impl<'a> SourceMapCache<'a> {
    fn new(sources: &'a SourceMap) -> Self {
        Self {
            sources,
            cached: HashMap::new(),
        }
    }
}

impl<'a> Cache<FileId> for SourceMapCache<'a> {
    type Storage = &'a str;

    fn fetch(&mut self, id: &FileId) -> Result<&Source<Self::Storage>, impl fmt::Debug> {
        if !self.cached.contains_key(id) {
            let Some(file) = self.sources.get(*id) else {
                return Err(format!("unknown file {id:?}"));
            };
            self.cached.insert(*id, Source::from(file.text()));
        }
        self.cached
            .get(id)
            .ok_or_else(|| format!("unknown file {id:?}"))
    }

    fn display<'b>(&self, id: &'b FileId) -> Option<impl fmt::Display + 'b> {
        let name = self
            .sources
            .path(*id)
            .map_or_else(|| format!("<file:{}>", id.0), |p| p.display().to_string());
        Some(name)
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(code) = self.code {
            write!(f, "{code}: ")?;
        }
        f.write_str(&self.message)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn renders_cross_file_secondary_labels_and_json() {
        let mut map = SourceMap::default();
        let f1 = map
            .add(PathBuf::from("pkg/a.ril"), b"let x = 1\n")
            .unwrap_or(FileId(0));
        let f2 = map
            .add(PathBuf::from("pkg/b.ril"), b"let y = x\n")
            .unwrap_or(FileId(1));
        let diag = Diagnostic::error(Code::E0520, Span::new(f2, 8, 9), "conflicting write")
            .with_label(Span::new(f1, 4, 5), "original binding declared here")
            .with_note("mutable access requires exclusive authority")
            .with_help("pass mut explicitly");
        let mut rendered = Vec::new();
        assert!(diag.render(&map, &mut rendered).is_ok());
        let text = String::from_utf8_lossy(&rendered);
        assert!(text.contains("pkg/a.ril"));
        assert!(text.contains("pkg/b.ril"));
        assert!(text.contains("original binding declared here"));
        let json = diag.to_json_line(&map);
        assert!(json.contains("\"code\":\"E0520\""));
        assert!(json.contains("\"file\":\"pkg/b.ril\""));
        assert!(json.contains("\"file\":\"pkg/a.ril\""));
        assert!(json.contains("\"notes\":[\"mutable access requires exclusive authority\"]"));
    }
}
