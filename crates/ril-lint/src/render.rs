//! Human (`ariadne`) and machine (`--message-format=json`) renderers for `LintDiagnostic`.

use std::{collections::HashMap, fmt, io};

use ariadne::{Cache, Config, IndexType, Label, Report, ReportKind, Source};
use ril_source::span::{FileId, SourceMap, Span};

use crate::{LintDiagnostic, config::LintLevel};

impl LintDiagnostic {
    pub fn render_with_color(
        &self,
        sources: &SourceMap,
        color: bool,
        mut out: impl io::Write,
    ) -> io::Result<()> {
        if sources.get(self.primary.file).is_some() {
            let kind = match self.level {
                LintLevel::Deny => ReportKind::Error,
                LintLevel::Warn | LintLevel::Allow => ReportKind::Warning,
            };
            let range = self.primary.start..self.primary.end;
            let mut report = Report::build(kind, (self.primary.file, range.clone()))
                .with_config(
                    Config::new()
                        .with_index_type(IndexType::Byte)
                        .with_color(color),
                )
                .with_code(&self.rule)
                .with_message(&self.message)
                .with_label(Label::new((self.primary.file, range)).with_message(&self.message));
            for secondary in &self.labels {
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
            for note in &self.notes {
                report = report.with_note(note);
            }
            for help in &self.help {
                report = report.with_help(help);
            }
            let cache = LintSourceCache::new(sources);
            return report.finish().write(cache, out);
        }
        writeln!(out, "{}: {}", self.rule, self.message)
    }

    pub fn to_json_line(&self, sources: &SourceMap) -> String {
        let severity = match self.level {
            LintLevel::Deny => "error",
            LintLevel::Warn | LintLevel::Allow => "warning",
        };
        let labels: Vec<serde_json::Value> = self
            .labels
            .iter()
            .map(|l| {
                serde_json::json!({
                    "span": span_json(sources, l.span),
                    "message": l.message,
                })
            })
            .collect();
        let fixes: Vec<serde_json::Value> = self
            .fixes
            .iter()
            .map(|f| {
                let edits: Vec<serde_json::Value> = f
                    .edits
                    .iter()
                    .map(|e| {
                        serde_json::json!({
                            "span": span_json(sources, e.span),
                            "replacement": e.replacement,
                        })
                    })
                    .collect();
                serde_json::json!({
                    "id": f.id,
                    "title": f.title,
                    "safety": f.safety.as_str(),
                    "kind": f.kind.as_str(),
                    "is_preferred": f.is_preferred,
                    "edits": edits,
                })
            })
            .collect();
        let tags: Vec<&'static str> = self.tags.iter().map(|t| t.as_str()).collect();
        serde_json::json!({
            "source": "ril-lint",
            "severity": severity,
            "code": self.rule,
            "category": self.category.as_str(),
            "message": self.message,
            "primary": span_json(sources, self.primary),
            "labels": labels,
            "notes": self.notes,
            "help": self.help,
            "tags": tags,
            "fixes": fixes,
        })
        .to_string()
    }
}

fn span_json(sources: &SourceMap, span: Span) -> serde_json::Value {
    let file = sources
        .path(span.file)
        .map(|p| p.to_string_lossy().into_owned());
    let loc = sources.get(span.file).and_then(|f| f.location(span.start));
    match loc {
        Some(loc) => serde_json::json!({
            "file": file,
            "start": span.start,
            "end": span.end,
            "line": loc.line,
            "column": loc.column,
        }),
        None => serde_json::json!({
            "file": file,
            "start": span.start,
            "end": span.end,
        }),
    }
}

struct LintSourceCache<'a> {
    sources: &'a SourceMap,
    cached: HashMap<FileId, Source<&'a str>>,
}

impl<'a> LintSourceCache<'a> {
    fn new(sources: &'a SourceMap) -> Self {
        Self {
            sources,
            cached: HashMap::new(),
        }
    }
}

impl<'a> Cache<FileId> for LintSourceCache<'a> {
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
