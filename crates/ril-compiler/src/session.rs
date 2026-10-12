//! In-memory compilation sessions; all source changes enter the query layer.
use crate::db::{Database, SourceFacts, SourceInput, source_facts, update_source};
use ril_compiler_core::{
    diagnostic::{Diagnostic, Label, Severity},
    phase::{NotImplemented, Stage},
    source::{FileId, Span},
};
use serde::Serialize;

pub struct Session {
    db: Database,
    source: SourceInput,
}
impl Session {
    pub fn new(bytes: Vec<u8>) -> Self {
        let db = Database::default();
        let source = SourceInput::new(&db, bytes);
        Self { db, source }
    }
    pub fn update(&mut self, bytes: Vec<u8>) {
        update_source(&mut self.db, self.source, bytes);
    }
    pub fn facts(&self) -> SourceFacts {
        source_facts(&self.db, self.source).clone()
    }
    pub fn check(&self) -> CompilationOutcome {
        let facts = self.facts();
        if let Some(offset) = facts.invalid_utf8_at {
            let start = u32::try_from(offset).unwrap_or(u32::MAX);
            return CompilationOutcome::Rejected {
                diagnostics: vec![Diagnostic {
                    code: "E0104".into(),
                    severity: Severity::Error,
                    message: "source is not valid UTF-8".into(),
                    labels: vec![Label {
                        span: Span {
                            file: FileId(0),
                            start,
                            end: start.saturating_add(1),
                        },
                        message: "invalid byte sequence".into(),
                    }],
                    causes: vec![],
                }],
            };
        }
        let text = std::str::from_utf8(self.source.bytes(&self.db)).expect("checked UTF-8");
        match ril_syntax::parse(text) {
            Err(reason) => CompilationOutcome::NotImplemented { reason },
            Ok(_) => CompilationOutcome::NotImplemented {
                reason: NotImplemented::new(Stage::Resolution, "semantic pipeline"),
            },
        }
    }
}

#[derive(Debug, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum CompilationOutcome {
    Rejected { diagnostics: Vec<Diagnostic> },
    NotImplemented { reason: NotImplemented },
}
impl CompilationOutcome {
    pub fn exit_code(&self) -> u8 {
        match self {
            Self::Rejected { .. } => 1,
            Self::NotImplemented { .. } => 2,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn incomplete_compiler_never_accepts_source() {
        assert!(matches!(
            Session::new(b"pub fn main() {}".to_vec()).check(),
            CompilationOutcome::NotImplemented { .. }
        ));
        assert!(matches!(
            Session::new(vec![0xff]).check(),
            CompilationOutcome::Rejected { .. }
        ));
    }
}
