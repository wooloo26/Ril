//! In-memory compilation sessions; all source changes enter the query layer.
use crate::db::{Database, SourceFacts, SourceInput, parsed_source, source_facts, update_source};
use ril_compiler_core::{
    diagnostic::{Cause, Diagnostic, Label, Severity},
    phase::{NotImplemented, Stage},
    source::{FileId, Span},
    target::TargetLayout,
};
use serde::Serialize;
pub(crate) mod entry;
mod project;
pub use project::{ProjectError, ProjectSource};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum UnitKind {
    #[default]
    Library,
    Executable,
}

#[derive(Debug, Clone)]
pub struct CheckOptions {
    pub target: String,
    pub unit: UnitKind,
    pub explain: bool,
    /// Language events per independent static evaluation root.
    pub static_budget: std::num::NonZeroU64,
}
impl Default for CheckOptions {
    fn default() -> Self {
        Self {
            target: "pointer64".into(),
            unit: UnitKind::Library,
            explain: false,
            static_budget: crate::static_eval::DEFAULT_STATIC_BUDGET,
        }
    }
}

pub struct Session {
    db: Database,
    source: SourceInput,
    options: CheckOptions,
    project: Option<project::ProjectInputs>,
}
impl Session {
    pub fn new(bytes: Vec<u8>) -> Self {
        let db = Database::default();
        let source = SourceInput::new(&db, bytes);
        Self {
            db,
            source,
            options: CheckOptions::default(),
            project: None,
        }
    }
    pub fn with_options(bytes: Vec<u8>, options: CheckOptions) -> Self {
        let mut session = Self::new(bytes);
        session.options = options;
        session
    }
    pub fn layout(&self) -> Option<TargetLayout> {
        TargetLayout::from_name(&self.options.target)
    }
    pub fn update(&mut self, bytes: Vec<u8>) {
        update_source(&mut self.db, self.source, bytes);
    }
    pub fn facts(&self) -> SourceFacts {
        source_facts(&self.db, self.source).clone()
    }
    pub fn check(&self) -> CompilationOutcome {
        match self.verify() {
            Ok(program) => CompilationOutcome::Accepted {
                diagnostics: program.diagnostics().to_vec(),
                causes: if self.options.explain {
                    program.facts().explanations.causes.clone()
                } else {
                    vec![]
                },
            },
            Err(outcome) => outcome,
        }
    }
    pub fn verify(&self) -> Result<crate::hir::VerifiedProgram, CompilationOutcome> {
        if self.layout().is_none() {
            return Err(CompilationOutcome::UnsupportedEnvironment {
                detail: format!("unknown abstract target {}", self.options.target),
            });
        }
        if let Some(project) = &self.project {
            return self.verify_sources(project);
        }
        let facts = self.facts();
        if let Some(offset) = facts.invalid_utf8_at {
            let start = u32::try_from(offset).unwrap_or(u32::MAX);
            return Err(CompilationOutcome::Rejected {
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
            });
        }
        let parsed = parsed_source(&self.db, self.source, 0);
        if parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == Severity::Error)
        {
            return Err(CompilationOutcome::Rejected {
                diagnostics: parsed.diagnostics.clone(),
            });
        }
        if parsed.incomplete {
            return Err(CompilationOutcome::NotImplemented {
                reason: NotImplemented::new(Stage::Syntax, "unsupported syntax"),
            });
        }
        self.verify_program(&parsed.program)
    }
    /// An owned source AST crosses resolution and static evaluation before the
    /// private semantic boundary, just like byte and multi-file Sessions.
    pub fn verify_program(
        &self,
        program: &ril_syntax::ast::Program,
    ) -> Result<crate::hir::VerifiedProgram, CompilationOutcome> {
        let diagnostics = ril_syntax::validate_program(program);
        if !diagnostics.is_empty() {
            return Err(CompilationOutcome::Rejected { diagnostics });
        }
        if self.layout().is_none() {
            return Err(CompilationOutcome::UnsupportedEnvironment {
                detail: format!("unknown abstract target {}", self.options.target),
            });
        }
        self.verify_resolved(crate::modules::resolve(
            vec![crate::modules::ModuleUnit {
                path: std::path::PathBuf::from("/ril-memory-source.ril"),
                file: FileId(0),
                program: program.clone(),
                is_declaration: false,
            }],
            FileId(0),
        ))
    }
    fn verify_project_at(
        &self,
        program: &ril_syntax::ast::Program,
        root: FileId,
        declarations: &[FileId],
    ) -> Result<crate::hir::VerifiedProgram, CompilationOutcome> {
        let Some(layout) = self.layout() else {
            return Err(CompilationOutcome::UnsupportedEnvironment {
                detail: format!("unknown abstract target {}", self.options.target),
            });
        };
        if self.options.unit == UnitKind::Executable
            && let Some(diagnostic) = entry_diagnostic(program)
        {
            return Err(CompilationOutcome::Rejected {
                diagnostics: vec![diagnostic],
            });
        }
        let resolved_source = program.clone();
        let evaluated =
            crate::static_eval::evaluate_with_budget(program, layout, self.options.static_budget);
        if !evaluated.diagnostics.is_empty() {
            return Err(CompilationOutcome::Rejected {
                diagnostics: evaluated.diagnostics,
            });
        }
        if !evaluated.unsupported.is_empty() {
            return Err(CompilationOutcome::NotImplemented {
                reason: NotImplemented::new(
                    Stage::StaticEvaluation,
                    evaluated
                        .unsupported
                        .iter()
                        .map(|feature| feature.description.clone())
                        .collect::<Vec<_>>()
                        .join("; "),
                ),
            });
        }
        let analyzed = crate::sema::analyze_project_for(
            &evaluated.program,
            root,
            declarations,
            layout,
            &evaluated.constants,
        );
        if analyzed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == Severity::Error)
        {
            return Err(CompilationOutcome::Rejected {
                diagnostics: analyzed.diagnostics,
            });
        }
        if let Some(mut program) = analyzed.program {
            if self.options.unit == UnitKind::Executable {
                entry::verify_environment(&program, "main", true)?;
            }
            program.attach_resolved_source(resolved_source);
            program.attach_static_metadata(
                evaluated.static_definitions,
                evaluated.type_functions,
                evaluated.static_termination,
            );
            return Ok(program);
        }
        let details = analyzed
            .unsupported
            .iter()
            .take(8)
            .map(|feature| {
                format!(
                    "{} at {}:{}",
                    feature.description, feature.span.file.0, feature.span.start
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        Err(CompilationOutcome::NotImplemented {
            reason: NotImplemented::new(
                Stage::Provenance,
                if details.is_empty() {
                    "semantic verification is incomplete".into()
                } else {
                    details
                },
            ),
        })
    }
}

fn entry_diagnostic(program: &ril_syntax::ast::Program) -> Option<Diagnostic> {
    use ril_syntax::ast::{StmtKind, Visibility};
    let functions = program
        .statements
        .iter()
        .filter_map(|statement| {
            if let StmtKind::Function(function) = &statement.kind {
                Some(function)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let (code, span, message) = if let Some(main) =
        functions.iter().find(|function| function.name == "main")
    {
        // Transparent root aliases are expanded here; detailed type validity is
        // still checked by semantic analysis.
        if main.visibility == Visibility::Public
            && main.parameters.is_empty()
            && main.generics.is_empty()
            && !main.is_meta
        {
            return None;
        }
        (
            "E0904",
            main.span,
            "main must be public, ordinary, take no parameters, and return () or Result<(), str>",
        )
    } else {
        (
            "E0903",
            Span {
                file: FileId(0),
                start: 0,
                end: 0,
            },
            "executable root has no main function",
        )
    };
    Some(Diagnostic {
        code: code.into(),
        severity: Severity::Error,
        message: message.into(),
        labels: vec![Label {
            span,
            message: message.into(),
        }],
        causes: vec![],
    })
}

#[derive(Debug, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum CompilationOutcome {
    Accepted {
        diagnostics: Vec<Diagnostic>,
        #[serde(skip_serializing_if = "Vec::is_empty")]
        causes: Vec<Cause>,
    },
    Built {
        artifact: BuiltArtifact,
        diagnostics: Vec<Diagnostic>,
    },
    Rejected {
        diagnostics: Vec<Diagnostic>,
    },
    NotImplemented {
        reason: NotImplemented,
    },
    UnsupportedEnvironment {
        detail: String,
    },
}
#[derive(Debug, Serialize)]
pub struct BuiltArtifact {
    pub path: std::path::PathBuf,
    pub target: String,
    pub runtime_contract_version: u32,
}
impl CompilationOutcome {
    pub fn exit_code(&self) -> u8 {
        match self {
            Self::Accepted { .. } | Self::Built { .. } => 0,
            Self::Rejected { .. } => 1,
            Self::NotImplemented { .. } | Self::UnsupportedEnvironment { .. } => 2,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn accepted_source_is_verified_and_invalid_bytes_are_rejected() {
        assert!(matches!(
            Session::new(b"pub fn main() {}".to_vec()).check(),
            CompilationOutcome::Accepted { .. }
        ));
        assert!(matches!(
            Session::new(vec![0xff]).check(),
            CompilationOutcome::Rejected { .. }
        ));
    }

    #[test]
    fn editing_a_source_invalidates_parse_and_semantic_results() {
        let mut session = Session::new(b"pub fn main() {}".to_vec());
        assert!(matches!(
            session.check(),
            CompilationOutcome::Accepted { .. }
        ));
        session.update(b"pub fn main() { missing }".to_vec());
        let incremental = session.check();
        let fresh = Session::new(b"pub fn main() { missing }".to_vec()).check();
        let codes = |outcome: CompilationOutcome| match outcome {
            CompilationOutcome::Rejected { diagnostics } => diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            _ => panic!("unresolved source must not be accepted"),
        };
        assert_eq!(codes(incremental), codes(fresh));
        session.update(b"pub fn main() {}".to_vec());
        assert!(matches!(
            session.check(),
            CompilationOutcome::Accepted { .. }
        ));
    }
}
