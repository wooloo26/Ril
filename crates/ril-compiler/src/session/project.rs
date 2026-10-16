//! In-memory project inputs with per-file incremental parse dependencies.
use super::*;
use crate::modules::{ModuleUnit, ResolvedProject};
use std::{
    collections::BTreeMap,
    path::{Component, Path, PathBuf},
};

#[derive(Debug, Clone)]
pub struct ProjectSource {
    pub path: PathBuf,
    pub bytes: Vec<u8>,
}
#[derive(Debug, thiserror::Error)]
pub enum ProjectError {
    #[error("project root source is missing: {0}")]
    MissingRoot(PathBuf),
    #[error("duplicate project source: {0}")]
    DuplicateSource(PathBuf),
    #[error("source is not in the project: {0}")]
    MissingSource(PathBuf),
    #[error("project contains too many source files")]
    TooManySources,
    #[error(transparent)]
    Io(#[from] std::io::Error),
}
pub(super) struct ProjectInputs {
    root: PathBuf,
    sources: BTreeMap<PathBuf, (FileId, SourceInput)>,
    next_file: u32,
}
fn normalize(path: &Path) -> std::io::Result<PathBuf> {
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    let mut output = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                output.pop();
            }
            _ => output.push(component.as_os_str()),
        }
    }
    Ok(output)
}
impl Session {
    /// All supplied units form one compilation project; no filesystem contents
    /// are consulted. Paths are resolved relative to the process directory.
    pub fn with_project(
        root: PathBuf,
        sources: Vec<ProjectSource>,
        options: CheckOptions,
    ) -> Result<Self, ProjectError> {
        let root = normalize(&root)?;
        let mut bytes = BTreeMap::new();
        for source in sources {
            let path = normalize(&source.path)?;
            if bytes.insert(path.clone(), source.bytes).is_some() {
                return Err(ProjectError::DuplicateSource(path));
            }
        }
        let root_bytes = bytes
            .remove(&root)
            .ok_or_else(|| ProjectError::MissingRoot(root.clone()))?;
        let mut session = Self::with_options(root_bytes, options);
        let mut inputs = BTreeMap::from([(root.clone(), (FileId(0), session.source))]);
        let mut next_file = 1u32;
        for (path, bytes) in bytes {
            let file = FileId(next_file);
            next_file = next_file
                .checked_add(1)
                .ok_or(ProjectError::TooManySources)?;
            inputs.insert(path, (file, SourceInput::new(&session.db, bytes)));
        }
        session.project = Some(ProjectInputs {
            root,
            sources: inputs,
            next_file,
        });
        Ok(session)
    }
    pub fn project_sources(&self) -> impl Iterator<Item = (&Path, FileId)> {
        self.project.iter().flat_map(|project| {
            project
                .sources
                .iter()
                .map(|(path, (file, _))| (path.as_path(), *file))
        })
    }
    pub fn update_file(&mut self, path: &Path, bytes: Vec<u8>) -> Result<(), ProjectError> {
        let path = normalize(path)?;
        let source = self
            .project
            .as_ref()
            .and_then(|project| project.sources.get(&path))
            .map(|(_, source)| *source)
            .ok_or(ProjectError::MissingSource(path))?;
        update_source(&mut self.db, source, bytes);
        Ok(())
    }
    pub fn add_file(&mut self, source: ProjectSource) -> Result<FileId, ProjectError> {
        let path = normalize(&source.path)?;
        let project = self
            .project
            .as_mut()
            .ok_or_else(|| ProjectError::MissingSource(path.clone()))?;
        if project.sources.contains_key(&path) {
            return Err(ProjectError::DuplicateSource(path));
        }
        let file = FileId(project.next_file);
        project.next_file = project
            .next_file
            .checked_add(1)
            .ok_or(ProjectError::TooManySources)?;
        project
            .sources
            .insert(path, (file, SourceInput::new(&self.db, source.bytes)));
        Ok(file)
    }
    pub fn remove_file(&mut self, path: &Path) -> Result<(), ProjectError> {
        let path = normalize(path)?;
        let project = self
            .project
            .as_mut()
            .ok_or_else(|| ProjectError::MissingSource(path.clone()))?;
        if path == project.root {
            return Err(ProjectError::MissingRoot(path));
        }
        project
            .sources
            .remove(&path)
            .ok_or(ProjectError::MissingSource(path))?;
        Ok(())
    }
    pub(super) fn analyze_sources(&self, project: &ProjectInputs) -> AnalysisSnapshot {
        let mut units = Vec::new();
        let mut diagnostics = Vec::new();
        let mut incomplete = false;
        for (path, (file, source)) in &project.sources {
            if let Some(offset) = source_facts(&self.db, *source).invalid_utf8_at {
                let start = offset.min(u32::MAX as usize) as u32;
                diagnostics.push(Diagnostic {
                    code: "E0104".into(),
                    severity: Severity::Error,
                    message: "source is not valid UTF-8".into(),
                    labels: vec![Label {
                        span: Span {
                            file: *file,
                            start,
                            end: start.saturating_add(1),
                        },
                        message: "invalid byte sequence".into(),
                    }],
                    causes: vec![],
                });
                continue;
            }
            let parsed = parsed_source(&self.db, *source, file.0);
            diagnostics.extend(parsed.diagnostics.iter().cloned());
            incomplete |= parsed.incomplete;
            units.push(ModuleUnit {
                path: path.clone(),
                file: *file,
                program: parsed.program.clone(),
                is_declaration: path.to_string_lossy().ends_with(".d.ril"),
            });
        }
        if diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == Severity::Error)
        {
            let source = ril_syntax::ast::Program {
                statements: units
                    .iter()
                    .flat_map(|unit| unit.program.statements.iter().cloned())
                    .collect(),
            };
            return AnalysisSnapshot::failed(
                CompilationOutcome::Rejected { diagnostics },
                Some(source),
            );
        }
        if incomplete {
            let source = ril_syntax::ast::Program {
                statements: units
                    .iter()
                    .flat_map(|unit| unit.program.statements.iter().cloned())
                    .collect(),
            };
            return AnalysisSnapshot::failed(
                CompilationOutcome::NotImplemented {
                    reason: NotImplemented::new(Stage::Syntax, "unsupported project syntax"),
                },
                Some(source),
            );
        }
        self.analyze_resolved(crate::modules::resolve(units, FileId(0)))
    }
    pub(crate) fn verify_resolved(
        &self,
        project: ResolvedProject,
    ) -> Result<crate::hir::VerifiedProgram, CompilationOutcome> {
        self.analyze_resolved(project).into_verified()
    }
    pub(crate) fn analyze_resolved(&self, project: ResolvedProject) -> AnalysisSnapshot {
        if project
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == Severity::Error)
        {
            return AnalysisSnapshot::failed(
                CompilationOutcome::Rejected {
                    diagnostics: project.diagnostics,
                },
                Some(project.program),
            );
        }
        if project.syntax_incomplete {
            return AnalysisSnapshot::failed(
                CompilationOutcome::NotImplemented {
                    reason: NotImplemented::new(
                        Stage::Syntax,
                        "unsupported module syntax or syntax analysis budget reached",
                    ),
                },
                Some(project.program),
            );
        }
        if !project.unsupported.is_empty() {
            return AnalysisSnapshot::failed(
                CompilationOutcome::NotImplemented {
                    reason: NotImplemented::new(
                        Stage::Resolution,
                        project
                            .unsupported
                            .iter()
                            .map(|item| item.description.clone())
                            .collect::<Vec<_>>()
                            .join("; "),
                    ),
                },
                Some(project.program),
            )
            .with_unresolved(project.unsupported);
        }
        let declarations = project
            .units
            .iter()
            .filter(|unit| unit.is_declaration)
            .map(|unit| unit.file)
            .collect::<Vec<_>>();
        let mut snapshot = self.analyze_project_at(&project.program, project.root, &declarations);
        if let Some(verified) = snapshot.verified_mut() {
            verified.attach_external_declarations(project.external_declarations);
            verified.attach_type_declarations(project.type_declarations);
        }
        snapshot
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn project(helper: &str) -> Session {
        Session::with_project(
            "virtual/main.ril".into(),
            vec![
                ProjectSource {
                    path: "virtual/main.ril".into(),
                    bytes: b"use helper\nfn example(){assert(Helper::answer()==42)}".to_vec(),
                },
                ProjectSource {
                    path: "virtual/helper.ril".into(),
                    bytes: helper.as_bytes().to_vec(),
                },
            ],
            CheckOptions::default(),
        )
        .unwrap()
    }
    #[test]
    fn imported_edits_invalidate_only_their_inputs_and_match_fresh_project_diagnostics() {
        let valid = "pub fn answer()->int{42}";
        let invalid = "pub fn answer()->int{missing}";
        let mut incremental = project(valid);
        assert!(matches!(
            incremental.check(),
            CompilationOutcome::Accepted { .. }
        ));
        let before = incremental
            .project_sources()
            .map(|(path, file)| (path.to_owned(), file))
            .collect::<Vec<_>>();
        incremental
            .update_file(Path::new("virtual/helper.ril"), invalid.as_bytes().to_vec())
            .unwrap();
        let (
            CompilationOutcome::Rejected {
                diagnostics: incremental_errors,
            },
            CompilationOutcome::Rejected {
                diagnostics: fresh_errors,
            },
        ) = (incremental.check(), project(invalid).check())
        else {
            panic!("unresolved name must be rejected");
        };
        assert_eq!(incremental_errors, fresh_errors);
        incremental
            .update_file(Path::new("virtual/helper.ril"), valid.as_bytes().to_vec())
            .unwrap();
        assert!(matches!(
            incremental.check(),
            CompilationOutcome::Accepted { .. }
        ));
        assert_eq!(
            before,
            incremental
                .project_sources()
                .map(|(path, file)| (path.to_owned(), file))
                .collect::<Vec<_>>()
        );
        incremental
            .remove_file(Path::new("virtual/helper.ril"))
            .unwrap();
        let CompilationOutcome::Rejected { diagnostics } = incremental.check() else {
            panic!("missing import must be rejected")
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0208")
        );
    }
}
