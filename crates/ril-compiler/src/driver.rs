//! Filesystem and target selection boundary for compilation requests.
use crate::{CheckOptions, CompilationOutcome, Session};
use ril_codegen::{BackendError, LinkRequest, Linker, NativeBackend};
pub use ril_ir::foreign::{Binding, ProviderConfig};
use std::path::{Path, PathBuf};

#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error("invalid native binding configuration: {0}")]
    Binding(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Target(#[from] ril_codegen::target::UnsupportedTarget),
    #[error("source exceeds the supported size")]
    SourceTooLarge,
    #[error(transparent)]
    Backend(#[from] BackendError),
}

#[derive(Debug, Clone)]
pub struct BuildOptions {
    pub check: CheckOptions,
    pub entry: String,
    pub output: PathBuf,
    pub runtime_library: PathBuf,
    pub foreign_bindings: Vec<Binding>,
}

pub fn check_path(path: &Path, target: &str) -> Result<CompilationOutcome, DriverError> {
    check_path_with(
        path,
        &CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
}
pub fn check_path_with(
    path: &Path,
    options: &CheckOptions,
) -> Result<CompilationOutcome, DriverError> {
    tracing::debug!(path = %path.display(), target=%options.target, "checking compilation input");
    match verify_path(path, options)? {
        Ok(program) => Ok(CompilationOutcome::Accepted {
            diagnostics: program.diagnostics().to_vec(),
            causes: if options.explain {
                program.facts().explanations.causes.clone()
            } else {
                vec![]
            },
        }),
        Err(outcome) => Ok(outcome),
    }
}

fn verify_path(
    path: &Path,
    options: &CheckOptions,
) -> Result<Result<crate::hir::VerifiedProgram, CompilationOutcome>, DriverError> {
    let project = crate::modules::load_project(path)?;
    Ok(Session::with_options(vec![], options.clone()).verify_resolved(project))
}

/// The build path cannot create artifacts before successful semantic analysis.
pub fn build_path(
    path: &Path,
    options: &BuildOptions,
    backend: &dyn NativeBackend,
    linker: &dyn Linker,
) -> Result<CompilationOutcome, DriverError> {
    let target = match ril_codegen::target::TargetSpec::native(&options.check.target) {
        Ok(target) => target,
        Err(error) => {
            return Ok(CompilationOutcome::UnsupportedEnvironment {
                detail: error.to_string(),
            });
        }
    };
    let verified = match verify_path(path, &options.check)? {
        Ok(program) => program,
        Err(outcome) => return Ok(outcome),
    };
    if let Err(outcome) = crate::session::entry::verify_environment(
        &verified,
        &options.entry,
        options.entry == "main",
    ) {
        return Ok(outcome);
    }
    let layout = ril_compiler_core::target::TargetLayout::from_name(&options.check.target).unwrap();
    let core = match crate::lower::lower_core_for(&verified, layout) {
        Ok(core) => core,
        Err(reason) => return Ok(CompilationOutcome::NotImplemented { reason }),
    };
    let mut bound = std::collections::BTreeSet::new();
    for binding in &options.foreign_bindings {
        if !bound.insert(binding.declaration.as_str()) {
            return Err(DriverError::Binding(format!(
                "duplicate declaration {}",
                binding.declaration
            )));
        }
        if binding.provider.id.is_empty()
            || !binding.provider.program.is_absolute()
            || binding.provider.max_frame_bytes == 0
            || binding.export.is_empty()
        {
            return Err(DriverError::Binding(format!(
                "invalid provider for {}",
                binding.declaration
            )));
        }
    }
    for declaration in core
        .external_functions
        .iter()
        .map(|function| &function.declaration)
        .chain(
            core.external_constants
                .iter()
                .map(|constant| &constant.declaration),
        )
    {
        if !bound.contains(declaration.as_str()) {
            return Err(DriverError::Binding(format!(
                "missing provider for {declaration}"
            )));
        }
    }
    let mut native = match ril_codegen::lower::lower_native_with_entry(&core, &options.entry) {
        Ok(native) => native,
        Err(reason) => return Ok(CompilationOutcome::NotImplemented { reason }),
    };
    native
        .foreign_bindings
        .clone_from(&options.foreign_bindings);
    let object = match backend.emit(&native, &target) {
        Ok(object) => object,
        Err(BackendError::NotImplemented(reason)) => {
            return Ok(CompilationOutcome::NotImplemented { reason });
        }
        Err(error) => return Err(error.into()),
    };
    if !options.runtime_library.is_file() {
        return Ok(CompilationOutcome::UnsupportedEnvironment {
            detail: format!(
                "native runtime library not found: {}",
                options.runtime_library.display()
            ),
        });
    }
    let output = std::path::absolute(&options.output)?;
    if let Some(parent) = output.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut temporary = tempfile::Builder::new()
        .prefix(".ril-")
        .suffix(".obj")
        .tempfile_in(output.parent().unwrap_or(Path::new(".")))?;
    use std::io::Write;
    temporary.write_all(&object.bytes)?;
    temporary.flush()?;
    let object_path = temporary.into_temp_path();
    let linked = linker.link(&LinkRequest {
        target: target.clone(),
        objects: vec![object_path.to_path_buf()],
        runtime_library: std::path::absolute(&options.runtime_library)?,
        output: output.clone(),
    });
    match linked {
        Ok(path) => Ok(CompilationOutcome::Built {
            artifact: crate::session::BuiltArtifact {
                path,
                target: target.triple,
                runtime_contract_version: object.runtime_contract_version,
            },
            diagnostics: verified.diagnostics().to_vec(),
        }),
        Err(BackendError::NotImplemented(reason)) => {
            Ok(CompilationOutcome::NotImplemented { reason })
        }
        Err(error) => Err(error.into()),
    }
}
