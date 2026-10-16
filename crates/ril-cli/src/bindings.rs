//! Binding configuration is explicit input to native builds; semantic checking
//! never launches a provider or reads an ambient binding manifest.
use ril_compiler::driver::{Binding, ProviderConfig};
use std::{io, path::Path};

pub(super) fn load(path: &Path) -> Result<Vec<Binding>, Box<dyn std::error::Error>> {
    let path = std::fs::canonicalize(path)?;
    let mut manifest: ril_runtime::api::foreign::Manifest =
        serde_json::from_slice(&std::fs::read(&path)?)?;
    manifest.validate().map_err(io::Error::other)?;
    let directory = path
        .parent()
        .ok_or_else(|| io::Error::other("binding manifest has no parent directory"))?;
    let mut bindings = Vec::new();
    for provider in &mut manifest.providers {
        if !provider.program.is_absolute() {
            provider.program = directory.join(&provider.program);
        }
        provider.program = std::fs::canonicalize(&provider.program)?;
        if !provider.program.is_file() {
            return Err(io::Error::other("provider program must be a file").into());
        }
        for (declaration, export) in &provider.bindings {
            bindings.push(Binding {
                declaration: declaration.clone(),
                export: export.clone(),
                provider: ProviderConfig {
                    id: provider.id.clone(),
                    program: provider.program.clone(),
                    args: provider.args.clone(),
                    max_frame_bytes: provider.max_frame_bytes,
                },
            });
        }
    }
    Ok(bindings)
}
