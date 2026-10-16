//! Platform linking is independent from object emission.
use crate::{backend::BackendError, target::TargetSpec};
use ril_compiler_core::phase::{NotImplemented, Stage};
use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

/// Linkers receive an explicit argument vector; drivers must not concatenate a shell command.
#[derive(Debug, Clone)]
pub struct LinkRequest {
    pub target: TargetSpec,
    pub objects: Vec<PathBuf>,
    pub runtime_library: PathBuf,
    pub output: PathBuf,
}
pub trait Linker {
    fn link(&self, request: &LinkRequest) -> Result<PathBuf, BackendError>;
}

/// Link native objects using the host's system toolchain, with no shell expansion.
pub struct SystemLinker;

fn unavailable(detail: impl Into<String>) -> BackendError {
    BackendError::NotImplemented(NotImplemented::new(Stage::Linking, detail))
}

impl Linker for SystemLinker {
    fn link(&self, request: &LinkRequest) -> Result<PathBuf, BackendError> {
        request
            .target
            .validate()
            .map_err(|error| BackendError::Target(error.to_string()))?;
        let native_host = if cfg!(all(windows, target_arch = "x86_64")) {
            "x86_64-pc-windows-msvc"
        } else if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
            "x86_64-unknown-linux-gnu"
        } else {
            return Err(unavailable("no native host linker integration"));
        };
        if request.target.triple != native_host {
            return Err(unavailable(format!(
                "cross-linking {} on {native_host}",
                request.target.triple
            )));
        }
        if request.objects.is_empty() {
            return Err(BackendError::InvalidIr(
                "link request has no objects".into(),
            ));
        }
        for input in request
            .objects
            .iter()
            .chain(std::iter::once(&request.runtime_library))
        {
            if !input.is_file() {
                return Err(unavailable(format!(
                    "link input is unavailable: {}",
                    input.display()
                )));
            }
        }
        let output = std::path::absolute(&request.output)
            .map_err(|error| BackendError::Codegen(error.to_string()))?;
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent).map_err(|error| BackendError::Codegen(error.to_string()))?;
        }
        let mut command = host_command(&output)?;
        for object in &request.objects {
            command.arg(object);
        }
        command.arg(&request.runtime_library);
        if cfg!(windows) {
            command.args([
                "kernel32.lib",
                "advapi32.lib",
                "userenv.lib",
                "ws2_32.lib",
                "bcrypt.lib",
                "ntdll.lib",
                "dbghelp.lib",
                "ole32.lib",
                "shell32.lib",
                "uuid.lib",
                "/DEFAULTLIB:msvcrt",
                "/DEFAULTLIB:legacy_stdio_definitions",
            ]);
        } else {
            command.args(["-ldl", "-lpthread", "-lm", "-lrt", "-lutil"]);
        }
        let result = command.output().map_err(|error| {
            if error.kind() == std::io::ErrorKind::NotFound {
                unavailable(format!("system linker executable was not found: {error}"))
            } else {
                BackendError::Codegen(format!("could not invoke system linker: {error}"))
            }
        })?;
        if !result.status.success() {
            return Err(BackendError::Codegen(format!(
                "system linker failed ({:?}):\n{}{}",
                result.status.code(),
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            )));
        }
        if !output.is_file() {
            return Err(BackendError::Codegen(
                "system linker did not produce requested output".into(),
            ));
        }
        Ok(output)
    }
}

fn host_command(output: &Path) -> Result<Command, BackendError> {
    if cfg!(windows) {
        let tools = windows_tools()?;
        let mut command = Command::new(tools.linker);
        if !tools.libraries.is_empty() {
            let libraries = std::env::join_paths(tools.libraries)
                .map_err(|error| BackendError::Codegen(error.to_string()))?;
            command.env("LIB", libraries);
        }
        command.args(["/NOLOGO", "/SUBSYSTEM:CONSOLE", "/INCREMENTAL:NO"]);
        let mut out = OsString::from("/OUT:");
        out.push(output);
        command.arg(out);
        Ok(command)
    } else {
        let mut command =
            Command::new(std::env::var_os("CC").unwrap_or_else(|| OsString::from("cc")));
        command.arg("-o").arg(output);
        Ok(command)
    }
}

struct WindowsTools {
    linker: PathBuf,
    libraries: Vec<PathBuf>,
}

fn windows_tools() -> Result<WindowsTools, BackendError> {
    let mut libraries: Vec<_> = std::env::var_os("LIB")
        .map(|value| std::env::split_paths(&value).collect())
        .unwrap_or_default();
    let configured = std::env::var_os("RIL_LINKER").map(PathBuf::from);
    if let Some(linker) = configured {
        return Ok(WindowsTools { linker, libraries });
    }
    let program_files = std::env::var_os("ProgramFiles(x86)")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("C:/Program Files (x86)"));
    let vswhere = program_files.join("Microsoft Visual Studio/Installer/vswhere.exe");
    let installation = if vswhere.is_file() {
        let output = Command::new(vswhere)
            .args([
                "-latest",
                "-products",
                "*",
                "-requires",
                "Microsoft.VisualStudio.Component.VC.Tools.x86.x64",
                "-property",
                "installationPath",
            ])
            .output()
            .map_err(|error| unavailable(format!("Visual Studio discovery failed: {error}")))?;
        if output.status.success() {
            String::from_utf8_lossy(&output.stdout)
                .lines()
                .find(|line| !line.trim().is_empty())
                .map(|line| PathBuf::from(line.trim()))
        } else {
            None
        }
    } else {
        None
    };
    let toolchain = installation
        .and_then(|installation| latest_subdirectory(&installation.join("VC/Tools/MSVC")));
    let linker = if let Some(toolchain) = toolchain {
        let lib = toolchain.join("lib/x64");
        if lib.is_dir() {
            libraries.push(lib);
        }
        toolchain.join("bin/Hostx64/x64/link.exe")
    } else {
        PathBuf::from("link.exe")
    };
    let sdk = std::env::var_os("WindowsSdkDir")
        .map(PathBuf::from)
        .unwrap_or_else(|| program_files.join("Windows Kits/10"));
    if let Some(version) = latest_subdirectory(&sdk.join("Lib")) {
        for name in ["ucrt/x64", "um/x64"] {
            let path = version.join(name);
            if path.is_dir() {
                libraries.push(path);
            }
        }
    }
    if libraries.is_empty() {
        return Err(unavailable(
            "MSVC/Windows SDK library paths are unavailable; run in a developer environment or install C++ Build Tools",
        ));
    }
    Ok(WindowsTools { linker, libraries })
}

fn latest_subdirectory(path: &Path) -> Option<PathBuf> {
    let mut paths: Vec<_> = fs::read_dir(path)
        .ok()?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.is_dir())
        .collect();
    paths.sort();
    paths.pop()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn missing_native_inputs_are_explicitly_unavailable() {
        let request = LinkRequest {
            target: TargetSpec::native(if cfg!(windows) {
                "x86_64-pc-windows-msvc"
            } else {
                "x86_64-unknown-linux-gnu"
            })
            .unwrap(),
            objects: vec![PathBuf::from("no-such-object")],
            runtime_library: PathBuf::from("no-such-runtime"),
            output: PathBuf::from("output"),
        };
        assert!(matches!(
            SystemLinker.link(&request),
            Err(BackendError::NotImplemented(_))
        ));
    }
}
