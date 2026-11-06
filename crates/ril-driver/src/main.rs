use ril_compiler::frontend::{UnitKind, frontend};
use std::{
    env, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

const USAGE: &str = "Usage: ril frontend [--library] [--module-root DIR] [--emit-hir] FILE.ril";

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("ril: {error}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<bool, Box<dyn std::error::Error>> {
    let mut args = env::args_os().skip(1);
    let Some(command) = args.next() else {
        return Err(USAGE.into());
    };
    if command == "--help" || command == "-h" {
        println!("{USAGE}");
        return Ok(true);
    }
    if command == "--version" {
        println!("ril {}", env!("CARGO_PKG_VERSION"));
        return Ok(true);
    }
    if command != "frontend" {
        return Err(USAGE.into());
    }
    let mut file = None;
    let mut module_root = None;
    let mut library = false;
    let mut emit_hir = false;
    while let Some(argument) = args.next() {
        match argument.to_str() {
            Some("--library") => library = true,
            Some("--emit-hir") => emit_hir = true,
            Some("--module-root") => {
                module_root = Some(PathBuf::from(
                    args.next().ok_or("--module-root requires a directory")?,
                ));
            }
            Some("--help" | "-h") => {
                println!("{USAGE}");
                return Ok(true);
            }
            Some(flag) if flag.starts_with('-') => {
                return Err(format!("unknown flag '{flag}'").into());
            }
            _ if file.is_none() => file = Some(PathBuf::from(argument)),
            _ => return Err(USAGE.into()),
        }
    }
    let file = fs::canonicalize(file.ok_or(USAGE)?)?;
    let name = file
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("source filename must be UTF-8")?;
    let kind = if name.ends_with(".d.ril") {
        UnitKind::External
    } else if name.ends_with(".ril") {
        if library {
            UnitKind::Library
        } else {
            UnitKind::Executable
        }
    } else {
        return Err("source must have a .ril or .d.ril extension".into());
    };
    let base = match module_root {
        Some(path) => fs::canonicalize(path)?,
        None => file
            .parent()
            .ok_or("source has no parent directory")?
            .to_owned(),
    };
    let root = file
        .strip_prefix(&base)
        .map_err(|_| "source must be inside the module root")?;
    let result = frontend(root, kind, |path: &Path| fs::read(base.join(path)))?;
    for diagnostic in &result.diagnostics {
        if let Some(label) = diagnostic.labels.first()
            && let Some(source) = result.sources.get(label.span.file)
        {
            let (line, column) = source.location(label.span.start);
            eprintln!(
                "{}:{line}:{column}: {} {}",
                base.join(source.path()).display(),
                diagnostic.code,
                diagnostic.message
            );
        } else {
            eprintln!("{} {}", diagnostic.code, diagnostic.message);
        }
    }
    if emit_hir && let Some(hir) = &result.hir {
        println!("{hir:#?}");
    }
    Ok(result.is_ok())
}
