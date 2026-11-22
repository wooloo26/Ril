#![forbid(unsafe_code)]

use std::{
    io::Write as _,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

use clap::{Parser, Subcommand, ValueEnum};
use ril_base::diag::Diagnostic;
use ril_driver::{AVAILABLE, Driver, infer_unit, load_package};
use ril_test::{Activation, Stage, Unit};

#[derive(Parser)]
#[command(version, about = "Ril compiler")]
struct Cli {
    #[command(subcommand)]
    command: Action,
}

#[derive(Clone, Copy, ValueEnum)]
enum Backend {
    Jit,
    Aot,
}

#[derive(Clone, Copy, ValueEnum)]
enum IrFormat {
    Mir,
    Clif,
    Horn,
}

#[derive(Subcommand)]
enum Action {
    Check {
        path: PathBuf,
        #[arg(long, default_value = "access")]
        stage: Stage,
        #[arg(long)]
        unit: Option<Unit>,
        #[arg(long)]
        emit_interface: Option<PathBuf>,
    },
    Build {
        path: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
        #[arg(long, value_name = "OBJECT_OR_LIBRARY")]
        link: Vec<PathBuf>,
    },
    Run {
        path: PathBuf,
        #[arg(long, value_enum, default_value = "jit")]
        backend: Backend,
        #[arg(long, value_name = "OBJECT_OR_LIBRARY")]
        link: Vec<PathBuf>,
    },
    EmitIr {
        path: PathBuf,
        #[arg(long, value_enum, default_value = "mir")]
        format: IrFormat,
    },
    Test {
        path: Option<PathBuf>,
        #[arg(long)]
        sync_spec_md: bool,
        #[arg(long, requires = "sync_spec_md", default_value = "parse")]
        stage: Stage,
    },
}

fn main() -> ExitCode {
    if let Some(status) = ril_driver::worker_entry() {
        std::process::exit(status);
    }
    match run(Cli::parse().command) {
        Ok(status) => status,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

fn run(action: Action) -> Result<ExitCode, String> {
    match action {
        Action::Check {
            path,
            stage,
            unit,
            emit_interface,
        } => {
            let package = load_package(&path, unit.unwrap_or_else(|| infer_unit(&path)))?;
            let checked = Driver.check(&package, stage);
            for diagnostic in &checked.result.diagnostics {
                diagnostic
                    .render(&checked.sources, std::io::stderr().lock())
                    .map_err(|err| err.to_string())?;
            }
            if !checked.result.diagnostics.is_empty() {
                return Ok(ExitCode::FAILURE);
            }
            if let Some(path) = emit_interface {
                let interface = Driver.interface(&package).map_err(display)?;
                let bytes = interface.encode().map_err(|err| err.to_string())?;
                std::fs::write(path, bytes).map_err(|err| err.to_string())?;
            }
        }
        Action::Build { path, output, link } => {
            let package = load_package(&path, Unit::Bin)?;
            let output =
                output.unwrap_or_else(|| path.with_extension(std::env::consts::EXE_EXTENSION));
            if same_file(&path, &output) {
                return Err("output would overwrite the source file".into());
            }
            Driver
                .compile_aot_with_links(&package, &output, &link)
                .map_err(display)?;
        }
        Action::Run {
            path,
            backend,
            link,
        } => {
            if matches!(backend, Backend::Jit) && !link.is_empty() {
                return Err("select --backend aot to use --link".into());
            }
            let package = load_package(&path, Unit::Bin)?;
            let output = match backend {
                Backend::Jit => Driver.execute_jit(&package).map_err(display)?,
                Backend::Aot => {
                    let dir = tempfile::tempdir().map_err(|err| err.to_string())?;
                    let output = dir
                        .path()
                        .join(format!("ril_program{}", std::env::consts::EXE_SUFFIX));
                    Driver
                        .compile_aot_with_links(&package, &output, &link)
                        .map_err(display)?;
                    ril_test::run_worker(&mut Command::new(output))
                        .map_err(|err| err.to_string())?
                }
            };
            std::io::stdout()
                .write_all(&output.stdout)
                .map_err(|err| err.to_string())?;
            std::io::stderr()
                .write_all(&output.stderr)
                .map_err(|err| err.to_string())?;
            return Ok(exit(output.status));
        }
        Action::EmitIr { path, format } => {
            let unit = if matches!(format, IrFormat::Horn) {
                Unit::Lib
            } else {
                Unit::Bin
            };
            let package = load_package(&path, unit)?;
            let text = match format {
                IrFormat::Mir => format!("{:#?}", Driver.lower(&package).map_err(display)?),
                IrFormat::Clif => Driver.clif(&package).map_err(display)?,
                IrFormat::Horn => Driver.horn_json(&package).map_err(display)?,
            };
            println!("{text}");
        }
        Action::Test {
            path,
            sync_spec_md,
            stage,
        } => return test(path, sync_spec_md, stage),
    }
    Ok(ExitCode::SUCCESS)
}

fn same_file(a: &Path, b: &Path) -> bool {
    a == b
        || b.canonicalize()
            .is_ok_and(|output| a.canonicalize().is_ok_and(|input| output == input))
}

fn exit(status: std::process::ExitStatus) -> ExitCode {
    if let Some(code) = status.code().and_then(|code| u8::try_from(code).ok()) {
        return ExitCode::from(code);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;
        if let Some(code) = status
            .signal()
            .and_then(|signal| u8::try_from(128 + signal).ok())
        {
            return ExitCode::from(code);
        }
    }
    ExitCode::FAILURE
}

fn display(diagnostics: Vec<Diagnostic>) -> String {
    diagnostics
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn test(path: Option<PathBuf>, sync_spec_md: bool, stage: Stage) -> Result<ExitCode, String> {
    let suites = if sync_spec_md {
        let path = path.unwrap_or_else(|| PathBuf::from("doc/SPEC.md"));
        let source =
            std::fs::read_to_string(&path).map_err(|err| format!("{}: {err}", path.display()))?;
        vec![ril_test::spec_suite(&path, &source, stage)?]
    } else {
        ril_test::discover(&path.unwrap_or_else(|| PathBuf::from("tests")))?
    };
    let mut failed = 0;
    let mut passed = 0;
    let mut skipped = 0;
    for suite in suites {
        for case in suite.cases {
            if case.activation(AVAILABLE) != Activation::Ready {
                skipped += 1;
            } else if let Err(error) = ril_test::run_case(&case, &Driver) {
                eprintln!(
                    "{}:{} {}::{}\n{error}",
                    suite.path.display(),
                    case.line,
                    suite.name,
                    case.id
                );
                failed += 1;
            } else {
                passed += 1;
            }
        }
    }
    println!("{passed} passed, {failed} failed, {skipped} pending");
    Ok(if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}
