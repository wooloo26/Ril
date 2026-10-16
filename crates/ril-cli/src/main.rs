use clap::{Args, Parser, Subcommand, ValueEnum};
mod bindings;
use ril_compiler::{BuildOptions, CheckOptions, CompilationOutcome, UnitKind};
use std::{
    path::{Path, PathBuf},
    process::{Command as Process, ExitCode, Stdio},
};

#[derive(Parser)]
#[command(name = "ril", version, about = "Ril compiler")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}
#[derive(Subcommand)]
enum Command {
    Targets {
        #[arg(long)]
        json: bool,
    },
    Check {
        #[command(flatten)]
        source: SourceOptions,
    },
    Build {
        #[command(flatten)]
        source: SourceOptions,
        #[arg(long)]
        output: Option<PathBuf>,
        #[arg(long)]
        runtime_library: Option<PathBuf>,
        /// Explicit external-provider binding manifest.
        #[arg(long)]
        bindings: Option<PathBuf>,
    },
    Test {
        #[command(flatten)]
        source: SourceOptions,
        #[arg(long)]
        entry: String,
        #[arg(long)]
        runtime_library: Option<PathBuf>,
        /// Explicit external-provider binding manifest.
        #[arg(long)]
        bindings: Option<PathBuf>,
        #[arg(last = true)]
        args: Vec<String>,
    },
}
#[derive(Args)]
struct SourceOptions {
    source: PathBuf,
    #[arg(long)]
    target: Option<String>,
    #[arg(long, value_enum, default_value = "library")]
    unit: Unit,
    #[arg(long)]
    json: bool,
    #[arg(long)]
    explain: bool,
    /// Positive meta/type evaluation budget, counted in language events.
    #[arg(long, default_value_t = ril_compiler::static_eval::DEFAULT_STATIC_BUDGET)]
    static_budget: std::num::NonZeroU64,
}
#[derive(Debug, Clone, Copy, ValueEnum)]
enum Unit {
    Library,
    Executable,
}
impl SourceOptions {
    fn options(&self) -> CheckOptions {
        CheckOptions {
            target: self
                .target
                .clone()
                .unwrap_or_else(|| default_target().into()),
            unit: match self.unit {
                Unit::Library => UnitKind::Library,
                Unit::Executable => UnitKind::Executable,
            },
            explain: self.explain,
            static_budget: self.static_budget,
        }
    }
}
fn default_target() -> &'static str {
    ril_codegen::target::NATIVE_TARGETS[usize::from(!cfg!(target_os = "windows"))]
}

fn runtime_library(explicit: Option<PathBuf>, target: &str) -> PathBuf {
    if let Some(path) =
        explicit.or_else(|| std::env::var_os("RIL_RUNTIME_LIBRARY").map(PathBuf::from))
    {
        return path;
    }
    // This dependency ensures Cargo builds the runtime alongside the CLI. The
    // adjacent un-hashed file is also the distribution layout.
    let _contract = ril_runtime::STATUS.contract_version;
    let name = if target.contains("windows") {
        "ril_runtime.lib"
    } else {
        "libril_runtime.a"
    };
    let profile = std::env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(Path::to_owned))
        .unwrap_or_default();
    let direct = profile.join(name);
    let prefix = if target.contains("windows") {
        "ril_runtime-"
    } else {
        "libril_runtime-"
    };
    let extension = if target.contains("windows") {
        "lib"
    } else {
        "a"
    };
    let mut candidates = std::fs::read_dir(profile.join("deps"))
        .into_iter()
        .flatten()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry.file_name().to_string_lossy().starts_with(prefix)
                && entry
                    .path()
                    .extension()
                    .is_some_and(|suffix| suffix == extension)
        })
        .map(|entry| entry.path())
        .collect::<Vec<_>>();
    if direct.is_file() {
        candidates.push(direct.clone());
    }
    candidates.sort_by_key(|entry| {
        entry
            .metadata()
            .ok()
            .and_then(|metadata| metadata.modified().ok())
    });
    candidates.pop().unwrap_or(direct)
}

fn display(outcome: &CompilationOutcome, json: bool) -> Result<u8, Box<dyn std::error::Error>> {
    if json {
        println!("{}", serde_json::to_string(outcome)?);
    } else {
        match outcome {
            CompilationOutcome::Accepted { diagnostics, .. } => {
                for diagnostic in diagnostics {
                    eprintln!("{}: {}", diagnostic.code, diagnostic.message);
                }
                println!("Accepted");
            }
            CompilationOutcome::Built { artifact, .. } => println!("{}", artifact.path.display()),
            CompilationOutcome::NotImplemented { reason } => eprintln!("{reason}"),
            CompilationOutcome::UnsupportedEnvironment { detail } => eprintln!("{detail}"),
            CompilationOutcome::Rejected { diagnostics } => {
                for diagnostic in diagnostics {
                    eprintln!("{}: {}", diagnostic.code, diagnostic.message);
                    for label in &diagnostic.labels {
                        eprintln!(
                            "  {}:{}..{}: {}",
                            label.span.file.0, label.span.start, label.span.end, label.message
                        );
                    }
                }
            }
        }
    }
    Ok(outcome.exit_code())
}
fn build(
    source: &SourceOptions,
    output: PathBuf,
    runtime: Option<PathBuf>,
    entry: &str,
    bindings: Option<PathBuf>,
) -> Result<CompilationOutcome, Box<dyn std::error::Error>> {
    let check = source.options();
    let options = BuildOptions {
        runtime_library: runtime_library(runtime, &check.target),
        check,
        entry: entry.into(),
        output,
        foreign_bindings: bindings
            .map(|path| bindings::load(&path))
            .transpose()?
            .unwrap_or_default(),
    };
    Ok(ril_compiler::build_path(
        &source.source,
        &options,
        &ril_codegen_cranelift::CraneliftBackend,
        &ril_codegen::link::SystemLinker,
    )?)
}
fn run() -> Result<u8, Box<dyn std::error::Error>> {
    match Cli::parse().command {
        Command::Targets { json } => {
            let targets = ril_codegen::target::NATIVE_TARGETS
                .into_iter()
                .map(ril_codegen::target::TargetSpec::native)
                .collect::<Result<Vec<_>, _>>()?;
            if json {
                println!("{}", serde_json::to_string(&targets)?);
            } else {
                for target in targets {
                    println!("{}", target.triple);
                }
            }
            Ok(0)
        }
        Command::Check { source } => display(
            &ril_compiler::check_path_with(&source.source, &source.options())?,
            source.json,
        ),
        Command::Build {
            source,
            output,
            runtime_library,
            bindings,
        } => {
            let output = output.unwrap_or_else(|| {
                source
                    .source
                    .with_extension(if default_target().contains("windows") {
                        "exe"
                    } else {
                        ""
                    })
            });
            display(
                &build(&source, output, runtime_library, "main", bindings)?,
                source.json,
            )
        }
        Command::Test {
            source,
            entry,
            runtime_library,
            bindings,
            args,
        } => {
            let directory = tempfile::tempdir()?;
            let output = directory
                .path()
                .join(if cfg!(windows) { "test.exe" } else { "test" });
            let outcome = build(&source, output, runtime_library, &entry, bindings)?;
            let CompilationOutcome::Built { artifact, .. } = &outcome else {
                return display(&outcome, source.json);
            };
            let report_path = directory.path().join("outcome.json");
            let child = Process::new(&artifact.path)
                .args(args)
                .env("RIL_EXECUTION_REPORT", &report_path)
                .stdin(Stdio::inherit())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()?;
            let child_id = child.id();
            let output = child.wait_with_output()?;
            let mut owned_report = report_path.into_os_string();
            owned_report.push(format!(".{child_id}"));
            let mut report = std::fs::read(&owned_report)
                .ok()
                .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok())
                .filter(|report| {
                    report["pid"].as_u64() == Some(u64::from(child_id))
                        && report["exit"].as_i64() == output.status.code().map(i64::from)
                })
                .unwrap_or_else(
                    || serde_json::json!({"runtime":"native-crash","exit":output.status.code()}),
                );
            report["status"] = "executed".into();
            report["stdout"] = serde_json::to_value(&output.stdout)?;
            report["stderr"] = serde_json::to_value(&output.stderr)?;
            if source.json {
                println!("{}", serde_json::to_string(&report)?);
            } else {
                use std::io::Write;
                std::io::stdout().write_all(&output.stdout)?;
                std::io::stderr().write_all(&output.stderr)?;
                println!(
                    "{}: {}",
                    entry,
                    report["runtime"].as_str().unwrap_or("unknown")
                );
            }
            Ok(0)
        }
    }
}
fn main() -> ExitCode {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_writer(std::io::stderr)
        .init();
    match run() {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(1)
        }
    }
}
