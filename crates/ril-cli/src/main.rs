use clap::{Parser, Subcommand};
use ril_compiler::CompilationOutcome;
use std::{path::PathBuf, process::ExitCode};

#[derive(Parser)]
#[command(name = "ril", version, about = "Ril compiler infrastructure")]
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
        source: PathBuf,
        #[arg(long)]
        target: Option<String>,
        #[arg(long)]
        json: bool,
    },
    Build {
        source: PathBuf,
        #[arg(long)]
        target: Option<String>,
        #[arg(long)]
        json: bool,
    },
}
fn default_target() -> &'static str {
    if cfg!(target_os = "windows") {
        ril_codegen::target::NATIVE_TARGETS[0]
    } else {
        ril_codegen::target::NATIVE_TARGETS[1]
    }
}
fn run() -> Result<u8, Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    match cli.command {
        Command::Targets { json } => {
            let targets: Vec<_> = ril_codegen::target::NATIVE_TARGETS
                .into_iter()
                .map(ril_codegen::target::TargetSpec::native)
                .collect::<Result<_, _>>()?;
            if json {
                println!("{}", serde_json::to_string_pretty(&targets)?);
            } else {
                for target in targets {
                    println!(
                        "{} (native object emission; Ril frontend not implemented)",
                        target.triple
                    );
                }
            }
            Ok(0)
        }
        command => {
            let (source, target, json, build) = match command {
                Command::Check {
                    source,
                    target,
                    json,
                } => (source, target, json, false),
                Command::Build {
                    source,
                    target,
                    json,
                } => (source, target, json, true),
                Command::Targets { .. } => unreachable!(),
            };
            let target = target.as_deref().unwrap_or(default_target());
            let outcome = if build {
                ril_compiler::build_path(&source, target)?
            } else {
                ril_compiler::check_path(&source, target)?
            };
            if json {
                println!("{}", serde_json::to_string_pretty(&outcome)?);
            } else {
                match &outcome {
                    CompilationOutcome::NotImplemented { reason } => eprintln!("{reason}"),
                    CompilationOutcome::Rejected { diagnostics } => {
                        for diagnostic in diagnostics {
                            eprintln!("{}: {}", diagnostic.code, diagnostic.message);
                        }
                    }
                }
            }
            Ok(outcome.exit_code())
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
