#![forbid(unsafe_code)]

use std::{path::PathBuf, process::ExitCode};

use clap::{Parser, Subcommand};
use ril_driver::{AVAILABLE, Driver};
use ril_test::{Stage, Unit, VirtualPackage};

#[derive(Parser)]
#[command(version, about = "Ril compiler")]
struct Cli {
    #[command(subcommand)]
    command: Action,
}

#[derive(Subcommand)]
enum Action {
    Check {
        path: PathBuf,
        #[arg(long, default_value = "type")]
        stage: Stage,
        #[arg(long, default_value = "lib")]
        unit: Unit,
    },
    Test {
        path: Option<PathBuf>,
        #[arg(long)]
        sync_spec_md: bool,
    },
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(status) => status,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<ExitCode, String> {
    match cli.command {
        Action::Check { path, stage, unit } => {
            let bytes = std::fs::read(&path).map_err(|err| format!("{}: {err}", path.display()))?;
            let mut pkg = VirtualPackage::new(unit);
            pkg.entry = path.clone();
            pkg.insert(path, bytes);
            let checked = Driver.check(&pkg, stage);
            for diagnostic in &checked.result.diagnostics {
                diagnostic
                    .render(&checked.sources, std::io::stderr().lock())
                    .map_err(|err| err.to_string())?;
            }
            Ok(if checked.result.diagnostics.is_empty() {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            })
        }
        Action::Test { path, sync_spec_md } => {
            let suites = if sync_spec_md {
                let path = path.unwrap_or_else(|| PathBuf::from("doc/SPEC.md"));
                let source = std::fs::read_to_string(&path)
                    .map_err(|err| format!("{}: {err}", path.display()))?;
                vec![ril_test::spec_suite(&path, &source, Stage::Parse)?]
            } else {
                ril_test::discover(&path.unwrap_or_else(|| PathBuf::from("tests")))?
            };
            let mut failed = 0;
            let mut passed = 0;
            let mut skipped = 0;
            for suite in suites {
                for case in suite.cases {
                    if case.activation(AVAILABLE) != ril_test::Activation::Ready {
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
    }
}
