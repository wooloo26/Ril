use clap::{Parser, Subcommand};
use std::{
    path::{Path, PathBuf},
    process::{Command as Process, ExitCode},
    time::Duration,
};

#[derive(Parser)]
#[command(about = "Ril development tasks")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}
#[derive(Subcommand)]
enum Command {
    Ci,
    Corpus {
        #[command(subcommand)]
        command: Corpus,
    },
    Hooks {
        #[command(subcommand)]
        command: Hooks,
    },
}
#[derive(Subcommand)]
enum Corpus {
    Validate,
    List {
        #[arg(long)]
        json: bool,
    },
    Extract {
        case_id: String,
        #[arg(long)]
        out: PathBuf,
    },
    Run {
        /// Select exact corpus case IDs; may be repeated.
        #[arg(long = "case")]
        cases: Vec<String>,
        /// Keep case IDs containing this substring.
        #[arg(long)]
        filter: Option<String>,
        /// Keep only these execution modes; may be repeated.
        #[arg(long = "mode", value_parser = parse_mode)]
        modes: Vec<ril_test::Mode>,
        /// Exclude native cases explicitly requiring the other supported OS.
        #[arg(long)]
        applicable_only: bool,
        /// Compiler executable; omitted builds the workspace ril binary.
        #[arg(long)]
        compiler: Option<PathBuf>,
        #[arg(long)]
        json: bool,
        /// Total time allowed for checking, building and executing each case.
        #[arg(long, default_value_t = 30_000, value_parser = clap::value_parser!(u64).range(1..))]
        timeout_ms: u64,
    },
}
#[derive(Subcommand)]
enum Hooks {
    Install,
}

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}

fn parse_mode(value: &str) -> Result<ril_test::Mode, String> {
    ril_test::Mode::ALL
        .into_iter()
        .find(|mode| mode.to_string() == value)
        .ok_or_else(|| format!("unknown corpus mode: {value}"))
}

fn validate(
    repo: &Path,
) -> Result<(Vec<ril_test::Case>, ril_test::CorpusStats), Box<dyn std::error::Error>> {
    let cases = ril_test::discover_cases(&repo.join("tests"))?;
    let stats = ril_test::validate_corpus(&cases, &repo.join("doc"), true)?;
    Ok((cases, stats))
}
fn report(stats: &ril_test::CorpusStats) {
    println!(
        "Validated {} theme files, {} cases, {} diagnostic codes and {} companion links.",
        stats.bundles, stats.cases, stats.diagnostic_codes, stats.companions
    );
    for (mode, count) in &stats.modes {
        println!("{mode}: {count}");
    }
    println!("Structural validation only. Ril semantic executions remain not-run.");
}
fn run() -> Result<u8, Box<dyn std::error::Error>> {
    let repo = repository();
    match Cli::parse().command {
        Command::Corpus { command } => {
            let (cases, stats) = validate(&repo)?;
            match command {
                Corpus::Validate => report(&stats),
                Corpus::List { json: false } => {
                    for item in &cases {
                        println!("{}\t{}", item.id, item.meta.mode);
                    }
                }
                Corpus::List { json: true } => {
                    let expected = cases
                        .iter()
                        .map(ril_test::expected_outcome)
                        .collect::<ril_test::Result<Vec<_>>>()?;
                    println!(
                        "{}",
                        serde_json::to_string(
                            &serde_json::json!({"stats": stats, "cases": cases, "expected": expected})
                        )?
                    );
                }
                Corpus::Extract { case_id, out } => {
                    let case = cases
                        .iter()
                        .find(|item| item.id == case_id)
                        .ok_or_else(|| format!("unknown case: {case_id}"))?;
                    let extracted = ril_test::extract_case(case, &out)?;
                    println!("Extracted {case_id} to {}", extracted.directory.display());
                    println!("Root: {}", extracted.root.display());
                    println!("Materialized inputs only; no builds or Ril execution occurred.");
                }
                Corpus::Run {
                    cases: ids,
                    filter,
                    modes,
                    applicable_only,
                    compiler,
                    json,
                    timeout_ms,
                } => {
                    let compiler = match compiler {
                        Some(compiler) => compiler,
                        None => {
                            let metadata = xtask::architecture::load(&repo)?;
                            if !Process::new("cargo")
                                .current_dir(&repo)
                                .args(["build", "--locked", "--package", "ril-cli", "--bin", "ril"])
                                .status()?
                                .success()
                            {
                                return Err("could not build corpus compiler".into());
                            }
                            metadata
                                .target_directory
                                .join("debug")
                                .join(if cfg!(windows) { "ril.exe" } else { "ril" })
                        }
                    };
                    let execution = xtask::runner::run_corpus(
                        &cases,
                        &xtask::runner::RunOptions {
                            compiler,
                            cases: ids,
                            filter,
                            modes,
                            applicable_only,
                            timeout: Duration::from_millis(timeout_ms),
                        },
                    )?;
                    if json {
                        println!("{}", serde_json::to_string(&execution)?);
                    } else {
                        for case in &execution.excluded {
                            println!("Excluded\t{}: {}", case.id, case.reason);
                        }
                        for case in &execution.cases {
                            println!(
                                "{:?}\t{}{}",
                                case.verdict,
                                case.id,
                                case.detail
                                    .as_ref()
                                    .map(|detail| format!(": {detail}"))
                                    .unwrap_or_default()
                            );
                        }
                        println!(
                            "{:?}: selected {}, attempted {}, passed {}, failed {}, harness errors {}, unimplemented {}, unsupported environments {}.",
                            execution.verdict,
                            execution.report.selected,
                            execution.report.attempted,
                            execution.report.passed,
                            execution.report.failed,
                            execution.report.harness_error,
                            execution.report.unimplemented,
                            execution.report.unsupported_environment
                        );
                    }
                    return Ok(match execution.verdict {
                        ril_test::Verdict::Pass => 0,
                        ril_test::Verdict::Incomplete => 2,
                        ril_test::Verdict::Fail | ril_test::Verdict::HarnessError => 1,
                    });
                }
            }
        }
        Command::Hooks {
            command: Hooks::Install,
        } => {
            println!(
                "Installed {}",
                xtask::hooks::build_and_install(&repo)?.display()
            );
        }
        Command::Ci => {
            // Windows cannot replace the running xtask executable during a workspace build.
            let metadata = xtask::architecture::load(&repo)?;
            let packages = xtask::architecture::check(&metadata)?;
            println!("Architecture checks passed for {packages} workspace packages.");
            let ci_target = metadata.target_directory.join("ci");
            let commands: &[&[&str]] = &[
                &["fmt", "--all", "--", "--check"],
                &[
                    "clippy",
                    "--workspace",
                    "--all-targets",
                    "--locked",
                    "--",
                    "-D",
                    "warnings",
                ],
                &["build", "--workspace", "--all-targets", "--locked"],
                &[
                    "nextest",
                    "run",
                    "--workspace",
                    "--locked",
                    "--profile",
                    "ci",
                ],
                &["test", "--workspace", "--doc", "--locked"],
            ];
            for args in commands {
                eprintln!("cargo {}", args.join(" "));
                if !Process::new("cargo")
                    .current_dir(&repo)
                    .env("CARGO_TARGET_DIR", &ci_target)
                    .args(*args)
                    .status()?
                    .success()
                {
                    return Err(format!("cargo {} failed", args.join(" ")).into());
                }
            }
            report(&validate(&repo)?.1);
        }
    }
    Ok(0)
}
fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
