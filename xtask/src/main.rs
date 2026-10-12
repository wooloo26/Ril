use clap::{Parser, Subcommand};
use std::{
    path::{Path, PathBuf},
    process::{Command as Process, ExitCode},
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
fn run() -> Result<(), Box<dyn std::error::Error>> {
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
    Ok(())
}
fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
