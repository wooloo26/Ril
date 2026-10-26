use clap::{Parser, Subcommand};
use std::{
    path::{Path, PathBuf},
    process::ExitCode,
};

#[derive(Parser)]
#[command(about = "Ril development tools")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Validate .ril test file structure in the corpus.
    Validate,
    /// Corpus commands.
    Corpus {
        #[command(subcommand)]
        command: Corpus,
    },
    /// Git hook management.
    Hooks {
        #[command(subcommand)]
        command: Hooks,
    },
    /// Check a commit message file.
    CheckCommit { path: PathBuf },
}

#[derive(Subcommand)]
enum Corpus {
    /// Validate all .ril test files in the corpus.
    Validate,
    /// List corpus cases.
    List {
        #[arg(long)]
        json: bool,
    },
    /// Extract a case's virtual files to a directory.
    Extract {
        case_id: String,
        #[arg(long)]
        out: PathBuf,
    },
}

#[derive(Subcommand)]
enum Hooks {
    /// Build and install the commit-msg git hook.
    Install,
}

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).to_owned()
}

fn validate(repo: &Path) -> Result<(Vec<ril::Case>, ril::CorpusStats), Box<dyn std::error::Error>> {
    let cases = ril::discover_cases(&repo.join("tests"))?;
    let stats = ril::validate_corpus(&cases, &repo.join("doc"), true)?;
    Ok((cases, stats))
}

fn report(stats: &ril::CorpusStats) {
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
        Command::Validate => {
            let (_, stats) = validate(&repo)?;
            report(&stats);
        }
        Command::Corpus { command } => match command {
            Corpus::Validate => {
                let (_, stats) = validate(&repo)?;
                report(&stats);
            }
            Corpus::List { json: false } => {
                let (cases, _) = validate(&repo)?;
                for item in &cases {
                    println!("{}\t{}", item.id, item.meta.mode);
                }
            }
            Corpus::List { json: true } => {
                let (cases, stats) = validate(&repo)?;
                println!(
                    "{}",
                    serde_json::to_string(&serde_json::json!({
                        "stats": stats,
                        "cases": cases
                    }))?
                );
            }
            Corpus::Extract { case_id, out } => {
                let (cases, _) = validate(&repo)?;
                let case = cases
                    .iter()
                    .find(|item| item.id == case_id)
                    .ok_or_else(|| format!("unknown case: {case_id}"))?;
                let extracted = ril::extract_case(case, &out)?;
                println!("Extracted {case_id} to {}", extracted.directory.display());
                println!("Root: {}", extracted.root.display());
            }
        },
        Command::Hooks {
            command: Hooks::Install,
        } => {
            println!(
                "Installed {}",
                ril::hooks::build_and_install(&repo)?.display()
            );
        }
        Command::CheckCommit { path } => {
            ril::hooks::check_file(&path)?;
            println!("Commit message is valid.");
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
