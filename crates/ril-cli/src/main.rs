#![forbid(unsafe_code)]

use std::{
    io::{IsTerminal as _, Write as _},
    path::{Path, PathBuf},
    process::{Command, ExitCode},
    time::{Duration, Instant, SystemTime},
};

use clap::{Parser, Subcommand, ValueEnum};
use ril_driver::{CompileOptions, Driver, OptLevel, infer_unit, load_package};
use ril_source::diag::Diagnostic;
use ril_test::{Stage, Unit};

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

#[derive(Clone, Copy, ValueEnum)]
enum MessageFormat {
    Human,
    Json,
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
        #[arg(long)]
        emit_interface_json: Option<PathBuf>,
        #[arg(long)]
        opt_stack_promote: bool,
        #[arg(long, num_args = 0..=1, default_missing_value = ".ril-cache", value_name = "CACHE_DIR")]
        incremental: Option<PathBuf>,
        #[arg(long, value_enum, default_value = "human")]
        message_format: MessageFormat,
        #[arg(long)]
        timings: bool,
        #[arg(long)]
        watch: bool,
    },
    Build {
        path: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
        #[arg(long, value_name = "OBJECT_OR_LIBRARY")]
        link: Vec<PathBuf>,
        #[arg(long)]
        opt_stack_promote: bool,
        #[arg(long)]
        release: bool,
        #[arg(short = 'O', value_name = "0|1|2|s")]
        opt: Option<String>,
        #[arg(long, default_value_t = 1)]
        cgus: usize,
        #[arg(long, num_args = 0..=1, default_missing_value = ".ril-cache", value_name = "CACHE_DIR")]
        incremental: Option<PathBuf>,
        #[arg(long)]
        timings: bool,
    },
    Fmt {
        #[arg(required = true)]
        paths: Vec<PathBuf>,
        #[arg(long)]
        check: bool,
    },
    Inspect {
        path: PathBuf,
        #[arg(long)]
        unit: Option<Unit>,
        #[arg(long = "file", value_name = "PATH")]
        files: Vec<String>,
        #[arg(long = "symbol", value_name = "NAME")]
        symbols: Vec<String>,
        #[arg(long = "at", value_name = "LOC")]
        at: Vec<String>,
        #[arg(long)]
        symbols_only: bool,
        #[arg(long = "include", value_name = "SECTION")]
        includes: Vec<String>,
        #[arg(long, num_args = 0..=1, default_missing_value = ".ril-cache", value_name = "CACHE_DIR")]
        incremental: Option<PathBuf>,
        #[arg(long)]
        pretty: bool,
        #[arg(long)]
        fail_on_error: bool,
    },
    Lsp,
    Run {
        path: PathBuf,
        #[arg(long, value_enum, default_value = "jit")]
        backend: Backend,
        #[arg(long, value_name = "OBJECT_OR_LIBRARY")]
        link: Vec<PathBuf>,
        #[arg(long)]
        opt_stack_promote: bool,
        #[arg(long)]
        release: bool,
        #[arg(short = 'O', value_name = "0|1|2|s")]
        opt: Option<String>,
        #[arg(long, num_args = 0..=1, default_missing_value = ".ril-cache", value_name = "CACHE_DIR")]
        incremental: Option<PathBuf>,
    },
    EmitIr {
        path: PathBuf,
        #[arg(long, value_enum, default_value = "mir")]
        format: IrFormat,
        #[arg(long)]
        opt_stack_promote: bool,
        #[arg(long)]
        release: bool,
        #[arg(short = 'O', value_name = "0|1|2|s")]
        opt: Option<String>,
        #[arg(long, num_args = 0..=1, default_missing_value = ".ril-cache", value_name = "CACHE_DIR")]
        incremental: Option<PathBuf>,
    },
    Test {
        path: Option<PathBuf>,
        #[arg(long, conflicts_with = "doc")]
        sync_spec_md: bool,
        #[arg(long, conflicts_with = "sync_spec_md")]
        doc: bool,
        #[arg(long)]
        stage: Option<Stage>,
        #[arg(long)]
        opt_stack_promote: bool,
    },
}

fn parse_opt_level(release: bool, opt: Option<&str>) -> Result<(OptLevel, bool), String> {
    match opt {
        Some("0") => Ok((OptLevel::None, false)),
        Some("1" | "2") => Ok((OptLevel::Speed, true)),
        Some("s" | "z") => Ok((OptLevel::SpeedAndSize, true)),
        Some(other) => Err(format!(
            "invalid optimization level `-O {other}` (expected 0, 1, 2, or s)"
        )),
        None if release => Ok((OptLevel::Speed, true)),
        None => Ok((OptLevel::None, false)),
    }
}

fn compiler_for(
    opt_stack_promote: bool,
    opt_level: OptLevel,
    incremental: Option<PathBuf>,
) -> ril_driver::Compiler {
    let options = CompileOptions {
        opt_stack_promote,
        opt_level,
    };
    match incremental {
        Some(dir) => Driver.with_disk_cache(options, dir),
        None => Driver.with_options(options),
    }
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
            emit_interface_json,
            opt_stack_promote,
            incremental,
            message_format,
            timings,
            watch,
        } => {
            let compiler = compiler_for(opt_stack_promote, OptLevel::None, incremental);
            let run_once = || -> Result<ExitCode, String> {
                let t0 = Instant::now();
                let package = load_package(&path, unit.unwrap_or_else(|| infer_unit(&path)))?;
                let t_load = t0.elapsed();
                let t1 = Instant::now();
                let checked = compiler.check(&package, stage);
                let t_check = t1.elapsed();
                let use_color = std::io::stderr().is_terminal();
                for diagnostic in &checked.result.diagnostics {
                    match message_format {
                        MessageFormat::Human => {
                            diagnostic
                                .render_with_color(
                                    &checked.sources,
                                    use_color,
                                    std::io::stderr().lock(),
                                )
                                .map_err(|err| err.to_string())?;
                        }
                        MessageFormat::Json => {
                            writeln!(
                                std::io::stderr().lock(),
                                "{}",
                                diagnostic.to_json_line(&checked.sources)
                            )
                            .map_err(|err| err.to_string())?;
                        }
                    }
                }
                if timings {
                    eprintln!(
                        "timings: load={:.2}ms check={:.2}ms total={:.2}ms",
                        t_load.as_secs_f64() * 1000.0,
                        t_check.as_secs_f64() * 1000.0,
                        t0.elapsed().as_secs_f64() * 1000.0,
                    );
                }
                if !checked.result.diagnostics.is_empty() {
                    return Ok(ExitCode::FAILURE);
                }
                if emit_interface.is_some() || emit_interface_json.is_some() {
                    let interface = compiler.interface_arc(&package).map_err(display)?;
                    if let Some(ref out_path) = emit_interface {
                        let bytes = interface.encode().map_err(|err| err.to_string())?;
                        std::fs::write(out_path, bytes).map_err(|err| err.to_string())?;
                    }
                    if let Some(ref out_path) = emit_interface_json {
                        let bytes = interface.encode_json().map_err(|err| err.to_string())?;
                        std::fs::write(out_path, bytes).map_err(|err| err.to_string())?;
                    }
                }
                Ok(ExitCode::SUCCESS)
            };
            if watch {
                let mut last_mtime = file_mtime(&path);
                let _ = run_once()?;
                loop {
                    std::thread::sleep(Duration::from_millis(250));
                    let current = file_mtime(&path);
                    if current != last_mtime {
                        last_mtime = current;
                        eprintln!("--- change detected, re-checking {} ---", path.display());
                        let _ = run_once()?;
                    }
                }
            } else {
                return run_once();
            }
        }
        Action::Build {
            path,
            output,
            link,
            opt_stack_promote,
            release,
            opt,
            cgus,
            incremental,
            timings,
        } => {
            let t0 = Instant::now();
            let (opt_level, default_promote) = parse_opt_level(release, opt.as_deref())?;
            let compiler =
                compiler_for(opt_stack_promote || default_promote, opt_level, incremental);
            let package = load_package(&path, Unit::Bin)?;
            let t_load = t0.elapsed();
            let output =
                output.unwrap_or_else(|| path.with_extension(std::env::consts::EXE_EXTENSION));
            if same_file(&path, &output) {
                return Err("output would overwrite the source file".into());
            }
            let t1 = Instant::now();
            compiler
                .compile_aot_with_cgus(&package, &output, &link, cgus)
                .map_err(display)?;
            if timings {
                eprintln!(
                    "timings: load={:.2}ms build={:.2}ms total={:.2}ms (cgus={})",
                    t_load.as_secs_f64() * 1000.0,
                    t1.elapsed().as_secs_f64() * 1000.0,
                    t0.elapsed().as_secs_f64() * 1000.0,
                    cgus.max(1),
                );
            }
        }
        Action::Fmt { paths, check } => {
            let mut files = Vec::new();
            for path in paths {
                collect_ril_files(&path, &mut files)?;
            }
            files.sort();
            files.dedup();
            let mut needs_formatting = false;
            for path in files {
                let original = std::fs::read_to_string(&path)
                    .map_err(|e| format!("{}: {e}", path.display()))?;
                if original
                    .lines()
                    .find(|line| !line.trim().is_empty())
                    .is_some_and(|first| first.trim_start().starts_with("-- @suite"))
                {
                    continue;
                }
                let formatted = ril_driver::format_file(&path)?;
                if formatted != original {
                    if check {
                        eprintln!("would reformat {}", path.display());
                        needs_formatting = true;
                    } else {
                        std::fs::write(&path, formatted)
                            .map_err(|e| format!("{}: {e}", path.display()))?;
                    }
                }
            }
            if check && needs_formatting {
                return Ok(ExitCode::FAILURE);
            }
        }
        Action::Inspect {
            path,
            unit,
            files,
            symbols,
            at,
            symbols_only,
            includes,
            incremental,
            pretty,
            fail_on_error,
        } => {
            let mut parsed_at = Vec::with_capacity(at.len());
            for raw in &at {
                match ril_driver::inspect::AtQuery::parse(raw) {
                    Ok(loc) => parsed_at.push(loc),
                    Err(err) => {
                        println!(
                            "{}",
                            ril_driver::inspect::InspectReport::fatal_json(&err, pretty)
                        );
                        return Ok(ExitCode::from(2));
                    }
                }
            }
            let query = ril_driver::inspect::InspectQuery {
                files,
                symbols,
                at: parsed_at,
                symbols_only,
                includes,
            };
            if let Err(err) = query.validate() {
                println!(
                    "{}",
                    ril_driver::inspect::InspectReport::fatal_json(&err, pretty)
                );
                return Ok(ExitCode::from(2));
            }
            let package = match load_package(&path, unit.unwrap_or_else(|| infer_unit(&path))) {
                Ok(pkg) => pkg,
                Err(err) => {
                    println!(
                        "{}",
                        ril_driver::inspect::InspectReport::fatal_json(&err, pretty)
                    );
                    return Ok(ExitCode::from(2));
                }
            };
            let compiler = compiler_for(false, OptLevel::None, incremental);
            let report = compiler.inspect_package(&package, &query);
            println!("{}", report.to_json(pretty));
            if fail_on_error && !report.ok {
                return Ok(ExitCode::FAILURE);
            }
            return Ok(ExitCode::SUCCESS);
        }
        Action::Lsp => {
            ril_lsp::serve_stdio()?;
        }
        Action::Run {
            path,
            backend,
            link,
            opt_stack_promote,
            release,
            opt,
            incremental,
        } => {
            if matches!(backend, Backend::Jit) && !link.is_empty() {
                return Err("select --backend aot to use --link".into());
            }
            let (opt_level, default_promote) = parse_opt_level(release, opt.as_deref())?;
            let compiler =
                compiler_for(opt_stack_promote || default_promote, opt_level, incremental);
            let package = load_package(&path, Unit::Bin)?;
            let output = match backend {
                Backend::Jit => compiler.execute_jit(&package).map_err(display)?,
                Backend::Aot => {
                    let dir = tempfile::tempdir().map_err(|err| err.to_string())?;
                    let output = dir
                        .path()
                        .join(format!("ril_program{}", std::env::consts::EXE_SUFFIX));
                    compiler
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
        Action::EmitIr {
            path,
            format,
            opt_stack_promote,
            release,
            opt,
            incremental,
        } => {
            let (opt_level, default_promote) = parse_opt_level(release, opt.as_deref())?;
            let compiler =
                compiler_for(opt_stack_promote || default_promote, opt_level, incremental);
            let unit = if matches!(format, IrFormat::Horn) {
                Unit::Lib
            } else {
                Unit::Bin
            };
            let package = load_package(&path, unit)?;
            let text = match format {
                IrFormat::Mir => format!("{:#?}", compiler.lower_arc(&package).map_err(display)?),
                IrFormat::Clif => compiler.clif(&package).map_err(display)?,
                IrFormat::Horn => compiler.horn_json(&package).map_err(display)?,
            };
            println!("{text}");
        }
        Action::Test {
            path,
            sync_spec_md,
            doc,
            stage,
            opt_stack_promote,
        } => return test(path, sync_spec_md, doc, stage, opt_stack_promote),
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

fn collect_ril_files(path: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if path.is_dir() {
        let entries = std::fs::read_dir(path).map_err(|e| format!("{}: {e}", path.display()))?;
        for entry in entries {
            let entry = entry.map_err(|e| format!("{}: {e}", path.display()))?;
            let child = entry.path();
            if child.is_dir() {
                if child.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
                    matches!(
                        n,
                        ".git" | "target" | ".local" | ".ril-cache" | "node_modules"
                    )
                }) {
                    continue;
                }
                collect_ril_files(&child, out)?;
            } else if child.extension().is_some_and(|ext| ext == "ril") {
                out.push(child);
            }
        }
    } else {
        out.push(path.to_owned());
    }
    Ok(())
}

fn file_mtime(path: &Path) -> Option<SystemTime> {
    std::fs::metadata(path).ok()?.modified().ok()
}

fn display(diagnostics: Vec<Diagnostic>) -> String {
    diagnostics
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn test(
    path: Option<PathBuf>,
    sync_spec_md: bool,
    doc: bool,
    stage: Option<Stage>,
    opt_stack_promote: bool,
) -> Result<ExitCode, String> {
    if !sync_spec_md && !doc && stage.is_some() {
        return Err("--stage requires --sync-spec-md or --doc".into());
    }
    let compiler = Driver.with_options(CompileOptions {
        opt_stack_promote,
        ..CompileOptions::default()
    });
    let suites = if sync_spec_md {
        let path = path.unwrap_or_else(|| PathBuf::from("doc/SPEC.md"));
        let source =
            std::fs::read_to_string(&path).map_err(|err| format!("{}: {err}", path.display()))?;
        vec![ril_test::spec_suite(
            &path,
            &source,
            stage.unwrap_or(Stage::Parse),
        )?]
    } else if doc {
        let path = path.unwrap_or_else(|| PathBuf::from("std"));
        ril_test::discover_doc(&path, stage.unwrap_or(Stage::Access))?
    } else {
        ril_test::discover(&path.unwrap_or_else(|| PathBuf::from("tests")))?
    };
    let mut failed = 0;
    let mut passed = 0;
    for suite in suites {
        for case in suite.cases {
            if let Err(error) = ril_test::run_case(&case, &compiler) {
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
    println!("{passed} passed, {failed} failed");
    Ok(if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}
