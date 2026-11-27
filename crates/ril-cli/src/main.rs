#![forbid(unsafe_code)]

use std::{
    io::{IsTerminal as _, Write as _},
    path::{Path, PathBuf},
    process::{Command, ExitCode},
    time::{Duration, Instant, SystemTime},
};

use clap::{Parser, Subcommand, ValueEnum};
use ril_driver::{CompileOptions, Driver, OptLevel, infer_unit, load_package};
use ril_source::diag::{Diagnostic, Severity};
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

#[derive(Clone, Copy, ValueEnum)]
enum FixFilterArg {
    All,
    Errors,
    Lints,
    Sigs,
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
        #[arg(required_unless_present = "stdin", conflicts_with = "stdin")]
        paths: Vec<PathBuf>,
        #[arg(long)]
        check: bool,
        #[arg(long)]
        diff: bool,
        #[arg(long)]
        stdin: bool,
        #[arg(long, value_enum, default_value = "human")]
        message_format: MessageFormat,
    },
    Lint {
        #[arg(required_unless_present = "list_rules")]
        path: Option<PathBuf>,
        #[arg(long)]
        unit: Option<Unit>,
        #[arg(long, value_name = "TOML")]
        config: Option<PathBuf>,
        #[arg(long = "allow", value_name = "RULE|CATEGORY|all")]
        allow: Vec<String>,
        #[arg(long = "warn", value_name = "RULE|CATEGORY|all")]
        warn: Vec<String>,
        #[arg(long = "deny", value_name = "RULE|CATEGORY|warnings|all")]
        deny: Vec<String>,
        #[arg(long, value_enum, default_value = "human")]
        message_format: MessageFormat,
        #[arg(long, num_args = 0..=1, default_missing_value = ".ril-cache", value_name = "CACHE_DIR")]
        incremental: Option<PathBuf>,
        #[arg(long)]
        list_rules: bool,
        #[arg(long)]
        timings: bool,
    },
    Fix {
        path: PathBuf,
        #[arg(long)]
        unit: Option<Unit>,
        #[arg(long, value_enum, default_value = "all")]
        only: FixFilterArg,
        #[arg(long = "code", value_name = "CODE|RULE")]
        codes: Vec<String>,
        #[arg(long)]
        no_sigs: bool,
        #[arg(long)]
        allow_api_change: bool,
        #[arg(long = "unsafe")]
        allow_unsafe: bool,
        #[arg(long)]
        dry_run: bool,
        #[arg(long)]
        check: bool,
        #[arg(long)]
        diff: bool,
        #[arg(long)]
        fmt: bool,
        #[arg(long, value_name = "TOML")]
        config: Option<PathBuf>,
        #[arg(long, value_enum, default_value = "human")]
        message_format: MessageFormat,
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
                if checked
                    .result
                    .diagnostics
                    .iter()
                    .any(|diag| diag.severity == Severity::Error)
                {
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
                let mut last_state = watch_fingerprint(&path);
                let _ = run_once()?;
                loop {
                    std::thread::sleep(Duration::from_millis(250));
                    let current = watch_fingerprint(&path);
                    if current != last_state {
                        last_state = current;
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
        Action::Fmt {
            paths,
            check,
            diff,
            stdin,
            message_format,
        } => {
            let use_color = std::io::stderr().is_terminal();
            if stdin {
                let mut buf = Vec::new();
                std::io::Read::read_to_end(&mut std::io::stdin().lock(), &mut buf)
                    .map_err(|e| format!("<stdin>: {e}"))?;
                let original = String::from_utf8(buf).map_err(|e| format!("<stdin>: {e}"))?;
                if ril_syntax::directive::is_suite_file(&original) {
                    std::io::stdout()
                        .write_all(original.as_bytes())
                        .map_err(|e| e.to_string())?;
                    return Ok(ExitCode::SUCCESS);
                }
                let logical = PathBuf::from("<stdin>");
                let mut sources = ril_source::span::SourceMap::default();
                let file_id = match sources.add(logical, original.as_bytes()) {
                    Ok(id) => id,
                    Err(diag) => {
                        render_diagnostic(&diag, &sources, message_format, use_color)?;
                        return Ok(ExitCode::from(2));
                    }
                };
                let Some(source) = sources.get(file_id) else {
                    return Ok(ExitCode::from(2));
                };
                match ril_syntax::fmt::format_source_auto(source) {
                    Ok(formatted) => {
                        if diff {
                            print!(
                                "{}",
                                ril_syntax::fmt::unified_diff("<stdin>", &original, &formatted)
                            );
                        } else if !check {
                            std::io::stdout()
                                .write_all(formatted.as_bytes())
                                .map_err(|e| e.to_string())?;
                        }
                        if (check || diff) && formatted != original {
                            if check {
                                match message_format {
                                    MessageFormat::Human => eprintln!("would reformat <stdin>"),
                                    MessageFormat::Json => {
                                        eprintln!(
                                            "{{\"kind\":\"unformatted\",\"path\":\"<stdin>\"}}"
                                        );
                                    }
                                }
                            }
                            return Ok(ExitCode::FAILURE);
                        }
                        return Ok(ExitCode::SUCCESS);
                    }
                    Err(diags) => {
                        for diag in &diags {
                            render_diagnostic(diag, &sources, message_format, use_color)?;
                        }
                        return Ok(ExitCode::from(2));
                    }
                }
            }

            let mut files = Vec::new();
            for path in paths {
                collect_ril_files(&path, &mut files)?;
            }
            files.sort();
            files.dedup();
            let mut needs_formatting = false;
            let mut had_error = false;
            for path in files {
                let bytes = match std::fs::read(&path) {
                    Ok(b) => b,
                    Err(e) => {
                        eprintln!("{}: {e}", path.display());
                        had_error = true;
                        continue;
                    }
                };
                let original = match String::from_utf8(bytes.clone()) {
                    Ok(s) => s,
                    Err(e) => {
                        eprintln!("{}: {e}", path.display());
                        had_error = true;
                        continue;
                    }
                };
                if ril_syntax::directive::is_suite_file(&original) {
                    continue;
                }
                let mut sources = ril_source::span::SourceMap::default();
                let file_id = match sources.add(path.clone(), &bytes) {
                    Ok(id) => id,
                    Err(diag) => {
                        render_diagnostic(&diag, &sources, message_format, use_color)?;
                        had_error = true;
                        continue;
                    }
                };
                let Some(source) = sources.get(file_id) else {
                    had_error = true;
                    continue;
                };
                let formatted = match ril_syntax::fmt::format_source_auto(source) {
                    Ok(f) => f,
                    Err(diags) => {
                        for diag in &diags {
                            render_diagnostic(diag, &sources, message_format, use_color)?;
                        }
                        had_error = true;
                        continue;
                    }
                };
                if formatted != original {
                    if diff {
                        let label = path.display().to_string();
                        print!(
                            "{}",
                            ril_syntax::fmt::unified_diff(&label, &original, &formatted)
                        );
                        needs_formatting = true;
                    } else if check {
                        match message_format {
                            MessageFormat::Human => {
                                eprintln!("would reformat {}", path.display());
                            }
                            MessageFormat::Json => {
                                let escaped = serde_json::to_string(&path.display().to_string())
                                    .unwrap_or_else(|_| "\"\"".to_owned());
                                eprintln!("{{\"kind\":\"unformatted\",\"path\":{escaped}}}");
                            }
                        }
                        needs_formatting = true;
                    } else {
                        std::fs::write(&path, formatted)
                            .map_err(|e| format!("{}: {e}", path.display()))?;
                    }
                }
            }
            if had_error {
                return Ok(ExitCode::from(2));
            }
            if (check || diff) && needs_formatting {
                return Ok(ExitCode::FAILURE);
            }
        }
        Action::Lint {
            path,
            unit,
            config,
            allow,
            warn,
            deny,
            message_format,
            incremental,
            list_rules,
            timings,
        } => {
            if list_rules {
                for desc in ril_lint::ALL_LINTS {
                    let fix_tag = desc.fix_safety.map_or("none", |s| s.as_str());
                    println!(
                        "{:<30} {:<12} {:<6} fix={:<6} {}",
                        desc.id,
                        desc.category.as_str(),
                        desc.default_level.as_str(),
                        fix_tag,
                        desc.summary
                    );
                }
                return Ok(ExitCode::SUCCESS);
            }
            let Some(path) = path else {
                eprintln!("missing <PATH> argument");
                return Ok(ExitCode::from(2));
            };
            let mut lint_cfg = if let Some(cfg_path) = config {
                let text = std::fs::read_to_string(&cfg_path)
                    .map_err(|e| format!("{}: {e}", cfg_path.display()))?;
                match ril_driver::parse_manifest(&text) {
                    Ok(m) => m.lint,
                    Err(e) => {
                        eprintln!("{e}");
                        return Ok(ExitCode::from(2));
                    }
                }
            } else {
                ril_driver::find_manifest_for(&path)
                    .map(|(_, m)| m.lint)
                    .unwrap_or_default()
            };
            for raw in allow {
                match ril_lint::LintConfig::parse_cli_override(ril_lint::LintLevel::Allow, &raw) {
                    Ok(ov) => lint_cfg.cli_overrides.push(ov),
                    Err(e) => {
                        eprintln!("{e}");
                        return Ok(ExitCode::from(2));
                    }
                }
            }
            for raw in warn {
                match ril_lint::LintConfig::parse_cli_override(ril_lint::LintLevel::Warn, &raw) {
                    Ok(ov) => lint_cfg.cli_overrides.push(ov),
                    Err(e) => {
                        eprintln!("{e}");
                        return Ok(ExitCode::from(2));
                    }
                }
            }
            for raw in deny {
                match ril_lint::LintConfig::parse_cli_override(ril_lint::LintLevel::Deny, &raw) {
                    Ok(ov) => lint_cfg.cli_overrides.push(ov),
                    Err(e) => {
                        eprintln!("{e}");
                        return Ok(ExitCode::from(2));
                    }
                }
            }

            let t0 = Instant::now();
            let package = load_package(&path, unit.unwrap_or_else(|| infer_unit(&path)))?;
            let t_load = t0.elapsed();
            let t1 = Instant::now();
            let compiler = compiler_for(false, OptLevel::None, incremental);
            let linted = compiler.lint_package(&package, &lint_cfg);
            let t_lint = t1.elapsed();
            let use_color = std::io::stderr().is_terminal();

            let mut fixable_count = 0usize;
            for diag in &linted.partial.diagnostics {
                if diag
                    .fixes()
                    .iter()
                    .any(|f| f.safety == ril_source::fix::FixSafety::Safe)
                {
                    fixable_count += 1;
                }
                render_diagnostic(diag, &linted.partial.sources, message_format, use_color)?;
            }
            for diag in &linted.lint.diagnostics {
                if diag
                    .fixes
                    .iter()
                    .any(|f| f.safety == ril_source::fix::FixSafety::Safe)
                {
                    fixable_count += 1;
                }
                match message_format {
                    MessageFormat::Human => {
                        diag.render_with_color(
                            &linted.partial.sources,
                            use_color,
                            std::io::stderr().lock(),
                        )
                        .map_err(|e| e.to_string())?;
                    }
                    MessageFormat::Json => {
                        writeln!(
                            std::io::stdout().lock(),
                            "{}",
                            diag.to_json_line(&linted.partial.sources)
                        )
                        .map_err(|e| e.to_string())?;
                    }
                }
            }
            if matches!(message_format, MessageFormat::Human) && fixable_count > 0 {
                eprintln!(
                    "hint: {fixable_count} issue(s) are auto-fixable; run `ril fix {}`",
                    path.display()
                );
            }
            if timings {
                eprintln!(
                    "timings: load={:.2}ms lint={:.2}ms total={:.2}ms",
                    t_load.as_secs_f64() * 1000.0,
                    t_lint.as_secs_f64() * 1000.0,
                    t0.elapsed().as_secs_f64() * 1000.0,
                );
            }
            let has_errors = linted
                .partial
                .diagnostics
                .iter()
                .any(|d| d.severity == Severity::Error);
            if has_errors || linted.lint.has_denied() {
                return Ok(ExitCode::FAILURE);
            }
        }
        Action::Fix {
            path,
            unit,
            only,
            codes,
            no_sigs,
            allow_api_change,
            allow_unsafe,
            dry_run,
            check,
            diff,
            fmt,
            config,
            message_format,
        } => {
            let lint_cfg = if let Some(cfg_path) = config {
                let text = std::fs::read_to_string(&cfg_path)
                    .map_err(|e| format!("{}: {e}", cfg_path.display()))?;
                match ril_driver::parse_manifest(&text) {
                    Ok(m) => m.lint,
                    Err(e) => {
                        eprintln!("{e}");
                        return Ok(ExitCode::from(2));
                    }
                }
            } else {
                ril_driver::find_manifest_for(&path)
                    .map(|(_, m)| m.lint)
                    .unwrap_or_default()
            };
            let filter = match only {
                FixFilterArg::All => ril_driver::fix::FixFilter::All,
                FixFilterArg::Errors => ril_driver::fix::FixFilter::Errors,
                FixFilterArg::Lints => ril_driver::fix::FixFilter::Lints,
                FixFilterArg::Sigs => ril_driver::fix::FixFilter::Sigs,
            };
            let options = ril_driver::fix::FixOptions {
                filter,
                codes: codes.into_iter().collect(),
                no_sigs,
                allow_api_change,
                allow_unsafe,
                dry_run: dry_run || check || diff,
                fmt_after: fmt,
                max_passes: 12,
            };
            let compiler = compiler_for(false, OptLevel::None, None);
            let report = ril_driver::fix::fix_package_files(
                &compiler,
                &path,
                unit.unwrap_or_else(|| infer_unit(&path)),
                &options,
                &lint_cfg,
            )?;

            match message_format {
                MessageFormat::Json => {
                    let json = serde_json::to_string(&report).map_err(|e| e.to_string())?;
                    println!("{json}");
                }
                MessageFormat::Human => {
                    if !report.syntax_errors.is_empty() {
                        eprintln!("ril fix refused: fix syntax errors first");
                        for err in &report.syntax_errors {
                            eprint!("{err}");
                        }
                        return Ok(ExitCode::from(2));
                    }
                    if diff {
                        for file in &report.modified_files {
                            print!(
                                "{}",
                                ril_syntax::fmt::unified_diff(
                                    &file.path,
                                    &file.original,
                                    &file.updated
                                )
                            );
                        }
                    }
                    if let Some(banner) = report.format_capability_banner() {
                        eprint!("{banner}");
                    }
                    for skip in &report.skipped {
                        let cause = skip
                            .capability_delta
                            .as_ref()
                            .filter(|d| d.causal_chain.len() > 1)
                            .map(|d| format!(" (via {})", d.causal_chain.join(" -> ")))
                            .unwrap_or_default();
                        eprintln!(
                            "skipped [{}] {} ({}): {}{cause}",
                            skip.code, skip.title, skip.file, skip.reason
                        );
                    }
                    if report.oscillated {
                        eprintln!(
                            "warning: fix loop stopped early after {} pass(es) due to edit oscillation",
                            report.passes
                        );
                    }
                    let mode_label = if options.dry_run {
                        "would apply"
                    } else {
                        "applied"
                    };
                    eprintln!(
                        "{mode_label} {} fix(es) across {} file(s) in {} pass(es); {} remaining error(s), {} warning(s)",
                        report.applied.len(),
                        report.modified_files.len(),
                        report.passes,
                        report.remaining_errors.len(),
                        report.remaining_warnings.len()
                    );
                }
            }

            if !report.syntax_errors.is_empty() {
                return Ok(ExitCode::from(2));
            }
            if (check && !report.modified_files.is_empty()) || !report.remaining_errors.is_empty() {
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

fn file_stamp(path: &Path) -> Option<(SystemTime, u64)> {
    let meta = std::fs::metadata(path).ok()?;
    Some((meta.modified().ok()?, meta.len()))
}

fn watch_fingerprint(path: &Path) -> Vec<(PathBuf, Option<(SystemTime, u64)>)> {
    let mut watched = Vec::new();
    let root = if path.is_dir() {
        path.to_path_buf()
    } else {
        path.parent()
            .map_or_else(|| path.to_path_buf(), Path::to_path_buf)
    };
    let mut files = Vec::new();
    let _ = collect_ril_files(&root, &mut files);
    files.sort();
    files.dedup();
    for file in files {
        let stamp = file_stamp(&file);
        watched.push((file, stamp));
    }
    for ancestor in root.ancestors() {
        let manifest = ancestor.join("ril.toml");
        if manifest.is_file() {
            let stamp = file_stamp(&manifest);
            watched.push((manifest, stamp));
            break;
        }
    }
    if watched.is_empty() {
        watched.push((path.to_path_buf(), file_stamp(path)));
    }
    watched
}

fn render_diagnostic(
    diagnostic: &Diagnostic,
    sources: &ril_source::span::SourceMap,
    message_format: MessageFormat,
    use_color: bool,
) -> Result<(), String> {
    match message_format {
        MessageFormat::Human => diagnostic
            .render_with_color(sources, use_color, std::io::stderr().lock())
            .map_err(|err| err.to_string()),
        MessageFormat::Json => writeln!(
            std::io::stderr().lock(),
            "{}",
            diagnostic.to_json_line(sources)
        )
        .map_err(|err| err.to_string()),
    }
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
