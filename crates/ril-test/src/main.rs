mod suite;

use ril_compiler::{frontend::frontend, input::SourceIndex, types::TypeTemplates};
use std::{
    env, fs, io,
    path::{Path, PathBuf},
    process::ExitCode,
};
use suite::{Case, Mode, parse_suite};

fn main() -> ExitCode {
    match run() {
        Ok(0) => ExitCode::SUCCESS,
        Ok(_) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("ril-test: {error}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<usize, Box<dyn std::error::Error>> {
    let mut selections = env::args().skip(1).collect::<Vec<_>>();
    if selections.iter().any(|arg| arg == "--help" || arg == "-h") {
        println!("Usage: ril-test [DIRECTORY | FILE.ril[#CASE]] ...");
        return Ok(0);
    }
    if selections.is_empty() {
        selections = ["tests/conformance", "tests/stdlib", "tests/regressions"]
            .into_iter()
            .filter(|path| Path::new(path).exists())
            .map(str::to_owned)
            .collect();
    }
    let mut passed = 0;
    let mut failed = 0;
    for selection in selections {
        let (path, name) = selection
            .split_once('#')
            .map_or((selection.as_str(), None), |(path, name)| {
                (path, Some(name))
            });
        let mut suites = vec![];
        discover(Path::new(path), &mut suites)?;
        suites.sort();
        let mut selected = 0;
        for path in suites {
            let bytes = fs::read(&path)?;
            let cases =
                parse_suite(&bytes).map_err(|error| format!("{}:{error}", path.display()))?;
            for case in cases {
                if name.is_some_and(|name| {
                    name != case.name
                        && !case
                            .name
                            .strip_prefix(name)
                            .is_some_and(|suffix| matches!(suffix, "/accept" | "/reject"))
                }) {
                    continue;
                }
                selected += 1;
                match run_case(&case) {
                    Ok(()) => passed += 1,
                    Err(error) => {
                        failed += 1;
                        eprintln!("{}:{} [{}] {error}", path.display(), case.line, case.name);
                    }
                }
            }
        }
        if selected == 0 {
            return Err(format!("'{selection}' selected no cases").into());
        }
    }
    if passed + failed == 0 {
        return Err("no corpus cases found".into());
    }
    println!("{passed} passed, {failed} failed");
    Ok(failed)
}

fn discover(path: &Path, suites: &mut Vec<PathBuf>) -> io::Result<()> {
    if path.is_dir() {
        for child in fs::read_dir(path)? {
            let child = child?;
            if !child.file_type()?.is_symlink() {
                discover(&child.path(), suites)?;
            }
        }
    } else if path.extension().is_some_and(|extension| extension == "ril") {
        path.metadata()?;
        suites.push(path.to_owned());
    }
    Ok(())
}

fn run_case(case: &Case) -> Result<(), String> {
    if let Mode::Later(mode) = &case.mode {
        return Err(format!("mode '{mode}' requires a later compiler stage"));
    }
    let result = frontend(Path::new("root.ril"), case.kind, |path| {
        case.files
            .get(path)
            .map(|file| file.bytes.clone())
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))
    })
    .map_err(|error| error.to_string())?;
    let describe = || {
        result
            .diagnostics
            .iter()
            .map(|diagnostic| {
                let location = diagnostic
                    .labels
                    .first()
                    .and_then(|label| {
                        let source = result.sources.get(label.span.file)?;
                        let file = case.files.get(source.path())?;
                        let line = file.suite_line(label.span.start as usize)?;
                        Some(format!("line {line} "))
                    })
                    .unwrap_or_default();
                format!("{location}{} {}", diagnostic.code, diagnostic.message)
            })
            .collect::<Vec<_>>()
            .join("\n  ")
    };
    match case.mode {
        Mode::FrontPass if !result.is_ok() => Err(format!("expected HIR\n  {}", describe())),
        Mode::FrontPass => {
            let input = SourceIndex::new(&result)
                .map_err(|error| format!("incomplete checking inputs: {error}"))?;
            TypeTemplates::lower(&input)
                .map(|_| ())
                .map_err(|error| error.to_string())
        }
        Mode::FrontFail => {
            if result.is_ok() {
                return Err("expected frontend rejection".into());
            }
            for expected in &case.errors {
                let found = result.diagnostics.iter().any(|diagnostic| {
                    if diagnostic.code != expected.code {
                        return false;
                    }
                    expected.line.is_none_or(|line| {
                        diagnostic.labels.iter().any(|label| {
                            result
                                .sources
                                .get(label.span.file)
                                .and_then(|source| case.files.get(source.path()))
                                .and_then(|file| file.suite_line(label.span.start as usize))
                                == Some(line)
                        })
                    })
                });
                if !found {
                    return Err(format!(
                        "missing expected {}{}\n  {}",
                        expected.code,
                        expected
                            .line
                            .map(|line| format!(" at line {line}"))
                            .unwrap_or_default(),
                        describe()
                    ));
                }
            }
            for diagnostic in &result.diagnostics {
                if !case
                    .errors
                    .iter()
                    .any(|expected| expected.code == diagnostic.code)
                {
                    return Err(format!("unexpected diagnostic\n  {}", describe()));
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}
