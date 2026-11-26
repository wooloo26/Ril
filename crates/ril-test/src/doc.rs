use std::path::{Path, PathBuf};

use crate::{Case, CaseMode, Stage, Suite, Unit, VirtualPackage};

/// Extracts fenced ```` ```ril ```` code examples from contiguous `--` doc comments
/// in a single `.ril` source file and turns them into `Unit::Snippet` test cases.
///
/// Supported info-string modifiers on `ril` fences:
/// - ```` ```ril ```` — compile-check at `stage` (default `Stage::Access`).
/// - ```` ```ril,no_run ```` — compile-check at `stage` (never executed).
/// - ```` ```ril,ignore ```` — skip this example.
pub fn doc_suite(path: &Path, source: &str, stage: Stage) -> Result<Option<Suite>, String> {
    #[derive(Clone, Copy)]
    enum FenceKind {
        Check,
        Ignore,
        Other,
    }

    let mut open: Option<(usize, usize, FenceKind)> = None;
    let mut snippet: Vec<(usize, String)> = Vec::new();
    let mut cases = Vec::new();

    for (index, raw_line) in source.split_inclusive('\n').enumerate() {
        let current = index + 1;
        let trimmed = raw_line.trim_start();
        if let Some(after_dashes) = trimmed.strip_prefix("--") {
            let content = after_dashes.strip_prefix(' ').unwrap_or(after_dashes);
            let fence_text = content.trim();
            let ticks = fence_text.bytes().take_while(|&b| b == b'`').count();

            if let Some((count, start, kind)) = open {
                if ticks >= count && fence_text.get(ticks..).is_some_and(str::is_empty) {
                    if matches!(kind, FenceKind::Check) {
                        cases.push(make_doc_case(stage, start, &snippet));
                    }
                    snippet.clear();
                    open = None;
                } else if matches!(kind, FenceKind::Check) {
                    let mut code = content.to_owned();
                    if !code.ends_with('\n') {
                        code.push('\n');
                    }
                    snippet.push((current, code));
                }
            } else if ticks >= 3 {
                let info = fence_text.get(ticks..).unwrap_or("").trim();
                let mut parts = info
                    .split(',')
                    .map(str::trim)
                    .filter(|part| !part.is_empty());
                let kind = match parts.next() {
                    Some("ril") => {
                        let mut ignored = false;
                        for flag in parts {
                            match flag {
                                "ignore" => ignored = true,
                                "no_run" => {}
                                other => {
                                    return Err(format!(
                                        "{}:{current}: unknown ril doc-test fence modifier {other:?}",
                                        path.display()
                                    ));
                                }
                            }
                        }
                        if ignored {
                            FenceKind::Ignore
                        } else {
                            FenceKind::Check
                        }
                    }
                    _ => FenceKind::Other,
                };
                open = Some((ticks, current, kind));
            }
        } else if let Some((_, start, _)) = open {
            return Err(format!(
                "{}:{start}: unclosed doc-comment code fence",
                path.display()
            ));
        }
    }

    if let Some((_, start, _)) = open {
        return Err(format!(
            "{}:{start}: unclosed doc-comment code fence",
            path.display()
        ));
    }

    if cases.is_empty() {
        return Ok(None);
    }

    let name = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("doc")
        .to_owned();
    Ok(Some(Suite {
        name: format!("doc/{name}"),
        path: path.to_path_buf(),
        cases,
    }))
}

/// Discovers `.ril` files under `path` (or checks a single `.ril` file) and collects
/// all doc-comment code example suites.
pub fn discover_doc(path: &Path, stage: Stage) -> Result<Vec<Suite>, String> {
    let mut files = Vec::new();
    collect_ril_files(path, &mut files)?;
    files.sort();
    let mut suites = Vec::new();
    for file in files {
        let source =
            std::fs::read_to_string(&file).map_err(|err| format!("{}: {err}", file.display()))?;
        if let Some(suite) = doc_suite(&file, &source, stage)? {
            suites.push(suite);
        }
    }
    Ok(suites)
}

fn collect_ril_files(path: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if path.is_dir() {
        let entries =
            std::fs::read_dir(path).map_err(|err| format!("{}: {err}", path.display()))?;
        for entry in entries {
            let entry = entry.map_err(|err| format!("{}: {err}", path.display()))?;
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
        out.push(path.to_path_buf());
    }
    Ok(())
}

fn make_doc_case(stage: Stage, line: usize, snippet: &[(usize, String)]) -> Case {
    let mut pkg = VirtualPackage::new(Unit::Snippet);
    let file = pkg.files.entry(pkg.entry.clone()).or_default();
    for (number, source) in snippet {
        file.push(source, *number);
    }
    Case::spec(
        format!("line_{line}"),
        line,
        CaseMode::CompilePass,
        stage,
        pkg,
    )
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::doc_suite;
    use crate::Stage;

    #[test]
    fn extracts_ril_and_no_run_skips_ignore_and_other_languages() {
        let src = "\
-- Example 1
-- ```ril
-- let x = 1 + 2
-- ```
-- ```ril,no_run
-- let y = 3
-- ```
-- ```ril,ignore
-- broken @@@ syntax
-- ```
-- ```json
-- {\"a\": 1}
-- ```
pub fn f() -> () {}
";
        let suite = doc_suite(Path::new("demo.ril"), src, Stage::Access)
            .unwrap()
            .unwrap();
        assert_eq!(suite.name, "doc/demo");
        assert_eq!(suite.cases.len(), 2);
        assert_eq!(suite.cases[0].id, "line_2");
        assert_eq!(suite.cases[1].id, "line_5");
    }

    #[test]
    fn rejects_unclosed_fence_before_code_line() {
        let src = "-- ```ril\n-- let x = 1\npub fn f() -> () {}\n";
        let err = doc_suite(Path::new("bad.ril"), src, Stage::Access).unwrap_err();
        assert!(err.contains("unclosed doc-comment code fence"), "{err}");
    }
}
