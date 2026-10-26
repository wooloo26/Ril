use crate::{Case, Error, Metadata, Mode, Result, parse_bundle, require, validate_case};
use regex::Regex;
use serde::Serialize;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
    io::Write,
    path::{Path, PathBuf},
    sync::LazyLock,
};

pub fn discover_cases(base: &Path) -> Result<Vec<Case>> {
    static PATH: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"^[a-z0-9-]+(/[a-z0-9-]+)+\.ril$").unwrap());
    fn visit(base: &Path, folder: &Path, result: &mut Vec<Case>) -> Result<()> {
        require(
            !is_link(&fs::symlink_metadata(folder)?),
            format!("unexpected symlink: {}", folder.display()),
        )?;
        let mut entries = fs::read_dir(folder)?.collect::<std::io::Result<Vec<_>>>()?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            let relative = path
                .strip_prefix(base)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            let metadata = fs::symlink_metadata(&path)?;
            require(
                !is_link(&metadata),
                format!("unexpected symlink: {relative}"),
            )?;
            if metadata.is_dir() {
                visit(base, &path, result)?;
            } else {
                require(
                    metadata.is_file() && PATH.is_match(&relative),
                    format!("unexpected file in corpus: {relative}"),
                )?;
                let bytes = fs::read(&path)?;
                let text = std::str::from_utf8(&bytes)
                    .map_err(|error| Error::Invalid(format!("{relative}: {error}")))?;
                result.extend(parse_bundle(text, &format!("tests/{relative}"))?);
            }
        }
        Ok(())
    }
    let mut cases = Vec::new();
    visit(base, base, &mut cases)?;
    Ok(cases)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CorpusStats {
    pub bundles: usize,
    pub cases: usize,
    pub categories: BTreeMap<String, usize>,
    pub modes: BTreeMap<Mode, usize>,
    pub diagnostic_codes: usize,
    pub companions: usize,
}

pub fn validate_corpus(
    cases: &[Case],
    docs: &Path,
    require_all_diagnostics: bool,
) -> Result<CorpusStats> {
    static HEADINGS: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"(?m)^#{1,6} (.+)$").unwrap());
    static CODES: LazyLock<Regex> =
        LazyLock::new(|| Regex::new("(?m)^\\| \\*\\*`(E[0-9]{4})`\\*\\*").unwrap());
    require(!cases.is_empty(), "empty corpus")?;
    let documents = ["SPEC", "STD"]
        .into_iter()
        .map(|name| Ok((name, fs::read_to_string(docs.join(format!("{name}.md")))?)))
        .collect::<Result<HashMap<_, _>>>()?;
    let anchors: HashMap<_, HashSet<String>> = documents
        .iter()
        .map(|(name, text)| {
            (
                *name,
                HEADINGS
                    .captures_iter(text)
                    .map(|capture| {
                        capture[1]
                            .trim()
                            .to_lowercase()
                            .chars()
                            .filter(|c| c.is_alphanumeric() || "_ -".contains(*c))
                            .collect::<String>()
                            .replace(' ', "-")
                    })
                    .collect(),
            )
        })
        .collect();
    let known: HashSet<_> = CODES
        .captures_iter(&documents["SPEC"])
        .map(|capture| capture[1].to_owned())
        .collect();
    let (mut ids, mut codes, mut bundles) = (HashSet::new(), HashSet::new(), HashSet::new());
    let mut categories: BTreeMap<String, usize> = BTreeMap::new();
    let mut counts: BTreeMap<_, _> = Mode::ALL.into_iter().map(|mode| (mode, 0)).collect();
    for original in cases {
        let mut item = original.clone();
        validate_case(&mut item)?;
        require(
            ids.insert(item.id.clone()),
            format!("duplicate case: {}", item.id),
        )?;
        bundles.insert(item.bundle.clone());
        let category = original
            .bundle
            .strip_prefix("tests/")
            .unwrap_or(&original.bundle)
            .split('/')
            .next()
            .unwrap_or("unknown")
            .to_string();
        *categories.entry(category).or_default() += 1;
        for reference in &item.meta.spec {
            let (document, anchor) = reference.split_once('#').unwrap();
            require(
                anchors
                    .get(document)
                    .is_some_and(|values| values.contains(anchor)),
                format!("{}: unknown specification reference {reference}", item.id),
            )?;
        }
        for code in &item.errors {
            require(
                known.contains(code),
                format!("{}: unknown diagnostic {code}", item.id),
            )?;
            codes.insert(code.clone());
        }
        *counts.get_mut(&item.meta.mode).unwrap() += 1;
    }
    let mut companions = 0;
    for item in cases {
        if let Some(companion) = &item.meta.companion {
            require(
                companion != &item.name && ids.contains(&format!("{}::{companion}", item.bundle)),
                format!("{}: invalid companion", item.id),
            )?;
            companions += 1;
        }
    }
    let mut missing: Vec<_> = known.difference(&codes).cloned().collect();
    missing.sort();
    require(
        !require_all_diagnostics || missing.is_empty(),
        format!("missing diagnostic cases: {}", missing.join(", ")),
    )?;
    Ok(CorpusStats {
        bundles: bundles.len(),
        cases: cases.len(),
        categories,
        modes: counts,
        diagnostic_codes: codes.len(),
        companions,
    })
}

fn is_link(metadata: &fs::Metadata) -> bool {
    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt;
        metadata.file_attributes() & 0x400 != 0
    }
    #[cfg(not(windows))]
    {
        metadata.file_type().is_symlink()
    }
}

fn reject_link_components(path: &Path) -> Result<()> {
    for ancestor in path.ancestors() {
        match fs::symlink_metadata(ancestor) {
            Ok(metadata) => require(
                !is_link(&metadata),
                format!("output cannot traverse a symlink: {}", ancestor.display()),
            )?,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.into()),
        }
    }
    Ok(())
}

#[derive(Debug)]
pub struct ExtractedCase {
    pub directory: PathBuf,
    pub root: PathBuf,
    pub meta: Metadata,
}

pub fn extract_case(item: &Case, output: &Path) -> Result<ExtractedCase> {
    let mut item = item.clone();
    validate_case(&mut item)?;
    let absolute = std::path::absolute(output)?;
    reject_link_components(&absolute)?;
    match fs::symlink_metadata(&absolute) {
        Ok(metadata) => {
            require(metadata.is_dir(), "output must be a directory")?;
            require(
                fs::read_dir(&absolute)?.next().is_none(),
                "output directory must be empty",
            )?;
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    fs::create_dir_all(&absolute)?;
    let canonical = fs::canonicalize(absolute)?;
    for file in &item.files {
        let destination = canonical.join(&file.name);
        require(
            destination.starts_with(&canonical),
            "file path leaves output directory",
        )?;
        fs::create_dir_all(destination.parent().unwrap())?;
        reject_link_components(&destination)?;
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(destination)?
            .write_all(&file.bytes)?;
    }
    Ok(ExtractedCase {
        root: canonical.join(&item.root),
        directory: canonical,
        meta: item.meta,
    })
}

pub fn migrate_file(text: &str) -> String {
    if !text.contains("--@ case:") && !text.contains("--@ source:") {
        return text.to_string();
    }

    let mut output = Vec::new();
    let lines: Vec<&str> = text.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i];

        if let Some(source_name) = line.strip_prefix("--@ source: ") {
            let source_name = source_name.trim();
            if output.last().is_some_and(|l: &String| !l.is_empty()) {
                output.push(String::new());
            }
            output.push(format!("-- [source: {source_name}]"));
            i += 1;
            let mut s_files = Vec::new();
            while i < lines.len() {
                let s_line = lines[i];
                if s_line == "--@ end-source" {
                    i += 1;
                    break;
                }
                if let Some(rest) = s_line.strip_prefix("--@ file: ") {
                    let parts: Vec<_> = rest.split_whitespace().collect();
                    let f_name = parts[0].to_string();
                    let flag = parts.get(1).map(|s| s.to_string());
                    let mut f_lines = Vec::new();
                    i += 1;
                    while i < lines.len() {
                        let f_line = lines[i];
                        if f_line == "--@ end-file" {
                            i += 1;
                            break;
                        }
                        f_lines.push(f_line.to_string());
                        i += 1;
                    }
                    s_files.push((f_name, flag, f_lines));
                    continue;
                }
                i += 1;
            }
            for (f_idx, (f_name, flag, f_lines)) in s_files.into_iter().enumerate() {
                if f_idx > 0 {
                    output.push(String::new());
                }
                let flag_suffix = flag.map(|f| format!(" {f}")).unwrap_or_default();
                output.push(format!("-- file: {f_name}{flag_suffix}"));
                for l in f_lines {
                    output.push(l);
                }
            }
            continue;
        }

        if let Some(case_name) = line.strip_prefix("--@ case: ") {
            let case_name = case_name.trim();
            i += 1;
            let mut mode = None;
            let mut directives = Vec::new();
            let mut annotations = Vec::new();
            let mut use_source = None;
            let mut files = Vec::new();

            while i < lines.len() {
                let c_line = lines[i];
                if c_line == "--@ end-case" {
                    i += 1;
                    break;
                }
                if let Some(m) = c_line.strip_prefix("--@ mode: ") {
                    mode = Some(m.trim().to_string());
                    i += 1;
                    continue;
                }
                if let Some(u) = c_line.strip_prefix("--@ use-source: ") {
                    use_source = Some(u.trim().to_string());
                    i += 1;
                    continue;
                }
                if let Some(rest) = c_line.strip_prefix("--@ file: ") {
                    let parts: Vec<_> = rest.split_whitespace().collect();
                    let f_name = parts[0].to_string();
                    let flag = parts.get(1).map(|s| s.to_string());
                    let mut f_lines = Vec::new();
                    i += 1;
                    while i < lines.len() {
                        let f_line = lines[i];
                        if f_line == "--@ end-file" {
                            i += 1;
                            break;
                        }
                        f_lines.push(f_line.to_string());
                        i += 1;
                    }
                    files.push((f_name, flag, f_lines));
                    continue;
                }
                if let Some(rest) = c_line.strip_prefix("--@ ") {
                    if let Some((k, v)) = rest.split_once(": ") {
                        directives.push((k.trim().to_string(), v.trim().to_string()));
                    }
                    i += 1;
                    continue;
                }
                if files.is_empty() {
                    let trimmed = c_line.trim();
                    if !trimmed.is_empty() {
                        annotations.push(c_line.to_string());
                    }
                }
                i += 1;
            }

            if output.last().is_some_and(|l: &String| !l.is_empty()) {
                output.push(String::new());
            }

            let mode_str = mode.as_deref().unwrap_or("check-pass");
            output.push(format!("-- [case: {case_name}, {mode_str}]"));

            for (k, v) in directives {
                if k == "entry" && v == format!("test_{}", case_name.replace('-', "_")) {
                    continue;
                }
                output.push(format!("-- {k}: {v}"));
            }

            for ann in annotations {
                output.push(ann);
            }

            if let Some(src) = use_source {
                output.push(format!("-- use-source: {src}"));
            }

            let is_single_default = files.len() == 1
                && files[0].0 == format!("{case_name}.ril")
                && files[0].1.is_none();

            if is_single_default {
                for l in &files[0].2 {
                    output.push(l.clone());
                }
            } else {
                for (f_idx, (f_name, flag, f_lines)) in files.into_iter().enumerate() {
                    if f_idx > 0 {
                        output.push(String::new());
                    }
                    let flag_suffix = flag.map(|f| format!(" {f}")).unwrap_or_default();
                    output.push(format!("-- file: {f_name}{flag_suffix}"));
                    for l in f_lines {
                        output.push(l);
                    }
                }
            }
            continue;
        }

        if line.trim().is_empty() {
            if output.last().is_some_and(|l: &String| !l.is_empty()) {
                output.push(String::new());
            }
            i += 1;
            continue;
        }

        output.push(line.to_string());
        i += 1;
    }

    let mut result = output.join("\n");
    if !result.ends_with('\n') {
        result.push('\n');
    }
    result
}

pub fn migrate_all(base: &Path) -> Result<usize> {
    let mut count = 0;
    fn visit(folder: &Path, count: &mut usize) -> Result<()> {
        for entry in fs::read_dir(folder)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                visit(&path, count)?;
            } else if path.extension().is_some_and(|ext| ext == "ril") {
                let original = fs::read_to_string(&path)?;
                let migrated = migrate_file(&original);
                if migrated != original {
                    fs::write(&path, migrated)?;
                    *count += 1;
                }
            }
        }
        Ok(())
    }
    visit(base, &mut count)?;
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_repository_corpus() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"));
        let cases = discover_cases(&repo.join("tests")).expect("discover cases");
        assert!(!cases.is_empty());
        let stats = validate_corpus(&cases, &repo.join("doc"), true).expect("validate corpus");
        assert!(stats.bundles > 0);
        assert!(stats.cases > 0);
    }

    #[test]
    fn test_migrate_file() {
        let text = r#"--@ case: simple
--@ mode: check-pass
--@ spec: SPEC#advisory-warnings
--@ file: simple.ril
pub fn test_hello() {}
--@ end-file
--@ end-case
"#;
        let migrated = migrate_file(text);
        assert_eq!(
            migrated,
            r#"-- [case: simple, check-pass]
-- spec: SPEC#advisory-warnings
pub fn test_hello() {}
"#
        );
    }
}
