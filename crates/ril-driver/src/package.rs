use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use ril_sema::iface::Interface;
use ril_source::span::{FileId, SourceFile};
use ril_syntax::lexer::{self, Kind, Token};
use ril_test::{Unit, VirtualPackage};

/// Lightweight token-stream check for a top-level `fn main` without constructing an AST.
fn has_top_level_main(source: &SourceFile, tokens: &[Token]) -> bool {
    ril_syntax::parser::infer_file_kind(source, tokens) == ril_syntax::parser::FileKind::Executable
}

/// Lightweight token-stream scanner collecting module `use a/b/c` import paths without full parsing.
fn scan_use_imports(source: &SourceFile, tokens: &[Token]) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(tok) = tokens.get(i) {
        if tok.text(source) == "use" {
            let mut j = i + 1;
            // Collect `use a/b/c` import paths (`/` immediately after the first segment).
            let mut parts = Vec::new();
            if let Some(first) = tokens.get(j)
                && matches!(first.kind, Kind::Word(_))
            {
                let first_text = first.text(source);
                if tokens.get(j + 1).is_some_and(|t| t.text(source) == "/") {
                    parts.push(first_text.to_owned());
                    j += 1;
                    while tokens.get(j).is_some_and(|t| t.text(source) == "/") {
                        j += 1;
                        if let Some(seg) = tokens.get(j)
                            && matches!(seg.kind, Kind::Word(_))
                        {
                            parts.push(seg.text(source).to_owned());
                            j += 1;
                        } else {
                            break;
                        }
                    }
                    if parts.len() >= 2 {
                        out.push(parts);
                    }
                    i = j;
                    continue;
                }
            }
        }
        i += 1;
    }
    out
}

pub fn infer_unit(path: &Path) -> Unit {
    let target = if path.is_dir() {
        fs::read_to_string(path.join("ril.toml"))
            .ok()
            .and_then(|text| parse_manifest(&text).ok())
            .and_then(|m| m.entry)
            .map_or_else(|| path.join("src/main.ril"), |entry| path.join(entry))
    } else {
        path.to_owned()
    };
    let main = (|| {
        let bytes = fs::read(&target).ok()?;
        let source =
            SourceFile::from_bytes(FileId::from_path(&target), target.clone(), &bytes).ok()?;
        let tokens = lexer::lex(&source).ok()?;
        Some(has_top_level_main(&source, &tokens))
    })();
    if main == Some(true) {
        Unit::Bin
    } else {
        Unit::Lib
    }
}

/// Parsed subset of a `ril.toml` package manifest.
#[derive(Clone, Debug, Default)]
pub struct PackageManifest {
    pub name: Option<String>,
    pub entry: Option<PathBuf>,
    pub dependencies: BTreeMap<String, PathBuf>,
    pub lint: ril_lint::LintConfig,
}

fn strip_toml_comment(raw: &str) -> &str {
    let mut in_double = false;
    let mut in_single = false;
    let mut escaped = false;
    for (idx, ch) in raw.char_indices() {
        if in_double {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_double = false;
            }
        } else if in_single {
            if ch == '\'' {
                in_single = false;
            }
        } else {
            match ch {
                '"' => in_double = true,
                '\'' => in_single = true,
                '#' => return raw.get(..idx).unwrap_or(raw),
                _ => {}
            }
        }
    }
    raw
}

fn unquote_toml_string(raw: &str) -> Option<String> {
    let trimmed = raw.trim();
    if let Some(inner) = trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        Some(inner.replace("\\\"", "\""))
    } else {
        trimmed
            .strip_prefix('\'')
            .and_then(|s| s.strip_suffix('\''))
            .map(str::to_owned)
    }
}

/// Parse a `ril.toml` manifest (`[package]`, `[dependencies]`, `[lint]`, `[lint.options]`).
pub fn parse_manifest(text: &str) -> Result<PackageManifest, String> {
    let mut manifest = PackageManifest::default();
    let mut section = String::new();
    for (line_no, raw_line) in text.lines().enumerate() {
        let line = strip_toml_comment(raw_line).trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            section = header.trim().to_owned();
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("ril.toml:{}: expected `key = value`", line_no + 1));
        };
        let key = key.trim();
        let value = value.trim();
        match section.as_str() {
            "package" => match key {
                "name" => {
                    manifest.name = Some(unquote_toml_string(value).ok_or_else(|| {
                        format!("ril.toml:{}: expected string for `name`", line_no + 1)
                    })?);
                }
                "entry" => {
                    manifest.entry = Some(PathBuf::from(unquote_toml_string(value).ok_or_else(
                        || format!("ril.toml:{}: expected string for `entry`", line_no + 1),
                    )?));
                }
                _ => {}
            },
            "dependencies" => {
                let dep_path = if let Some(s) = unquote_toml_string(value) {
                    s
                } else if let Some(inner) =
                    value.strip_prefix('{').and_then(|s| s.strip_suffix('}'))
                {
                    let mut found = None;
                    for pair in inner.split(',') {
                        if let Some((k, v)) = pair.split_once('=')
                            && k.trim() == "path"
                        {
                            found = unquote_toml_string(v);
                        }
                    }
                    found.ok_or_else(|| {
                        format!(
                            "ril.toml:{}: dependency `{key}` requires `path = \"...\"`",
                            line_no + 1
                        )
                    })?
                } else {
                    return Err(format!(
                        "ril.toml:{}: invalid dependency `{key}`",
                        line_no + 1
                    ));
                };
                manifest
                    .dependencies
                    .insert(key.to_owned(), PathBuf::from(dep_path));
            }
            "lint" => {
                let level_str = unquote_toml_string(value).ok_or_else(|| {
                    format!(
                        "ril.toml:{}: expected string level (\"allow\"|\"warn\"|\"deny\") for `{key}`",
                        line_no + 1
                    )
                })?;
                manifest
                    .lint
                    .insert_manifest_entry(key, &level_str)
                    .map_err(|e| format!("ril.toml:{}: {e}", line_no + 1))?;
            }
            "lint.options" => {
                let num = value.parse::<usize>().map_err(|_| {
                    format!(
                        "ril.toml:{}: expected non-negative integer for `lint.options.{key}`",
                        line_no + 1
                    )
                })?;
                match key {
                    "max_args" => manifest.lint.options.max_args = num,
                    "max_nesting" => manifest.lint.options.max_nesting = num,
                    "max_lines" => manifest.lint.options.max_lines = num,
                    _ => {
                        return Err(format!(
                            "ril.toml:{}: unknown lint option `{key}`",
                            line_no + 1
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(manifest)
}

/// Locates and parses the nearest enclosing `ril.toml` manifest for `path`.
pub fn find_manifest_for(path: &Path) -> Option<(PathBuf, PackageManifest)> {
    let start = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or(path)
    };
    find_manifest(start)
}

fn find_manifest(start: &Path) -> Option<(PathBuf, PackageManifest)> {
    for dir in start.ancestors() {
        let candidate = dir.join("ril.toml");
        if candidate.is_file() {
            let text = fs::read_to_string(&candidate).ok()?;
            let manifest = parse_manifest(&text).ok()?;
            return Some((dir.to_owned(), manifest));
        }
    }
    None
}

fn resolve_dep_root(base_dir: &Path, raw: &Path) -> PathBuf {
    let joined = base_dir.join(raw);
    let resolved = joined.canonicalize().unwrap_or(joined);
    let pkg_sub = resolved.join("pkg");
    if pkg_sub.is_dir() {
        return pkg_sub;
    }
    let src_sub = resolved.join("src");
    if src_sub.is_dir() {
        return src_sub;
    }
    resolved
}

fn check_manifest_cycles(root_dir: &Path, root_manifest: &PackageManifest) -> Result<(), String> {
    fn dfs(
        dir: &Path,
        manifest: &PackageManifest,
        visiting: &mut Vec<PathBuf>,
        visited: &mut BTreeSet<PathBuf>,
    ) -> Result<(), String> {
        let canonical = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
        visiting.push(canonical.clone());
        for (dep_name, dep_path) in &manifest.dependencies {
            let joined = dir.join(dep_path);
            let dep_dir = joined.canonicalize().unwrap_or(joined);
            if visiting.contains(&dep_dir) {
                return Err(format!(
                    "cyclic package dependency in ril.toml involving `{dep_name}` ({})",
                    dep_dir.display()
                ));
            }
            if !visited.contains(&dep_dir) {
                let toml_path = dep_dir.join("ril.toml");
                if toml_path.is_file() {
                    let text = fs::read_to_string(&toml_path)
                        .map_err(|err| format!("{}: {err}", toml_path.display()))?;
                    let dep_manifest = parse_manifest(&text)?;
                    dfs(&dep_dir, &dep_manifest, visiting, visited)?;
                }
            }
        }
        visiting.pop();
        visited.insert(canonical);
        Ok(())
    }

    let mut visiting = Vec::new();
    let mut visited = BTreeSet::new();
    dfs(root_dir, root_manifest, &mut visiting, &mut visited)
}

pub fn load_package(entry: &Path, unit: Unit) -> Result<VirtualPackage, String> {
    load_package_with_paths(entry, unit).map(|(pkg, _)| pkg)
}

pub fn load_package_with_paths(
    entry: &Path,
    unit: Unit,
) -> Result<(VirtualPackage, BTreeMap<PathBuf, PathBuf>), String> {
    let mut entry = entry
        .canonicalize()
        .map_err(|err| format!("{}: {err}", entry.display()))?;
    let mut manifest_info: Option<(PathBuf, PackageManifest)> = None;
    if entry.is_dir() {
        let toml_path = entry.join("ril.toml");
        let text = fs::read_to_string(&toml_path)
            .map_err(|err| format!("{}: {err}", toml_path.display()))?;
        let manifest = parse_manifest(&text)?;
        let rel = manifest
            .entry
            .clone()
            .unwrap_or_else(|| PathBuf::from("src/main.ril"));
        let dir = entry;
        entry = dir
            .join(&rel)
            .canonicalize()
            .map_err(|err| format!("{}: {err}", dir.join(&rel).display()))?;
        manifest_info = Some((dir, manifest));
    } else if entry.file_name().is_some_and(|name| name == "ril.toml") {
        let dir = entry
            .parent()
            .ok_or("ril.toml needs a parent directory")?
            .to_owned();
        let text =
            fs::read_to_string(&entry).map_err(|err| format!("{}: {err}", entry.display()))?;
        let manifest = parse_manifest(&text)?;
        let rel = manifest
            .entry
            .clone()
            .unwrap_or_else(|| PathBuf::from("src/main.ril"));
        entry = dir
            .join(&rel)
            .canonicalize()
            .map_err(|err| format!("{}: {err}", dir.join(&rel).display()))?;
        manifest_info = Some((dir, manifest));
    } else if let Some(parent) = entry.parent() {
        manifest_info = find_manifest(parent);
    }

    let package_dir: PathBuf = entry
        .ancestors()
        .skip(1)
        .find(|parent| parent.file_name().is_some_and(|name| name == "pkg"))
        .map(Path::to_path_buf)
        .or_else(|| {
            manifest_info.as_ref().and_then(|(dir, _)| {
                let src = dir.join("src");
                entry.starts_with(&src).then_some(src)
            })
        })
        .or_else(|| entry.parent().map(Path::to_path_buf))
        .ok_or("source path needs a parent directory")?;
    let local = entry
        .strip_prefix(&package_dir)
        .map_err(|err| err.to_string())?;
    let mut package = VirtualPackage::new(unit);
    package.entry = Path::new("pkg").join(local);
    let mut mounts = BTreeMap::from([("pkg".to_owned(), package_dir.clone())]);
    if let Some((manifest_dir, manifest)) = &manifest_info {
        check_manifest_cycles(manifest_dir, manifest)?;
        for (dep_name, dep_path) in &manifest.dependencies {
            mounts.insert(dep_name.clone(), resolve_dep_root(manifest_dir, dep_path));
        }
    }
    let mut bundled = BTreeMap::new();
    let parent = package_dir.parent().unwrap_or(&package_dir).to_owned();
    let mut pending = vec![(package.entry.clone(), entry)];
    let mut visited = BTreeSet::new();
    let mut disk_paths = BTreeMap::new();
    while let Some((path, source_path)) = pending.pop() {
        if !visited.insert(path.clone()) {
            continue;
        }
        disk_paths.insert(path.clone(), source_path.clone());
        let data =
            fs::read(&source_path).map_err(|err| format!("{}: {err}", source_path.display()))?;
        let mut module = path.clone();
        let current_mount = path
            .iter()
            .next()
            .and_then(std::ffi::OsStr::to_str)
            .unwrap_or("pkg");
        let interface = if path
            .extension()
            .is_some_and(|extension| extension == "rili")
        {
            module.set_extension("ril");
            let interface = Interface::decode(&data)
                .map_err(|error| format!("{}: {error}", source_path.display()))?;
            for name in interface.modules.keys() {
                let Ok(relative) = Path::new(name).strip_prefix("pkg") else {
                    continue;
                };
                let mut logical = Path::new(current_mount).join(relative);
                logical.set_extension("rili");
                bundled
                    .entry(logical)
                    .or_insert_with(|| source_path.clone());
            }
            Some(interface)
        } else {
            None
        };
        let declaration = if let Some(interface) = &interface {
            interface
                .module(&module)
                .ok_or_else(|| {
                    format!(
                        "{}: no declarations for {}",
                        source_path.display(),
                        module.display()
                    )
                })?
                .1
                .as_bytes()
        } else {
            &data
        };
        if let Ok(src) = SourceFile::from_bytes(FileId::from_path(&module), module, declaration) {
            let lexed = lexer::lex_with_recovery(&src);
            let imports = scan_use_imports(&src, &lexed.tokens);
            for parts in imports {
                let Some(anchor) = parts.first() else {
                    continue;
                };
                let anchor = if anchor == "pkg" {
                    current_mount
                } else {
                    anchor
                };
                let mount = mounts
                    .entry(anchor.to_owned())
                    .or_insert_with(|| parent.join(anchor));
                let tail: PathBuf = parts.iter().skip(1).collect();
                let mut source_available = false;
                for extension in ["ril", "d.ril"] {
                    let mut candidate = mount.join(&tail);
                    candidate.set_extension(extension);
                    if candidate.is_file() {
                        source_available = true;
                        let mut vpath = Path::new(anchor).join(&tail);
                        vpath.set_extension(extension);
                        pending.push((vpath, candidate));
                    }
                }
                if !source_available {
                    let mut candidate = mount.join(&tail);
                    candidate.set_extension("rili");
                    let mut vpath = Path::new(anchor).join(&tail);
                    vpath.set_extension("rili");
                    if candidate.is_file() {
                        pending.push((vpath, candidate));
                    } else if let Some(artifact) = bundled.get(&vpath) {
                        pending.push((vpath, artifact.clone()));
                    }
                }
            }
        }
        package.insert(path, data);
    }
    Ok((package, disk_paths))
}
