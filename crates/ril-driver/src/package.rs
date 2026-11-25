use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use ril_base::span::{FileId, SourceFile};
use ril_frontend::lexer::{self, Kind, Token};
use ril_sema::iface::Interface;
use ril_test::{Unit, VirtualPackage};

/// Lightweight token-stream check for a top-level `fn main` without constructing an AST.
fn has_top_level_main(source: &SourceFile, tokens: &[Token]) -> bool {
    let mut depth = 0usize;
    let mut i = 0;
    while let Some(tok) = tokens.get(i) {
        let text = tok.text(source);
        match text {
            "{" | ".{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            "fn" if depth == 0 => {
                if let Some(next) = tokens.get(i + 1)
                    && next.text(source) == "main"
                {
                    return true;
                }
            }
            _ => {}
        }
        i += 1;
    }
    false
}

/// Lightweight token-stream scanner collecting module `use a/b/c` import paths without full parsing.
fn scan_use_imports(source: &SourceFile, tokens: &[Token]) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(tok) = tokens.get(i) {
        if tok.text(source) == "use" {
            let mut j = i + 1;
            // Distinguish `use a/b/c` import from `use [mut] x = expr` scoped resource binding:
            // an import has `/` immediately after the first segment.
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
    if path.to_string_lossy().ends_with(".d.ril") {
        return Unit::Decl;
    }
    let main = (|| {
        let bytes = fs::read(path).ok()?;
        let source =
            SourceFile::from_bytes(FileId::from_path(path), path.to_owned(), &bytes).ok()?;
        let tokens = lexer::lex(&source).ok()?;
        Some(has_top_level_main(&source, &tokens))
    })();
    if main == Some(true) {
        Unit::Bin
    } else {
        Unit::Lib
    }
}

pub fn load_package(entry: &Path, unit: Unit) -> Result<VirtualPackage, String> {
    let entry = entry
        .canonicalize()
        .map_err(|err| format!("{}: {err}", entry.display()))?;
    let package_dir = entry
        .ancestors()
        .skip(1)
        .find(|parent| parent.file_name().is_some_and(|name| name == "pkg"))
        .or_else(|| entry.parent())
        .ok_or("source path needs a parent directory")?;
    let local = entry
        .strip_prefix(package_dir)
        .map_err(|err| err.to_string())?;
    let mut package = VirtualPackage::new(unit);
    package.entry = Path::new("pkg").join(local);
    let mut mounts = BTreeMap::from([("pkg".to_owned(), package_dir.to_owned())]);
    let mut bundled = BTreeMap::new();
    let parent = package_dir.parent().unwrap_or(package_dir).to_owned();
    let mut pending = vec![(package.entry.clone(), entry)];
    let mut visited = BTreeSet::new();
    while let Some((path, source_path)) = pending.pop() {
        if !visited.insert(path.clone()) {
            continue;
        }
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
    Ok(package)
}
