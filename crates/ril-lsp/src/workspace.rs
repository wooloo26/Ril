use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use ril_driver::{infer_unit, load_package};
use ril_test::{Unit, VirtualPackage};

use crate::protocol::{fs_path_to_uri, uri_to_fs_path, uri_to_logical_path};

pub(crate) const STD_MODULES: &[(&str, &str)] = &[
    ("prelude", "Prelude"),
    ("numeric", "Numeric"),
    ("array", "Array"),
    ("map", "Map"),
    ("set", "Set"),
    ("string", "String"),
    ("bytes", "Bytes"),
    ("reflect", "Reflect"),
    ("io", "Io"),
    ("file", "File"),
    ("math", "Math"),
    ("panic", "Panic"),
    ("platform", "Platform"),
];

#[derive(Clone, Debug)]
pub(crate) struct LspConfig {
    pub(crate) dot_to_pipe: bool,
    pub(crate) auto_import: bool,
    pub(crate) inlay_hints: bool,
    pub(crate) lint_enabled: bool,
}

impl Default for LspConfig {
    fn default() -> Self {
        Self {
            dot_to_pipe: true,
            auto_import: true,
            inlay_hints: true,
            lint_enabled: true,
        }
    }
}

pub(crate) struct WorkspacePackage {
    pub(crate) pkg: VirtualPackage,
    pub(crate) entry_logical: PathBuf,
    pub(crate) package_dir: Option<PathBuf>,
    pub(crate) logical_to_uri: BTreeMap<PathBuf, String>,
}

/// Detects whether `fs_path` is one of Ril's standard library source files
/// (`<repo>/std/<stem>.ril`), returning `(std_dir, stem)`.
pub(crate) fn detect_std_file(fs_path: &Path) -> Option<(PathBuf, &'static str)> {
    let file_name = fs_path.file_name()?.to_str()?;
    let stem_raw = file_name.strip_suffix(".ril")?;
    let &(stem, _) = STD_MODULES.iter().find(|&&(s, _)| s == stem_raw)?;
    let parent = fs_path.parent()?;
    if parent.file_name()?.to_str()? != "std" {
        return None;
    }
    let repo_root = parent.parent()?;
    let looks_like_std_repo =
        parent.join("prelude.ril").is_file() || repo_root.join("crates").join("ril-hir").is_dir();
    looks_like_std_repo.then(|| (parent.to_path_buf(), stem))
}

pub(crate) fn build_package_with_override(
    documents: &BTreeMap<String, String>,
    uri: &str,
    override_text: Option<&str>,
) -> Option<WorkspacePackage> {
    let text = override_text.or_else(|| documents.get(uri).map(String::as_str))?;

    if let Some(fs_path) = uri_to_fs_path(uri)
        && fs_path.is_file()
    {
        // Live stdlib source editing: mount as `ril/std/<stem>.ril` so bodyless primitives
        // and compiler-known opaque types validate cleanly without false E0902 errors.
        if let Some((std_dir, stem)) = detect_std_file(&fs_path) {
            let entry_logical = PathBuf::from(format!("ril/std/{stem}.ril"));
            let mut pkg = VirtualPackage::new(Unit::Lib);
            pkg.entry = entry_logical.clone();
            pkg.insert(entry_logical.clone(), text.as_bytes().to_vec());

            let mut logical_to_uri = BTreeMap::new();
            logical_to_uri.insert(entry_logical.clone(), uri.to_owned());

            for &(other_stem, _) in STD_MODULES {
                let logical = PathBuf::from(format!("ril/std/{other_stem}.ril"));
                if logical == entry_logical {
                    continue;
                }
                let disk = std_dir.join(format!("{other_stem}.ril"));
                if disk.is_file() {
                    let canonical = disk.canonicalize().unwrap_or(disk);
                    let disk_uri = fs_path_to_uri(&canonical);
                    if let Some(open_text) = documents.get(&disk_uri) {
                        pkg.insert(logical.clone(), open_text.as_bytes().to_vec());
                    }
                    logical_to_uri.entry(logical).or_insert(disk_uri);
                }
            }
            return Some(WorkspacePackage {
                pkg,
                entry_logical,
                package_dir: Some(std_dir),
                logical_to_uri,
            });
        }

        if let Ok(mut pkg) = load_package(&fs_path, infer_unit(&fs_path)) {
            let entry_logical = pkg.entry.clone();
            let canonical = fs_path.canonicalize().unwrap_or(fs_path);
            let package_dir = entry_logical
                .strip_prefix("pkg")
                .ok()
                .and_then(|rel| {
                    let comps = rel.components().count();
                    canonical.ancestors().nth(comps).map(Path::to_path_buf)
                })
                .or_else(|| canonical.parent().map(Path::to_path_buf));

            let mut logical_to_uri = BTreeMap::new();
            logical_to_uri.insert(entry_logical.clone(), uri.to_owned());

            pkg.insert(entry_logical.clone(), text.as_bytes().to_vec());
            if let Some(ref root_dir) = package_dir {
                let keys: Vec<PathBuf> = pkg.files.keys().cloned().collect();
                for logical in keys {
                    if let Ok(rel) = logical.strip_prefix("pkg") {
                        let disk = root_dir.join(rel);
                        if disk.is_file() {
                            let disk_uri = fs_path_to_uri(&disk);
                            if let Some(open_text) = documents.get(&disk_uri) {
                                pkg.insert(logical.clone(), open_text.as_bytes().to_vec());
                            }
                            logical_to_uri.entry(logical).or_insert(disk_uri);
                        }
                    }
                }
            }
            return Some(WorkspacePackage {
                pkg,
                entry_logical,
                package_dir,
                logical_to_uri,
            });
        }
    }

    // Fallback for unsaved/virtual URIs not backed by an on-disk file.
    let logical = uri_to_logical_path(uri);
    let unit = ril_source::span::SourceFile::from_bytes(
        ril_source::span::FileId::from_path(&logical),
        logical.clone(),
        text.as_bytes(),
    )
    .ok()
    .map(|source| {
        let lexed = ril_syntax::lexer::lex_with_recovery(&source);
        match ril_syntax::parser::infer_file_kind(&source, &lexed.tokens) {
            ril_syntax::parser::FileKind::Executable => Unit::Bin,
            _ => Unit::Lib,
        }
    })
    .unwrap_or(Unit::Lib);
    let mut pkg = VirtualPackage::new(unit);
    pkg.entry = logical.clone();
    pkg.insert(logical.clone(), text.as_bytes().to_vec());
    let mut logical_to_uri = BTreeMap::new();
    logical_to_uri.insert(logical.clone(), uri.to_owned());
    for (other_uri, other_text) in documents {
        if other_uri == uri {
            continue;
        }
        let other_logical = uri_to_logical_path(other_uri);
        pkg.insert(other_logical.clone(), other_text.as_bytes().to_vec());
        logical_to_uri.insert(other_logical, other_uri.clone());
    }
    Some(WorkspacePackage {
        pkg,
        entry_logical: logical,
        package_dir: None,
        logical_to_uri,
    })
}

pub(crate) fn resolve_std_uri(
    workspace_root: Option<&Path>,
    std_rel: &Path,
    active_uri: &str,
) -> Option<String> {
    let mut candidates = Vec::new();
    if let Some(root) = workspace_root {
        candidates.push(root.join("std").join(std_rel));
    }
    if let Some(fs_path) = uri_to_fs_path(active_uri) {
        for ancestor in fs_path.ancestors() {
            candidates.push(ancestor.join("std").join(std_rel));
        }
    }
    candidates
        .into_iter()
        .find(|p| p.is_file())
        .map(|p| fs_path_to_uri(&p.canonicalize().unwrap_or(p)))
}

pub(crate) fn logical_path_to_uri(
    workspace_root: Option<&Path>,
    ws: &WorkspacePackage,
    logical: &Path,
    active_uri: &str,
) -> String {
    if let Some(mapped) = ws.logical_to_uri.get(logical) {
        return mapped.clone();
    }
    if let Ok(std_rel) = logical.strip_prefix("ril/std") {
        return resolve_std_uri(workspace_root, std_rel, active_uri)
            .unwrap_or_else(|| format!("file:///{}", logical.display()));
    }
    if let Some(ref root_dir) = ws.package_dir
        && let Ok(rel) = logical.strip_prefix("pkg")
    {
        return fs_path_to_uri(&root_dir.join(rel));
    }
    active_uri.to_owned()
}
