use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use ril_base::span::{FileId, SourceFile};
use ril_frontend::{
    lexer,
    parser::{self, FileKind},
    syntax::{Ast, StmtId, StmtKind},
};
use ril_test::{Unit, VirtualPackage};

pub fn infer_unit(path: &Path) -> Unit {
    if path.to_string_lossy().ends_with(".d.ril") {
        return Unit::Decl;
    }
    let main = (|| {
        let bytes = fs::read(path).ok()?;
        let source = SourceFile::from_bytes(FileId(0), path.to_owned(), &bytes).ok()?;
        let tokens = lexer::lex(&source).ok()?;
        let syntax = parser::parse(&source, &tokens, FileKind::Snippet).ok()?;
        Some(syntax.items.iter().any(|&stmt| {
            matches!(&syntax.stmt(stmt).value.kind, StmtKind::Function(function) if function.name.value == "main")
        }))
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
    let parent = package_dir.parent().unwrap_or(package_dir).to_owned();
    let mut pending = vec![(package.entry.clone(), entry)];
    let mut visited = BTreeSet::new();
    while let Some((path, source_path)) = pending.pop() {
        if !visited.insert(path.clone()) {
            continue;
        }
        let data =
            fs::read(&source_path).map_err(|err| format!("{}: {err}", source_path.display()))?;
        let kind = if source_path.to_string_lossy().ends_with(".d.ril") {
            FileKind::Foreign
        } else if path == package.entry {
            match unit {
                Unit::Bin => FileKind::Executable,
                Unit::Decl => FileKind::Foreign,
                Unit::Lib => FileKind::Module,
                Unit::Snippet => FileKind::Snippet,
            }
        } else {
            FileKind::Module
        };
        if let Ok(src) = SourceFile::from_bytes(FileId(0), path.clone(), &data)
            && let Ok(tokens) = lexer::lex(&src)
            && let Ok(ast) = parser::parse(&src, &tokens, kind)
        {
            let mut imports = Vec::new();
            collect(&ast, &ast.items, &mut imports);
            let current_mount = path
                .iter()
                .next()
                .and_then(std::ffi::OsStr::to_str)
                .unwrap_or("pkg");
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
                for extension in ["ril", "d.ril"] {
                    let mut candidate = mount.join(&tail);
                    candidate.set_extension(extension);
                    if candidate.is_file() {
                        let mut vpath = Path::new(anchor).join(&tail);
                        vpath.set_extension(extension);
                        pending.push((vpath, candidate));
                    }
                }
            }
        }
        package.insert(path, data);
    }
    Ok(package)
}

fn collect(ast: &Ast, items: &[StmtId], files: &mut Vec<Vec<String>>) {
    for &item in items {
        match &ast.stmt(item).value.kind {
            StmtKind::Import(import) => {
                if let Some(path) = &import.file {
                    files.push(path.iter().map(|name| name.value.clone()).collect());
                }
            }
            StmtKind::Sub { items, .. } => collect(ast, items, files),
            _ => {}
        }
    }
}
