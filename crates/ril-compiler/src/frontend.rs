//! Source loading and the declaration-aware CST-to-HIR pipeline.
use crate::{
    Parse,
    ast::{BindingMode, ExprKind, Program, Stmt, StmtKind, Visibility},
    diagnostic::Diagnostic,
    hir::{Hir, Index},
    lexer::diagnostic,
    parse::{parse_skeleton, parse_with_heads},
    source::{FileId, SourceMap, Span},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    path::{Path, PathBuf},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnitKind {
    Executable,
    Library,
    External,
}

pub struct Frontend {
    pub sources: SourceMap,
    pub files: BTreeMap<FileId, Parse>,
    pub diagnostics: Vec<Diagnostic>,
    pub hir: Option<Hir>,
}

impl Frontend {
    pub fn is_ok(&self) -> bool {
        self.hir.is_some()
    }
}

struct Unit {
    file: FileId,
    module_path: Option<PathBuf>,
    kind: UnitKind,
}

pub fn frontend(
    root: &Path,
    kind: UnitKind,
    read: impl Fn(&Path) -> io::Result<Vec<u8>>,
) -> io::Result<Frontend> {
    let mut sources = SourceMap::default();
    let mut diagnostics = vec![];
    let mut units = vec![];
    let mut heads = Index::new();
    let mut seen = BTreeSet::new();
    let module_path = unit_module_path(root);
    seen.extend(module_path.clone());
    let mut pending = vec![(
        root.to_owned(),
        (kind != UnitKind::Executable)
            .then_some(module_path)
            .flatten(),
        kind,
        read(root)?,
    )];
    while let Some((path, module_path, kind, bytes)) = pending.pop() {
        let file = sources
            .add(path, bytes)
            .map_err(|e| io::Error::other(e.to_string()))?;
        let source = sources.get(file).expect("newly added source");
        match source.text() {
            Ok(text) => {
                let program = parse_skeleton(text, file);
                heads.file(file, module_path.clone(), text.len() as u32, &program);
                units.push(Unit {
                    file,
                    module_path,
                    kind,
                });
            }
            Err(error) => {
                let start = error.valid_up_to();
                let end = start + error.error_len().unwrap_or(source.bytes().len() - start);
                diagnostics.push(diagnostic(
                    file,
                    start,
                    end,
                    "E0104",
                    "source must be valid UTF-8",
                ));
                continue;
            }
        }
        let imports = heads.paths().collect::<Vec<_>>();
        for import in imports {
            if !seen.insert(import.clone()) {
                continue;
            }
            for (extension, kind) in [("ril", UnitKind::Library), ("d.ril", UnitKind::External)] {
                let path = import.with_extension(extension);
                match read(&path) {
                    Ok(bytes) => {
                        pending.push((path, Some(import), kind, bytes));
                        break;
                    }
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error),
                }
            }
        }
    }
    heads.link_imports();

    let mut files = BTreeMap::new();
    let mut resolved = Index::new();
    for unit in units {
        let source = sources.get(unit.file).expect("indexed source");
        let text = source.text().expect("decoded source");
        let parse = parse_with_heads(text, unit.file, &|path, offset| {
            heads.application(unit.file, path, offset)
        });
        diagnostics.extend(parse.diagnostics.iter().cloned());
        if parse.incomplete {
            return Err(io::Error::other(format!(
                "frontend resource limit exceeded in {}",
                source.path().display()
            )));
        }
        if parse.is_ok() {
            diagnostics.extend(crate::validation::validate(&parse.program));
            unit_rules(&parse.program, unit.kind, unit.file, &mut diagnostics);
            resolved.file(
                unit.file,
                unit.module_path,
                text.len() as u32,
                &parse.program,
            );
        }
        files.insert(unit.file, parse);
    }
    let hir = if diagnostics.is_empty() {
        resolved.link_imports();
        let (hir, errors) = resolved.finish();
        diagnostics.extend(errors);
        diagnostics.is_empty().then_some(hir)
    } else {
        None
    };
    Ok(Frontend {
        sources,
        files,
        diagnostics,
        hir,
    })
}

fn unit_module_path(path: &Path) -> Option<PathBuf> {
    let name = path.file_name()?.to_str()?;
    let stem = name
        .strip_suffix(".d.ril")
        .or_else(|| name.strip_suffix(".ril"))?;
    Some(path.with_file_name(stem))
}

fn unit_rules(program: &Program, kind: UnitKind, file: FileId, diagnostics: &mut Vec<Diagnostic>) {
    let mut main = false;
    let mut report = |span: Span, code, message| {
        diagnostics.push(diagnostic(
            span.file,
            span.start as usize,
            span.end as usize,
            code,
            message,
        ));
    };
    for stmt in &program.statements {
        main |= matches!(&stmt.kind, StmtKind::Function(function) if function.name == "main");
        item_rules(stmt, kind, true, &mut report);
    }
    if kind == UnitKind::Executable && !main {
        report(
            Span {
                file,
                start: 0,
                end: 0,
            },
            "E0903",
            "executable root requires an ordinary fn main",
        );
    }
}

fn item_rules(
    stmt: &Stmt,
    kind: UnitKind,
    root: bool,
    report: &mut impl FnMut(Span, &'static str, &'static str),
) {
    let visibility = match &stmt.kind {
        StmtKind::Binding(binding) => {
            if kind == UnitKind::External
                && (binding.mode != BindingMode::Let
                    || binding.is_meta
                    || !matches!(binding.value.kind, ExprKind::Ambient))
            {
                report(
                    stmt.span,
                    "E0901",
                    "foreign constants require an immutable declaration without an initializer",
                );
            }
            if kind != UnitKind::External && matches!(binding.value.kind, ExprKind::Ambient) {
                report(stmt.span, "E0124", "binding requires an initializer");
            }
            if binding.visibility == Visibility::Public
                && (binding.mode.is_mutable() || binding.mode.is_reassignable())
            {
                report(stmt.span, "E0906", "mutable module state cannot be public");
            }
            binding.visibility
        }
        StmtKind::Function(function) => {
            if kind == UnitKind::External
                && (function.body.is_some() || function.is_meta || function.is_halt)
            {
                report(
                    stmt.span,
                    "E0901",
                    "foreign functions require an ordinary bodyless declaration",
                );
            } else if kind != UnitKind::External && function.body.is_none() {
                report(stmt.span, "E0902", "function body required in a .ril file");
            }
            if function.name == "main" {
                if !root
                    || kind != UnitKind::Executable
                    || function.visibility == Visibility::Public
                    || function.is_meta
                    || !function.parameters.is_empty()
                    || !function.generics.is_empty()
                {
                    report(
                        stmt.span,
                        "E0904",
                        "main must be an ordinary private parameterless function at executable root",
                    );
                }
                return;
            }
            function.visibility
        }
        StmtKind::Type(ty) => ty.visibility,
        StmtKind::Use(import) => import.visibility,
        StmtKind::Sub(sub) => {
            for item in &sub.items {
                item_rules(item, kind, false, report);
            }
            sub.visibility
        }
        StmtKind::Effect(effect) if kind != UnitKind::External => effect.visibility,
        _ => {
            if kind == UnitKind::External {
                report(
                    stmt.span,
                    "E0901",
                    "this item is not allowed in a foreign interface",
                );
            } else {
                report(stmt.span, "E0120", "a module item must be a declaration");
            }
            return;
        }
    };
    if kind == UnitKind::Executable && root && visibility == Visibility::Public {
        report(
            stmt.span,
            "E0905",
            "executable root cannot export declarations",
        );
    }
}
