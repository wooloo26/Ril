//! Source loading and the declaration-aware CST-to-HIR pipeline.
use crate::{
    Parse,
    ast::{BindingMode, PatternKind, Program, Stmt, StmtKind, Visibility},
    diagnostic::Diagnostic,
    hir::{DeclarationHead, HeadKind, Hir, Index},
    lexer::diagnostic,
    library::{PrimitiveSource, SOURCES, bundled_module},
    parse::{parse_skeleton, parse_with_heads},
    source::{FileId, SourceMap, Span},
};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    io,
    path::{Path, PathBuf},
    sync::Mutex,
};

pub use crate::source::UnitKind;

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
    origin: UnitOrigin,
}

enum UnitOrigin {
    User {
        module_path: Option<PathBuf>,
        kind: UnitKind,
    },
    Primitive(&'static PrimitiveSource),
}

impl Unit {
    fn declarations_only(&self) -> bool {
        matches!(
            self.origin,
            UnitOrigin::User {
                kind: UnitKind::External,
                ..
            } | UnitOrigin::Primitive(_)
        )
    }

    fn index(&self, index: &mut Index, text_len: u32, program: &Program) {
        match &self.origin {
            UnitOrigin::User { module_path, kind } => {
                index.file(self.file, module_path.clone(), *kind, text_len, program);
            }
            UnitOrigin::Primitive(source) => {
                index.primitive_unit(self.file, text_len, source, program);
            }
        }
    }
}

struct Project {
    sources: SourceMap,
    units: Vec<Unit>,
    modules: BTreeMap<PathBuf, Option<FileId>>,
}

struct HeadObservation {
    file: FileId,
    offset: u32,
    kind: HeadKind,
    path: Vec<String>,
    head: Option<DeclarationHead>,
}

struct Pass {
    index: Index,
    files: BTreeMap<FileId, Parse>,
    diagnostics: Vec<Diagnostic>,
    observations: Vec<HeadObservation>,
    discovered_source: bool,
    read_error: Option<io::Error>,
}

impl Pass {
    fn needs_reparse(&self) -> bool {
        self.discovered_source
            || self.observations.iter().any(|observation| {
                let resolved = self.index.head(
                    observation.file,
                    &observation.path,
                    observation.offset,
                    observation.kind,
                );
                if resolved.is_none() && self.files[&observation.file].is_err() {
                    // Recovery may have lost a declaration. Retain diagnostics
                    // from a committed parse unless another head was found.
                    return false;
                }
                resolved != observation.head
            })
    }
}

impl Project {
    fn new(root: &Path, kind: UnitKind, bytes: Vec<u8>) -> io::Result<Self> {
        let mut project = Self {
            sources: SourceMap::default(),
            units: vec![],
            modules: BTreeMap::new(),
        };
        let path = unit_module_path(root).filter(|path| !bundled_module(path));
        let module_path = path.clone().filter(|_| kind != UnitKind::Executable);
        let file = project.add(
            root.to_owned(),
            bytes,
            UnitOrigin::User { module_path, kind },
        )?;
        if let Some(path) = path {
            project
                .modules
                .insert(path, (kind != UnitKind::Executable).then_some(file));
        }
        for source in SOURCES {
            project.add(
                source.display_path.into(),
                source.source.as_bytes().to_vec(),
                UnitOrigin::Primitive(source),
            )?;
        }
        Ok(project)
    }

    fn add(&mut self, path: PathBuf, bytes: Vec<u8>, origin: UnitOrigin) -> io::Result<FileId> {
        let file = self
            .sources
            .add(path, bytes)
            .map_err(|error| io::Error::other(error.to_string()))?;
        self.units.push(Unit { file, origin });
        Ok(file)
    }

    fn load_module(
        &mut self,
        path: PathBuf,
        read: &impl Fn(&Path) -> io::Result<Vec<u8>>,
    ) -> io::Result<Option<FileId>> {
        if bundled_module(&path) {
            return Ok(None);
        }
        if let Some(file) = self.modules.get(&path) {
            return Ok(*file);
        }
        for (extension, kind) in [("ril", UnitKind::Library), ("d.ril", UnitKind::External)] {
            let filename = path.with_extension(extension);
            match read(&filename) {
                Ok(bytes) => {
                    let file = self.add(
                        filename,
                        bytes,
                        UnitOrigin::User {
                            module_path: Some(path.clone()),
                            kind,
                        },
                    )?;
                    self.modules.insert(path, Some(file));
                    return Ok(Some(file));
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(io::Error::new(
                        error.kind(),
                        format!("cannot read {}: {error}", filename.display()),
                    ));
                }
            }
        }
        self.modules.insert(path, None);
        Ok(None)
    }

    fn pass(
        &mut self,
        heads: Option<&Index>,
        read: &impl Fn(&Path) -> io::Result<Vec<u8>>,
    ) -> io::Result<Pass> {
        let mut pass = Pass {
            index: Index::new(),
            files: BTreeMap::new(),
            diagnostics: vec![],
            observations: vec![],
            discovered_source: false,
            read_error: None,
        };
        let mut queue: VecDeque<_> = self
            .units
            .iter()
            .filter(|unit| {
                unit.file == FileId(0) || matches!(unit.origin, UnitOrigin::Primitive(_))
            })
            .map(|unit| unit.file)
            .collect();
        let mut visited = BTreeSet::new();
        while let Some(file) = queue.pop_front() {
            if !visited.insert(file) {
                continue;
            }
            let source = self.sources.get(file).expect("loaded source");
            let unit = &self.units[file.0 as usize];
            let text = match source.text() {
                Ok(text) => text,
                Err(error) => {
                    let start = error.valid_up_to();
                    let end = start + error.error_len().unwrap_or(source.bytes().len() - start);
                    pass.diagnostics.push(diagnostic(
                        file,
                        start,
                        end,
                        "E0104",
                        "source must be valid UTF-8",
                    ));
                    continue;
                }
            };
            let available_heads = heads.filter(|index| index.has_file(file));
            if let Some(heads) = available_heads {
                let observations = Mutex::new(BTreeMap::new());
                let parse = parse_with_heads(
                    text,
                    file,
                    unit.declarations_only(),
                    &|path, offset, kind| {
                        let head = heads.head(file, path, offset, kind);
                        observations
                            .lock()
                            .expect("head observations")
                            .insert((offset, kind, path.to_vec()), head.clone());
                        head
                    },
                );
                if parse.incomplete {
                    return Err(io::Error::other(format!(
                        "frontend resource limit exceeded in {}",
                        source.path().display()
                    )));
                }
                pass.observations.extend(
                    observations
                        .into_inner()
                        .expect("head observations")
                        .into_iter()
                        .map(|((offset, kind, path), head)| HeadObservation {
                            file,
                            offset,
                            kind,
                            path,
                            head,
                        }),
                );
                unit.index(&mut pass.index, text.len() as u32, &parse.program);
                pass.files.insert(file, parse);
            } else {
                let program = parse_skeleton(text, file, unit.declarations_only());
                unit.index(&mut pass.index, text.len() as u32, &program);
                pass.discovered_source |= heads.is_some();
            }
            let imports: Vec<_> = pass.index.paths(file).collect();
            for import in imports {
                match self.load_module(import, read) {
                    Ok(Some(file)) => queue.push_back(file),
                    Ok(None) => {}
                    Err(error) if available_heads.is_some() => {
                        pass.read_error.get_or_insert(error);
                    }
                    // Speculative imports do not establish source dependencies.
                    Err(_) => {}
                }
            }
        }
        pass.index.link_imports();
        Ok(pass)
    }

    fn finish(self, mut pass: Pass) -> io::Result<Frontend> {
        if let Some(error) = pass.read_error.take() {
            return Err(error);
        }
        for (&file, parse) in &pass.files {
            pass.diagnostics.extend(parse.diagnostics.iter().cloned());
            if !parse.is_ok() {
                continue;
            }
            let (unit_kind, primitive_source) = match self.units[file.0 as usize].origin {
                UnitOrigin::User { kind, .. } => {
                    unit_rules(&parse.program, kind, file, &mut pass.diagnostics);
                    if kind != UnitKind::Executable
                        && let Some(source) = self.sources.get(file)
                        && let Some(path) = unit_module_path(source.path())
                        && let Some(stem) = path.file_name().and_then(|stem| stem.to_str())
                    {
                        pass.diagnostics
                            .extend(crate::validation::validate_module_stem(
                                stem,
                                Span {
                                    file,
                                    start: 0,
                                    end: 0,
                                },
                            ));
                    }
                    (Some(kind), None)
                }
                UnitOrigin::Primitive(source) => {
                    if !source.matches_manifest(&parse.program) {
                        return Err(io::Error::other(format!(
                            "bundled declarations in {} do not match the primitive inventory",
                            source.display_path,
                        )));
                    }
                    (None, Some(source))
                }
            };
            pass.diagnostics.extend(crate::validation::validate(
                &parse.program,
                unit_kind,
                primitive_source,
            ));
        }
        let hir = if pass.diagnostics.is_empty() {
            let (hir, errors) = pass.index.finish();
            pass.diagnostics.extend(errors);
            pass.diagnostics.is_empty().then_some(hir)
        } else {
            None
        };
        Ok(Frontend {
            sources: self.sources,
            files: pass.files,
            diagnostics: pass.diagnostics,
            hir,
        })
    }
}

pub fn frontend(
    root: &Path,
    kind: UnitKind,
    read: impl Fn(&Path) -> io::Result<Vec<u8>>,
) -> io::Result<Frontend> {
    let mut project = Project::new(root, kind, read(root)?)?;
    let mut heads = project.pass(None, &read)?.index;
    // Revisit syntax only when actual declarations or reachable files supply
    // different metadata. Invalid arguments do not select an infix parse.
    const MAX_DECLARATION_PASSES: usize = 64;
    for _ in 0..MAX_DECLARATION_PASSES {
        let pass = project.pass(Some(&heads), &read)?;
        if !pass.needs_reparse() {
            return project.finish(pass);
        }
        heads = pass.index;
    }
    Err(io::Error::other(
        "frontend declaration discovery exceeded its pass limit",
    ))
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
                    || !matches!(binding.pattern.kind, PatternKind::Name(_))
                    || binding.initializer.is_some())
            {
                report(
                    stmt.span,
                    "E0901",
                    "foreign constants require an immutable declaration without an initializer",
                );
            }
            if kind != UnitKind::External {
                if binding.initializer.is_none() {
                    report(stmt.span, "E0124", "binding requires an initializer");
                }
                if matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut) {
                    report(
                        stmt.span,
                        "E0120",
                        "a scoped binding requires an executable block",
                    );
                }
                if binding.mode == BindingMode::Via {
                    report(
                        stmt.span,
                        "E0412",
                        "via reception requires a local template binding",
                    );
                }
            }
            if binding.visibility == Visibility::Public
                && (binding.mode.is_mutable() || binding.mode.is_reassignable())
            {
                report(stmt.span, "E0906", "mutable module state cannot be public");
            }
            binding.visibility
        }
        StmtKind::Function(function) => {
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
        StmtKind::Type(ty) => {
            if kind == UnitKind::External && ty.opaque {
                report(
                    stmt.span,
                    "E0901",
                    "a foreign abstract type has no written representation",
                );
            }
            ty.visibility
        }
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
