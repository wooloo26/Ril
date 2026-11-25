#![forbid(unsafe_code)]

use std::{collections::BTreeMap, path::PathBuf, sync::Arc};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceMap, Span},
};
use ril_frontend::{
    hir::{self, Program},
    lexer,
    parser::{self, FileKind},
};
use ril_sema::{
    access::{self, Analysis},
    iface::{self, Export, Interface},
    ty::{self, TypedProgram},
};
use ril_test::{CheckResult, ExecOutput, Stage, TestDriver, Unit, VirtualPackage};

mod incremental;
mod native;
mod package;

pub use incremental::{IncrementalCache, QueryStats};
pub use native::worker_entry;
pub use package::{infer_unit, load_package};

use incremental::{CheckKey, ContentDigest, FileFingerprint, MirKey, PackageKey, TypeKey, sha256};

pub const AVAILABLE: ril_test::Milestone = ril_test::Milestone::M5;

#[derive(
    Clone, Copy, Debug, Default, Eq, Hash, PartialEq, serde::Serialize, serde::Deserialize,
)]
pub struct CompileOptions {
    pub opt_stack_promote: bool,
}

impl CompileOptions {
    pub const fn lower_options(self) -> ril_backend::mir::LowerOptions {
        ril_backend::mir::LowerOptions {
            stack_promote: self.opt_stack_promote,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Driver;

#[derive(Clone, Debug, Default)]
pub struct Compiler {
    options: CompileOptions,
    cache: Option<Arc<IncrementalCache>>,
}

impl Compiler {
    pub const fn new(options: CompileOptions) -> Self {
        Self {
            options,
            cache: None,
        }
    }

    pub fn incremental(options: CompileOptions) -> Self {
        Self {
            options,
            cache: Some(Arc::new(IncrementalCache::new())),
        }
    }

    pub fn with_disk_cache(options: CompileOptions, dir: PathBuf) -> Self {
        Self {
            options,
            cache: Some(Arc::new(IncrementalCache::with_disk_dir(dir))),
        }
    }

    pub fn with_options(&self, options: CompileOptions) -> Self {
        Self {
            options,
            cache: self.cache.clone(),
        }
    }

    pub const fn options(&self) -> CompileOptions {
        self.options
    }

    pub fn stats(&self) -> Option<QueryStats> {
        self.cache.as_ref().map(|cache| cache.stats())
    }

    pub fn reset_stats(&self) {
        if let Some(cache) = &self.cache {
            cache.reset_stats();
        }
    }

    pub(crate) fn cache(&self) -> Option<&IncrementalCache> {
        self.cache.as_deref()
    }

    pub fn check(&self, pkg: &VirtualPackage, stage: Stage) -> Checked {
        if let Some(cache) = &self.cache {
            let prepared = prepare_inputs(pkg, Some(cache));
            let key = CheckKey::new(
                prepared.package_key.clone(),
                pkg.budget,
                stage,
                self.options,
            );
            if let Some((sources, result)) = cache.get_check(&key) {
                return Checked { sources, result };
            }
            if let Some(result) = cache.read_disk_check(&key) {
                cache.put_check(key, prepared.sources.clone(), result.clone());
                return Checked {
                    sources: prepared.sources,
                    result,
                };
            }
            let result = self.check_prepared(pkg, stage, prepared.clone());
            cache.write_disk_check(&key, &result);
            cache.put_check(key, prepared.sources.clone(), result.clone());
            return Checked {
                sources: prepared.sources,
                result,
            };
        }
        let prepared = prepare_inputs(pkg, None);
        let result = self.check_prepared(pkg, stage, prepared.clone());
        Checked {
            sources: prepared.sources,
            result,
        }
    }

    fn check_prepared(
        &self,
        pkg: &VirtualPackage,
        stage: Stage,
        prepared: PreparedInputs,
    ) -> CheckResult {
        let file_paths = prepared.sources.file_paths();
        let mut result = (|| {
            if stage < Stage::Type {
                let _ = run_frontend(pkg, stage, prepared, self.cache())?;
                return Ok(CheckResult::default());
            }
            let type_key = TypeKey {
                package: prepared.package_key.clone(),
                budget: pkg.budget,
            };
            let typed = self.typed_with(pkg, prepared, type_key.clone())?;
            if stage == Stage::Access {
                self.analyze_with(typed.clone(), type_key)?;
            } else if stage >= Stage::Mir {
                let (typed, analysis) = self.analyze_with(typed.clone(), type_key.clone())?;
                let mir_key = MirKey {
                    access: type_key,
                    options: self.options,
                };
                self.lower_with(typed, analysis, mir_key)?;
            }
            Ok(CheckResult {
                signatures: iface::signatures(&typed),
                ..CheckResult::default()
            })
        })()
        .unwrap_or_else(|diagnostics| CheckResult {
            diagnostics,
            ..CheckResult::default()
        });
        result.file_paths = file_paths;
        result
    }

    pub fn analyze(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<(TypedProgram, Analysis), Vec<Diagnostic>> {
        let prepared = prepare_inputs(pkg, self.cache());
        let (_, program, imports) = run_frontend_full(pkg, Stage::Hir, prepared, self.cache())?;
        let program =
            program.ok_or_else(|| vec![Diagnostic::unsupported("missing frontend program")])?;
        let typed = check_types(program, pkg.budget, imports)?;
        let analysis = access::check(&typed)?;
        Ok((typed, analysis))
    }

    pub fn analyze_cached(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<(Arc<TypedProgram>, Arc<Analysis>), Vec<Diagnostic>> {
        let (typed, analysis, _) = self.analyze_arc(pkg)?;
        Ok((typed, analysis))
    }

    pub(crate) fn analyze_arc(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<(Arc<TypedProgram>, Arc<Analysis>, TypeKey), Vec<Diagnostic>> {
        let prepared = prepare_inputs(pkg, self.cache());
        let key = TypeKey {
            package: prepared.package_key.clone(),
            budget: pkg.budget,
        };
        let typed = self.typed_with(pkg, prepared, key.clone())?;
        let (typed, analysis) = self.analyze_with(typed, key.clone())?;
        Ok((typed, analysis, key))
    }

    fn typed_with(
        &self,
        pkg: &VirtualPackage,
        prepared: PreparedInputs,
        key: TypeKey,
    ) -> Result<Arc<TypedProgram>, Vec<Diagnostic>> {
        if let Some(cache) = &self.cache
            && let Some(hit) = cache.get_typed(&key)
        {
            return hit;
        }
        let result = (|| {
            let (_, program, imports) = run_frontend_full(pkg, Stage::Hir, prepared, self.cache())?;
            let program =
                program.ok_or_else(|| vec![Diagnostic::unsupported("missing frontend program")])?;
            check_types(program, pkg.budget, imports).map(Arc::new)
        })();
        if let Some(cache) = &self.cache {
            cache.put_typed(key, result.clone());
        }
        result
    }

    fn analyze_with(
        &self,
        typed: Arc<TypedProgram>,
        key: TypeKey,
    ) -> Result<(Arc<TypedProgram>, Arc<Analysis>), Vec<Diagnostic>> {
        if let Some(cache) = &self.cache
            && let Some(hit) = cache.get_analysis(&key)
        {
            return hit;
        }
        let result = access::check(&typed).map(|analysis| (typed, Arc::new(analysis)));
        if let Some(cache) = &self.cache {
            cache.put_analysis(key, result.clone());
        }
        result
    }

    pub(crate) fn lower_with(
        &self,
        typed: Arc<TypedProgram>,
        analysis: Arc<Analysis>,
        key: MirKey,
    ) -> Result<Arc<ril_backend::mir::Program>, Vec<Diagnostic>> {
        if let Some(cache) = &self.cache
            && let Some(hit) = cache.get_mir(&key)
        {
            return hit;
        }
        let result =
            ril_backend::mir::lower_with_options(&typed, &analysis, self.options.lower_options())
                .map(Arc::new)
                .map_err(|err| vec![err]);
        if let Some(cache) = &self.cache {
            cache.put_mir(key, result.clone());
        }
        result
    }

    pub fn horn_rules(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<Vec<access::horn::Rule<usize>>, Vec<Diagnostic>> {
        let prepared = prepare_inputs(pkg, self.cache());
        let key = TypeKey {
            package: prepared.package_key.clone(),
            budget: pkg.budget,
        };
        let typed = self.typed_with(pkg, prepared, key)?;
        Ok(access::horn_rules(&typed))
    }

    pub fn interface(&self, pkg: &VirtualPackage) -> Result<Interface, Vec<Diagnostic>> {
        self.interface_arc(pkg).map(|iface| (*iface).clone())
    }

    pub fn interface_arc(&self, pkg: &VirtualPackage) -> Result<Arc<Interface>, Vec<Diagnostic>> {
        let prepared = prepare_inputs(pkg, self.cache());
        let key = TypeKey {
            package: prepared.package_key.clone(),
            budget: pkg.budget,
        };
        if let Some(cache) = &self.cache
            && let Some(hit) = cache.get_interface(&key)
        {
            return hit;
        }
        let result = (|| {
            let typed = self.typed_with(pkg, prepared, key.clone())?;
            let (typed, analysis) = self.analyze_with(typed, key.clone())?;
            Ok(Arc::new(Interface::build(&typed, &analysis)))
        })();
        if let Some(cache) = &self.cache {
            cache.put_interface(key, result.clone());
        }
        result
    }
}

pub struct Checked {
    pub sources: SourceMap,
    pub result: CheckResult,
}

impl Driver {
    pub const fn with_options(self, options: CompileOptions) -> Compiler {
        Compiler::new(options)
    }

    pub fn incremental(self, options: CompileOptions) -> Compiler {
        Compiler::incremental(options)
    }

    pub fn with_disk_cache(self, options: CompileOptions, dir: PathBuf) -> Compiler {
        Compiler::with_disk_cache(options, dir)
    }

    pub fn check(&self, pkg: &VirtualPackage, stage: Stage) -> Checked {
        self.with_options(CompileOptions::default())
            .check(pkg, stage)
    }

    pub fn analyze(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<(TypedProgram, Analysis), Vec<Diagnostic>> {
        self.with_options(CompileOptions::default()).analyze(pkg)
    }

    pub fn horn_rules(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<Vec<access::horn::Rule<usize>>, Vec<Diagnostic>> {
        self.with_options(CompileOptions::default()).horn_rules(pkg)
    }

    pub fn interface(&self, pkg: &VirtualPackage) -> Result<Interface, Vec<Diagnostic>> {
        self.with_options(CompileOptions::default()).interface(pkg)
    }
}

fn check_types(
    program: Program,
    budget: Option<u64>,
    imports: BTreeMap<String, Export>,
) -> Result<TypedProgram, Vec<Diagnostic>> {
    let mut typed = ty::check(program, budget)?;
    if !imports.is_empty() {
        let mut imports = imports;
        typed.imported_functions = typed
            .callables
            .keys()
            .filter(|&&id| typed.hir.operation_effect(id).is_none())
            .filter_map(|&id| {
                imports
                    .remove(&typed.hir.export_name(id))
                    .map(|export| (id, export))
            })
            .collect();
    }
    Ok(typed)
}

#[derive(Clone)]
struct PreparedFile {
    id: FileId,
    from_interface: bool,
    content_hash: ContentDigest,
}

#[derive(Clone)]
struct PreparedInputs {
    sources: SourceMap,
    valid: Vec<PreparedFile>,
    entry: Option<FileId>,
    imports: BTreeMap<String, Export>,
    diagnostics: Vec<Diagnostic>,
    package_key: PackageKey,
}

fn prepare_inputs(pkg: &VirtualPackage, cache: Option<&IncrementalCache>) -> PreparedInputs {
    let mut sources = SourceMap::default();
    let mut diagnostics = Vec::new();
    let mut valid = Vec::new();
    let mut entry = None;
    let mut imports = BTreeMap::new();
    let mut fingerprints = Vec::new();
    for (path, file) in &pkg.files {
        let mut logical = path.clone();
        let from_interface = path
            .extension()
            .is_some_and(|extension| extension == "rili");
        let declarations;
        let data = if from_interface {
            logical.set_extension("ril");
            if pkg.files.contains_key(&logical) {
                continue;
            }
            let decoded = match cache {
                Some(cache) => cache.decode_interface(&file.bytes),
                None => Interface::decode(&file.bytes).map(Arc::new),
            };
            match decoded.and_then(|interface| {
                let (module, source) = interface
                    .module(&logical)
                    .ok_or_else(|| format!("no declarations for {}", logical.display()))?;
                let prefix = format!("{module}::");
                imports.extend(interface.functions.iter().filter_map(|(name, export)| {
                    name.strip_prefix(&prefix)
                        .map(|local| (format!("{}::{local}", logical.display()), export.clone()))
                }));
                Ok((interface.abi_hash.clone(), source.as_bytes().to_vec()))
            }) {
                Ok((abi_hash, data)) => {
                    fingerprints.push(FileFingerprint::Interface {
                        path: path.clone(),
                        abi_hash,
                    });
                    declarations = data;
                    &declarations
                }
                Err(error) => {
                    fingerprints.push(FileFingerprint::InvalidInterface {
                        path: path.clone(),
                        hash: sha256(&file.bytes),
                    });
                    diagnostics.push(Diagnostic::unsupported(format!(
                        "{}: {error}",
                        path.display()
                    )));
                    continue;
                }
            }
        } else {
            fingerprints.push(FileFingerprint::Source {
                path: path.clone(),
                hash: sha256(&file.bytes),
            });
            &file.bytes
        };
        let content_hash = sha256(data);
        let stable_id = FileId::from_path(&logical);
        match sources.add_with_id(stable_id, logical, data) {
            Ok(id) => {
                if path == &pkg.entry {
                    entry = Some(id);
                }
                valid.push(PreparedFile {
                    id,
                    from_interface,
                    content_hash,
                });
            }
            Err(diagnostic) => diagnostics.push(*diagnostic),
        }
    }
    PreparedInputs {
        sources,
        valid,
        entry,
        imports,
        diagnostics,
        package_key: PackageKey::new(pkg.unit, pkg.entry.clone(), fingerprints),
    }
}

fn run_frontend(
    pkg: &VirtualPackage,
    stage: Stage,
    prepared: PreparedInputs,
    cache: Option<&IncrementalCache>,
) -> Result<Option<Program>, Vec<Diagnostic>> {
    run_frontend_full(pkg, stage, prepared, cache).map(|(_, program, _)| program)
}

type FrontendOutput = (SourceMap, Option<Program>, BTreeMap<String, Export>);

fn run_frontend_full(
    pkg: &VirtualPackage,
    stage: Stage,
    prepared: PreparedInputs,
    cache: Option<&IncrementalCache>,
) -> Result<FrontendOutput, Vec<Diagnostic>> {
    let PreparedInputs {
        sources,
        valid,
        entry,
        imports,
        mut diagnostics,
        ..
    } = prepared;
    if stage == Stage::Source || !diagnostics.is_empty() {
        return if diagnostics.is_empty() {
            Ok((sources, None, imports))
        } else {
            Err(diagnostics)
        };
    }

    let mut parsed = Vec::new();
    if stage == Stage::Lex {
        for item in valid {
            if let Some(file) = sources.get(item.id) {
                let lexed = lexer::lex_with_recovery(file);
                diagnostics.extend(lexed.diagnostics);
            }
        }
    } else {
        for item in valid {
            let Some(file) = sources.get(item.id) else {
                continue;
            };
            let kind = if item.from_interface {
                FileKind::Interface
            } else if file.path().to_string_lossy().ends_with(".d.ril")
                || Some(file.id()) == entry && pkg.unit == Unit::Decl
            {
                FileKind::Foreign
            } else if Some(file.id()) != entry {
                FileKind::Module
            } else {
                match pkg.unit {
                    Unit::Bin => FileKind::Executable,
                    Unit::Lib => FileKind::Module,
                    Unit::Snippet => FileKind::Snippet,
                    Unit::Decl => FileKind::Foreign,
                }
            };
            let file_result = match cache {
                Some(cache) => cache.parse_file(file, kind, item.content_hash),
                None => {
                    let lexed = lexer::lex_with_recovery(file);
                    if !lexed.diagnostics.is_empty() {
                        Err(lexed.diagnostics)
                    } else {
                        let out = parser::parse_with_recovery(file, &lexed.tokens, kind);
                        if !out.diagnostics.is_empty() {
                            Err(out.diagnostics)
                        } else {
                            Ok(hir::File::new(file.clone(), kind, out.ast, lexed.tokens))
                        }
                    }
                }
            };
            match file_result {
                Ok(hir_file) => parsed.push(hir_file),
                Err(mut file_diags) => diagnostics.append(&mut file_diags),
            }
        }
    }
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }
    if stage < Stage::Hir {
        return Ok((sources, None, imports));
    }
    let Some(entry) = entry else {
        let missing_id = FileId::from_path(&pkg.entry);
        return Err(vec![Diagnostic::error(
            Code::E0208,
            Span::new(missing_id, 0, 0),
            format!("missing entry {}", pkg.entry.display()),
        )]);
    };
    let program = hir::lower(parsed, entry)?;
    Ok((sources, Some(program), imports))
}

impl TestDriver for Compiler {
    fn check_stage(&self, pkg: &VirtualPackage, upto: Stage) -> CheckResult {
        self.check(pkg, upto).result
    }

    fn check_compat(&self, base: &VirtualPackage, revision: &VirtualPackage) -> CheckResult {
        let file_paths = prepare_inputs(revision, self.cache()).sources.file_paths();
        let diagnostics = match (self.interface(base), self.interface(revision)) {
            (Ok(base), Ok(revision)) => base.compare(&revision),
            (Err(diagnostics), _) | (_, Err(diagnostics)) => diagnostics,
        };
        CheckResult {
            diagnostics,
            file_paths,
            ..CheckResult::default()
        }
    }

    fn run_jit(&self, package: &VirtualPackage) -> Result<ExecOutput, Vec<Diagnostic>> {
        self.execute_jit(package)
    }

    fn build_aot(
        &self,
        package: &VirtualPackage,
        output: &std::path::Path,
    ) -> Result<(), Vec<Diagnostic>> {
        self.compile_aot(package, output)
    }
}

impl TestDriver for Driver {
    fn check_stage(&self, pkg: &VirtualPackage, upto: Stage) -> CheckResult {
        self.with_options(CompileOptions::default())
            .check_stage(pkg, upto)
    }

    fn check_compat(&self, base: &VirtualPackage, revision: &VirtualPackage) -> CheckResult {
        self.with_options(CompileOptions::default())
            .check_compat(base, revision)
    }

    fn run_jit(&self, package: &VirtualPackage) -> Result<ExecOutput, Vec<Diagnostic>> {
        self.with_options(CompileOptions::default())
            .run_jit(package)
    }

    fn build_aot(
        &self,
        package: &VirtualPackage,
        output: &std::path::Path,
    ) -> Result<(), Vec<Diagnostic>> {
        self.with_options(CompileOptions::default())
            .build_aot(package, output)
    }
}
