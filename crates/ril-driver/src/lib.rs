#![forbid(unsafe_code)]

use std::collections::BTreeMap;

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

mod native;
mod package;

pub use native::worker_entry;
pub use package::{infer_unit, load_package};

pub const AVAILABLE: ril_test::Milestone = ril_test::Milestone::M5;

#[derive(Default)]
pub struct Driver;

pub struct Checked {
    pub sources: SourceMap,
    pub result: CheckResult,
}

impl Driver {
    pub fn check(&self, pkg: &VirtualPackage, stage: Stage) -> Checked {
        let (sources, program, imports) = frontend(pkg, stage);
        let result = (|| {
            let Some(program) = program? else {
                return Ok(CheckResult::default());
            };
            if stage < Stage::Type {
                return Ok(CheckResult::default());
            }
            let typed = check_types(program, pkg.budget, imports)?;
            if stage == Stage::Access {
                access::check(&typed)?;
            }
            if stage >= Stage::Mir {
                let analysis = access::check(&typed)?;
                ril_backend::mir::lower(&typed, &analysis).map_err(|err| vec![err])?;
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
        Checked { sources, result }
    }

    pub fn analyze(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<(TypedProgram, Analysis), Vec<Diagnostic>> {
        let typed = self.typed(pkg)?;
        let analysis = access::check(&typed)?;
        Ok((typed, analysis))
    }

    fn typed(&self, pkg: &VirtualPackage) -> Result<TypedProgram, Vec<Diagnostic>> {
        let (_, program, imports) = frontend(pkg, Stage::Hir);
        let program =
            program?.ok_or_else(|| vec![Diagnostic::unsupported("missing frontend program")])?;
        check_types(program, pkg.budget, imports)
    }

    pub fn horn_rules(
        &self,
        pkg: &VirtualPackage,
    ) -> Result<Vec<access::horn::Rule<usize>>, Vec<Diagnostic>> {
        Ok(access::horn_rules(&self.typed(pkg)?))
    }
    pub fn interface(&self, pkg: &VirtualPackage) -> Result<Interface, Vec<Diagnostic>> {
        let (program, analysis) = self.analyze(pkg)?;
        Ok(Interface::build(&program, &analysis))
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

type Frontend = (
    SourceMap,
    Result<Option<Program>, Vec<Diagnostic>>,
    BTreeMap<String, Export>,
);

fn frontend(pkg: &VirtualPackage, stage: Stage) -> Frontend {
    let mut sources = SourceMap::default();
    let mut diagnostics = Vec::new();
    let mut valid = Vec::new();
    let mut entry = None;
    let mut imports = BTreeMap::new();
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
            match Interface::decode(&file.bytes).and_then(|interface| {
                let (module, source) = interface
                    .module(&logical)
                    .ok_or_else(|| format!("no declarations for {}", logical.display()))?;
                let prefix = format!("{module}::");
                imports.extend(interface.functions.iter().filter_map(|(name, export)| {
                    name.strip_prefix(&prefix)
                        .map(|local| (format!("{}::{local}", logical.display()), export.clone()))
                }));
                Ok(source.as_bytes().to_vec())
            }) {
                Ok(data) => {
                    declarations = data;
                    &declarations
                }
                Err(error) => {
                    diagnostics.push(Diagnostic::unsupported(format!(
                        "{}: {error}",
                        path.display()
                    )));
                    continue;
                }
            }
        } else {
            &file.bytes
        };
        match sources.add(logical, data) {
            Ok(id) => {
                if path == &pkg.entry {
                    entry = Some(id);
                }
                valid.push((id, from_interface));
            }
            Err(diagnostic) => diagnostics.push(*diagnostic),
        }
    }
    if stage == Stage::Source || !diagnostics.is_empty() {
        let result = if diagnostics.is_empty() {
            Ok(None)
        } else {
            Err(diagnostics)
        };
        return (sources, result, imports);
    }

    let mut tokenized = Vec::new();
    for (file, from_interface) in valid
        .into_iter()
        .filter_map(|(id, interface)| sources.get(id).map(|file| (file, interface)))
    {
        match lexer::lex(file) {
            Ok(tokens) => tokenized.push((file, tokens, from_interface)),
            Err(diagnostic) => diagnostics.push(diagnostic),
        }
    }
    let mut parsed = Vec::new();
    if stage >= Stage::Parse && diagnostics.is_empty() {
        for (file, tokens, from_interface) in tokenized {
            let kind = if from_interface {
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
            match parser::parse(file, &tokens, kind) {
                Ok(ast) => parsed.push(hir::File::new(file.clone(), kind, ast, tokens)),
                Err(diagnostic) => diagnostics.push(diagnostic),
            }
        }
    }
    let result = if !diagnostics.is_empty() {
        Err(diagnostics)
    } else if stage < Stage::Hir {
        Ok(None)
    } else {
        let Some(entry) = entry else {
            return (
                sources,
                Err(vec![Diagnostic::error(
                    Code::E0208,
                    Span::new(FileId(0), 0, 0),
                    format!("missing entry {}", pkg.entry.display()),
                )]),
                imports,
            );
        };
        hir::lower(parsed, entry).map(Some)
    };
    (sources, result, imports)
}

impl TestDriver for Driver {
    fn check_stage(&self, pkg: &VirtualPackage, upto: Stage) -> CheckResult {
        self.check(pkg, upto).result
    }

    fn check_compat(&self, base: &VirtualPackage, revision: &VirtualPackage) -> CheckResult {
        let diagnostics = match (self.interface(base), self.interface(revision)) {
            (Ok(base), Ok(revision)) => base.compare(&revision),
            (Err(diagnostics), _) | (_, Err(diagnostics)) => diagnostics,
        };
        CheckResult {
            diagnostics,
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
