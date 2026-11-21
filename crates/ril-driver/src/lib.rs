#![forbid(unsafe_code)]

use ril_base::{
    diag::Diagnostic,
    span::{FileId, SourceMap},
};
use ril_frontend::{
    hir::{self, Program},
    lexer,
    parser::{self, FileKind},
};
use ril_sema::{
    access::{self, Analysis},
    iface::{self, Interface},
    ty::{self, TypedProgram},
};
use ril_test::{CheckResult, Stage, TestDriver, Unit, VirtualPackage};

pub const AVAILABLE: ril_test::Milestone = ril_test::Milestone::M3;

#[derive(Default)]
pub struct Driver;

pub struct Checked {
    pub sources: SourceMap,
    pub result: CheckResult,
}

impl Driver {
    pub fn check(&self, pkg: &VirtualPackage, stage: Stage) -> Checked {
        let (sources, program) = frontend(pkg, stage);
        let result = (|| {
            let Some(program) = program? else {
                return Ok(CheckResult::default());
            };
            if stage < Stage::Type {
                return Ok(CheckResult::default());
            }
            let typed = ty::check(program, pkg.budget)?;
            if stage >= Stage::Access {
                access::check(&typed)?;
            }
            if stage > Stage::Access {
                return Ok(CheckResult::unsupported(format!(
                    "compiler stage {stage:?} is unavailable"
                )));
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
        let (_, frontend) = frontend(pkg, Stage::Hir);
        let program =
            frontend?.ok_or_else(|| vec![Diagnostic::unsupported("missing frontend program")])?;
        let typed = ty::check(program, pkg.budget)?;
        let analysis = access::check(&typed)?;
        Ok((typed, analysis))
    }

    pub fn interface(&self, pkg: &VirtualPackage) -> Result<Interface, Vec<Diagnostic>> {
        let (program, analysis) = self.analyze(pkg)?;
        Ok(Interface::build(&program, &analysis))
    }
}

fn frontend(
    pkg: &VirtualPackage,
    stage: Stage,
) -> (SourceMap, Result<Option<Program>, Vec<Diagnostic>>) {
    let mut sources = SourceMap::default();
    let mut diagnostics = Vec::new();
    let mut valid = Vec::new();
    let mut entry = None;
    for (path, file) in &pkg.files {
        match sources.add(path.clone(), &file.bytes) {
            Ok(id) => {
                if path == &pkg.entry {
                    entry = Some(id);
                }
                valid.push(id);
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
        return (sources, result);
    }

    let mut tokenized = Vec::new();
    for file in valid.into_iter().filter_map(|id| sources.get(id)) {
        match lexer::lex(file) {
            Ok(tokens) => tokenized.push((file, tokens)),
            Err(diagnostic) => diagnostics.push(diagnostic),
        }
    }
    let mut parsed = Vec::new();
    if stage >= Stage::Parse && diagnostics.is_empty() {
        for (file, tokens) in tokenized {
            let kind = if file.path().to_string_lossy().ends_with(".d.ril")
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
                Ok(ast) => parsed.push(hir::File {
                    id: file.id(),
                    kind,
                    path: file.path().into(),
                    ast,
                }),
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
                    ril_base::diag::Code::E0208,
                    ril_base::span::Span::new(FileId(0), 0, 0),
                    format!("missing entry {}", pkg.entry.display()),
                )]),
            );
        };
        hir::lower(parsed, entry).map(Some)
    };
    (sources, result)
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
}
