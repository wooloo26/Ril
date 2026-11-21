#![forbid(unsafe_code)]

use ril_base::span::SourceMap;
use ril_test::{CheckResult, Stage, TestDriver, VirtualPackage};

pub const AVAILABLE: ril_test::Milestone = ril_test::Milestone::M1;

#[derive(Default)]
pub struct Driver;

pub struct Checked {
    pub sources: SourceMap,
    pub result: CheckResult,
}

impl Driver {
    pub fn check(&self, pkg: &VirtualPackage, stage: Stage) -> Checked {
        let mut sources = SourceMap::default();
        let mut result = CheckResult::default();
        let mut valid = Vec::new();
        for (path, file) in &pkg.files {
            match sources.add(path.clone(), &file.bytes) {
                Ok(id) => valid.push(id),
                Err(diagnostic) => result.diagnostics.push(*diagnostic),
            }
        }
        if result.diagnostics.is_empty() && stage >= Stage::Lex {
            for file in valid.into_iter().filter_map(|id| sources.get(id)) {
                if let Err(diagnostic) = ril_frontend::lexer::lex(file) {
                    result.diagnostics.push(diagnostic);
                }
            }
        }
        if result.diagnostics.is_empty() && stage > Stage::Lex {
            result = CheckResult::unsupported(format!("compiler stage {stage:?} is unavailable"));
        }
        Checked { sources, result }
    }
}

impl TestDriver for Driver {
    fn check_stage(&self, pkg: &VirtualPackage, upto: Stage) -> CheckResult {
        self.check(pkg, upto).result
    }
}
