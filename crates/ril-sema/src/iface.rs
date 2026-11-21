use std::collections::BTreeMap;

use ril_base::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_frontend::{
    hir::{DefinitionKind, Program},
    syntax::Visibility,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    access::{Analysis, Instance, Summary},
    ty::{Ty, TypedProgram},
};

pub const FORMAT_VERSION: u32 = 1;

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Interface {
    pub format_version: u32,
    pub abi_hash: String,
    pub functions: BTreeMap<String, Export>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Export {
    pub signature: String,
    pub shape: String,
    pub summary: Summary,
    pub domain: Vec<Instance>,
    #[serde(skip)]
    span: Span,
}

impl Interface {
    pub fn build(program: &TypedProgram, analysis: &Analysis) -> Self {
        let mut functions = BTreeMap::new();
        for (&id, callable) in &program.callables {
            let def = program.hir.definition(id);
            if def.kind != DefinitionKind::Function || def.visibility == Visibility::Private {
                continue;
            }
            let key = program.hir.export_name(id);
            let signature = format!("{}", Ty::Callable(callable.clone()).display(&program.hir));
            let mut shape = (**callable).clone();
            shape.effects.clear();
            shape.state.clear();
            let shape = Ty::Callable(std::sync::Arc::new(shape))
                .display(&program.hir)
                .to_string();
            functions.insert(
                key,
                Export {
                    signature,
                    shape,
                    summary: analysis.summaries.get(&id).cloned().unwrap_or_default(),
                    domain: analysis.via.get(&id).cloned().unwrap_or_default(),
                    span: def.name.span,
                },
            );
        }
        let mut result = Self {
            format_version: FORMAT_VERSION,
            abi_hash: String::new(),
            functions,
        };
        result.abi_hash = result.compute_hash();
        result
    }

    fn compute_hash(&self) -> String {
        let data = serde_json::to_vec(&(self.format_version, &self.functions))
            .unwrap_or_else(|err| ril_base::ice!("interface export serialization failed: {err}"));
        format!("{:x}", Sha256::digest(data))
    }

    pub fn encode(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec_pretty(self)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        let value: Self = serde_json::from_slice(bytes).map_err(|err| err.to_string())?;
        if value.format_version != FORMAT_VERSION {
            return Err(format!(
                "unsupported .rili format version {}",
                value.format_version
            ));
        }
        if value.compute_hash() != value.abi_hash {
            return Err(".rili ABI hash does not match its contents".into());
        }
        Ok(value)
    }

    pub fn compare(&self, revision: &Self) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        for (name, baseline) in &self.functions {
            let revised = revision.functions.get(name);
            let compatible = revised.is_some_and(|export| {
                baseline.shape == export.shape
                    && if baseline.domain.is_empty() {
                        subsumes_abi(&baseline.summary, &export.summary)
                    } else {
                        baseline.domain.iter().all(|row| {
                            export
                                .domain
                                .iter()
                                .find(|new| row.modes == new.modes)
                                .is_some_and(|new| subsumes_abi(&row.summary, &new.summary))
                        })
                    }
            });
            if !compatible {
                diagnostics.push(Diagnostic::error(
                    Code::E0552,
                    revised.map_or(baseline.span, |entry| entry.span),
                    format!("incompatible published interface for {name}"),
                ));
            }
        }
        diagnostics
    }
}

fn subsumes_abi(baseline: &Summary, revision: &Summary) -> bool {
    baseline.subsumes(revision)
        && baseline.roots == revision.roots
        && baseline.contained == revision.contained
}

pub fn signatures(program: &TypedProgram) -> BTreeMap<String, String> {
    let mut result = BTreeMap::new();
    for (&id, callable) in &program.callables {
        let def = program.hir.definition(id);
        let ty = Ty::Callable(callable.clone())
            .display(&program.hir)
            .to_string();
        let signature = ty
            .strip_prefix("fn")
            .map_or_else(|| ty.clone(), |sig| format!("fn {}{sig}", def.name.value));
        result.insert(program.hir.export_name(id), signature.clone());
        result.entry(def.name.value.clone()).or_insert(signature);
    }
    result
}

pub fn module_names(program: &Program) -> impl Iterator<Item = &std::path::Path> {
    program.files().map(|file| file.path.as_path())
}
