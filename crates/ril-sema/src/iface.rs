use std::collections::BTreeMap;

use ril_base::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_frontend::{
    hir::{DefinitionKind, Program, Resolution},
    syntax::{
        Ast, GenericArg, GenericParam, StmtKind, Type, TypeDefinition, TypeId, TypeKind, Variant,
        Visibility,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    access::{Analysis, Instance, Summary},
    ty::{Ty, TypedProgram},
};

pub const FORMAT_VERSION: u32 = 3;

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Interface {
    pub format_version: u32,
    pub abi_hash: String,
    pub functions: BTreeMap<String, Export>,
    pub declarations: BTreeMap<String, Declaration>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Export {
    pub signature: String,
    pub shape: String,
    pub public: bool,
    pub compile_time: bool,
    pub generics: Vec<Generic>,
    pub parameter_defaults: Vec<Option<String>>,
    pub meta_parameters: Vec<bool>,
    pub summary: Summary,
    pub domain: Vec<Instance>,
    #[serde(skip)]
    span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Declaration {
    pub shape: String,
    pub generics: Vec<Generic>,
    pub public: bool,
    #[serde(skip)]
    span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Generic {
    pub name: String,
    pub bounds: Vec<String>,
    pub guards: Vec<String>,
    pub default: Option<String>,
}

impl Interface {
    pub fn build(program: &TypedProgram, analysis: &Analysis) -> Self {
        let mut functions = BTreeMap::new();
        for (&id, callable) in &program.callables {
            let def = program.hir.definition(id);
            if def.kind != DefinitionKind::Function || def.visibility == Visibility::Private {
                continue;
            }
            let Some(stmt) = def.stmt else {
                continue;
            };
            let ast = &program.hir.file(def.name.span.file).ast;
            let StmtKind::Function(function) = &ast.stmt(stmt).value.kind else {
                continue;
            };
            let key = program.hir.export_name(id);
            let signature = format!("{}", Ty::Callable(callable.clone()).display(&program.hir));
            let mut shape = (**callable).clone();
            if function.body.is_some() {
                shape.effects.clear();
                shape.state.clear();
            }
            let shape = Ty::Callable(std::sync::Arc::new(shape))
                .qualified_display(&program.hir)
                .to_string();
            functions.insert(
                key,
                Export {
                    signature,
                    shape,
                    public: def.visibility == Visibility::Public,
                    compile_time: function.is_meta,
                    generics: generics(program, ast, &function.generics),
                    parameter_defaults: function
                        .signature
                        .params
                        .iter()
                        .map(|param| {
                            param
                                .default
                                .map(|expr| fingerprint(program, ast.expr(expr).span))
                        })
                        .collect(),
                    meta_parameters: callable
                        .parameters
                        .iter()
                        .map(|param| param.is_meta)
                        .collect(),
                    summary: analysis.summaries.get(&id).cloned().unwrap_or_default(),
                    domain: analysis.via.get(&id).cloned().unwrap_or_default(),
                    span: def.name.span,
                },
            );
        }
        let declarations = program
            .hir
            .definitions()
            .filter_map(|(id, def)| {
                if def.visibility == Visibility::Private {
                    return None;
                }
                let stmt = def.stmt?;
                let ast = &program.hir.file(def.name.span.file).ast;
                let (shape, params) = match (&ast.stmt(stmt).value.kind, def.kind) {
                    (StmtKind::Type(decl), DefinitionKind::Type | DefinitionKind::Sum(_)) => {
                        let body = if decl.kind == TypeKind::Opaque {
                            "sealed".into()
                        } else {
                            match &decl.definition {
                                TypeDefinition::Data(ty) => type_shape(program, ast, *ty),
                                TypeDefinition::Opaque => "unit".into(),
                                TypeDefinition::Function(_, body) => format!(
                                    "type function {}",
                                    fingerprint(program, ast.expr(*body).span)
                                ),
                                TypeDefinition::Sum(variants) => {
                                    let mut shape: Vec<_> = variants
                                        .iter()
                                        .map(|variant| match variant {
                                            Variant::Constructor { name, payload, .. } => {
                                                payload.as_ref().map_or_else(
                                                    || name.value.clone(),
                                                    |types| {
                                                        let fields: Vec<_> = types
                                                            .iter()
                                                            .map(|&ty| type_shape(program, ast, ty))
                                                            .collect();
                                                        format!(
                                                            "{}({})",
                                                            name.value,
                                                            fields.join(", ")
                                                        )
                                                    },
                                                )
                                            }
                                            Variant::Spread(ty) => {
                                                format!("..{}", type_shape(program, ast, *ty))
                                            }
                                            Variant::Extensible => "..".into(),
                                        })
                                        .collect();
                                    shape.sort();
                                    format!("{{ {} }}", shape.join("; "))
                                }
                            }
                        };
                        let cleanup = decl
                            .cleanup
                            .as_ref()
                            .map_or_else(String::new, |cleanup| format!(" use({})", cleanup.value));
                        let parameters = match &decl.definition {
                            TypeDefinition::Function(params, _) => params.as_slice(),
                            _ => decl.generics.as_slice(),
                        };
                        (format!("{:?} {body}{cleanup}", decl.kind), parameters)
                    }
                    (
                        StmtKind::Effect {
                            generics, spreads, ..
                        },
                        DefinitionKind::Effect(_),
                    ) => {
                        let mut members: Vec<_> = spreads
                            .iter()
                            .map(|&spread| match &ast.ty(spread).value {
                                Type::Named(path) => path_shape(program, path),
                                _ => type_shape(program, ast, spread),
                            })
                            .collect();
                        members.sort();
                        (
                            format!("eff {{ {} }}", members.join("; ")),
                            generics.as_slice(),
                        )
                    }
                    (StmtKind::Binding { is_meta, value, .. }, DefinitionKind::Constant) => {
                        let ty = program.bindings.get(&id)?;
                        let mut shape = ty.qualified_display(&program.hir).to_string();
                        if *is_meta
                            && let Some(value) =
                                value.and_then(|id| program.static_values.get(&ast.expr(id).span))
                        {
                            shape = format!("meta {shape} = {}", crate::ty::render(value));
                        }
                        (shape, &[][..])
                    }
                    _ => return None,
                };
                Some((
                    program.hir.export_name(id),
                    Declaration {
                        shape,
                        generics: generics(program, ast, params),
                        public: def.visibility == Visibility::Public,
                        span: def.name.span,
                    },
                ))
            })
            .collect();
        let mut result = Self {
            format_version: FORMAT_VERSION,
            abi_hash: String::new(),
            functions,
            declarations,
        };
        result.abi_hash = result.compute_hash();
        result
    }

    fn compute_hash(&self) -> String {
        let data = serde_json::to_vec(&(self.format_version, &self.functions, &self.declarations))
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
                    && (!baseline.public || export.public)
                    && baseline.compile_time == export.compile_time
                    && baseline.generics == export.generics
                    && baseline.meta_parameters == export.meta_parameters
                    && baseline
                        .parameter_defaults
                        .iter()
                        .zip(&export.parameter_defaults)
                        .all(|(old, new)| old.is_none() || new.is_some())
                    && if baseline.domain.is_empty() {
                        baseline.summary.subsumes(&export.summary)
                    } else {
                        Instance::domain_subsumes(&baseline.domain, &export.domain)
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
        for (name, baseline) in &self.declarations {
            let revised = revision.declarations.get(name);
            if !revised.is_some_and(|entry| {
                baseline.shape == entry.shape
                    && baseline.generics == entry.generics
                    && (!baseline.public || entry.public)
            }) {
                diagnostics.push(Diagnostic::error(
                    Code::E0552,
                    revised.map_or(baseline.span, |entry| entry.span),
                    format!("incompatible published declaration for {name}"),
                ));
            }
        }
        diagnostics
    }
}

fn type_shape(program: &TypedProgram, ast: &Ast, id: TypeId) -> String {
    program
        .types
        .get(&ast.ty(id).span)
        .unwrap_or(&Ty::Unknown)
        .qualified_display(&program.hir)
        .to_string()
}

fn fingerprint(program: &TypedProgram, span: Span) -> String {
    let tokens: Vec<_> = program.hir.file(span.file).token_text(span).collect();
    let bytes = serde_json::to_vec(&tokens)
        .unwrap_or_else(|err| ril_base::ice!("token encoding failed: {err}"));
    format!("{:x}", Sha256::digest(bytes))
}

fn path_shape(program: &TypedProgram, path: &ril_frontend::syntax::Path) -> String {
    if let Some(Resolution::Definition(def)) = program.hir.resolve(path.span) {
        program.hir.export_name(def)
    } else {
        path.segments
            .iter()
            .map(|segment| segment.name.value.as_str())
            .collect::<Vec<_>>()
            .join("::")
    }
}

fn generics(program: &TypedProgram, ast: &Ast, params: &[GenericParam]) -> Vec<Generic> {
    params
        .iter()
        .map(|param| {
            let mut bounds: Vec<_> = param
                .bound
                .iter()
                .map(|&ty| type_shape(program, ast, ty))
                .collect();
            bounds.sort();
            let default = param.default.as_ref().map(|default| match default {
                GenericArg::Type(ty) => fingerprint(program, ast.ty(*ty).span),
                GenericArg::Value(expr) => fingerprint(program, ast.expr(*expr).span),
                GenericArg::Mode(storage) => format!("{:?} {}", storage.mode, storage.variable),
            });
            Generic {
                name: param.name.value.clone(),
                bounds,
                guards: param
                    .guards
                    .iter()
                    .map(|guard| path_shape(program, guard))
                    .collect(),
                default,
            }
        })
        .collect()
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
