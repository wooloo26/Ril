use std::{collections::BTreeMap, path::Path};

use ril_hir::{DefinitionKind, Program, Resolution};
use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceFile, Span},
};
use ril_syntax::{
    lexer,
    parser::{self, FileKind},
    syntax::{
        Ast, GenericArg, GenericParam, StmtId, StmtKind, Type, TypeDefinition, TypeId, TypeKind,
        Variant, Visibility,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    access::{Analysis, Summary, ViaDomain},
    ty::{Ty, TypedProgram},
};

const BINARY_MAGIC: &[u8; 5] = b"RILI\x00";
pub const FORMAT_VERSION: u32 = 1;

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Interface {
    pub format_version: u32,
    pub abi_hash: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub codegen_abi_hash: String,
    pub functions: BTreeMap<String, Export>,
    pub declarations: BTreeMap<String, Declaration>,
    pub modules: BTreeMap<String, String>,
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
    pub domain: ViaDomain,
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
            if def.kind != DefinitionKind::Function
                || def.visibility == Visibility::Private
                || program.hir.is_stdlib_file(def.name.span.file)
            {
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
            if function.body.is_some() || program.imported_functions.contains_key(&id) {
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
                    domain: analysis
                        .via
                        .get(&id)
                        .map_or_else(ViaDomain::default, ViaDomain::compact),
                    span: def.name.span,
                },
            );
        }
        let declarations = program
            .hir
            .definitions()
            .filter_map(|(id, def)| {
                if def.visibility == Visibility::Private
                    || program.hir.is_stdlib_file(def.name.span.file)
                {
                    return None;
                }
                let stmt = def.stmt?;
                let ast = &program.hir.file(def.name.span.file).ast;
                let (shape, params) = match (&ast.stmt(stmt).value.kind, def.kind) {
                    (StmtKind::Type(decl), DefinitionKind::Type | DefinitionKind::Sum(_)) => {
                        let body = if decl.kind == TypeKind::Opaque {
                            if program.hir.file(def.name.span.file).kind == FileKind::Foreign {
                                "foreign".into()
                            } else {
                                match &decl.definition {
                                    TypeDefinition::Sum(_) => "sealed sum".into(),
                                    TypeDefinition::Data(_) => {
                                        let param_ids: Vec<_> = decl
                                            .generics
                                            .iter()
                                            .map(|p| match program.hir.resolve(p.name.span) {
                                                Some(ril_hir::Resolution::Definition(pid)) => {
                                                    Some(pid)
                                                }
                                                _ => None,
                                            })
                                            .collect();
                                        let self_args = param_ids
                                            .iter()
                                            .filter_map(|opt| {
                                                opt.map(|pid| {
                                                    crate::ty::GenericValue::Type(
                                                        crate::ty::Ty::Param(pid),
                                                    )
                                                })
                                            })
                                            .collect();
                                        let adt = crate::ty::Adt {
                                            definition: id,
                                            kind: crate::ty::AdtKind::Opaque,
                                            defining_scope: def.scope,
                                            visibility: def.visibility,
                                            arguments: self_args,
                                        };
                                        let unwrapped = program.unwrap_wrapper(
                                            &crate::ty::Ty::Adt(std::sync::Arc::new(adt)),
                                        );
                                        if unwrapped.is_primitive_value() {
                                            "sealed value".into()
                                        } else if let crate::ty::Ty::Param(pid) = unwrapped
                                            && let Some(idx) =
                                                param_ids.iter().position(|p| *p == Some(pid))
                                        {
                                            format!("sealed param({idx})")
                                        } else {
                                            "sealed shared".into()
                                        }
                                    }
                                    TypeDefinition::Opaque => "foreign".into(),
                                    TypeDefinition::Function(..) => "sealed".into(),
                                }
                            }
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
        let mut opaque_layouts = BTreeMap::new();
        for (id, def) in program.hir.definitions() {
            if def.visibility == Visibility::Private
                || program.hir.is_stdlib_file(def.name.span.file)
            {
                continue;
            }
            let Some(stmt) = def.stmt else {
                continue;
            };
            let ast = &program.hir.file(def.name.span.file).ast;
            if let StmtKind::Type(decl) = &ast.stmt(stmt).value.kind
                && decl.kind == TypeKind::Opaque
            {
                let layout = match &decl.definition {
                    TypeDefinition::Data(ty) => type_shape(program, ast, *ty),
                    TypeDefinition::Opaque => "foreign".into(),
                    TypeDefinition::Function(_, body) => fingerprint(program, ast.expr(*body).span),
                    TypeDefinition::Sum(variants) => format!("sum:{}", variants.len()),
                };
                opaque_layouts.insert(program.hir.export_name(id), layout);
            }
        }
        let mut result = Self {
            format_version: FORMAT_VERSION,
            abi_hash: String::new(),
            codegen_abi_hash: String::new(),
            functions,
            declarations,
            modules: program
                .hir
                .files()
                .filter(|file| {
                    matches!(file.kind, FileKind::Module | FileKind::Interface)
                        && file.path.starts_with("pkg")
                })
                .map(|file| (file.path.display().to_string(), declaration_source(file)))
                .collect(),
        };
        result.abi_hash = result.compute_hash();
        result.codegen_abi_hash = result.compute_codegen_hash(&opaque_layouts);
        result
    }

    fn compute_hash(&self) -> String {
        let sealed = self.sealed_modules();
        let data = serde_json::to_vec(&(
            self.format_version,
            &self.functions,
            &self.declarations,
            &sealed,
        ))
        .unwrap_or_else(|err| ril_source::ice!("interface export serialization failed: {err}"));
        format!("{:x}", Sha256::digest(data))
    }

    fn sealed_modules(&self) -> BTreeMap<String, String> {
        self.modules
            .iter()
            .map(|(path, src)| (path.clone(), seal_opaque_representations(path, src)))
            .collect()
    }

    fn compute_codegen_hash(&self, opaque_layouts: &BTreeMap<String, String>) -> String {
        let data = serde_json::to_vec(&(&self.abi_hash, opaque_layouts))
            .unwrap_or_else(|err| ril_source::ice!("codegen hash serialization failed: {err}"));
        format!("{:x}", Sha256::digest(data))
    }

    /// Encodes the interface into the canonical binary `RILI\x00` envelope with header SHA-256.
    pub fn encode(&self) -> Result<Vec<u8>, serde_json::Error> {
        let payload = serde_json::to_vec(self)?;
        let digest = Sha256::digest(&payload);
        let len = u32::try_from(payload.len()).unwrap_or(u32::MAX);
        let mut out = Vec::with_capacity(BINARY_MAGIC.len() + 4 + 32 + 4 + payload.len());
        out.extend_from_slice(BINARY_MAGIC);
        out.extend_from_slice(&self.format_version.to_le_bytes());
        out.extend_from_slice(&digest);
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(&payload);
        Ok(out)
    }

    /// Encodes the interface as human-readable JSON (`--emit-interface-json`).
    pub fn encode_json(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec_pretty(self)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        if let Some(rest) = bytes.strip_prefix(BINARY_MAGIC) {
            let (header, payload) = rest
                .split_at_checked(40)
                .ok_or_else(|| "truncated binary .rili header".to_owned())?;
            let (ver_bytes, after_ver) = header
                .split_at_checked(4)
                .ok_or_else(|| "truncated binary .rili version".to_owned())?;
            let (expected_digest, len_bytes) = after_ver
                .split_at_checked(32)
                .ok_or_else(|| "truncated binary .rili digest".to_owned())?;
            let version = u32::from_le_bytes(
                ver_bytes
                    .try_into()
                    .map_err(|_| "invalid binary .rili version".to_owned())?,
            );
            if version != FORMAT_VERSION {
                return Err(format!("unsupported .rili format version {version}"));
            }
            let payload_len = u32::from_le_bytes(
                len_bytes
                    .try_into()
                    .map_err(|_| "invalid binary .rili length".to_owned())?,
            ) as usize;
            if payload.len() != payload_len {
                return Err("binary .rili payload length mismatch".into());
            }
            let actual_digest = Sha256::digest(payload);
            if actual_digest.as_slice() != expected_digest {
                return Err(".rili binary payload checksum mismatch".into());
            }
            let value: Self = serde_json::from_slice(payload).map_err(|err| err.to_string())?;
            if value.format_version != FORMAT_VERSION {
                return Err(".rili header version does not match payload version".into());
            }
            return Ok(value);
        }
        #[derive(Deserialize)]
        struct Version {
            format_version: u32,
        }
        let Version { format_version } =
            serde_json::from_slice(bytes).map_err(|err| err.to_string())?;
        if format_version != FORMAT_VERSION {
            return Err(format!("unsupported .rili format version {format_version}"));
        }
        let value: Self = serde_json::from_slice(bytes).map_err(|err| err.to_string())?;
        if value.compute_hash() != value.abi_hash {
            return Err(".rili ABI hash does not match its contents".into());
        }
        Ok(value)
    }

    /// Look up a module under its original name and return its bodyless declarations.
    pub fn module(&self, mounted: &Path) -> Option<(&str, &str)> {
        let relative = mounted.iter().skip(1).collect::<std::path::PathBuf>();
        let original = Path::new("pkg").join(relative);
        self.modules
            .get_key_value(original.to_str()?)
            .map(|(key, declarations)| (key.as_str(), declarations.as_str()))
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
                        baseline.domain.subsumes(&export.domain)
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

fn declaration_source(file: &ril_hir::File) -> String {
    fn omit_bodies(ast: &Ast, items: &[StmtId], spans: &mut Vec<Span>) {
        for &item in items {
            match &ast.stmt(item).value.kind {
                StmtKind::Function(function) if !function.is_meta => {
                    omit_bodies(ast, &function.helpers, spans);
                    if let Some(body) = function.body {
                        spans.push(ast.expr(body).span);
                    }
                }
                StmtKind::Sub { items, .. } => omit_bodies(ast, items, spans),
                _ => {}
            }
        }
    }
    let mut spans = Vec::new();
    omit_bodies(&file.ast, &file.ast.items, &mut spans);
    let mut source = file.source_text().to_owned();
    spans.sort_unstable();
    for span in spans.into_iter().rev() {
        source.replace_range(span.start..span.end, "");
    }
    source
}

fn seal_opaque_representations(path: &str, text: &str) -> String {
    fn collect_opaque_rhs(ast: &Ast, items: &[StmtId], spans: &mut Vec<Span>) {
        for &item in items {
            match &ast.stmt(item).value.kind {
                StmtKind::Type(decl) if decl.kind == TypeKind::Opaque => {
                    if let TypeDefinition::Data(ty) = decl.definition {
                        spans.push(ast.ty(ty).span);
                    }
                }
                StmtKind::Sub { items, .. } => collect_opaque_rhs(ast, items, spans),
                _ => {}
            }
        }
    }
    let Ok(src) = SourceFile::from_bytes(
        FileId::from_path(Path::new(path)),
        path.into(),
        text.as_bytes(),
    ) else {
        return text.to_owned();
    };
    let lexed = lexer::lex_with_recovery(&src);
    if !lexed.diagnostics.is_empty() {
        return text.to_owned();
    }
    let parsed = parser::parse_with_recovery(&src, &lexed.tokens, FileKind::Interface);
    let mut spans = Vec::new();
    collect_opaque_rhs(&parsed.ast, &parsed.ast.items, &mut spans);
    if spans.is_empty() {
        return text.to_owned();
    }
    let mut out = text.to_owned();
    spans.sort_unstable();
    for span in spans.into_iter().rev() {
        out.replace_range(span.start..span.end, "sealed");
    }
    out
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
        .unwrap_or_else(|err| ril_source::ice!("token encoding failed: {err}"));
    format!("{:x}", Sha256::digest(bytes))
}

fn path_shape(program: &TypedProgram, path: &ril_syntax::syntax::Path) -> String {
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
