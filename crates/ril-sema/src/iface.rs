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
    ty::{
        Ty, TypedProgram,
        proofs::{ExportProof, export_proofs_entail},
    },
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
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub behavior: BTreeMap<String, crate::behavior::BehaviorSummary>,
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
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub parameter_proofs: Vec<ExportProof>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub return_proofs: Vec<ExportProof>,
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
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub must_consume: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub must_consume_params: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub invariants: Vec<ExportProof>,
    #[serde(skip)]
    span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Generic {
    pub name: String,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub is_effect: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub direct_only: bool,
    pub bounds: Vec<String>,
    pub guards: Vec<String>,
    pub default: Option<String>,
}

impl Interface {
    pub fn build(program: &TypedProgram, analysis: &Analysis) -> Self {
        let mut functions = BTreeMap::new();
        let mut behavior = BTreeMap::new();
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
            if let Some(beh) = analysis.behavior.summaries.get(&id)
                && !beh.is_empty()
            {
                behavior.insert(key.clone(), beh.clone());
            }
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
                    parameter_proofs: program
                        .exported_param_proofs
                        .get(&id)
                        .cloned()
                        .unwrap_or_default(),
                    return_proofs: program
                        .exported_return_proofs
                        .get(&id)
                        .cloned()
                        .unwrap_or_default(),
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
                let (shape, params, must_consume, must_consume_params, invariants) =
                    match (&ast.stmt(stmt).value.kind, def.kind) {
                        (StmtKind::Type(decl), DefinitionKind::Type | DefinitionKind::Sum(_)) => {
                            let param_ids: Vec<_> = decl
                                .generics
                                .iter()
                                .map(|p| match program.hir.resolve(p.name.span) {
                                    Some(ril_hir::Resolution::Definition(pid)) => Some(pid),
                                    _ => None,
                                })
                                .collect();
                            let self_args: Vec<_> = param_ids
                                .iter()
                                .filter_map(|opt| {
                                    opt.map(|pid| {
                                        crate::ty::GenericValue::Type(crate::ty::Ty::Param(pid))
                                    })
                                })
                                .collect();
                            let adt_kind = if decl.kind == TypeKind::Opaque {
                                if matches!(decl.definition, TypeDefinition::Sum(_)) {
                                    crate::ty::AdtKind::OpaqueSum
                                } else {
                                    crate::ty::AdtKind::Opaque
                                }
                            } else if matches!(decl.definition, TypeDefinition::Sum(_)) {
                                crate::ty::AdtKind::Sum
                            } else {
                                crate::ty::AdtKind::Nominal
                            };
                            let self_adt = crate::ty::Adt {
                                definition: id,
                                kind: adt_kind,
                                is_linear: decl.is_linear,
                                defining_scope: def.scope,
                                visibility: def.visibility,
                                arguments: self_args,
                            };
                            let self_ty = crate::ty::Ty::Adt(std::sync::Arc::new(self_adt.clone()));
                            let is_must_consume = program.is_must_consume(&self_ty);
                            let mc_params: Vec<usize> = if decl.kind == TypeKind::Opaque {
                                param_ids
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(i, opt)| {
                                        let pid = (*opt)?;
                                        program
                                            .type_param_in_must_consume_position(&self_ty, pid)
                                            .then_some(i)
                                    })
                                    .collect()
                            } else {
                                Vec::new()
                            };
                            let body = if decl.kind == TypeKind::Opaque {
                                let base = match &decl.definition {
                                    TypeDefinition::Sum(_) => "sealed sum".into(),
                                    TypeDefinition::Data(_) => {
                                        let unwrapped = program.unwrap_wrapper(
                                            &crate::ty::Ty::Adt(std::sync::Arc::new(self_adt)),
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
                                    TypeDefinition::Opaque => "sealed".into(),
                                    TypeDefinition::Function(..) => "sealed".into(),
                                };
                                if is_must_consume {
                                    format!("{base} must_consume")
                                } else {
                                    base
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
                                                                .map(|&ty| {
                                                                    type_shape(program, ast, ty)
                                                                })
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
                            let parameters = match &decl.definition {
                                TypeDefinition::Function(params, _) => params.as_slice(),
                                _ => decl.generics.as_slice(),
                            };
                            let invariants = if decl.kind == TypeKind::Opaque {
                                Vec::new()
                            } else {
                                program
                                    .exported_type_invariants
                                    .get(&id)
                                    .cloned()
                                    .unwrap_or_default()
                            };
                            (
                                format!("{:?} {body}", decl.kind),
                                parameters,
                                is_must_consume,
                                mc_params,
                                invariants,
                            )
                        }
                        (
                            StmtKind::Effect {
                                generics,
                                spreads,
                                operations,
                                ..
                            },
                            DefinitionKind::Effect(_),
                        ) => {
                            let mut members: Vec<_> = spreads
                                .iter()
                                .map(|&spread| match &ast.ty(spread).value {
                                    Type::Named(path) => path_shape(program, path),
                                    _ => type_shape(program, ast, spread),
                                })
                                .chain(operations.iter().filter_map(|&stmt_id| {
                                    if let StmtKind::Function(op) = &ast.stmt(stmt_id).value.kind {
                                        let kind = if op.signature.is_ctl { "ctl" } else { "fn" };
                                        Some(format!("{kind} {}", op.name.value))
                                    } else {
                                        None
                                    }
                                }))
                                .collect();
                            members.sort();
                            (
                                format!("eff {{ {} }}", members.join("; ")),
                                generics.as_slice(),
                                false,
                                Vec::new(),
                                Vec::new(),
                            )
                        }
                        (StmtKind::Binding { is_meta, value, .. }, DefinitionKind::Constant) => {
                            let ty = program.bindings.get(&id)?;
                            let mut shape = ty.qualified_display(&program.hir).to_string();
                            if *is_meta
                                && let Some(value) = value
                                    .and_then(|id| program.static_values.get(&ast.expr(id).span))
                            {
                                shape = format!("meta {shape} = {}", crate::ty::render(value));
                            }
                            (shape, &[][..], false, Vec::new(), Vec::new())
                        }
                        _ => return None,
                    };
                Some((
                    program.hir.export_name(id),
                    Declaration {
                        shape,
                        generics: generics(program, ast, params),
                        public: def.visibility == Visibility::Public,
                        must_consume,
                        must_consume_params,
                        invariants,
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
            behavior,
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
                    && export_proofs_entail(&baseline.parameter_proofs, &export.parameter_proofs)
                    && export_proofs_entail(&export.return_proofs, &baseline.return_proofs)
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
                    && baseline.must_consume == entry.must_consume
                    && baseline.must_consume_params == entry.must_consume_params
                    && export_proofs_entail(&baseline.invariants, &entry.invariants)
                    && export_proofs_entail(&entry.invariants, &baseline.invariants)
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
    fn omit_bodies(ast: &Ast, items: &[StmtId], replacements: &mut Vec<(Span, &'static str)>) {
        for &item in items {
            match &ast.stmt(item).value.kind {
                StmtKind::Function(function) if !function.is_meta => {
                    omit_bodies(ast, &function.helpers, replacements);
                    if let Some(body) = function.body {
                        let repl = if function.helpers.is_empty() {
                            ""
                        } else {
                            "{}"
                        };
                        replacements.push((ast.expr(body).span, repl));
                    }
                }
                StmtKind::Sub { items, .. } => omit_bodies(ast, items, replacements),
                _ => {}
            }
        }
    }
    let mut replacements = Vec::new();
    omit_bodies(&file.ast, &file.ast.items, &mut replacements);
    let mut source = file.source_text().to_owned();
    replacements.sort_unstable_by_key(|(span, _)| *span);
    for (span, repl) in replacements.into_iter().rev() {
        source.replace_range(span.start..span.end, repl);
    }
    source
}

fn seal_opaque_representations(path: &str, text: &str) -> String {
    fn collect_opaque_rhs(
        ast: &Ast,
        items: &[StmtId],
        replacements: &mut Vec<(Span, &'static str)>,
    ) {
        for &item in items {
            match &ast.stmt(item).value.kind {
                StmtKind::Type(decl) if decl.kind == TypeKind::Opaque => {
                    if let TypeDefinition::Data(ty) = decl.definition {
                        let ty_span = ast.ty(ty).span;
                        replacements.push((ty_span, "sealed"));
                        if let Some(&last_guard) = decl.guards.last() {
                            let stmt_span = ast.stmt(item).span;
                            let guard_end = ast.expr(last_guard).span.end.min(stmt_span.end);
                            // Strip trailing `|> ...` guards after the closing `)` of `opaque type Name(T)`.
                            if guard_end > ty_span.end {
                                replacements.push((
                                    Span {
                                        file: ty_span.file,
                                        start: ty_span.end,
                                        end: guard_end,
                                    },
                                    ")",
                                ));
                            }
                        }
                    }
                }
                StmtKind::Sub { items, .. } => collect_opaque_rhs(ast, items, replacements),
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
    let mut replacements = Vec::new();
    collect_opaque_rhs(&parsed.ast, &parsed.ast.items, &mut replacements);
    if replacements.is_empty() {
        return text.to_owned();
    }
    let mut out = text.to_owned();
    replacements.sort_unstable_by_key(|(span, _)| *span);
    for (span, repl) in replacements.into_iter().rev() {
        out.replace_range(span.start..span.end, repl);
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
                GenericArg::Effect(_, span) => fingerprint(program, *span),
            });
            Generic {
                name: param.name.value.clone(),
                is_effect: param.is_effect,
                direct_only: param.direct_only,
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
