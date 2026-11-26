use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Path, PathBuf},
};

use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_syntax::{
    lexer::{Word, word_kind},
    parser::FileKind,
    syntax::{Name, Pattern, StmtId, StmtKind, Type, TypeDefinition, Variant, Visibility},
};

use crate::{
    DefinitionId, DefinitionKind, Entry, File, PrimitivePhase, Program, ScopeId, Target, builtins,
    walk,
};

pub fn lower(files: Vec<File>, entry: FileId) -> Result<Program, Vec<Diagnostic>> {
    let (program, errors) = lower_impl(files, entry, false);
    if errors.is_empty() {
        Ok(program)
    } else {
        Err(errors)
    }
}

/// Lowering variant for IDE/LSP use that always returns the partially resolved
/// `Program` alongside any HIR diagnostics.
pub fn lower_partial(files: Vec<File>, entry: FileId) -> (Program, Vec<Diagnostic>) {
    lower_impl(files, entry, true)
}

fn lower_impl(files: Vec<File>, entry: FileId, partial: bool) -> (Program, Vec<Diagnostic>) {
    let mut program = Program {
        files: files.into_iter().map(|file| (file.id.0, file)).collect(),
        modules: BTreeMap::new(),
        roots: BTreeMap::new(),
        scopes: Vec::new(),
        definitions: Vec::new(),
        resolutions: HashMap::new(),
        resolutions_by_file: HashMap::new(),
        namespace_owner: HashMap::new(),
        effect_owner: HashMap::new(),
        effect_by_label_map: HashMap::new(),
        local_effects: BTreeSet::new(),
        effect_spreads: BTreeMap::new(),
        package_edges: BTreeMap::new(),
        pending_operations: Vec::new(),
        std_types: BTreeMap::new(),
        std_type_ids: HashMap::new(),
        stdlib_files: BTreeSet::new(),
        entry,
        prelude: ScopeId(0),
    };
    program.init_prelude();
    let units: Vec<_> = program
        .files()
        .map(|file| {
            (
                file.id,
                file.path.clone(),
                file.kind,
                file.ast.items.clone(),
            )
        })
        .collect();
    let mut errors = Vec::new();
    let mut imports = Vec::new();
    for (id, path, kind, items) in units {
        if let Some(std_key) = builtins::std_import_key(&path) {
            program.stdlib_files.insert(id);
            if std_key == "ril/prelude" {
                let root = program.prelude;
                program.scope_mut(root).file = id;
                program.roots.insert(id.0, root);
                program.modules.insert(PathBuf::from(std_key), root);
                program.collect(root, &items, &mut imports, &mut errors);
                continue;
            }
            let root = program.new_scope(id, "ril".into(), None, Visibility::Public);
            program.scope_mut(root).primitive_module = builtins::module(&path);
            program.roots.insert(id.0, root);
            program.modules.insert(PathBuf::from(std_key), root);
            program.collect(root, &items, &mut imports, &mut errors);
            continue;
        }
        let package = mount(&path).to_owned();
        let has_pub = items.iter().any(|&id_stmt| {
            program.file(id).ast.stmt(id_stmt).value.visibility == Visibility::Public
        });
        let cap = if has_pub {
            Visibility::Public
        } else {
            Visibility::Package
        };
        let root = program.new_scope(id, package, None, cap);
        program.scope_mut(root).primitive_module = builtins::module(&path);
        program.roots.insert(id.0, root);
        if kind != FileKind::Executable {
            let name = module_key(&path);
            if program
                .modules
                .insert(name, root)
                .is_some_and(|old| program.scope(old).file != FileId::BUILTIN)
            {
                errors.push(Diagnostic::error(
                    Code::E0203,
                    Span::new(id, 0, 0),
                    "duplicate module file",
                ));
            }
        }
        program.collect(root, &items, &mut imports, &mut errors);
        if kind == FileKind::Executable {
            program.validate_main(root, &mut errors);
        }
    }
    program.attach_stdlib(&mut imports, &mut errors);
    program.load_imports(imports, &mut errors);
    if errors.is_empty() || partial {
        walk::check(&mut program, &mut errors);
        program.check_package_cycles(&mut errors);
        program.resolve_effect_spreads(&mut errors);
        program.finalize_indices();
    }
    (program, errors)
}

fn mount(path: &Path) -> &str {
    path.iter()
        .next()
        .and_then(std::ffi::OsStr::to_str)
        .filter(|_| path.components().count() >= 2)
        .unwrap_or("pkg")
}

pub(crate) fn module_key(path: &Path) -> PathBuf {
    let mut result = if path.components().count() == 1 {
        Path::new("pkg").join(path)
    } else {
        path.to_owned()
    };
    if let Some(name) = result.file_name().and_then(std::ffi::OsStr::to_str) {
        let stem = name
            .strip_suffix(".d.ril")
            .or_else(|| name.strip_suffix(".ril"))
            .unwrap_or(name)
            .to_owned();
        result.set_file_name(stem);
    }
    result
}

pub(crate) fn module_name(name: &Name) -> Result<Name, Diagnostic> {
    let mut derived = String::new();
    for part in name.value.split('_') {
        let mut letters = part.chars();
        let Some(first) = letters.next().filter(char::is_ascii_lowercase) else {
            return Err(Diagnostic::error(
                Code::E0102,
                name.span,
                "invalid derived module name",
            ));
        };
        derived.push(first.to_ascii_uppercase());
        derived.push_str(letters.as_str());
    }
    if word_kind(&derived) != Some(Word::Pascal) {
        return Err(Diagnostic::error(
            Code::E0102,
            name.span,
            "invalid derived module name",
        ));
    }
    Ok(Name::new(derived, name.span))
}

impl Program {
    pub(crate) fn collect(
        &mut self,
        scope: ScopeId,
        items: &[StmtId],
        imports: &mut Vec<(ScopeId, StmtId)>,
        errors: &mut Vec<Diagnostic>,
    ) {
        let file = self.scope(scope).file;
        let module_root = self.roots.get(&file.0) == Some(&scope);
        for &id in items {
            let node = self.file(file).ast.stmt(id).clone();
            let vis = node.value.visibility;
            let declaration = match node.value.kind {
                StmtKind::Function(function) => {
                    let kind = if function.body.is_none()
                        && !matches!(
                            self.file(file).kind,
                            FileKind::Foreign | FileKind::Interface
                        ) {
                        let registered = if module_root {
                            builtins::bodyless(self.file(file), node.span, &function)
                        } else {
                            Err(builtins::missing_body(function.name.span))
                        };
                        match registered {
                            Ok(phase) => DefinitionKind::Primitive(phase),
                            Err(diagnostic) => {
                                errors.push(diagnostic);
                                DefinitionKind::Function
                            }
                        }
                    } else {
                        DefinitionKind::Function
                    };
                    self.register(scope, function.name, kind, id, vis)
                }
                StmtKind::Type(decl) => {
                    let registration = if module_root {
                        builtins::registered_type(self.file(file), node.span, &decl)
                    } else {
                        None
                    };
                    let contract = match registration {
                        Some(Ok(registration)) => Some(registration),
                        Some(Err(diagnostic)) => {
                            errors.push(diagnostic);
                            continue;
                        }
                        None => None,
                    };
                    if matches!(decl.definition, TypeDefinition::Opaque)
                        && self.file(file).kind != FileKind::Foreign
                        && decl.kind == ril_syntax::syntax::TypeKind::Opaque
                        && contract.is_none()
                    {
                        errors.push(Diagnostic::error(
                            Code::E0902,
                            decl.name.span,
                            "opaque type requires a representation",
                        ));
                    }
                    if let TypeDefinition::Sum(variants) = decl.definition {
                        let namespace = self.child(scope, vis, false);
                        let type_name = decl.name.value.clone();
                        let Ok(sum) = self
                            .register(scope, decl.name, DefinitionKind::Sum(namespace), id, vis)
                            .map_err(|err| errors.push(err))
                        else {
                            continue;
                        };
                        if let Some(module_name) = self.scope(scope).primitive_module
                            && let Some(std_type) = builtins::std_type_for(module_name, &type_name)
                        {
                            self.std_types.entry(std_type).or_insert(sum);
                            self.std_type_ids.insert(sum, std_type);
                        }
                        for variant in variants {
                            if let Variant::Constructor { name, .. } = variant
                                && let Err(err) = self.register(
                                    namespace,
                                    name.clone(),
                                    DefinitionKind::Variant(sum),
                                    id,
                                    Visibility::Public,
                                )
                            {
                                errors.push(err);
                            }
                        }
                        Ok(sum)
                    } else {
                        let kind = if matches!(contract, Some(builtins::TypeRegistration::Object)) {
                            DefinitionKind::Primitive(PrimitivePhase::Runtime)
                        } else {
                            DefinitionKind::Type
                        };
                        let type_name = decl.name.value.clone();
                        let result = self.register(scope, decl.name, kind, id, vis);
                        if let Ok(def_id) = result
                            && let Some(module_name) = self.scope(scope).primitive_module
                            && let Some(std_type) = builtins::std_type_for(module_name, &type_name)
                        {
                            self.std_types.entry(std_type).or_insert(def_id);
                            self.std_type_ids.insert(def_id, std_type);
                        }
                        result
                    }
                }
                StmtKind::Effect {
                    name, operations, ..
                } => {
                    let namespace = self.child(scope, vis, false);
                    let effect =
                        self.register(scope, name, DefinitionKind::Effect(namespace), id, vis);
                    for operation in operations {
                        if let StmtKind::Function(function) =
                            &self.file(file).ast.stmt(operation).value.kind
                            && let Err(err) = self.register(
                                namespace,
                                function.name.clone(),
                                DefinitionKind::Function,
                                operation,
                                Visibility::Public,
                            )
                        {
                            errors.push(err);
                        }
                    }
                    effect
                }
                StmtKind::Sub { name, items } => {
                    let namespace = self.child(scope, vis, true);
                    let result =
                        self.register(scope, name, DefinitionKind::Namespace(namespace), id, vis);
                    self.collect(namespace, &items, imports, errors);
                    result
                }
                StmtKind::Binding {
                    pattern,
                    storage,
                    is_meta,
                    value,
                    ..
                } => {
                    if let Pattern::Binding(_, name) = &self.file(file).ast.pattern(pattern).value {
                        let source = self.file(file);
                        let kind = if source.kind == FileKind::Snippet
                            && !is_meta
                            && (storage.variable
                                || storage.mode != ril_syntax::syntax::Mode::Plain
                                || value.is_some_and(|value| {
                                    matches!(
                                        source.ast.expr(value).value,
                                        ril_syntax::syntax::Expr::Closure { .. }
                                    )
                                })) {
                            DefinitionKind::Local
                        } else {
                            DefinitionKind::Constant
                        };
                        self.register(scope, name.clone(), kind, id, vis)
                    } else {
                        continue;
                    }
                }
                StmtKind::Import(_) => {
                    imports.push((scope, id));
                    continue;
                }
                StmtKind::With(_) | StmtKind::Expr(_) | StmtKind::Error => continue,
            };
            if let Err(err) = declaration {
                errors.push(err);
            }
        }
    }

    fn finalize_indices(&mut self) {
        self.resolutions_by_file.clear();
        for (&span, &resolved) in &self.resolutions {
            if let Some(id) = resolved.definition() {
                self.resolutions_by_file
                    .entry(span.file)
                    .or_default()
                    .push((span, id));
            }
        }
        self.effect_by_label_map.clear();
        let effect_ids: Vec<_> = self
            .definitions
            .iter()
            .enumerate()
            .filter_map(|(idx, def)| {
                matches!(def.kind, DefinitionKind::Effect(_)).then_some(DefinitionId(idx))
            })
            .collect();
        for id in effect_ids {
            let label = self.effect_label(id);
            self.effect_by_label_map.insert(label, id);
        }
    }

    fn validate_main(&self, root: ScopeId, errors: &mut Vec<Diagnostic>) {
        let scope = self.scope(root);
        let Some(Entry {
            target: Target::Def(def),
            ..
        }) = scope.names.get("main")
        else {
            errors.push(Diagnostic::error(
                Code::E0903,
                Span::new(scope.file, 0, 0),
                "missing executable entry point",
            ));
            return;
        };
        let def = self.definition(*def);
        let ast = &self.file(scope.file).ast;
        let valid = def.stmt.is_some_and(|id| match &ast.stmt(id).value.kind {
            StmtKind::Function(fun) => {
                let signature = &fun.signature;
                let result_ok = match &ast.ty(signature.result).value {
                    Type::Unit => signature.result_mode == ril_syntax::syntax::Mode::Plain,
                    Type::Result(ok, err) => {
                        matches!(ast.ty(*ok).value, Type::Unit)
                            && matches!(&ast.ty(*err).value, Type::Named(path) if path.segments.len() == 1
                                && path.segments.first().is_some_and(|s| s.name.value == "str"))
                            && matches!(
                                signature.result_mode,
                                ril_syntax::syntax::Mode::New | ril_syntax::syntax::Mode::Plain
                            )
                    }
                    Type::Named(path)
                        if path.segments.len() == 1
                            && path.segments.first().is_some_and(|s| {
                                s.name.value == "Result" && s.arguments.len() == 2
                            }) =>
                    {
                        let args = path
                            .segments
                            .first()
                            .map_or(&[][..], |s| s.arguments.as_slice());
                        let ok_unit = matches!(
                            args.first(),
                            Some(ril_syntax::syntax::GenericArg::Type(ok))
                                if matches!(ast.ty(*ok).value, Type::Unit)
                        );
                        let err_str = matches!(
                            args.get(1),
                            Some(ril_syntax::syntax::GenericArg::Type(err))
                                if matches!(&ast.ty(*err).value, Type::Named(p)
                                    if p.segments.len() == 1
                                        && p.segments.first().is_some_and(|s| s.name.value == "str"))
                        );
                        ok_unit
                            && err_str
                            && matches!(
                                signature.result_mode,
                                ril_syntax::syntax::Mode::New | ril_syntax::syntax::Mode::Plain
                            )
                    }
                    _ => false,
                };
                !fun.is_meta && fun.generics.is_empty() && signature.params.is_empty() && result_ok
            }
            _ => false,
        });
        if !valid {
            errors.push(Diagnostic::error(
                Code::E0904,
                def.name.span,
                "invalid executable entry signature",
            ));
        }
    }
}
