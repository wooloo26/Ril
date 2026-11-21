mod builtins;
mod imports;
mod walk;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Path, PathBuf},
};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};

use crate::{
    lexer::{Word, word_kind},
    parser::FileKind,
    syntax::{Ast, Name, Pattern, StmtId, StmtKind, Type, TypeDefinition, Variant, Visibility},
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(usize);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefinitionId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrimitivePhase {
    Static,
    Runtime,
    Both,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefinitionKind {
    Function,
    Constant,
    Type,
    Namespace(ScopeId),
    Effect(ScopeId),
    Sum(ScopeId),
    Variant(DefinitionId),
    Local,
    Generic,
    Primitive(PrimitivePhase),
}

#[derive(Clone, Debug)]
pub struct Definition {
    pub name: Name,
    pub scope: ScopeId,
    pub visibility: Visibility,
    pub kind: DefinitionKind,
    pub stmt: Option<StmtId>,
}

#[derive(Debug)]
pub struct File {
    pub id: FileId,
    pub path: PathBuf,
    pub kind: FileKind,
    pub ast: Ast,
}

struct Scope {
    file: FileId,
    package: String,
    parent: Option<ScopeId>,
    cap: Visibility,
    names: BTreeMap<String, Entry>,
    variants: BTreeMap<String, Vec<DefinitionId>>,
    primitive_module: Option<&'static str>,
}

#[derive(Clone, Copy)]
struct Entry {
    target: Target,
    visibility: Visibility,
}

#[derive(Clone, Copy)]
enum Target {
    Def(DefinitionId),
    Module(ScopeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Resolution {
    Definition(DefinitionId),
    Module(ScopeId),
}

impl From<Target> for Resolution {
    fn from(target: Target) -> Self {
        match target {
            Target::Def(id) => Self::Definition(id),
            Target::Module(id) => Self::Module(id),
        }
    }
}

pub struct Program {
    files: BTreeMap<usize, File>,
    modules: BTreeMap<PathBuf, ScopeId>,
    roots: BTreeMap<usize, ScopeId>,
    scopes: Vec<Scope>,
    definitions: Vec<Definition>,
    resolutions: HashMap<Span, Resolution>,
    local_effects: BTreeSet<DefinitionId>,
    pub entry: FileId,
    prelude: ScopeId,
}

impl Program {
    pub fn file(&self, id: FileId) -> &File {
        self.files
            .get(&id.0)
            .unwrap_or_else(|| ril_base::ice!("missing HIR file {}", id.0))
    }

    pub fn export_name(&self, id: DefinitionId) -> String {
        let def = self.definition(id);
        let origin = self.scope(def.scope).file;
        let mut chain = vec![def.name.value.as_str()];
        let mut scope = def.scope;
        while let Some(parent) = self.scope(scope).parent {
            if let Some((_, namespace)) = self
                .definitions()
                .find(|(_, item)| item.kind == DefinitionKind::Namespace(scope))
            {
                chain.push(namespace.name.value.as_str());
            }
            scope = parent;
        }
        chain.reverse();
        if let Some(file) = self.files.get(&origin.0) {
            format!("{}::{}", file.path.display(), chain.join("::"))
        } else {
            chain.join("::")
        }
    }

    pub fn primitive_module(&self, id: DefinitionId) -> Option<&'static str> {
        self.scope(self.definition(id).scope).primitive_module
    }

    pub fn operation_effect(&self, operation: DefinitionId) -> Option<DefinitionId> {
        let scope = self.definition(operation).scope;
        self.definitions().find_map(|(id, definition)| {
            (definition.kind == DefinitionKind::Effect(scope)).then_some(id)
        })
    }

    pub fn effect_label(&self, effect: DefinitionId) -> String {
        let export = self.export_name(effect);
        if self.local_effects.contains(&effect) {
            format!("{export}#{}", self.definition(effect).name.span.start)
        } else {
            export
        }
    }

    pub fn operation_label(&self, operation: DefinitionId) -> Option<String> {
        let effect = self.operation_effect(operation)?;
        Some(format!(
            "{}::{}",
            self.effect_label(effect),
            self.definition(operation).name.value
        ))
    }

    pub fn effect_operations(&self, effect: DefinitionId) -> impl Iterator<Item = DefinitionId> {
        let DefinitionKind::Effect(scope) = self.definition(effect).kind else {
            ril_base::ice!("operation lookup for a non-effect declaration");
        };
        self.scope(scope)
            .names
            .values()
            .filter_map(|entry| match entry.target {
                Target::Def(operation) => Some(operation),
                Target::Module(_) => None,
            })
    }

    pub fn same_package(&self, a: ScopeId, b: ScopeId) -> bool {
        self.scope(a).package == self.scope(b).package
    }

    pub fn module_scope(&self, id: FileId) -> ScopeId {
        self.roots
            .get(&id.0)
            .copied()
            .unwrap_or_else(|| ril_base::ice!("missing module scope {}", id.0))
    }

    pub fn files(&self) -> impl Iterator<Item = &File> {
        self.files.values()
    }

    pub fn definition(&self, id: DefinitionId) -> &Definition {
        self.definitions
            .get(id.0)
            .unwrap_or_else(|| ril_base::ice!("missing HIR definition {:?}", id))
    }

    pub fn definitions(&self) -> impl Iterator<Item = (DefinitionId, &Definition)> {
        self.definitions
            .iter()
            .enumerate()
            .map(|(index, def)| (DefinitionId(index), def))
    }

    pub fn resolve(&self, span: Span) -> Option<Resolution> {
        self.resolutions.get(&span).copied()
    }

    pub fn references_within(
        &self,
        outer: Span,
    ) -> impl Iterator<Item = (Span, DefinitionId)> + '_ {
        self.resolutions
            .iter()
            .filter_map(move |(&span, &resolved)| {
                (span.file == outer.file && span.start >= outer.start && span.end <= outer.end)
                    .then_some(match resolved {
                        Resolution::Definition(id) => Some((span, id)),
                        Resolution::Module(_) => None,
                    })
                    .flatten()
            })
    }

    pub fn ast_for(&self, defining: DefinitionId) -> &Ast {
        &self.file(self.definition(defining).name.span.file).ast
    }

    fn scope(&self, id: ScopeId) -> &Scope {
        self.scopes
            .get(id.0)
            .unwrap_or_else(|| ril_base::ice!("missing HIR scope {:?}", id))
    }

    fn scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        self.scopes
            .get_mut(id.0)
            .unwrap_or_else(|| ril_base::ice!("missing HIR scope {:?}", id))
    }

    fn new_scope(
        &mut self,
        file: FileId,
        package: String,
        parent: Option<ScopeId>,
        cap: Visibility,
    ) -> ScopeId {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope {
            file,
            package,
            parent,
            cap,
            names: BTreeMap::new(),
            variants: BTreeMap::new(),
            primitive_module: None,
        });
        id
    }

    fn child(&mut self, scope: ScopeId, visibility: Visibility, isolated: bool) -> ScopeId {
        let parent = self.scope(scope);
        let cap = parent.cap.min(visibility);
        self.new_scope(
            parent.file,
            parent.package.clone(),
            isolated.then_some(scope),
            cap,
        )
    }

    fn new_def(
        &mut self,
        scope: ScopeId,
        name: Name,
        kind: DefinitionKind,
        stmt: Option<StmtId>,
        visibility: Visibility,
    ) -> DefinitionId {
        let id = DefinitionId(self.definitions.len());
        if name.value != "_" && (stmt.is_some() || !matches!(kind, DefinitionKind::Primitive(_))) {
            self.resolutions
                .insert(name.span, Resolution::Definition(id));
        }
        self.definitions.push(Definition {
            name,
            scope,
            kind,
            stmt,
            visibility: visibility.min(self.scope(scope).cap),
        });
        id
    }

    fn insert(&mut self, scope: ScopeId, name: &Name, entry: Entry) -> Result<(), Diagnostic> {
        if matches!(name.value.as_str(), "Type" | "Super")
            || self.scope(scope).names.contains_key(&name.value)
        {
            return Err(Diagnostic::error(
                Code::E0203,
                name.span,
                format!("duplicate or protected declaration {}", name.value),
            ));
        }
        self.scope_mut(scope)
            .names
            .insert(name.value.clone(), entry);
        Ok(())
    }

    fn register(
        &mut self,
        scope: ScopeId,
        name: Name,
        kind: DefinitionKind,
        stmt: StmtId,
        visibility: Visibility,
    ) -> Result<DefinitionId, Diagnostic> {
        let def = self.new_def(scope, name.clone(), kind, Some(stmt), visibility);
        self.insert(
            scope,
            &name,
            Entry {
                target: Target::Def(def),
                visibility,
            },
        )?;
        Ok(def)
    }

    fn namespace(&self, target: Target) -> Option<ScopeId> {
        match target {
            Target::Module(scope) => Some(scope),
            Target::Def(def) => match self.definition(def).kind {
                DefinitionKind::Namespace(scope)
                | DefinitionKind::Effect(scope)
                | DefinitionKind::Sum(scope) => Some(scope),
                _ => None,
            },
        }
    }

    fn visible(&self, owner: ScopeId, viewer: ScopeId, visibility: Visibility) -> bool {
        owner == viewer
            || visibility == Visibility::Public
            || visibility == Visibility::Package
                && self.scope(owner).package == self.scope(viewer).package
    }

    fn lookup(
        &self,
        caller: ScopeId,
        scope: ScopeId,
        name: &Name,
        missing: Code,
    ) -> Result<Target, Diagnostic> {
        if let Some(entry) = self.scope(scope).names.get(&name.value) {
            return if self.visible(scope, caller, entry.visibility) {
                Ok(entry.target)
            } else {
                Err(Diagnostic::error(
                    Code::E0201,
                    name.span,
                    format!("{} is private to its module", name.value),
                ))
            };
        }
        match self
            .scope(scope)
            .variants
            .get(&name.value)
            .map(Vec::as_slice)
        {
            Some([variant]) => return Ok(Target::Def(*variant)),
            Some(variants) if !variants.is_empty() => {
                return Err(Diagnostic::error(
                    Code::E0206,
                    name.span,
                    format!("ambiguous constructor {}", name.value),
                ));
            }
            _ => {}
        }
        Err(Diagnostic::error(
            missing,
            name.span,
            format!("cannot resolve {}", name.value),
        ))
    }
}

pub fn lower(files: Vec<File>, entry: FileId) -> Result<Program, Vec<Diagnostic>> {
    let mut program = Program {
        files: files.into_iter().map(|file| (file.id.0, file)).collect(),
        modules: BTreeMap::new(),
        roots: BTreeMap::new(),
        scopes: Vec::new(),
        definitions: Vec::new(),
        resolutions: HashMap::new(),
        local_effects: BTreeSet::new(),
        entry,
        prelude: ScopeId(0),
    };
    program.add_prelude();
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
        program.roots.insert(id.0, root);
        if kind != FileKind::Executable {
            let name = module_key(&path);
            if program
                .modules
                .insert(name, root)
                .is_some_and(|old| program.scope(old).file != FileId(usize::MAX))
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
    program.load_imports(imports, &mut errors);
    if errors.is_empty() {
        walk::check(&mut program, &mut errors);
    }
    if errors.is_empty() {
        Ok(program)
    } else {
        Err(errors)
    }
}

fn mount(path: &Path) -> &str {
    path.iter()
        .next()
        .and_then(std::ffi::OsStr::to_str)
        .filter(|_| path.components().count() >= 2)
        .unwrap_or("pkg")
}

fn module_key(path: &Path) -> PathBuf {
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

fn module_name(name: &Name) -> Result<Name, Diagnostic> {
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
    fn collect(
        &mut self,
        scope: ScopeId,
        items: &[StmtId],
        imports: &mut Vec<(ScopeId, StmtId)>,
        errors: &mut Vec<Diagnostic>,
    ) {
        let file = self.scope(scope).file;
        for &id in items {
            let node = self.file(file).ast.stmt(id).clone();
            let vis = node.value.visibility;
            let declaration = match node.value.kind {
                StmtKind::Function(function) => {
                    let kind =
                        if function.body.is_none() && self.file(file).kind != FileKind::Foreign {
                            let file = self.file(file);
                            match builtins::bodyless(&file.path, &file.ast, &function) {
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
                    if matches!(decl.definition, TypeDefinition::Opaque)
                        && self.file(file).kind != FileKind::Foreign
                        && decl.kind == crate::syntax::TypeKind::Opaque
                    {
                        errors.push(Diagnostic::error(
                            Code::E0902,
                            decl.name.span,
                            "opaque type requires a representation",
                        ));
                    }
                    if let TypeDefinition::Sum(variants) = decl.definition {
                        let namespace = self.child(scope, vis, false);
                        let Ok(sum) = self
                            .register(scope, decl.name, DefinitionKind::Sum(namespace), id, vis)
                            .map_err(|err| errors.push(err))
                        else {
                            continue;
                        };
                        for variant in variants {
                            if let Variant::Constructor { name, .. } = variant
                                && let Ok(def) = self
                                    .register(
                                        namespace,
                                        name.clone(),
                                        DefinitionKind::Variant(sum),
                                        id,
                                        Visibility::Public,
                                    )
                                    .map_err(|err| errors.push(err))
                            {
                                self.scope_mut(scope)
                                    .variants
                                    .entry(name.value)
                                    .or_default()
                                    .push(def);
                            }
                        }
                        Ok(sum)
                    } else {
                        self.register(scope, decl.name, DefinitionKind::Type, id, vis)
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
                StmtKind::Binding { pattern, .. } => {
                    if let Pattern::Binding(_, name) = &self.file(file).ast.pattern(pattern).value {
                        self.register(scope, name.clone(), DefinitionKind::Constant, id, vis)
                    } else {
                        continue;
                    }
                }
                StmtKind::Import(_) => {
                    imports.push((scope, id));
                    continue;
                }
                StmtKind::With(_) | StmtKind::Expr(_) => continue,
            };
            if let Err(err) = declaration {
                errors.push(err);
            }
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
                    Type::Unit => signature.result_mode == crate::syntax::Mode::Plain,
                    Type::Result(ok, err) => {
                        matches!(ast.ty(*ok).value, Type::Unit)
                            && matches!(&ast.ty(*err).value, Type::Named(path) if path.segments.len() == 1
                                && path.segments.first().is_some_and(|s| s.name.value == "str"))
                            && matches!(signature.result_mode, crate::syntax::Mode::New | crate::syntax::Mode::Plain)
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

const PRELUDE: &[(PrimitivePhase, &[&str])] = &[
    (
        PrimitivePhase::Both,
        &[
            "bool",
            "int",
            "f64",
            "str",
            "bytes",
            "never",
            "Type",
            "Option",
            "Result",
            "Set",
            "PanicInfo",
            "PanicError",
            "MemberMode",
            "Draft",
            "Some",
            "None",
            "Ok",
            "Err",
            "len",
            "inner",
            "clone",
            "derive",
            "panic",
            "assert",
        ],
    ),
    (
        PrimitivePhase::Runtime,
        &["absorb_panic", "panic_message", "print", "println"],
    ),
    (
        PrimitivePhase::Static,
        &[
            "type_name",
            "coords",
            "variants",
            "SharedObject",
            "Sendable",
            "LenTarget",
            "Tuple",
            "NominalWrapper",
            "Unwrap",
            "CoordKey",
            "Key",
        ],
    ),
];

impl Program {
    fn add_prelude(&mut self) {
        let file = FileId(usize::MAX);
        self.prelude = self.new_scope(file, "ril".into(), None, Visibility::Public);
        for &(phase, names) in PRELUDE {
            for &name in names {
                self.primitive(self.prelude, name, phase);
            }
        }
        use PrimitivePhase::{Both, Runtime, Static};
        let modules: &[(&str, &str, PrimitivePhase, &[&str])] = &[
            (
                "",
                "Array",
                Both,
                &[
                    "get", "at", "push", "pop", "insert", "remove", "filter", "map", "contains",
                    "sort", "clear", "len",
                ],
            ),
            (
                "",
                "Map",
                Both,
                &[
                    "get", "insert", "remove", "contains", "clear", "keys", "values", "len",
                ],
            ),
            ("", "Set", Both, &["insert", "remove", "contains", "len"]),
            (
                "",
                "String",
                Both,
                &["inspect", "len", "bytes", "from_bytes", "split"],
            ),
            ("", "Bytes", Both, &["len", "from_str"]),
            (
                "",
                "Numeric",
                Both,
                &[
                    "to_int",
                    "to_f64",
                    "convert",
                    "trunc",
                    "checked_div",
                    "checked_rem",
                ],
            ),
            (
                "",
                "MemberMode",
                Both,
                &[
                    "Let",
                    "Var",
                    "Mut",
                    "Ref",
                    "SharedMut",
                    "VarMut",
                    "VarRef",
                    "VarSharedMut",
                ],
            ),
            (
                "",
                "Reflect",
                Static,
                &["MemberMode", "has_default", "coords", "variants", "key"],
            ),
            ("io", "Io", Runtime, &["print", "println"]),
            ("file", "File", Runtime, &["read", "write", "open", "close"]),
            (
                "platform",
                "Platform",
                Static,
                &["HAS_OPENAT", "OS", "ARCH"],
            ),
            (
                "fiber",
                "Fiber",
                Runtime,
                &[
                    "run",
                    "scope",
                    "try_scope",
                    "spawn",
                    "join",
                    "yield",
                    "yield_now",
                    "cancel",
                    "cancel_scope",
                    "sleep",
                    "sleep_ms",
                    "is_cancelled",
                    "uncancellable",
                    "timeout_ms",
                    "supervise",
                    "zip",
                    "try_zip",
                    "map",
                    "try_map",
                    "race",
                    "Scope",
                    "Task",
                    "Zip",
                    "TaskFault",
                    "TimeoutError",
                ],
            ),
            (
                "channel",
                "Channel",
                Runtime,
                &[
                    "mpsc",
                    "bounded",
                    "unbounded",
                    "send",
                    "try_send",
                    "recv",
                    "try_recv",
                    "close",
                    "close_recv",
                    "drain",
                    "clone",
                    "Sender",
                    "Receiver",
                    "ChannelPair",
                    "SendError",
                    "TrySendError",
                    "TryRecvError",
                ],
            ),
            ("os", "Os", Runtime, &[]),
            ("math", "Math", Both, &[]),
            ("crypto", "Crypto", Runtime, &[]),
        ];
        for &(file_name, name, phase, members) in modules {
            let module = self.new_scope(file, "ril".into(), None, Visibility::Public);
            self.scope_mut(module).primitive_module = Some(name);
            for &member in members {
                self.primitive(module, member, phase);
            }
            if file_name.is_empty() {
                if name == "Set" || name == "MemberMode" {
                    self.scope_mut(self.prelude).names.remove(name);
                }
                self.scope_mut(self.prelude).names.insert(
                    name.into(),
                    Entry {
                        target: Target::Module(module),
                        visibility: Visibility::Public,
                    },
                );
            } else {
                self.modules
                    .insert(PathBuf::from("ril").join(file_name), module);
            }
        }
    }

    fn primitive(&mut self, scope: ScopeId, name: &str, phase: PrimitivePhase) {
        let def = self.new_def(
            scope,
            Name::new(name.into(), Span::new(FileId(usize::MAX), 0, 0)),
            DefinitionKind::Primitive(phase),
            None,
            Visibility::Public,
        );
        self.scope_mut(scope).names.insert(
            name.into(),
            Entry {
                target: Target::Def(def),
                visibility: Visibility::Public,
            },
        );
    }
}
