mod builtins;
mod effects;
mod imports;
mod walk;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Path, PathBuf},
};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceFile, Span},
};

use crate::{
    lexer::{Kind, Token, Word, word_kind},
    parser::FileKind,
    syntax::{
        Ast, Expr, ExprId, Mode, Name, Pattern, StmtId, StmtKind, Type, TypeDefinition, Variant,
        Visibility,
    },
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
pub enum TextBuiltin {
    Join,
    StartsWith,
    EndsWith,
    ScalarAt,
    Scalars,
    FromScalars,
    EncodeUtf8,
    DecodeUtf8,
    ByteAt,
    ToArray,
    FromArray,
}

impl TextBuiltin {
    pub const fn parameters(self) -> &'static [&'static str] {
        use TextBuiltin::*;
        match self {
            Join => &["parts", "separator"],
            StartsWith => &["text", "prefix"],
            EndsWith => &["text", "suffix"],
            ScalarAt => &["text", "index"],
            Scalars | EncodeUtf8 => &["text"],
            FromScalars | FromArray => &["values"],
            DecodeUtf8 | ToArray => &["data"],
            ByteAt => &["data", "index"],
        }
    }

    pub fn argument_order<'a>(
        self,
        labels: impl IntoIterator<Item = Option<&'a str>>,
    ) -> Option<Vec<usize>> {
        let parameters = self.parameters();
        let mut order = vec![None; parameters.len()];
        for (written, label) in labels.into_iter().enumerate() {
            let expected = if let Some(label) = label {
                parameters.iter().position(|&param| param == label)?
            } else {
                order.iter().position(Option::is_none)?
            };
            if order.get_mut(expected)?.replace(written).is_some() {
                return None;
            }
        }
        order.into_iter().collect()
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BuiltinSum {
    PanicError,
    TaskFault,
    TimeoutError,
    SendError,
    TrySendError,
    TryRecvError,
}

#[derive(Clone, Copy, Debug)]
pub enum BuiltinPayload {
    UnitTag,
    PanicInfo,
    Element,
}

impl BuiltinSum {
    pub const fn name(self) -> &'static str {
        use BuiltinSum::*;
        match self {
            PanicError => "PanicError",
            TaskFault => "TaskFault",
            TimeoutError => "TimeoutError",
            SendError => "SendError",
            TrySendError => "TrySendError",
            TryRecvError => "TryRecvError",
        }
    }

    pub const fn variants(self) -> &'static [(&'static str, BuiltinPayload)] {
        use BuiltinPayload::*;
        use BuiltinSum::*;
        match self {
            PanicError => &[("Panicked", PanicInfo)],
            TaskFault => &[("Panicked", PanicInfo), ("Cancelled", UnitTag)],
            TimeoutError => &[("Elapsed", UnitTag)],
            SendError => &[("Closed", Element)],
            TrySendError => &[("Closed", Element), ("Full", Element)],
            TryRecvError => &[("Closed", UnitTag), ("Empty", UnitTag)],
        }
    }

    pub const fn has_parameter(self) -> bool {
        matches!(self, Self::SendError | Self::TrySendError)
    }
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

#[derive(Clone, Debug)]
pub struct File {
    pub id: FileId,
    pub path: PathBuf,
    pub kind: FileKind,
    pub ast: Ast,
    source: SourceFile,
    tokens: Vec<Token>,
}

impl File {
    pub fn new(source: SourceFile, kind: FileKind, ast: Ast, tokens: Vec<Token>) -> Self {
        Self {
            id: source.id(),
            path: source.path().into(),
            kind,
            ast,
            source,
            tokens,
        }
    }

    pub fn token_text(&self, span: Span) -> impl Iterator<Item = &str> {
        let start = self
            .tokens
            .partition_point(|token| token.span.start < span.start);
        self.tokens
            .iter()
            .skip(start)
            .take_while(move |token| token.span.end <= span.end)
            .filter(|token| !matches!(token.kind, Kind::Newline | Kind::Eof))
            .map(|token| token.text(&self.source))
    }

    pub fn source_text(&self) -> &str {
        self.source.text()
    }

    pub fn is_interface(&self) -> bool {
        self.kind == FileKind::Interface
    }
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
    effect_spreads: BTreeMap<DefinitionId, BTreeSet<DefinitionId>>,
    pending_operations: Vec<effects::PendingOperation>,
    builtin_sums: BTreeMap<BuiltinSum, DefinitionId>,
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
        if let DefinitionKind::Variant(sum) = def.kind {
            return format!("{}::{}", self.export_name(sum), def.name.value);
        }
        if def.kind == DefinitionKind::Function
            && let Some(effect) = self.operation_effect(id)
        {
            return format!("{}::{}", self.export_name(effect), def.name.value);
        }
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

    /// Locate the receiver of a direct or piped call to the registered nominal primitive.
    pub fn inner_operand(&self, file: FileId, expression: &Expr) -> Option<(ExprId, Mode)> {
        let ast = &self.file(file).ast;
        let (callee, operand, mode) = match expression {
            Expr::Call { callee, args } => {
                let [argument] = args.as_slice() else {
                    return None;
                };
                (*callee, argument.value, argument.mode)
            }
            Expr::Pipeline {
                value,
                target,
                propagate: false,
                mode,
            } => match &ast.expr(*target).value {
                Expr::Call { callee, args } if args.is_empty() => (*callee, *value, *mode),
                Expr::Path(_) => (*target, *value, *mode),
                _ => return None,
            },
            _ => return None,
        };
        let Expr::Path(path) = &ast.expr(callee).value else {
            return None;
        };
        let Some(Resolution::Definition(id)) = self.resolve(path.span) else {
            return None;
        };
        let definition = self.definition(id);
        (matches!(definition.kind, DefinitionKind::Primitive(_))
            && definition.name.value == "inner")
            .then_some((operand, mode))
    }

    pub fn unit_constructor(&self, id: DefinitionId) -> bool {
        let def = self.definition(id);
        let Some(stmt) = def.stmt else {
            return false;
        };
        let file = self.file(def.name.span.file);
        file.kind != FileKind::Foreign
            && matches!(
                &file.ast.stmt(stmt).value.kind,
                StmtKind::Type(declaration)
                    if declaration.kind == crate::syntax::TypeKind::Nominal
                    && matches!(declaration.definition, TypeDefinition::Opaque)
            )
    }

    pub fn text_builtin(&self, id: DefinitionId) -> Option<TextBuiltin> {
        use TextBuiltin::*;
        if !matches!(self.definition(id).kind, DefinitionKind::Primitive(_)) {
            return None;
        }
        match (
            self.primitive_module(id)?,
            self.definition(id).name.value.as_str(),
        ) {
            ("String", "join") => Some(Join),
            ("String", "starts_with") => Some(StartsWith),
            ("String", "ends_with") => Some(EndsWith),
            ("String", "at") => Some(ScalarAt),
            ("String", "scalars") => Some(Scalars),
            ("String", "from_scalars") => Some(FromScalars),
            ("String", "encode_utf8" | "bytes") | ("Bytes", "from_str") => Some(EncodeUtf8),
            ("String", "decode_utf8" | "from_bytes") => Some(DecodeUtf8),
            ("Bytes", "at") => Some(ByteAt),
            ("Bytes", "to_array") => Some(ToArray),
            ("Bytes", "from_array") => Some(FromArray),
            _ => None,
        }
    }

    pub fn builtin_sum(&self, id: DefinitionId) -> Option<BuiltinSum> {
        self.builtin_sums
            .iter()
            .find_map(|(&kind, &definition)| (definition == id).then_some(kind))
    }

    pub fn builtin_sum_id(&self, kind: BuiltinSum) -> DefinitionId {
        self.builtin_sums
            .get(&kind)
            .copied()
            .unwrap_or_else(|| ril_base::ice!("unregistered built-in sum {kind:?}"))
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

    pub fn effect_includes(&self, covering: DefinitionId, actual: DefinitionId) -> bool {
        covering == actual
            || self
                .effect_spreads
                .get(&covering)
                .is_some_and(|set| set.contains(&actual))
    }

    pub fn effect_by_label(&self, label: &str) -> Option<DefinitionId> {
        self.definitions().find_map(|(id, def)| {
            (matches!(def.kind, DefinitionKind::Effect(_)) && self.effect_label(id) == label)
                .then_some(id)
        })
    }

    pub fn effect_covers(&self, covering: &str, actual: &str) -> bool {
        covering == actual
            || self
                .effect_by_label(covering)
                .zip(self.effect_by_label(actual))
                .is_some_and(|(covering, actual)| self.effect_includes(covering, actual))
    }

    pub fn included_effects(&self, effect: DefinitionId) -> impl Iterator<Item = DefinitionId> {
        std::iter::once(effect).chain(
            self.effect_spreads
                .get(&effect)
                .into_iter()
                .flatten()
                .copied(),
        )
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

    pub fn bindings_within(&self, outer: Span) -> BTreeSet<DefinitionId> {
        self.references_within(outer)
            .filter_map(|(span, id)| {
                let def = self.definition(id);
                (def.kind == DefinitionKind::Local && def.name.span == span).then_some(id)
            })
            .collect()
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
        effect_spreads: BTreeMap::new(),
        pending_operations: Vec::new(),
        builtin_sums: BTreeMap::new(),
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
        program.scope_mut(root).primitive_module = builtins::module(&path);
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
        program.resolve_effect_spreads(&mut errors);
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
                        && decl.kind == crate::syntax::TypeKind::Opaque
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
                        let Ok(sum) = self
                            .register(scope, decl.name, DefinitionKind::Sum(namespace), id, vis)
                            .map_err(|err| errors.push(err))
                        else {
                            continue;
                        };
                        if let Some(builtins::TypeRegistration::Sum(builtin)) = contract {
                            self.builtin_sums.insert(builtin, sum);
                        }
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
                        let kind = if matches!(contract, Some(builtins::TypeRegistration::Object)) {
                            DefinitionKind::Primitive(PrimitivePhase::Runtime)
                        } else {
                            DefinitionKind::Type
                        };
                        self.register(scope, decl.name, kind, id, vis)
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
                                || storage.mode != crate::syntax::Mode::Plain
                                || value.is_some_and(|value| {
                                    matches!(
                                        source.ast.expr(value).value,
                                        crate::syntax::Expr::Closure { .. }
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
        self.register_builtin_sum(self.prelude, BuiltinSum::PanicError);
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
                &[
                    "inspect",
                    "len",
                    "bytes",
                    "from_bytes",
                    "join",
                    "split",
                    "starts_with",
                    "ends_with",
                    "at",
                    "scalars",
                    "from_scalars",
                    "encode_utf8",
                    "decode_utf8",
                ],
            ),
            (
                "",
                "Bytes",
                Both,
                &["len", "from_str", "at", "to_array", "from_array"],
            ),
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
                &[
                    "MemberMode",
                    "attrs",
                    "field_attrs",
                    "variant_attrs",
                    "has_default",
                    "coords",
                    "variants",
                    "key",
                ],
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
            let sums = match name {
                "Fiber" => &[BuiltinSum::TaskFault, BuiltinSum::TimeoutError][..],
                "Channel" => &[
                    BuiltinSum::SendError,
                    BuiltinSum::TrySendError,
                    BuiltinSum::TryRecvError,
                ][..],
                _ => &[],
            };
            for &kind in sums {
                self.register_builtin_sum(module, kind);
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

    fn register_builtin_sum(&mut self, scope: ScopeId, kind: BuiltinSum) {
        let at = Span::new(self.scope(scope).file, 0, 0);
        let namespace = self.child(scope, Visibility::Public, false);
        let owner = self.new_def(
            scope,
            Name::new(kind.name().into(), at),
            DefinitionKind::Sum(namespace),
            None,
            Visibility::Public,
        );
        self.builtin_sums.insert(kind, owner);
        self.scope_mut(scope).names.insert(
            kind.name().into(),
            Entry {
                target: Target::Def(owner),
                visibility: Visibility::Public,
            },
        );
        for &(name, _) in kind.variants() {
            let operation = self.new_def(
                namespace,
                Name::new(name.into(), at),
                DefinitionKind::Variant(owner),
                None,
                Visibility::Public,
            );
            self.scope_mut(namespace).names.insert(
                name.into(),
                Entry {
                    target: Target::Def(operation),
                    visibility: Visibility::Public,
                },
            );
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
