#![forbid(unsafe_code)]
#![deny(clippy::indexing_slicing)]

mod builtins;
mod collect;
mod effects;
mod imports;
mod prelude;
mod walk;

pub use builtins::{PRIMITIVE_FNS, PRIMITIVE_TYPES, PrimitiveSpec, PrimitiveTypeSpec};
pub use collect::{lower, lower_partial};

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::PathBuf,
    sync::Arc,
};

use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceFile, Span},
};

use ril_syntax::{
    lexer::{Kind, Token},
    parser::FileKind,
    syntax::{Ast, Expr, ExprId, Mode, Name, StmtId, StmtKind, TypeDefinition, Visibility},
};

#[allow(unused_imports)]
use collect::{module_key, module_name};

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

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Intrinsic {
    Len,
    Inner,
    Clone,
    Derive,
    AbsorbPanic,
    PanicMessage,
    TypeName,
    Fields,
    Variants,
    CompileError,
    CompileErrorCode,
    Panic,
    Print,
    FileRead,
    FileWrite,
    NumericToF64,
    NumericTrunc,
    ArrayPush,
    ArrayPop,
    ArrayInsert,
    ArrayRemove,
    MapInsert,
    MapRemove,
    StringInspect,
    StringAt,
    StringFromScalars,
    StringEncodeUtf8,
    StringDecodeUtf8,
    BytesAt,
    BytesFromArray,
    ReflectAttrs,
    ReflectFieldAttrs,
    ReflectVariantAttrs,
    ReflectHasDefault,
}

impl Intrinsic {
    /// Ordinary bodyless stdlib intrinsics whose `.ril` signatures in `std/*.ril`
    /// are typechecked directly via `declare_function()`.
    pub const fn uses_declared_signature(self) -> bool {
        use Intrinsic::*;
        matches!(
            self,
            Panic
                | CompileError
                | CompileErrorCode
                | PanicMessage
                | TypeName
                | StringInspect
                | Print
                | FileRead
                | FileWrite
                | NumericToF64
                | NumericTrunc
                | ArrayPush
                | ArrayPop
                | ArrayInsert
                | ArrayRemove
                | MapInsert
                | MapRemove
                | StringAt
                | StringFromScalars
                | StringEncodeUtf8
                | StringDecodeUtf8
                | BytesAt
                | BytesFromArray
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StdType {
    Option,
    Result,
    Set,
    Draft,
    FieldMode,
    PanicInfo,
    PanicError,
    Scope,
    Task,
    Sender,
    Receiver,
    TaskFault,
    TimeoutError,
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
    pub ast: Arc<Ast>,
    source: SourceFile,
    tokens: Vec<Token>,
}

impl File {
    pub fn new(source: SourceFile, kind: FileKind, ast: Ast, tokens: Vec<Token>) -> Self {
        Self {
            id: source.id(),
            path: source.path().into(),
            kind,
            ast: Arc::new(ast),
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

    pub fn source(&self) -> &SourceFile {
        &self.source
    }

    pub fn source_text(&self) -> &str {
        self.source.text()
    }

    pub fn tokens(&self) -> &[Token] {
        &self.tokens
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
    TypeAndModule(DefinitionId, ScopeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Resolution {
    Definition(DefinitionId),
    Module(ScopeId),
    TypeAndModule(DefinitionId, ScopeId),
}

impl Resolution {
    pub const fn definition(self) -> Option<DefinitionId> {
        match self {
            Self::Definition(id) | Self::TypeAndModule(id, _) => Some(id),
            Self::Module(_) => None,
        }
    }

    pub const fn module(self) -> Option<ScopeId> {
        match self {
            Self::Module(id) | Self::TypeAndModule(_, id) => Some(id),
            Self::Definition(_) => None,
        }
    }
}

impl From<Target> for Resolution {
    fn from(target: Target) -> Self {
        match target {
            Target::Def(id) => Self::Definition(id),
            Target::Module(id) => Self::Module(id),
            Target::TypeAndModule(def, scope) => Self::TypeAndModule(def, scope),
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
    resolutions_by_file: HashMap<FileId, Vec<(Span, DefinitionId)>>,
    namespace_owner: HashMap<ScopeId, DefinitionId>,
    effect_owner: HashMap<ScopeId, DefinitionId>,
    effect_by_label_map: HashMap<String, DefinitionId>,
    local_effects: BTreeSet<DefinitionId>,
    effect_spreads: BTreeMap<DefinitionId, BTreeSet<DefinitionId>>,
    pending_operations: Vec<effects::PendingOperation>,
    std_types: BTreeMap<StdType, DefinitionId>,
    std_type_ids: HashMap<DefinitionId, StdType>,
    stdlib_files: BTreeSet<FileId>,
    pub entry: FileId,
    prelude: ScopeId,
}

impl Program {
    pub fn resolutions(&self) -> impl Iterator<Item = (&Span, &Resolution)> {
        self.resolutions.iter()
    }
    pub fn is_stdlib_file(&self, file: FileId) -> bool {
        self.stdlib_files.contains(&file)
    }

    pub fn file(&self, id: FileId) -> &File {
        self.files
            .get(&id.0)
            .unwrap_or_else(|| ril_source::ice!("missing HIR file {}", id.0))
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
            if let Some(&owner) = self.namespace_owner.get(&scope) {
                chain.push(self.definition(owner).name.value.as_str());
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
                    if declaration.kind == ril_syntax::syntax::TypeKind::Nominal
                    && matches!(declaration.definition, TypeDefinition::Opaque)
            )
    }

    pub fn std_type(&self, id: DefinitionId) -> Option<StdType> {
        self.std_type_ids.get(&id).copied()
    }

    pub fn std_type_id(&self, kind: StdType) -> Option<DefinitionId> {
        self.std_types.get(&kind).copied()
    }

    pub fn primitive_spec(&self, id: DefinitionId) -> Option<&'static PrimitiveSpec> {
        let def = self.definition(id);
        if !matches!(def.kind, DefinitionKind::Primitive(_)) {
            return None;
        }
        let module = self.primitive_module(id)?;
        builtins::lookup_primitive(module, def.name.value.as_str())
    }

    pub fn runtime_symbol(&self, id: DefinitionId) -> Option<&'static str> {
        self.primitive_spec(id)?.runtime_symbol
    }

    pub fn intrinsic(&self, id: DefinitionId) -> Option<Intrinsic> {
        self.primitive_spec(id)?.intrinsic
    }
    pub fn operation_effect(&self, operation: DefinitionId) -> Option<DefinitionId> {
        let scope = self.definition(operation).scope;
        self.effect_owner.get(&scope).copied()
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
            ril_source::ice!("operation lookup for a non-effect declaration");
        };
        self.scope(scope)
            .names
            .values()
            .filter_map(|entry| match entry.target {
                Target::Def(operation) | Target::TypeAndModule(operation, _) => Some(operation),
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
        if let Some(&id) = self.effect_by_label_map.get(label) {
            return Some(id);
        }
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
            .unwrap_or_else(|| ril_source::ice!("missing module scope {}", id.0))
    }

    pub fn prelude_scope(&self) -> ScopeId {
        self.prelude
    }

    pub fn scope_parent(&self, scope: ScopeId) -> Option<ScopeId> {
        self.scope(scope).parent
    }

    pub fn scope_file(&self, scope: ScopeId) -> FileId {
        self.scope(scope).file
    }

    pub fn scope_entries(&self, scope: ScopeId) -> Vec<(String, Resolution, Visibility)> {
        self.scope(scope)
            .names
            .iter()
            .map(|(name, entry)| (name.clone(), Resolution::from(entry.target), entry.visibility))
            .collect()
    }

    pub fn module_scopes(&self) -> impl Iterator<Item = (&PathBuf, ScopeId)> {
        self.modules.iter().map(|(k, &v)| (k, v))
    }

    pub fn is_visible(&self, owner: ScopeId, viewer: ScopeId, visibility: Visibility) -> bool {
        self.visible(owner, viewer, visibility)
    }

    pub fn files(&self) -> impl Iterator<Item = &File> {
        self.files.values()
    }

    pub fn definition(&self, id: DefinitionId) -> &Definition {
        self.definitions
            .get(id.0)
            .unwrap_or_else(|| ril_source::ice!("missing HIR definition {:?}", id))
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
        self.resolutions_by_file
            .get(&outer.file)
            .into_iter()
            .flat_map(|entries| entries.iter().copied())
            .filter(move |(span, _)| span.start >= outer.start && span.end <= outer.end)
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
            .unwrap_or_else(|| ril_source::ice!("missing HIR scope {:?}", id))
    }

    fn scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        self.scopes
            .get_mut(id.0)
            .unwrap_or_else(|| ril_source::ice!("missing HIR scope {:?}", id))
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
        match kind {
            DefinitionKind::Namespace(child_scope) => {
                self.namespace_owner.insert(child_scope, id);
            }
            DefinitionKind::Effect(child_scope) => {
                self.effect_owner.insert(child_scope, id);
            }
            _ => {}
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
        if matches!(name.value.as_str(), "Type" | "Super") {
            return Err(Diagnostic::error(
                Code::E0203,
                name.span,
                format!("duplicate or protected declaration {}", name.value),
            ));
        }
        if let Some(&existing) = self.scope(scope).names.get(&name.value) {
            let merged = match (existing.target, entry.target) {
                (Target::Module(module), Target::Def(def))
                | (Target::Def(def), Target::Module(module))
                    if self.definition(def).scope == module
                        && matches!(
                            self.definition(def).kind,
                            DefinitionKind::Type | DefinitionKind::Primitive(_)
                        ) =>
                {
                    Some(Entry {
                        target: Target::TypeAndModule(def, module),
                        visibility: existing.visibility.max(entry.visibility),
                    })
                }
                _ => None,
            };
            if let Some(merged) = merged {
                self.scope_mut(scope)
                    .names
                    .insert(name.value.clone(), merged);
                return Ok(());
            }
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
            Target::Module(scope) | Target::TypeAndModule(_, scope) => Some(scope),
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

    fn lookup_prelude(&self, caller: ScopeId, name: &Name) -> Result<Target, Diagnostic> {
        let scope = self.prelude;
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
        Err(Diagnostic::error(
            Code::E0204,
            name.span,
            format!("cannot resolve {}", name.value),
        ))
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
