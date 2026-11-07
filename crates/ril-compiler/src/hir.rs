//! Lexical declaration identities, defining scopes, and resolved source uses.
use crate::{
    ast::*,
    diagnostic::Diagnostic,
    lexer::{diagnostic, primitive},
    library::{
        LibraryBodyId, LibraryTypeId, Placement, PrimitiveId, PrimitiveSource, REFLECT_PATH,
    },
    source::{FileId, Span, UnitKind},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    ops::Range,
    path::PathBuf,
};

mod effects;
mod modes;
use effects::EffectAliasSite;
pub use effects::{EffectAliasMember, EffectInstanceUse, EffectMember, HandlerTarget};
pub use modes::{ModeCoordinate, ModeOwner, ModeParameter, ModeParameterId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopeId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionKind {
    Function,
    Primitive,
    MetaFunction,
    ForeignFunction,
    Type,
    NominalType,
    OpaqueType,
    ForeignType,
    Constructor,
    Effect,
    EffectAlias,
    EffectOperation,
    EffectProjection,
    Module,
    Binding,
    ForeignConstant,
    Parameter,
    GenericParameter,
    RowParameter,
    Builtin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstructorForm {
    Nullary,
    Callable,
}

#[derive(Debug)]
pub struct Definition {
    pub name: String,
    pub kind: DefinitionKind,
    pub scope: ScopeId,
    pub span: Option<Span>,
    pub public: bool,
    pub constructor_form: Option<ConstructorForm>,
    mutable: bool,
    signature: Option<Vec<ArgumentSort>>,
    members: Option<ScopeId>,
    alias: Option<(Vec<String>, Span)>,
}

#[derive(Debug)]
pub struct Reference {
    pub path: Vec<String>,
    pub span: Span,
    pub scope: ScopeId,
    pub definition: DefId,
    /// The explicit generic application's original item and parameter sorts.
    pub application: Option<ApplicationSignature>,
    /// The constructor chosen for a binding pattern or nonbinding test.
    pub constructor: Option<DefId>,
    pub effect_instance: Option<EffectInstanceUse>,
}

#[derive(Debug)]
pub struct ApplicationSignature {
    pub item: DefId,
    pub parameters: Vec<ArgumentSort>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclarationHead {
    pub application: Option<Vec<ArgumentSort>>,
    pub constructor: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum HeadKind {
    Value,
    Type,
}

#[derive(Debug)]
pub struct Hir {
    pub units: BTreeMap<FileId, CompilationUnit>,
    pub entry_point: Option<DefId>,
    pub definitions: Vec<Definition>,
    pub references: Vec<Reference>,
    pub scopes: Vec<Scope>,
    pub definition_scopes: BTreeMap<DefId, ScopeId>,
    pub type_scopes: BTreeMap<Span, ScopeId>,
    pub type_binding_scopes: BTreeMap<Span, ScopeId>,
    pub expression_scopes: BTreeMap<Span, ScopeId>,
    pub handler_applications: Vec<HandlerApplication>,
    pub control_transfers: Vec<ControlTransfer>,
    pub state_source_groups: Vec<ResolvedStateGroup>,
    pub effect_aliases: BTreeMap<DefId, Vec<EffectAliasMember>>,
    pub effect_members: BTreeMap<DefId, EffectMember>,
    pub primitives: BTreeMap<DefId, PrimitiveId>,
    pub library_bodies: BTreeMap<DefId, LibraryBodyId>,
    pub library_types: BTreeMap<DefId, LibraryTypeId>,
    pub mode_parameters: Vec<ModeParameter>,
}

#[derive(Debug)]
pub struct CompilationUnit {
    pub origin: CompilationUnitOrigin,
    pub scope: ScopeId,
    pub namespace: Option<DefId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilationUnitOrigin {
    User(UnitKind),
    Bundled,
}

#[derive(Debug)]
pub struct ResolvedStateGroup {
    pub span: Span,
    pub owner: StateOwner,
    pub enclosing_scope: ScopeId,
    pub source_layer: Option<ScopeId>,
    pub items: Vec<ResolvedStateSource>,
}

#[derive(Debug)]
pub struct ResolvedStateSource {
    pub definition: DefId,
    pub mode: StateMode,
    pub span: Span,
}

/// The source header is evaluated in `calling_scope`. Its final argument is
/// the anonymous callable whose body occupies `remainder_scope`.
#[derive(Debug)]
pub struct HandlerApplication {
    pub header: Span,
    pub calling_scope: ScopeId,
    pub remainder_scope: ScopeId,
}

#[derive(Debug)]
pub struct ControlTransfer {
    pub operation: ControlOperation,
    pub span: Span,
    pub scope: ScopeId,
    pub target: ScopeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Lexical,
    Callable,
    Loop,
    HandlerArm,
    HandlerRemainder,
    Fallback,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallableLayer {
    Named(DefId),
    Anonymous,
}

#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub span: Option<Span>,
    pub kind: ScopeKind,
    pub callable_layer: Option<CallableLayer>,
    pub mode_owner: Option<ModeOwner>,
    enclosing_module: Option<ScopeId>,
    lookup_exclusion: Option<Span>,
    default_kind: Option<DefaultKind>,
    bindings: BTreeMap<String, Entry>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefaultKind {
    Parameter,
    Generic,
}

impl DefaultKind {
    fn parameter_kind(self) -> DefinitionKind {
        match self {
            Self::Parameter => DefinitionKind::Parameter,
            Self::Generic => DefinitionKind::GenericParameter,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Entry {
    definition: DefId,
    visible_at: u32,
    public: bool,
}

#[derive(Debug)]
struct UseSite {
    scope: ScopeId,
    span: Span,
    path: Vec<String>,
    use_kind: UseKind,
    downward_error: Option<LookupError>,
}

#[derive(Debug)]
enum UseKind {
    Ordinary,
    Type {
        applied: bool,
        representation: bool,
    },
    Application,
    ConstructorPattern,
    ConstructorTest,
    StateProvider {
        allowed: bool,
    },
    StateSource {
        group: usize,
        mode: StateMode,
    },
    EffectName {
        applied: bool,
    },
    Operation {
        arguments: Option<Vec<TypeExpr>>,
        handler: Option<HandlerTarget>,
        applied: bool,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AnnotationSite {
    OrdinaryFunction,
    OtherDefinition,
    CallableType,
}

#[derive(Debug)]
struct Import {
    scope: ScopeId,
    item: UseDeclaration,
}

struct ImportEntry {
    name: String,
    definition: Result<DefId, LookupError>,
    span: Span,
}

#[derive(Debug)]
struct ImplicitRow {
    scope: ScopeId,
    span: Span,
    name: Option<String>,
}

#[derive(Debug)]
pub(crate) struct Index {
    hir: Hir,
    imports: Vec<Import>,
    uses: Vec<UseSite>,
    pending_effect_members: Vec<EffectAliasSite>,
    rows: Vec<ImplicitRow>,
    indexed_schema_sites: HashSet<Span>,
    files: BTreeMap<PathBuf, DefId>,
    pub diagnostics: Vec<Diagnostic>,
}

impl Index {
    pub fn new() -> Self {
        let mut this = Self {
            hir: Hir {
                units: BTreeMap::new(),
                entry_point: None,
                definitions: vec![],
                references: vec![],
                scopes: vec![],
                definition_scopes: BTreeMap::new(),
                type_scopes: BTreeMap::new(),
                type_binding_scopes: BTreeMap::new(),
                expression_scopes: BTreeMap::new(),
                handler_applications: vec![],
                control_transfers: vec![],
                state_source_groups: vec![],
                effect_aliases: BTreeMap::new(),
                effect_members: BTreeMap::new(),
                primitives: BTreeMap::new(),
                library_bodies: BTreeMap::new(),
                library_types: BTreeMap::new(),
                mode_parameters: vec![],
            },
            imports: vec![],
            uses: vec![],
            pending_effect_members: vec![],
            rows: vec![],
            indexed_schema_sites: HashSet::new(),
            files: BTreeMap::new(),
            diagnostics: vec![],
        };
        let prelude = this.scope(None, None, None);
        for (name, arity) in [
            ("Type", 1),
            ("Draft", 1),
            ("SharedObject", 1),
            ("LenTarget", 1),
            ("NominalWrapper", 1),
            ("Unwrap", 1),
        ] {
            this.builtin(prelude, name, DefinitionKind::Builtin, arity);
        }
        use ConstructorForm::Nullary;
        use DefinitionKind::{Constructor, Effect, EffectOperation, Type};
        for (family, kind, arity, members) in [
            (
                "Fiber",
                Effect,
                0,
                &[("yield", EffectOperation, 0, None)][..],
            ),
            ("Concurrent", Effect, 0, &[][..]),
            (
                "MemberMode",
                Type,
                0,
                &[
                    ("Let", Constructor, 0, Some(Nullary)),
                    ("Var", Constructor, 0, Some(Nullary)),
                    ("Mut", Constructor, 0, Some(Nullary)),
                ][..],
            ),
            (
                "Div",
                Effect,
                0,
                &[("exhausted", EffectOperation, 0, None)][..],
            ),
        ] {
            let owner = this.builtin(prelude, family, kind, arity);
            let scope = this.scope(None, None, None);
            this.hir.definitions[owner.0].members = Some(scope);
            for &(member, kind, arity, constructor_form) in members {
                let id = this.builtin(scope, member, kind, arity);
                this.hir.definitions[id.0].constructor_form = constructor_form;
                if kind == EffectOperation {
                    this.hir
                        .effect_members
                        .insert(id, EffectMember::Operation { family: owner });
                }
            }
        }
        this.install_reflect(prelude);
        this.install_async_alias(prelude);
        this
    }

    fn builtin(&mut self, scope: ScopeId, name: &str, kind: DefinitionKind, arity: usize) -> DefId {
        let id = self.allocate(Definition {
            name: name.into(),
            kind,
            scope,
            span: None,
            public: true,
            mutable: false,
            signature: Some(vec![ArgumentSort::Type; arity]),
            constructor_form: None,
            members: None,
            alias: None,
        });
        self.hir.scopes[scope.0].bindings.insert(
            name.into(),
            Entry {
                definition: id,
                visible_at: 0,
                public: true,
            },
        );
        id
    }

    fn scope(
        &mut self,
        parent: Option<ScopeId>,
        span: Option<Span>,
        enclosing_module: Option<ScopeId>,
    ) -> ScopeId {
        let id = ScopeId(self.hir.scopes.len());
        self.hir.scopes.push(Scope {
            parent,
            span,
            kind: ScopeKind::Lexical,
            callable_layer: None,
            mode_owner: None,
            enclosing_module,
            lookup_exclusion: None,
            default_kind: None,
            bindings: BTreeMap::new(),
        });
        id
    }

    fn region(&mut self, parent: ScopeId, span: Span, kind: ScopeKind) -> ScopeId {
        let scope = self.scope(Some(parent), Some(span), None);
        let region = &mut self.hir.scopes[scope.0];
        region.kind = kind;
        if kind == ScopeKind::HandlerRemainder {
            region.callable_layer = Some(CallableLayer::Anonymous);
        }
        scope
    }

    fn allocate(&mut self, def: Definition) -> DefId {
        let id = DefId(self.hir.definitions.len());
        self.hir.definitions.push(def);
        id
    }

    fn error(&mut self, span: Span, code: &str, message: &str) {
        self.diagnostics.push(diagnostic(
            span.file,
            span.start as usize,
            span.end as usize,
            code,
            message,
        ));
    }

    fn insert(&mut self, scope: ScopeId, name: &str, entry: Entry, span: Span) {
        if matches!(name, "Type" | "Super") {
            self.error(span, "E0203", "the name is reserved by the language");
        } else if self.hir.scopes[scope.0].bindings.contains_key(name) {
            self.error(span, "E0203", &format!("duplicate declaration of '{name}'"));
        } else {
            self.hir.scopes[scope.0].bindings.insert(name.into(), entry);
        }
    }

    fn declare(&mut self, def: Definition, visible_at: u32) -> DefId {
        let span = def.span.expect("user declarations have spans");
        let name = def.name.clone();
        let scope = def.scope;
        let public = def.public;
        let id = self.allocate(def);
        self.insert(
            scope,
            &name,
            Entry {
                definition: id,
                visible_at,
                public,
            },
            span,
        );
        id
    }

    pub fn file(
        &mut self,
        file: FileId,
        path: Option<PathBuf>,
        kind: UnitKind,
        text_len: u32,
        program: &Program,
    ) {
        let span = Span {
            file,
            start: 0,
            end: text_len,
        };
        let scope = self.scope(Some(ScopeId(0)), Some(span), None);
        self.hir.scopes[scope.0].mode_owner = Some(ModeOwner::Module(scope));
        let namespace = path.map(|path| self.module_definition(path, scope, Some(span)));
        self.hir.units.insert(
            file,
            CompilationUnit {
                origin: CompilationUnitOrigin::User(kind),
                scope,
                namespace,
            },
        );
        self.statements(scope, &program.statements);
        if kind == UnitKind::Executable {
            self.hir.entry_point = self.hir.scopes[scope.0]
                .bindings
                .get("main")
                .map(|entry| entry.definition)
                .filter(|definition| {
                    self.hir.definitions[definition.0].kind == DefinitionKind::Function
                });
        }
    }

    fn module_definition(&mut self, path: PathBuf, scope: ScopeId, span: Option<Span>) -> DefId {
        let name = path
            .file_name()
            .map_or_else(String::new, |stem| module_name(&stem.to_string_lossy()));
        let id = self.allocate(Definition {
            name,
            kind: DefinitionKind::Module,
            scope,
            span,
            public: true,
            mutable: false,
            signature: None,
            constructor_form: None,
            members: Some(scope),
            alias: None,
        });
        self.files.insert(path, id);
        self.hir.definition_scopes.insert(id, scope);
        id
    }

    fn expose_ambient_module(&mut self, module: DefId) {
        let name = self.hir.definitions[module.0].name.clone();
        self.hir.scopes[0].bindings.insert(
            name,
            Entry {
                definition: module,
                visible_at: 0,
                public: true,
            },
        );
    }

    fn install_reflect(&mut self, prelude: ScopeId) {
        let scope = self.scope(Some(prelude), None, None);
        let member_mode = self.hir.scopes[prelude.0].bindings["MemberMode"];
        self.hir.scopes[scope.0]
            .bindings
            .insert("MemberMode".into(), member_mode);
        let module = self.module_definition(REFLECT_PATH.into(), scope, None);
        self.expose_ambient_module(module);
    }

    pub fn primitive_unit(
        &mut self,
        file: FileId,
        text_len: u32,
        source: &PrimitiveSource,
        program: &Program,
    ) {
        let span = Span {
            file,
            start: 0,
            end: text_len,
        };
        let prelude = ScopeId(0);
        let (scope, namespace) = match source.placement {
            Placement::Prelude => {
                self.hir.scopes[prelude.0].span = Some(span);
                (prelude, None)
            }
            Placement::AmbientModule(path) => {
                let scope = self.scope(Some(prelude), Some(span), None);
                let module = self.module_definition(path.into(), scope, Some(span));
                self.expose_ambient_module(module);
                (scope, Some(module))
            }
            Placement::ExistingNamespace { name, module } => {
                let definition = self.hir.scopes[prelude.0].bindings[name].definition;
                let scope = self.member_scope(definition).unwrap_or_else(|_| {
                    let scope = self.scope(Some(prelude), Some(span), None);
                    self.hir.definitions[definition.0].members = Some(scope);
                    scope
                });
                self.hir.scopes[scope.0].parent = Some(prelude);
                self.hir.scopes[scope.0].span = Some(span);
                if let Some(path) = module {
                    self.files.insert(path.into(), definition);
                }
                (scope, Some(definition))
            }
        };
        self.hir.units.insert(
            file,
            CompilationUnit {
                origin: CompilationUnitOrigin::Bundled,
                scope,
                namespace,
            },
        );
        self.hir.scopes[scope.0].mode_owner = Some(ModeOwner::Module(scope));
        for statement in &program.statements {
            if let StmtKind::Function(function) = &statement.kind
                && let Some(primitive) = source.primitive(&function.name)
            {
                let id = self.item(
                    scope,
                    &function.name,
                    function.visibility,
                    DefinitionKind::Primitive,
                    statement.span,
                    Some(signature(&function.generics)),
                );
                self.hir.primitives.insert(id, primitive);
                self.function(scope, function, id);
            } else {
                self.statement(scope, statement);
                if let StmtKind::Function(function) = &statement.kind
                    && let Some(body) = source.body(&function.name)
                {
                    let definition = self.hir.scopes[scope.0].bindings[&function.name].definition;
                    self.hir.library_bodies.insert(definition, body);
                }
                if let StmtKind::Type(ty) = &statement.kind
                    && let Some(type_id) = source.type_id(&ty.name)
                {
                    let definition = self.hir.scopes[scope.0].bindings[&ty.name].definition;
                    self.hir.library_types.insert(definition, type_id);
                }
            }
        }
    }

    pub fn paths(&self, file: FileId) -> impl Iterator<Item = PathBuf> + '_ {
        self.imports
            .iter()
            .filter(move |import| import.item.span.file == file)
            .filter_map(|import| file_path(&import.item))
    }

    pub fn has_file(&self, file: FileId) -> bool {
        self.hir.units.contains_key(&file)
    }

    fn statements(&mut self, scope: ScopeId, items: &[Stmt]) {
        for item in items {
            self.statement(scope, item);
        }
    }

    fn statement(&mut self, scope: ScopeId, item: &Stmt) {
        let span = item.span;
        let foreign =
            self.hir.units[&span.file].origin == CompilationUnitOrigin::User(UnitKind::External);
        match &item.kind {
            StmtKind::Sub(sub) => {
                let inner = self.scope(Some(ScopeId(0)), Some(span), Some(scope));
                self.hir.scopes[inner.0].mode_owner = Some(ModeOwner::Module(inner));
                let definition = self.declare(
                    Definition {
                        name: sub.name.clone(),
                        kind: DefinitionKind::Module,
                        scope,
                        span: Some(span),
                        public: sub.visibility == Visibility::Public,
                        mutable: false,
                        signature: None,
                        constructor_form: None,
                        members: Some(inner),
                        alias: None,
                    },
                    0,
                );
                self.hir.definition_scopes.insert(definition, inner);
                self.statements(inner, &sub.items);
            }
            StmtKind::Use(item) => self.imports.push(Import {
                scope,
                item: item.clone(),
            }),
            StmtKind::Function(function) => {
                let kind = if function.is_meta {
                    DefinitionKind::MetaFunction
                } else if foreign && function.body.is_none() {
                    DefinitionKind::ForeignFunction
                } else {
                    DefinitionKind::Function
                };
                let id = self.item(
                    scope,
                    &function.name,
                    function.visibility,
                    kind,
                    span,
                    Some(signature(&function.generics)),
                );
                self.function(scope, function, id);
            }
            StmtKind::Type(ty) => {
                let variants = if ty.variants.is_empty() {
                    None
                } else {
                    Some(self.scope(None, None, None))
                };
                let application = ty
                    .value
                    .as_ref()
                    .and_then(|value| match &value.kind {
                        TypeKind::TypeFunction { parameters, .. } => Some(signature(parameters)),
                        _ => None,
                    })
                    .unwrap_or_else(|| signature(&ty.generics));
                let kind = if ty.opaque {
                    DefinitionKind::OpaqueType
                } else if foreign && ty.nominal && ty.value.is_none() {
                    DefinitionKind::ForeignType
                } else if ty.nominal {
                    DefinitionKind::NominalType
                } else {
                    DefinitionKind::Type
                };
                let id = self.item(
                    scope,
                    &ty.name,
                    ty.visibility,
                    kind,
                    span,
                    Some(application),
                );
                self.hir.definitions[id.0].members = variants;
                if kind == DefinitionKind::NominalType {
                    self.hir.definitions[id.0].constructor_form = Some(if ty.value.is_some() {
                        ConstructorForm::Callable
                    } else {
                        ConstructorForm::Nullary
                    });
                }
                let inner = self.scope(Some(scope), Some(span), None);
                self.hir.scopes[inner.0].mode_owner = Some(ModeOwner::Definition(id));
                self.hir.definition_scopes.insert(id, inner);
                self.generics(inner, &ty.generics);
                self.statements(inner, &ty.signature_where);
                if let Some(value) = &ty.value {
                    self.ty(inner, value);
                }
                if let Some(variants) = variants {
                    for variant in &ty.variants {
                        let mut application = signature(&ty.generics);
                        application.extend(signature(&variant.generics));
                        let id = self.item(
                            variants,
                            &variant.name,
                            Visibility::Public,
                            DefinitionKind::Constructor,
                            variant.span,
                            Some(application),
                        );
                        self.hir.definitions[id.0].constructor_form =
                            Some(if variant.payload.is_some() {
                                ConstructorForm::Callable
                            } else {
                                ConstructorForm::Nullary
                            });
                        let variant_scope = self.scope(Some(inner), Some(variant.span), None);
                        self.hir.definition_scopes.insert(id, variant_scope);
                        self.generics(variant_scope, &variant.generics);
                        if let Some(payload) = &variant.payload {
                            self.ty(variant_scope, payload);
                        }
                        if let Some(result) = &variant.result {
                            self.ty(variant_scope, result);
                        }
                    }
                }
            }
            StmtKind::Effect(effect) => {
                let operations = self.scope(None, None, None);
                let id = self.item(
                    scope,
                    &effect.name,
                    effect.visibility,
                    if effect.members.is_empty() {
                        DefinitionKind::Effect
                    } else {
                        DefinitionKind::EffectAlias
                    },
                    span,
                    Some(signature(&effect.generics)),
                );
                self.hir.definitions[id.0].members = Some(operations);
                let inner = self.scope(Some(scope), Some(span), None);
                self.hir.definition_scopes.insert(id, inner);
                self.generics(inner, &effect.generics);
                for operation in &effect.operations {
                    let operation_id = self.item(
                        operations,
                        &operation.name,
                        Visibility::Public,
                        DefinitionKind::EffectOperation,
                        operation.span,
                        Some(vec![]),
                    );
                    self.hir
                        .effect_members
                        .insert(operation_id, EffectMember::Operation { family: id });
                    self.function(inner, operation, operation_id);
                }
                if !effect.members.is_empty() {
                    self.index_effect_alias(id, inner, &effect.members);
                }
            }
            StmtKind::Binding(binding) => {
                let mut bound = vec![];
                binding.pattern.binding_names(&mut bound);
                bound.sort();
                bound.dedup();
                let mutable = binding.mode.is_mutable() || binding.mode.is_reassignable();
                for name in bound {
                    let alias = binding
                        .initializer
                        .as_ref()
                        .filter(|_| {
                            !mutable
                                && binding.mode == BindingMode::Let
                                && matches!(binding.pattern.kind, PatternKind::Name(_))
                        })
                        .and_then(|value| expression_path(value).map(|path| (path, value.span)));
                    self.declare(
                        Definition {
                            name,
                            kind: if foreign && binding.initializer.is_none() {
                                DefinitionKind::ForeignConstant
                            } else {
                                DefinitionKind::Binding
                            },
                            scope,
                            span: Some(binding.pattern.span),
                            public: binding.visibility == Visibility::Public,
                            mutable,
                            signature: None,
                            constructor_form: None,
                            members: None,
                            alias,
                        },
                        span.end,
                    );
                }
                if let Some(ty) = &binding.ty {
                    self.ty(scope, ty);
                }
                self.pattern(scope, &binding.pattern);
                if let Some(initializer) = &binding.initializer {
                    self.expr(scope, initializer);
                }
                if let Some(fallback) = &binding.fallback {
                    self.expr(scope, fallback);
                }
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    let inner = self.region(scope, arm.span, ScopeKind::HandlerArm);
                    self.handler_operation(
                        scope,
                        &arm.operation,
                        HandlerTarget {
                            group: span,
                            arm: inner,
                        },
                    );
                    self.parameters(inner, &arm.parameters, false);
                    self.expr(inner, &arm.body);
                }
            }
            StmtKind::HandlerApplication(expr)
            | StmtKind::Expr {
                expression: expr, ..
            } => self.expr(scope, expr),
        }
    }

    fn item(
        &mut self,
        scope: ScopeId,
        name: &str,
        visibility: Visibility,
        kind: DefinitionKind,
        span: Span,
        signature: Option<Vec<ArgumentSort>>,
    ) -> DefId {
        self.declare(
            Definition {
                name: name.into(),
                kind,
                scope,
                span: Some(span),
                public: visibility == Visibility::Public,
                mutable: false,
                signature,
                constructor_form: None,
                members: None,
                alias: None,
            },
            0,
        )
    }

    fn annotations(
        &mut self,
        signature: ScopeId,
        enclosing: ScopeId,
        annotations: &[Annotation],
        site: AnnotationSite,
    ) {
        // A callable type has formal labels for its return relations, but
        // captured and provider names belong to its declaration environment.
        let lexical = if site == AnnotationSite::CallableType {
            enclosing
        } else {
            signature
        };
        for annotation in annotations {
            match &annotation.kind {
                AnnotationKind::Effects(EffectRow::Closed(effects)) => {
                    for effect in effects {
                        self.effect_name(signature, effect);
                    }
                }
                AnnotationKind::State(StateClause::Sources { owner, items }) => {
                    let group = self.hir.state_source_groups.len();
                    self.hir.state_source_groups.push(ResolvedStateGroup {
                        span: annotation.span,
                        owner: owner.clone(),
                        enclosing_scope: enclosing,
                        source_layer: None,
                        items: vec![],
                    });
                    for item in items {
                        self.site(
                            lexical,
                            item.name.span,
                            item.name.path.clone(),
                            UseKind::StateSource {
                                group,
                                mode: item.mode,
                            },
                        );
                    }
                }
                AnnotationKind::State(StateClause::Return(dependencies)) => {
                    for dependency in dependencies {
                        self.site(
                            signature,
                            dependency.name.span,
                            dependency.name.path.clone(),
                            UseKind::Ordinary,
                        );
                    }
                }
                AnnotationKind::State(StateClause::Provider(name)) => {
                    self.site(
                        lexical,
                        name.span,
                        name.path.clone(),
                        UseKind::StateProvider {
                            allowed: site != AnnotationSite::OtherDefinition,
                        },
                    );
                }
                _ => {}
            }
        }
    }

    fn return_sources(&mut self, scope: ScopeId, mode: &ReturnMode) {
        if let ReturnMode::Ref(sources) | ReturnMode::SharedMut(sources) = mode {
            for source in sources {
                self.site(
                    scope,
                    source.span,
                    vec![source.name.clone()],
                    UseKind::Ordinary,
                );
            }
        }
    }

    fn function(&mut self, scope: ScopeId, function: &Function, definition: DefId) {
        let inner = self.scope(Some(scope), Some(function.span), None);
        self.hir.scopes[inner.0].mode_owner = Some(ModeOwner::Definition(definition));
        self.hir.definition_scopes.insert(definition, inner);
        if function.body.is_some() {
            self.hir.scopes[inner.0].callable_layer = Some(CallableLayer::Named(definition));
        }
        let head_start = self.uses.len();
        self.generics(inner, &function.generics);
        self.parameters(inner, &function.parameters, function.body.is_some());
        let helpers_start = self.uses.len();
        self.statements(inner, &function.signature_where);
        let helpers_end = self.uses.len();
        let site = if self.hir.definitions[definition.0].kind == DefinitionKind::Function {
            AnnotationSite::OrdinaryFunction
        } else {
            AnnotationSite::OtherDefinition
        };
        self.annotations(inner, scope, &function.annotations, site);
        self.return_sources(inner, &function.return_mode);
        if let Some(ty) = &function.return_type {
            self.ty(inner, ty);
        }
        if let Some(body) = &function.body {
            self.check_where_tiers(
                &function.signature_where,
                &body.where_items,
                head_start..self.uses.len(),
                helpers_start..helpers_end,
            );
            self.block(inner, body, None, ScopeKind::Callable);
        }
    }

    fn check_where_tiers(
        &mut self,
        signature_items: &[Stmt],
        block_items: &[Stmt],
        head_uses: Range<usize>,
        helper_uses: Range<usize>,
    ) {
        if block_items.is_empty() {
            return;
        }
        let block_items: BTreeMap<_, _> = block_items
            .iter()
            .filter_map(|item| item.item_name().map(|name| (name, item)))
            .collect();
        for item in signature_items {
            if let Some(name) = item.item_name()
                && let Some(local) = block_items.get(name)
            {
                self.error(
                    local.span,
                    "E0203",
                    &format!("'{name}' is already declared in signature where"),
                );
            }
        }
        // Keep lexical resolution unchanged. These errors apply only when
        // lookup fails to find a visible head outside the block's where tier.
        for index in head_uses {
            let site = &mut self.uses[index];
            let Some(item) = block_items.get(site.path[0].as_str()) else {
                continue;
            };
            if helper_uses.contains(&index) {
                site.downward_error
                    .get_or_insert(LookupError::DownwardReference);
            } else if matches!(site.use_kind, UseKind::Type { .. })
                && matches!(item.kind, StmtKind::Type(_))
            {
                site.downward_error
                    .get_or_insert(LookupError::SignatureType);
            }
        }
    }

    fn default_scope(&mut self, parent: ScopeId, span: Span, kind: DefaultKind) -> ScopeId {
        let scope = self.scope(Some(parent), Some(span), None);
        self.hir.scopes[scope.0].default_kind = Some(kind);
        scope
    }

    fn generics(&mut self, scope: ScopeId, generics: &[GenericParameter]) {
        for parameter in generics {
            if let Some(bound) = &parameter.bound {
                self.implicit_row(scope, bound, true);
                self.ty(scope, bound);
            }
            for guard in &parameter.guards {
                self.ty(scope, guard);
            }
            if let Some(default) = &parameter.default {
                let inner = self.default_scope(scope, default.span, DefaultKind::Generic);
                self.ty(inner, default);
            }
            self.declare(
                Definition {
                    name: parameter.name.clone(),
                    kind: DefinitionKind::GenericParameter,
                    scope,
                    span: Some(parameter.span),
                    public: false,
                    mutable: false,
                    signature: kind_signature(parameter.bound.as_ref()),
                    constructor_form: None,
                    members: None,
                    alias: None,
                },
                parameter.span.end,
            );
        }
    }

    fn parameters(&mut self, scope: ScopeId, parameters: &[Parameter], definition_inputs: bool) {
        for (index, parameter) in parameters.iter().enumerate() {
            self.parameter_mode_binder(scope, index, parameter);
            if let Some(ty) = &parameter.ty {
                if definition_inputs {
                    self.implicit_row(scope, ty, false);
                }
                self.ty(scope, ty);
            }
            if let Some(default) = &parameter.default {
                let inner = self.default_scope(scope, default.span, DefaultKind::Parameter);
                self.expr(inner, default);
            }
            self.pattern(scope, &parameter.pattern);
            self.bind_pattern(scope, &parameter.pattern, parameter.span.end);
        }
    }

    fn implicit_row(&mut self, scope: ScopeId, ty: &TypeExpr, constraint: bool) {
        let TypeKind::Record { row: Some(row), .. } = &ty.kind else {
            return;
        };
        let name = match &row.kind {
            TypeKind::OpenRow => None,
            TypeKind::Name { path, .. } if constraint && path.len() == 1 && path[0] != "never" => {
                Some(path[0].clone())
            }
            _ => return,
        };
        self.rows.push(ImplicitRow {
            scope,
            span: row.span,
            name,
        });
    }

    fn bind_implicit_rows(&mut self) {
        // A named row in a constraint introduces a binder only if lookup
        // still fails once imports and the enclosing declarations are known.
        for ImplicitRow { scope, span, name } in std::mem::take(&mut self.rows) {
            if let Some(name) = &name
                && self.lexical(scope, name, span.start, false) != Err(LookupError::Unknown)
            {
                continue;
            }
            let anonymous = name.is_none();
            let definition = Definition {
                name: name.unwrap_or_else(|| "..".into()),
                kind: DefinitionKind::RowParameter,
                scope,
                span: Some(span),
                public: false,
                mutable: false,
                signature: None,
                constructor_form: None,
                members: None,
                alias: None,
            };
            if anonymous {
                // Each input occurrence gets an identity without a lexical name.
                self.allocate(definition);
            } else {
                self.declare(definition, 0);
            }
        }
    }

    fn bind_pattern(&mut self, scope: ScopeId, pattern: &Pattern, visible_at: u32) {
        let mut bound = vec![];
        pattern.binding_names(&mut bound);
        bound.sort();
        bound.dedup();
        for name in bound {
            self.declare(
                Definition {
                    name,
                    kind: DefinitionKind::Parameter,
                    scope,
                    span: Some(pattern.span),
                    public: false,
                    mutable: false,
                    signature: None,
                    constructor_form: None,
                    members: None,
                    alias: None,
                },
                visible_at,
            );
        }
    }

    fn block(&mut self, scope: ScopeId, block: &Block, pattern: Option<&Pattern>, kind: ScopeKind) {
        let mut inner = self.region(scope, block.span, kind);
        if let Some(pattern) = pattern {
            self.bind_pattern(inner, pattern, block.span.start);
        }
        // These helpers are created at entry to the written block. Each
        // application then opens a new callable for the remaining statements.
        self.statements(inner, &block.where_items);
        let end = block
            .statements
            .last()
            .map_or(block.span.end, |item| item.span.end);
        for (index, item) in block.statements.iter().enumerate() {
            self.statement(inner, item);
            if matches!(item.kind, StmtKind::HandlerApplication(_)) {
                let start = block
                    .statements
                    .get(index + 1)
                    .map_or(item.span.end, |next| next.span.start);
                let span = Span {
                    file: item.span.file,
                    start,
                    end,
                };
                let remainder = self.region(inner, span, ScopeKind::HandlerRemainder);
                self.hir.handler_applications.push(HandlerApplication {
                    header: item.span,
                    calling_scope: inner,
                    remainder_scope: remainder,
                });
                inner = remainder;
            }
        }
    }

    fn site(&mut self, scope: ScopeId, span: Span, path: Vec<String>, use_kind: UseKind) {
        if path.is_empty() || path.len() == 1 && (primitive(&path[0]) || path[0] == "_") {
            return;
        }
        self.uses.push(UseSite {
            scope,
            span,
            path,
            use_kind,
            downward_error: None,
        });
    }

    fn type_name_use(&mut self, scope: ScopeId, ty: &TypeExpr, representation: bool) {
        self.record_type_scope(scope, ty);
        if let TypeKind::Name { path, arguments } = &ty.kind {
            self.site(
                scope,
                ty.span,
                path.clone(),
                UseKind::Type {
                    applied: !arguments.is_empty(),
                    representation,
                },
            );
            for argument in arguments {
                self.ty(scope, argument);
            }
        }
    }

    fn type_representation(&mut self, scope: ScopeId, ty: &TypeExpr) {
        if matches!(ty.kind, TypeKind::Name { .. }) {
            self.type_name_use(scope, ty, true);
        } else {
            self.ty(scope, ty);
        }
    }

    fn ty(&mut self, scope: ScopeId, ty: &TypeExpr) {
        self.record_type_scope(scope, ty);
        self.schema_mode_binders(scope, ty);
        match &ty.kind {
            TypeKind::Name { .. } => self.type_name_use(scope, ty, false),
            TypeKind::Optional(ty)
            | TypeKind::KeyOf(ty)
            | TypeKind::Rest(ty)
            | TypeKind::Member { ty, .. } => self.ty(scope, ty),
            TypeKind::Array { access, element } => {
                self.storage_mode(scope, access.as_ref());
                self.ty(scope, element);
            }
            TypeKind::ArrayPattern { length, element } => {
                if let Some(length) = length {
                    self.expr(scope, length);
                }
                self.ty(scope, element);
            }
            TypeKind::Map { key, access, value } => {
                self.ty(scope, key);
                self.storage_mode(scope, access.as_ref());
                self.ty(scope, value);
            }
            TypeKind::KindArrow {
                parameter: key,
                result: value,
            } => {
                self.ty(scope, key);
                self.ty(scope, value);
            }
            TypeKind::Tuple(types) | TypeKind::Alternatives(types) => {
                for ty in types {
                    self.ty(scope, ty);
                }
            }
            TypeKind::VariantPayload(fields) => {
                for field in fields {
                    self.ty(scope, &field.ty);
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.ty(scope, &field.ty);
                }
                if let Some(row) = row {
                    self.ty(scope, row);
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                return_mode,
                annotations,
            } => {
                let inner = self.scope(Some(scope), Some(ty.span), None);
                self.hir.scopes[inner.0].mode_owner = Some(ModeOwner::CallableType(inner));
                self.hir.type_binding_scopes.insert(ty.span, inner);
                self.parameters(inner, parameters, false);
                self.annotations(inner, scope, annotations, AnnotationSite::CallableType);
                self.return_sources(inner, return_mode);
                if let Some(result) = result {
                    self.ty(inner, result);
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                let inner = self.scope(Some(scope), Some(ty.span), None);
                self.hir.type_binding_scopes.insert(ty.span, inner);
                self.generics(inner, parameters);
                let body_scope = self.region(inner, body.span, ScopeKind::Callable);
                self.expr(body_scope, body);
            }
            TypeKind::Projection { base, .. } => self.type_representation(scope, base),
            TypeKind::ComputedProjection { base, key } => {
                self.type_representation(scope, base);
                self.expr(scope, key);
            }
            TypeKind::Computation(value) => self.expr(scope, value),
            TypeKind::Mapped {
                mode,
                binder,
                keys,
                value,
                ..
            } => {
                self.expr(scope, keys);
                let scope_span = Span {
                    start: ty.span.start,
                    ..value.span
                };
                let inner = self.scope(Some(scope), Some(scope_span), None);
                self.hir.type_binding_scopes.insert(ty.span, inner);
                self.hir.scopes[inner.0].lookup_exclusion = Some(keys.span);
                self.item(
                    inner,
                    binder,
                    Visibility::Private,
                    DefinitionKind::Parameter,
                    value.span,
                    None,
                );
                if let Some(ModeExpression::Static(mode)) = mode {
                    self.expr(inner, mode);
                }
                self.ty(inner, value);
            }
            TypeKind::PatternMode { ty, .. } => self.ty(scope, ty),
            TypeKind::QualifiedMemberMode => self.site(
                scope,
                ty.span,
                vec!["ril/reflect".into(), "MemberMode".into()],
                UseKind::Type {
                    applied: false,
                    representation: false,
                },
            ),
            TypeKind::TypeBinder(_)
            | TypeKind::PatternRest(_)
            | TypeKind::OpenRow
            | TypeKind::ModeLiteral(_)
            | TypeKind::Error => {}
        }
    }

    fn storage_mode(&mut self, scope: ScopeId, mode: Option<&StorageMode>) {
        if let Some(StorageMode {
            kind: StorageModeKind::Parameter(name),
            span,
        }) = mode
        {
            self.site(scope, *span, vec![name.clone()], UseKind::Ordinary);
        }
    }

    fn pattern(&mut self, scope: ScopeId, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                self.site(
                    scope,
                    pattern.span,
                    path.clone(),
                    UseKind::ConstructorPattern,
                );
                for pattern in arguments {
                    self.pattern(scope, pattern);
                }
            }
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items) => {
                for pattern in items {
                    self.pattern(scope, pattern);
                }
            }
            PatternKind::Record { ty, fields, .. } => {
                if let Some(ty) = ty {
                    self.type_representation(scope, ty);
                }
                for field in fields {
                    self.pattern(scope, &field.pattern);
                }
            }
            PatternKind::Mode { pattern, .. } => self.pattern(scope, pattern),
            PatternKind::Type(ty) => self.ty(scope, ty),
            _ => {}
        }
    }

    fn record_type_scope(&mut self, scope: ScopeId, ty: &TypeExpr) {
        let previous = self.hir.type_scopes.insert(ty.span, scope);
        debug_assert!(previous.is_none_or(|previous| previous == scope));
    }

    fn record_expression_scope(&mut self, scope: ScopeId, expression: &Expr) {
        let previous = self.hir.expression_scopes.insert(expression.span, scope);
        debug_assert!(previous.is_none_or(|previous| previous == scope));
    }

    fn expr(&mut self, scope: ScopeId, expr: &Expr) {
        self.record_expression_scope(scope, expr);
        match &expr.kind {
            ExprKind::Name(name) => {
                self.site(scope, expr.span, vec![name.clone()], UseKind::Ordinary)
            }
            ExprKind::Path(path) => self.site(scope, expr.span, path.clone(), UseKind::Ordinary),
            ExprKind::Generic { base, arguments } => {
                if let Some(path) = expression_path(base) {
                    self.record_expression_scope(scope, base);
                    self.site(scope, base.span, path, UseKind::Application);
                } else {
                    self.expr(scope, base);
                }
                for argument in arguments {
                    self.ty(scope, argument);
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(scope, expression);
                    }
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(scope, item);
                }
            }
            ExprKind::Map(entries) => {
                for (key, value) in entries {
                    self.expr(scope, key);
                    self.expr(scope, value);
                }
            }
            ExprKind::Record { ty, members } => {
                if let Some(ty) = ty {
                    self.type_representation(scope, ty);
                }
                for member in members {
                    match member {
                        RecordMember::Field(field) => self.expr(scope, &field.value),
                        RecordMember::Spread(value) => self.expr(scope, value),
                    }
                }
            }
            ExprKind::EffectOperation { effect, name } => {
                self.qualified_effect_operation(scope, expr.span, effect, name, None);
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(scope, callee);
                for argument in arguments {
                    self.expr(scope, &argument.value);
                }
            }
            ExprKind::Binary {
                left,
                right,
                operator,
            }
            | ExprKind::Assignment {
                target: left,
                value: right,
                operator,
            } => {
                self.expr(scope, left);
                let rhs_scope = if operator == "??" {
                    self.region(scope, right.span, ScopeKind::Fallback)
                } else {
                    scope
                };
                self.expr(rhs_scope, right);
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Observe { operand, .. }
            | ExprKind::TupleMember { value: operand, .. }
            | ExprKind::Field { base: operand, .. } => self.expr(scope, operand),
            ExprKind::ComputedField { base, key }
            | ExprKind::Index {
                base, index: key, ..
            } => {
                self.expr(scope, base);
                self.expr(scope, key);
            }
            ExprKind::Block(block) => self.block(scope, block, None, ScopeKind::Lexical),
            ExprKind::Loop(block) => self.block(scope, block, None, ScopeKind::Loop),
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                annotations,
            } => {
                let inner = self.scope(Some(scope), Some(expr.span), None);
                self.hir.scopes[inner.0].callable_layer = Some(CallableLayer::Anonymous);
                self.hir.scopes[inner.0].mode_owner = Some(ModeOwner::Closure(inner));
                self.parameters(inner, parameters, true);
                self.annotations(inner, scope, annotations, AnnotationSite::OtherDefinition);
                if let Some(ty) = return_type {
                    self.ty(inner, ty);
                }
                let body_scope = self.region(inner, body.span, ScopeKind::Callable);
                self.expr(body_scope, body);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(scope, condition);
                self.expr(scope, then_branch);
                if let Some(branch) = else_branch {
                    self.expr(scope, branch);
                }
            }
            ExprKind::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                self.expr(scope, value);
                self.pattern(scope, pattern);
                if let ExprKind::Block(block) = &then_branch.kind {
                    self.record_expression_scope(scope, then_branch);
                    self.block(scope, block, Some(pattern), ScopeKind::Lexical);
                }
                if let Some(branch) = else_branch {
                    self.expr(scope, branch);
                }
            }
            ExprKind::For {
                iterable: value,
                pattern,
                body,
            }
            | ExprKind::WhileLet {
                pattern,
                value,
                body,
            } => {
                self.expr(scope, value);
                self.pattern(scope, pattern);
                self.block(scope, body, Some(pattern), ScopeKind::Loop);
            }
            ExprKind::While { condition, body } => {
                self.expr(scope, condition);
                self.block(scope, body, None, ScopeKind::Loop);
            }
            ExprKind::Match { value, arms, .. } => {
                self.expr(scope, value);
                for arm in arms {
                    self.pattern(scope, &arm.pattern);
                    let inner = self.scope(Some(scope), Some(arm.span), None);
                    self.bind_pattern(inner, &arm.pattern, arm.pattern.span.end);
                    if let Some(guard) = &arm.guard {
                        self.expr(inner, guard);
                    }
                    self.expr(inner, &arm.body);
                }
            }
            ExprKind::Is { value, test } => {
                self.expr(scope, value);
                self.value_test(scope, test);
            }
            ExprKind::Control {
                operation,
                operator_span,
                value,
            } => {
                if let Some(value) = value {
                    self.expr(scope, value);
                }
                self.control_transfer(scope, *operator_span, *operation);
            }
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) | ExprKind::ModeOf(ty) => {
                self.ty(scope, ty)
            }
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    self.expr(scope, start);
                }
                if let Some(end) = end {
                    self.expr(scope, end);
                }
            }
            _ => {}
        }
    }

    fn value_test(&mut self, scope: ScopeId, test: &ValueTest) {
        match &test.kind {
            ValueTestKind::Value(value) => self.expr(scope, value),
            ValueTestKind::Range { start, end, .. } => {
                self.expr(scope, start);
                self.expr(scope, end);
            }
            ValueTestKind::Constructor {
                path,
                head,
                arguments,
            } => {
                self.site(scope, *head, path.clone(), UseKind::ConstructorTest);
                if let Some(arguments) = arguments {
                    for argument in arguments {
                        self.value_test(scope, argument);
                    }
                }
            }
            ValueTestKind::Tuple(tests) | ValueTestKind::Alternative(tests) => {
                for test in tests {
                    self.value_test(scope, test);
                }
            }
            ValueTestKind::Record { ty, fields } => {
                if let Some(ty) = ty {
                    self.type_representation(scope, ty);
                }
                for field in fields {
                    self.value_test(scope, &field.test);
                }
            }
            ValueTestKind::Wildcard | ValueTestKind::Error => {}
        }
    }

    fn control_transfer(&mut self, scope: ScopeId, span: Span, operation: ControlOperation) {
        let mut target = scope;
        let mut crosses_fallback = false;
        loop {
            let region = &self.hir.scopes[target.0];
            let is_callable = matches!(
                region.kind,
                ScopeKind::Callable | ScopeKind::HandlerRemainder
            );
            let is_target = match operation {
                ControlOperation::Return | ControlOperation::Propagate => is_callable,
                ControlOperation::Last | ControlOperation::Next => region.kind == ScopeKind::Loop,
                ControlOperation::Resume => region.kind == ScopeKind::HandlerArm,
            };
            if is_target {
                if crosses_fallback
                    && matches!(
                        operation,
                        ControlOperation::Return | ControlOperation::Last | ControlOperation::Next
                    )
                {
                    self.error(
                        span,
                        "E0710",
                        "control cannot transfer out of a fallback operand",
                    );
                } else {
                    self.hir.control_transfers.push(ControlTransfer {
                        operation,
                        span,
                        scope,
                        target,
                    });
                }
                return;
            }
            // A resume records its lexical arm even across a callable. The
            // checker will determine whether that resumption capture is lawful.
            if operation != ControlOperation::Resume
                && (is_callable || region.default_kind.is_some())
            {
                break;
            }
            crosses_fallback |= region.kind == ScopeKind::Fallback;
            let Some(parent) = region.parent else { break };
            target = parent;
        }
        let (code, message) = match operation {
            ControlOperation::Return => ("E0707", "return requires an enclosing callable"),
            ControlOperation::Last | ControlOperation::Next => {
                ("E0707", "loop transfer requires a loop in this callable")
            }
            ControlOperation::Resume => ("E0623", "resume requires an enclosing handler arm"),
            ControlOperation::Propagate => ("E0205", "postfix ? requires an enclosing callable"),
        };
        self.error(span, code, message);
    }
}

fn signature(parameters: &[GenericParameter]) -> Vec<ArgumentSort> {
    parameters
        .iter()
        .map(|parameter| GenericParameter::sort_for(&parameter.name, parameter.bound.as_ref()))
        .collect()
}

fn kind_signature(bound: Option<&TypeExpr>) -> Option<Vec<ArgumentSort>> {
    let mut kind = bound?;
    let mut parameters = vec![];
    while let TypeKind::KindArrow { result, .. } = &kind.kind {
        parameters.push(ArgumentSort::Type);
        kind = result;
    }
    (!parameters.is_empty()).then_some(parameters)
}

fn expression_path(expr: &Expr) -> Option<Vec<String>> {
    match &expr.kind {
        ExprKind::Name(name) => Some(vec![name.clone()]),
        ExprKind::Path(path) => Some(path.clone()),
        _ => None,
    }
}

fn file_path(item: &UseDeclaration) -> Option<PathBuf> {
    item.path.first()?;
    item.path
        .iter()
        .all(|part| {
            part.split('_').all(|word| {
                word.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
                    && word
                        .bytes()
                        .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit())
            })
        })
        .then(|| item.path.iter().collect())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LookupError {
    Unknown,
    Uninitialized,
    Private,
    NoModule,
    NoMember,
    Ambiguous,
    ForwardDefault(DefaultKind),
    DownwardReference,
    SignatureType,
}

impl LookupError {
    fn in_namespace_prefix(self) -> Self {
        match self {
            Self::Unknown | Self::NoMember => Self::NoModule,
            other => other,
        }
    }

    fn diagnostic(self) -> (&'static str, &'static str) {
        match self {
            Self::Unknown => ("E0204", "unresolved name"),
            Self::Uninitialized => ("E0207", "binding is unavailable before initialization"),
            Self::Private => ("E0201", "member is private to its defining scope"),
            Self::NoModule => ("E0208", "module path could not be resolved"),
            Self::NoMember => ("E0209", "namespace has no such member"),
            Self::Ambiguous => (
                "E0206",
                "constructor abbreviation has multiple declarations",
            ),
            Self::ForwardDefault(DefaultKind::Generic) => (
                "E0320",
                "generic default refers to its own or a later parameter",
            ),
            Self::ForwardDefault(DefaultKind::Parameter) => (
                "E0408",
                "parameter default refers to its own or a later parameter",
            ),
            Self::DownwardReference => (
                "E0705",
                "signature where cannot refer to a declaration in block where",
            ),
            Self::SignatureType => (
                "E0706",
                "function signature cannot refer to a type declared in block where",
            ),
        }
    }
}

impl Index {
    fn lexical(
        &self,
        mut scope: ScopeId,
        name: &str,
        at: u32,
        constructors: bool,
    ) -> Result<DefId, LookupError> {
        let mut late = false;
        let mut default_kind: Option<DefaultKind> = None;
        let constructors =
            constructors && name.as_bytes().first().is_some_and(u8::is_ascii_uppercase);
        let mut visible_names = BTreeSet::new();
        let mut candidates = BTreeSet::new();
        loop {
            let current = &self.hir.scopes[scope.0];
            if let Some(entry) = current.bindings.get(name) {
                if entry.visible_at <= at {
                    return Ok(entry.definition);
                }
                if let Some(kind) = default_kind
                    && self.hir.definitions[entry.definition.0].kind == kind.parameter_kind()
                {
                    return Err(LookupError::ForwardDefault(kind));
                }
                late = true;
            }
            if constructors {
                // An outer sum with a shadowed name is not directly visible.
                // Different names may still import the same sum declaration.
                for (spelling, entry) in &current.bindings {
                    if entry.visible_at > at || !visible_names.insert(spelling) {
                        continue;
                    }
                    let def = &self.hir.definitions[entry.definition.0];
                    if def.kind == DefinitionKind::Type
                        && let Some(members) = def.members
                        && let Some(variant) = self.hir.scopes[members.0].bindings.get(name)
                    {
                        candidates.insert(variant.definition);
                    }
                }
            }
            let Some(parent) = current.parent else { break };
            default_kind = current.default_kind;
            scope = parent;
        }
        let mut candidates = candidates.into_iter();
        match (candidates.next(), candidates.next()) {
            (Some(id), None) => Ok(id),
            (Some(_), Some(_)) => Err(LookupError::Ambiguous),
            _ if late => Err(LookupError::Uninitialized),
            _ => Err(LookupError::Unknown),
        }
    }

    fn parent_module(&self, mut scope: ScopeId) -> Result<ScopeId, LookupError> {
        loop {
            let current = &self.hir.scopes[scope.0];
            if let Some(parent) = current.enclosing_module {
                return Ok(parent);
            }
            scope = current.parent.ok_or(LookupError::NoModule)?;
        }
    }

    fn member(&self, scope: ScopeId, name: &str, upward: bool) -> Result<DefId, LookupError> {
        let entry = self.hir.scopes[scope.0]
            .bindings
            .get(name)
            .ok_or(LookupError::NoMember)?;
        if upward {
            if self.hir.definitions[entry.definition.0].mutable {
                return Err(LookupError::Private);
            }
        } else if !entry.public {
            return Err(LookupError::Private);
        }
        Ok(entry.definition)
    }

    fn member_scope(&self, id: DefId) -> Result<ScopeId, LookupError> {
        self.hir.definitions[id.0]
            .members
            .ok_or(LookupError::NoModule)
    }

    fn resolve(
        &self,
        scope: ScopeId,
        path: &[String],
        at: u32,
        constructors: bool,
    ) -> Result<DefId, LookupError> {
        if path == [REFLECT_PATH, "MemberMode"] {
            let module = self
                .files
                .get(std::path::Path::new(REFLECT_PATH))
                .ok_or(LookupError::NoModule)?;
            return self.member(self.member_scope(*module)?, "MemberMode", false);
        }
        let (first, rest) = path.split_first().ok_or(LookupError::Unknown)?;
        let (head, rest) = if first == "Super" {
            let mut upward = self.parent_module(scope)?;
            let mut rest = rest;
            while let Some((head, tail)) = rest.split_first() {
                if head != "Super" {
                    break;
                }
                upward = self.parent_module(upward)?;
                rest = tail;
            }
            let (name, rest) = rest.split_first().ok_or(LookupError::NoModule)?;
            (self.member(upward, name, true), rest)
        } else {
            (
                self.lexical(scope, first, at, constructors && rest.is_empty()),
                rest,
            )
        };
        let mut found = if rest.is_empty() {
            head?
        } else {
            head.map_err(LookupError::in_namespace_prefix)?
        };
        if let Some((last, prefixes)) = rest.split_last() {
            for name in prefixes {
                found = self
                    .member(self.member_scope(found)?, name, false)
                    .map_err(LookupError::in_namespace_prefix)?;
            }
            found = self.member(self.member_scope(found)?, last, false)?;
        }
        Ok(found)
    }

    fn signature_of(&self, mut id: DefId) -> Option<ApplicationSignature> {
        // An alias resolves in its initializer's lexical scope and position.
        // The bound limits damage from erroneous/cyclic source aliases.
        for _ in 0..self.hir.definitions.len() {
            let def = &self.hir.definitions[id.0];
            if let Some(signature) = &def.signature {
                return Some(ApplicationSignature {
                    item: id,
                    parameters: signature.clone(),
                });
            }
            let (path, span) = def.alias.as_ref()?;
            id = self.resolve(def.scope, path, span.start, true).ok()?;
            // A let initializer that names a nullary tag receives its value.
            // Selective imports, by contrast, keep the declaration itself.
            if self.hir.definitions[id.0].constructor_form == Some(ConstructorForm::Nullary) {
                return None;
            }
        }
        None
    }

    fn is_constructor(&self, item: DefId) -> bool {
        self.hir.definitions[item.0].constructor_form.is_some()
    }

    pub fn head(
        &self,
        file: FileId,
        path: &[String],
        offset: u32,
        kind: HeadKind,
    ) -> Option<DeclarationHead> {
        let scope = self
            .hir
            .scopes
            .iter()
            .enumerate()
            .rev()
            .filter_map(|(id, scope)| {
                let span = scope.span?;
                (span.file == file
                    && span.start <= offset
                    && offset < span.end
                    && !scope
                        .lookup_exclusion
                        .is_some_and(|excluded| excluded.start <= offset && offset < excluded.end))
                .then_some(ScopeId(id))
            })
            .next()
            .or_else(|| self.hir.units.get(&file).map(|unit| unit.scope))?;
        let id = self
            .resolve(scope, path, offset, kind == HeadKind::Value)
            .ok()?;
        let signature = self.signature_of(id);
        Some(DeclarationHead {
            constructor: signature
                .as_ref()
                .is_some_and(|signature| self.is_constructor(signature.item)),
            application: signature.map(|signature| signature.parameters),
        })
    }

    fn import_entries(&self, index: usize) -> Result<Vec<ImportEntry>, LookupError> {
        let Import { scope, item } = &self.imports[index];
        let mut upward = false;
        let mut path = item.namespaces.as_slice();
        let mut module = if let Some(file) = file_path(item) {
            let id = *self.files.get(&file).ok_or(LookupError::NoModule)?;
            if !item.glob && item.members.is_empty() {
                let name = item
                    .alias
                    .as_ref()
                    .unwrap_or(&self.hir.definitions[id.0].name);
                return Ok(vec![ImportEntry {
                    name: name.clone(),
                    definition: Ok(id),
                    span: item.span,
                }]);
            }
            self.member_scope(id)?
        } else if item.path.first().is_some_and(|name| name == "Super") {
            upward = true;
            let mut module = self.parent_module(*scope)?;
            while let Some((head, rest)) = path.split_first() {
                if head != "Super" {
                    break;
                }
                module = self.parent_module(module)?;
                path = rest;
            }
            module
        } else {
            let name = item.path.first().ok_or(LookupError::NoModule)?;
            let id = self
                .lexical(*scope, name, item.span.start, false)
                .map_err(|_| LookupError::NoModule)?;
            self.member_scope(id)?
        };
        for name in path {
            let member = self
                .member(module, name, upward)
                .map_err(LookupError::in_namespace_prefix)?;
            module = self.member_scope(member)?;
            upward = false;
        }
        if item.glob {
            let entries = self.hir.scopes[module.0]
                .bindings
                .iter()
                .filter_map(|(name, entry)| {
                    let accessible = if upward {
                        !self.hir.definitions[entry.definition.0].mutable
                    } else {
                        entry.public
                    };
                    accessible.then(|| ImportEntry {
                        name: name.clone(),
                        definition: Ok(entry.definition),
                        span: item.span,
                    })
                })
                .collect();
            return Ok(entries);
        }
        Ok(item
            .members
            .iter()
            .map(|member| ImportEntry {
                name: member.alias.as_ref().unwrap_or(&member.name).clone(),
                definition: self.member(module, &member.name, upward),
                span: member.span,
            })
            .collect())
    }

    pub fn link_imports(&mut self) {
        // A glob can acquire additional exports after another module links a
        // re-export. Apply each (import, name) once and revisit until stable.
        let mut linked = BTreeSet::new();
        loop {
            let count = linked.len();
            let mut unresolved = vec![];
            for index in 0..self.imports.len() {
                let import = &self.imports[index];
                let scope = import.scope;
                let public = import.item.visibility == Visibility::Public;
                let span = import.item.span;
                match self.import_entries(index) {
                    Ok(entries) => {
                        for ImportEntry {
                            name,
                            definition,
                            span,
                        } in entries
                        {
                            match definition {
                                Ok(definition) if linked.insert((index, name.clone())) => {
                                    self.insert(
                                        scope,
                                        &name,
                                        Entry {
                                            definition,
                                            public,
                                            visible_at: 0,
                                        },
                                        span,
                                    );
                                }
                                Err(error) => unresolved.push((index, error, span)),
                                Ok(_) => {}
                            }
                        }
                    }
                    Err(error) => unresolved.push((index, error, span)),
                }
            }
            // A declaration import can shadow an enclosing effect. Finish
            // linking available imports before freezing alias member names.
            if linked.len() != count || self.link_effect_aliases() {
                continue;
            }
            for (index, error, span) in unresolved {
                let (mut code, message) = error.diagnostic();
                let item = &self.imports[index].item;
                if error == LookupError::Private
                    && item.visibility == Visibility::Public
                    && item.path.first().is_some_and(|name| name == "Super")
                {
                    code = "E0906";
                }
                self.error(span, code, message);
            }
            break;
        }
        self.bind_implicit_rows();
    }

    fn enclosing_layers(
        &self,
        scope: ScopeId,
    ) -> impl Iterator<Item = (ScopeId, CallableLayer)> + '_ {
        std::iter::successors(Some(scope), |scope| self.hir.scopes[scope.0].parent).filter_map(
            |scope| {
                self.hir.scopes[scope.0]
                    .callable_layer
                    .map(|layer| (scope, layer))
            },
        )
    }

    fn state_source_layer(
        &self,
        group: &ResolvedStateGroup,
        source: &Definition,
    ) -> Result<Option<ScopeId>, &'static str> {
        if group.owner == StateOwner::Module {
            return if matches!(
                source.kind,
                DefinitionKind::Binding | DefinitionKind::ForeignConstant
            ) && self.hir.scopes[source.scope.0].parent == Some(ScopeId(0))
            {
                Ok(None)
            } else {
                Err("module state source must be a module binding")
            };
        }
        if !matches!(
            source.kind,
            DefinitionKind::Binding | DefinitionKind::Parameter
        ) {
            return Err("captured state source must be a binding");
        }
        let Some((source_scope, source_layer)) = self.enclosing_layers(source.scope).next() else {
            return Err("captured state source must belong to a callable layer");
        };
        let mut enclosing = self.enclosing_layers(group.enclosing_scope).peekable();
        let immediate = enclosing.peek().map(|(scope, _)| *scope);
        let selected = match &group.owner {
            StateOwner::Named { name, .. } => enclosing
                .find(|(_, layer)| {
                    matches!(layer, CallableLayer::Named(definition)
                    if self.hir.definitions[definition.0].name == *name)
                })
                .map(|(scope, _)| scope),
            StateOwner::Implicit => enclosing
                .find(|(scope, _)| *scope == source_scope)
                .filter(|(scope, _)| {
                    Some(*scope) == immediate || source_layer == CallableLayer::Anonymous
                })
                .map(|(scope, _)| scope),
            StateOwner::Module => unreachable!("module groups were handled separately"),
        };
        if selected != Some(source_scope) {
            return Err("captured state source does not belong to the selected enclosing layer");
        }
        if group
            .source_layer
            .is_some_and(|layer| layer != source_scope)
        {
            return Err("a captured state group must use one callable layer");
        }
        Ok(Some(source_scope))
    }

    fn resolve_state_source(
        &mut self,
        group: usize,
        definition: DefId,
        mode: StateMode,
        span: Span,
    ) {
        match self.state_source_layer(
            &self.hir.state_source_groups[group],
            &self.hir.definitions[definition.0],
        ) {
            Ok(layer) => {
                let group = &mut self.hir.state_source_groups[group];
                group.source_layer = layer;
                group.items.push(ResolvedStateSource {
                    definition,
                    mode,
                    span,
                });
            }
            Err(message) => self.error(span, "E0538", message),
        }
    }

    pub fn finish(mut self) -> (Hir, Vec<Diagnostic>) {
        let mut monomorphic_arms = BTreeSet::new();
        for UseSite {
            scope,
            span,
            path,
            use_kind,
            downward_error,
        } in std::mem::take(&mut self.uses)
        {
            match self.resolve(
                scope,
                &path,
                span.start,
                !matches!(use_kind, UseKind::Type { .. } | UseKind::EffectName { .. }),
            ) {
                Ok(definition) => {
                    let foreign_type =
                        self.hir.definitions[definition.0].kind == DefinitionKind::ForeignType;
                    if foreign_type
                        && matches!(
                            use_kind,
                            UseKind::Ordinary
                                | UseKind::Application
                                | UseKind::ConstructorPattern
                                | UseKind::ConstructorTest
                                | UseKind::Type {
                                    representation: true,
                                    ..
                                }
                        )
                    {
                        self.error(span, "E0907", "an abstract foreign type does not expose a value constructor or representation");
                    }
                    match use_kind {
                        UseKind::StateProvider { allowed }
                            if !allowed
                                || self.hir.definitions[definition.0].kind
                                    != DefinitionKind::Function =>
                        {
                            self.error(span, "E0539", "a state provider requires an ordinary named Ril definition and an allowed annotation position");
                        }
                        UseKind::StateSource { group, mode } => {
                            self.resolve_state_source(group, definition, mode, span);
                        }
                        UseKind::EffectName { .. } if !self.is_effect(definition) => {
                            self.error(
                                span,
                                "E0301",
                                "an effect name must resolve to an effect declaration",
                            );
                        }
                        _ => {}
                    }
                    let application = if matches!(
                        use_kind,
                        UseKind::Application
                            | UseKind::Type { applied: true, .. }
                            | UseKind::EffectName { applied: true }
                            | UseKind::Operation { applied: true, .. }
                    ) {
                        self.signature_of(definition)
                    } else {
                        None
                    };
                    let constructor = if matches!(
                        use_kind,
                        UseKind::ConstructorPattern | UseKind::ConstructorTest
                    ) {
                        let selected = self
                            .signature_of(definition)
                            .map(|signature| signature.item)
                            .filter(|item| self.is_constructor(*item));
                        if selected.is_none() && !foreign_type {
                            self.error(
                                span,
                                "E0349",
                                "a constructor pattern or test must name a constructor",
                            );
                        }
                        selected
                    } else {
                        None
                    };
                    let effect_instance = self.resolve_effect_use(definition, span, use_kind);
                    if let Some(instance) = &effect_instance
                        && let Some(handler) = instance.handler
                        && instance.arguments.is_none()
                        && let Some(operation) = self.monomorphic_operation(instance.operation)
                        && !monomorphic_arms.insert((
                            handler.group.file,
                            handler.group.start,
                            operation,
                        ))
                    {
                        self.error(
                            span,
                            "E0622",
                            "one handler cannot repeat the same effect operation instance",
                        );
                    }
                    self.hir.references.push(Reference {
                        path,
                        span,
                        scope,
                        definition,
                        application,
                        constructor,
                        effect_instance,
                    });
                }
                Err(mut error) => {
                    if let Some(downward_error) = downward_error
                        && (error == LookupError::Unknown
                            || error == LookupError::NoModule
                                && self.lexical(scope, &path[0], span.start, false)
                                    == Err(LookupError::Unknown))
                    {
                        error = downward_error;
                    }
                    let (code, message) = error.diagnostic();
                    self.error(span, code, &format!("{message} '{}'", path.join("::")));
                }
            }
        }
        (self.hir, self.diagnostics)
    }
}

pub(crate) fn module_name(stem: &str) -> String {
    let mut name = String::new();
    for word in stem.split('_') {
        let mut chars = word.chars();
        if let Some(first) = chars.next() {
            name.push(first.to_ascii_uppercase());
            name.extend(chars);
        }
    }
    name
}
