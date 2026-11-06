//! Lexical declaration identities, defining scopes, and resolved source uses.
use crate::{
    ast::*,
    diagnostic::Diagnostic,
    lexer::{diagnostic, primitive},
    source::{FileId, Span},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
    path::PathBuf,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScopeId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionKind {
    Function,
    Type,
    NominalType,
    Constructor,
    Effect,
    EffectOperation,
    Module,
    Binding,
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
}

#[derive(Debug)]
pub struct ApplicationSignature {
    pub item: DefId,
    pub parameters: Vec<ArgumentSort>,
}

pub(crate) struct DeclarationHead {
    pub application: Option<Vec<ArgumentSort>>,
    pub constructor: bool,
}

#[derive(Debug)]
pub struct Hir {
    pub definitions: Vec<Definition>,
    pub references: Vec<Reference>,
    pub scopes: Vec<Scope>,
    pub handler_applications: Vec<HandlerApplication>,
    pub control_transfers: Vec<ControlTransfer>,
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

#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub span: Option<Span>,
    pub kind: ScopeKind,
    enclosing_module: Option<ScopeId>,
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
    Type { applied: bool },
    Application,
    ConstructorPattern,
    ConstructorTest,
}

#[derive(Debug)]
struct Import {
    scope: ScopeId,
    item: UseDeclaration,
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
    rows: Vec<ImplicitRow>,
    roots: BTreeMap<FileId, ScopeId>,
    files: BTreeMap<PathBuf, DefId>,
    pub diagnostics: Vec<Diagnostic>,
}

impl Index {
    pub fn new() -> Self {
        let mut this = Self {
            hir: Hir {
                definitions: vec![],
                references: vec![],
                scopes: vec![],
                handler_applications: vec![],
                control_transfers: vec![],
            },
            imports: vec![],
            uses: vec![],
            rows: vec![],
            roots: BTreeMap::new(),
            files: BTreeMap::new(),
            diagnostics: vec![],
        };
        let prelude = this.scope(None, None, None);
        for (name, arity) in [
            ("len", 1),
            ("clone", 1),
            ("inner", 1),
            ("derive", 1),
            ("assert", 0),
            ("panic", 0),
            ("print", 0),
            ("println", 0),
            ("byte_size", 0),
            ("type_name", 0),
            ("Type", 1),
            ("Set", 1),
            ("Draft", 1),
            ("SharedObject", 1),
            ("LenTarget", 1),
            ("NominalWrapper", 1),
            ("Unwrap", 1),
            ("Tuple", 1),
            ("Concurrent", 0),
            ("Async", 0),
        ] {
            this.builtin(prelude, name, DefinitionKind::Builtin, arity);
        }
        use ConstructorForm::{Callable, Nullary};
        use DefinitionKind::{Builtin, Constructor, Effect, EffectOperation, Type};
        for (family, kind, arity, members) in [
            (
                "Option",
                Type,
                1,
                &[
                    ("Some", Constructor, 1, Some(Callable)),
                    ("None", Constructor, 1, Some(Nullary)),
                ][..],
            ),
            (
                "Result",
                Type,
                2,
                &[
                    ("Ok", Constructor, 2, Some(Callable)),
                    ("Err", Constructor, 2, Some(Callable)),
                ][..],
            ),
            (
                "Fiber",
                Effect,
                0,
                &[("yield", EffectOperation, 0, None)][..],
            ),
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
                &[
                    ("exhausted", EffectOperation, 0, None),
                    ("budget", Builtin, 1, None),
                ][..],
            ),
        ] {
            let owner = this.builtin(prelude, family, kind, arity);
            let scope = this.scope(None, None, None);
            this.hir.definitions[owner.0].members = Some(scope);
            for &(member, kind, arity, constructor_form) in members {
                let id = this.builtin(scope, member, kind, arity);
                this.hir.definitions[id.0].constructor_form = constructor_form;
            }
        }
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
            enclosing_module,
            default_kind: None,
            bindings: BTreeMap::new(),
        });
        id
    }

    fn region(&mut self, parent: ScopeId, span: Span, kind: ScopeKind) -> ScopeId {
        let scope = self.scope(Some(parent), Some(span), None);
        self.hir.scopes[scope.0].kind = kind;
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

    pub fn file(&mut self, file: FileId, path: Option<PathBuf>, text_len: u32, program: &Program) {
        let span = Span {
            file,
            start: 0,
            end: text_len,
        };
        let scope = self.scope(Some(ScopeId(0)), Some(span), None);
        self.roots.insert(file, scope);
        if let Some(path) = path {
            let name = path
                .file_name()
                .map_or_else(String::new, |stem| module_name(&stem.to_string_lossy()));
            let id = self.allocate(Definition {
                name,
                kind: DefinitionKind::Module,
                scope,
                span: Some(span),
                public: true,
                mutable: false,
                signature: None,
                constructor_form: None,
                members: Some(scope),
                alias: None,
            });
            self.files.insert(path, id);
        }
        self.statements(scope, &program.statements);
    }

    pub fn paths(&self) -> impl Iterator<Item = PathBuf> + '_ {
        self.imports
            .iter()
            .filter_map(|import| file_path(&import.item))
    }

    fn statements(&mut self, scope: ScopeId, items: &[Stmt]) {
        for item in items {
            self.statement(scope, item);
        }
    }

    fn statement(&mut self, scope: ScopeId, item: &Stmt) {
        let span = item.span;
        match &item.kind {
            StmtKind::Sub(sub) => {
                let inner = self.scope(Some(ScopeId(0)), Some(span), Some(scope));
                self.declare(
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
                self.statements(inner, &sub.items);
            }
            StmtKind::Use(item) => self.imports.push(Import {
                scope,
                item: item.clone(),
            }),
            StmtKind::Function(function) => {
                self.item(
                    scope,
                    &function.name,
                    function.visibility,
                    DefinitionKind::Function,
                    span,
                    Some(signature(&function.generics)),
                );
                self.function(scope, function);
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
                let id = self.item(
                    scope,
                    &ty.name,
                    ty.visibility,
                    if ty.nominal {
                        DefinitionKind::NominalType
                    } else {
                        DefinitionKind::Type
                    },
                    span,
                    Some(application),
                );
                self.hir.definitions[id.0].members = variants;
                if ty.nominal {
                    self.hir.definitions[id.0].constructor_form = Some(if ty.value.is_some() {
                        ConstructorForm::Callable
                    } else {
                        ConstructorForm::Nullary
                    });
                }
                let inner = self.scope(Some(scope), Some(span), None);
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
                    DefinitionKind::Effect,
                    span,
                    Some(signature(&effect.generics)),
                );
                self.hir.definitions[id.0].members = Some(operations);
                let inner = self.scope(Some(scope), Some(span), None);
                self.generics(inner, &effect.generics);
                for operation in &effect.operations {
                    self.item(
                        operations,
                        &operation.name,
                        Visibility::Public,
                        DefinitionKind::EffectOperation,
                        operation.span,
                        Some(vec![]),
                    );
                    self.function(inner, operation);
                }
                for member in &effect.members {
                    self.ty(inner, member);
                }
            }
            StmtKind::Binding(binding) => {
                let mut bound = vec![];
                binding.pattern.binding_names(&mut bound);
                bound.sort();
                bound.dedup();
                let mutable = binding.mode.is_mutable() || binding.mode.is_reassignable();
                for name in bound {
                    let alias = (!mutable
                        && binding.mode == BindingMode::Let
                        && matches!(binding.pattern.kind, PatternKind::Name(_)))
                    .then(|| expression_path(&binding.value).map(|path| (path, binding.value.span)))
                    .flatten();
                    self.declare(
                        Definition {
                            name,
                            kind: DefinitionKind::Binding,
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
                self.expr(scope, &binding.value);
                if let Some(fallback) = &binding.fallback {
                    self.expr(scope, fallback);
                }
            }
            StmtKind::Handler(arms) => {
                for arm in arms {
                    self.expr(scope, &arm.operation);
                    let inner = self.region(scope, arm.span, ScopeKind::HandlerArm);
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

    fn annotations(&mut self, scope: ScopeId, annotations: &[Annotation]) {
        for annotation in annotations {
            for reference in &annotation.references {
                let target = match reference.scope {
                    AnnotationScope::Lexical => scope,
                    AnnotationScope::Enclosing => self.hir.scopes[scope.0].parent.unwrap_or(scope),
                    AnnotationScope::Module => self.module_scope(scope),
                };
                self.ty(target, &reference.name);
            }
        }
    }

    fn module_scope(&self, mut scope: ScopeId) -> ScopeId {
        while let Some(parent) = self.hir.scopes[scope.0].parent {
            if parent == ScopeId(0) {
                break;
            }
            scope = parent;
        }
        scope
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

    fn function(&mut self, scope: ScopeId, function: &Function) {
        let inner = self.scope(Some(scope), Some(function.span), None);
        let head_start = self.uses.len();
        self.generics(inner, &function.generics);
        self.parameters(inner, &function.parameters, function.body.is_some());
        let helpers_start = self.uses.len();
        self.statements(inner, &function.signature_where);
        let helpers_end = self.uses.len();
        self.annotations(inner, &function.annotations);
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
        for parameter in parameters {
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

    fn ty(&mut self, scope: ScopeId, ty: &TypeExpr) {
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                self.site(
                    scope,
                    ty.span,
                    path.clone(),
                    UseKind::Type {
                        applied: !arguments.is_empty(),
                    },
                );
                for argument in arguments {
                    self.ty(scope, argument);
                }
            }
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
                self.parameters(inner, parameters, false);
                self.annotations(inner, annotations);
                self.return_sources(inner, return_mode);
                if let Some(result) = result {
                    self.ty(inner, result);
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                let inner = self.scope(Some(scope), Some(ty.span), None);
                self.generics(inner, parameters);
                let body_scope = self.region(inner, body.span, ScopeKind::Callable);
                self.expr(body_scope, body);
            }
            TypeKind::Projection { base, .. } => self.ty(scope, base),
            TypeKind::ComputedProjection { base, key } => {
                self.ty(scope, base);
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
                UseKind::Type { applied: false },
            ),
            TypeKind::TypeBinder(_)
            | TypeKind::PatternRest(_)
            | TypeKind::OpenRow
            | TypeKind::ModeLiteral
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
                    self.ty(scope, ty);
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

    fn expr(&mut self, scope: ScopeId, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(name) => {
                self.site(scope, expr.span, vec![name.clone()], UseKind::Ordinary)
            }
            ExprKind::Path(path) => self.site(scope, expr.span, path.clone(), UseKind::Ordinary),
            ExprKind::Generic { base, arguments } => {
                if let Some(path) = expression_path(base) {
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
                    self.ty(scope, ty);
                }
                for member in members {
                    match member {
                        RecordMember::Field(field) => self.expr(scope, &field.value),
                        RecordMember::Spread(value) => self.expr(scope, value),
                    }
                }
            }
            ExprKind::EffectOperation { effect, name } => {
                self.expr(scope, effect);
                if let ExprKind::Generic { base, .. } = &effect.kind
                    && let Some(mut path) = expression_path(base)
                {
                    path.push(name.clone());
                    self.site(scope, expr.span, path, UseKind::Ordinary);
                }
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
                self.parameters(inner, parameters, true);
                self.annotations(inner, annotations);
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
                    self.ty(scope, ty);
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
        if path == ["ril/reflect", "MemberMode"] {
            return self.lexical(ScopeId(0), "MemberMode", at, false);
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

    pub fn head(&self, file: FileId, path: &[String], offset: u32) -> Option<DeclarationHead> {
        let scope = self
            .hir
            .scopes
            .iter()
            .enumerate()
            .rev()
            .filter_map(|(id, scope)| {
                let span = scope.span?;
                (span.file == file && span.start <= offset && offset < span.end)
                    .then_some(ScopeId(id))
            })
            .next()
            .or_else(|| self.roots.get(&file).copied())?;
        let id = self.resolve(scope, path, offset, true).ok()?;
        let signature = self.signature_of(id);
        Some(DeclarationHead {
            constructor: signature
                .as_ref()
                .is_some_and(|signature| self.is_constructor(signature.item)),
            application: signature.map(|signature| signature.parameters),
        })
    }

    fn import_entries(&self, index: usize) -> Result<Vec<(String, DefId, Span)>, LookupError> {
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
                return Ok(vec![(name.clone(), id, item.span)]);
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
                    accessible.then(|| (name.clone(), entry.definition, item.span))
                })
                .collect();
            return Ok(entries);
        }
        item.members
            .iter()
            .map(|member| {
                let id = self.member(module, &member.name, upward)?;
                Ok((
                    member.alias.as_ref().unwrap_or(&member.name).clone(),
                    id,
                    member.span,
                ))
            })
            .collect()
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
                        for (name, definition, span) in entries {
                            if linked.insert((index, name.clone())) {
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
                        }
                    }
                    Err(error) => unresolved.push((index, error, span)),
                }
            }
            if linked.len() != count {
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

    pub fn finish(mut self) -> (Hir, Vec<Diagnostic>) {
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
                !matches!(use_kind, UseKind::Type { .. }),
            ) {
                Ok(definition) => {
                    let application = if matches!(
                        use_kind,
                        UseKind::Application | UseKind::Type { applied: true }
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
                        if selected.is_none() {
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
                    self.hir.references.push(Reference {
                        path,
                        span,
                        scope,
                        definition,
                        application,
                        constructor,
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
