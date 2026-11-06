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
    Constructor,
    Effect,
    Module,
    Binding,
    Parameter,
    GenericParameter,
    Builtin,
}

#[derive(Debug)]
pub struct Definition {
    pub name: String,
    pub kind: DefinitionKind,
    pub scope: ScopeId,
    pub span: Option<Span>,
    pub public: bool,
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
}

#[derive(Debug)]
pub struct ApplicationSignature {
    pub item: DefId,
    pub parameters: Vec<ArgumentSort>,
}

#[derive(Debug)]
pub struct Hir {
    pub definitions: Vec<Definition>,
    pub references: Vec<Reference>,
    pub scopes: Vec<Scope>,
}

#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub span: Option<Span>,
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
}

#[derive(Debug)]
struct Import {
    scope: ScopeId,
    item: UseDeclaration,
}

#[derive(Debug)]
pub(crate) struct Index {
    hir: Hir,
    imports: Vec<Import>,
    uses: Vec<UseSite>,
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
            },
            imports: vec![],
            uses: vec![],
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
            ("Option", 1),
            ("Result", 2),
            ("Set", 1),
            ("Draft", 1),
            ("SharedObject", 1),
            ("LenTarget", 1),
            ("NominalWrapper", 1),
            ("Unwrap", 1),
            ("Tuple", 1),
            ("MemberMode", 0),
            ("Fiber", 0),
            ("Concurrent", 0),
            ("Async", 0),
            ("Div", 0),
        ] {
            this.builtin(prelude, name, arity);
        }
        for (family, arity, members) in [
            ("Option", 1, &["Some", "None"][..]),
            ("Result", 2, &["Ok", "Err"][..]),
            ("Div", 0, &["exhausted", "budget"][..]),
        ] {
            let owner = this.hir.scopes[0].bindings[family].definition;
            let scope = this.scope(None, None, None);
            this.hir.definitions[owner.0].members = Some(scope);
            let is_sum = family != "Div";
            if is_sum {
                this.hir.definitions[owner.0].kind = DefinitionKind::Type;
            }
            for member in members {
                let id = this.builtin(scope, member, arity);
                if is_sum {
                    this.hir.definitions[id.0].kind = DefinitionKind::Constructor;
                }
            }
        }
        this
    }

    fn builtin(&mut self, scope: ScopeId, name: &str, arity: usize) -> DefId {
        let id = self.allocate(Definition {
            name: name.into(),
            kind: DefinitionKind::Builtin,
            scope,
            span: None,
            public: true,
            mutable: false,
            signature: Some(vec![ArgumentSort::Type; arity]),
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
            enclosing_module,
            default_kind: None,
            bindings: BTreeMap::new(),
        });
        id
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
                    DefinitionKind::Type,
                    span,
                    Some(application),
                );
                self.hir.definitions[id.0].members = variants;
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
                        self.item(
                            variants,
                            &variant.name,
                            Visibility::Public,
                            DefinitionKind::Constructor,
                            variant.span,
                            Some(application),
                        );
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
                        DefinitionKind::Function,
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
                    let inner = self.scope(Some(scope), Some(arm.span), None);
                    self.parameters(inner, &arm.parameters);
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
        self.parameters(inner, &function.parameters);
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
            self.block(inner, body, None);
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
                    signature: None,
                    members: None,
                    alias: None,
                },
                parameter.span.end,
            );
        }
    }

    fn parameters(&mut self, scope: ScopeId, parameters: &[Parameter]) {
        for parameter in parameters {
            if let Some(ty) = &parameter.ty {
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
                    members: None,
                    alias: None,
                },
                visible_at,
            );
        }
    }

    fn block(&mut self, scope: ScopeId, block: &Block, pattern: Option<&Pattern>) {
        let inner = self.scope(Some(scope), Some(block.span), None);
        if let Some(pattern) = pattern {
            self.bind_pattern(inner, pattern, block.span.start);
        }
        self.statements(inner, &block.where_items);
        self.statements(inner, &block.statements);
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
            TypeKind::Array {
                length, element, ..
            } => {
                if let Some(length) = length {
                    self.expr(scope, length);
                }
                self.ty(scope, element);
            }
            TypeKind::Map { key, value, .. }
            | TypeKind::KindArrow {
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
                self.parameters(inner, parameters);
                self.annotations(inner, annotations);
                self.return_sources(inner, return_mode);
                if let Some(result) = result {
                    self.ty(inner, result);
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                let inner = self.scope(Some(scope), Some(ty.span), None);
                self.generics(inner, parameters);
                self.expr(inner, body);
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
            TypeKind::TypeBinder(_)
            | TypeKind::PatternRest(_)
            | TypeKind::OpenRow
            | TypeKind::ModeLiteral
            | TypeKind::Error => {}
        }
    }

    fn pattern(&mut self, scope: ScopeId, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                self.site(scope, pattern.span, path.clone(), UseKind::Ordinary);
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
            PatternKind::Value(value) => self.expr(scope, value),
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
            ExprKind::Binary { left, right, .. }
            | ExprKind::Assignment {
                target: left,
                value: right,
                ..
            } => {
                self.expr(scope, left);
                self.expr(scope, right);
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
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(scope, block, None),
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                annotations,
            } => {
                let inner = self.scope(Some(scope), Some(expr.span), None);
                self.parameters(inner, parameters);
                self.annotations(inner, annotations);
                if let Some(ty) = return_type {
                    self.ty(inner, ty);
                }
                self.expr(inner, body);
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
                    self.block(scope, block, Some(pattern));
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
                self.block(scope, body, Some(pattern));
            }
            ExprKind::While { condition, body } => {
                self.expr(scope, condition);
                self.block(scope, body, None);
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
            ExprKind::Is { value, pattern } => {
                self.expr(scope, value);
                self.pattern(scope, pattern);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(scope, value),
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
}

fn signature(parameters: &[GenericParameter]) -> Vec<ArgumentSort> {
    parameters
        .iter()
        .map(|parameter| GenericParameter::sort_for(&parameter.name, parameter.bound.as_ref()))
        .collect()
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
        }
        None
    }

    pub fn application(
        &self,
        file: FileId,
        path: &[String],
        offset: u32,
    ) -> Option<Vec<ArgumentSort>> {
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
        self.signature_of(id).map(|signature| signature.parameters)
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
                    self.hir.references.push(Reference {
                        path,
                        span,
                        scope,
                        definition,
                        application,
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
