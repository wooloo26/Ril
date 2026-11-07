//! Borrowed source inputs for checking and static evaluation, keyed by HIR identity.
use crate::{
    ast::{
        walk::{Node, walk},
        *,
    },
    frontend::Frontend,
    hir::{DefId, DefinitionKind, EffectMember, Hir, Reference, ScopeId},
    source::{FileId, Span},
};
use std::{
    collections::{BTreeMap, HashMap},
    error::Error,
    fmt,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeSiteId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpressionSiteId(pub usize);

struct Sites<'a, T> {
    nodes: Vec<&'a T>,
    by_address: HashMap<usize, usize>,
    by_span: BTreeMap<Span, Vec<usize>>,
}

impl<'a, T> Sites<'a, T> {
    fn new() -> Self {
        Self {
            nodes: vec![],
            by_address: HashMap::new(),
            by_span: BTreeMap::new(),
        }
    }
    fn insert(&mut self, node: &'a T, span: Span) {
        // Addresses only locate borrowed immutable syntax. Public IDs follow
        // deterministic traversal order and never contain process addresses.
        let address = std::ptr::from_ref(node).addr();
        if self.by_address.contains_key(&address) {
            return;
        }
        let id = self.nodes.len();
        self.nodes.push(node);
        self.by_address.insert(address, id);
        self.by_span.entry(span).or_default().push(id);
    }
    fn id(&self, node: &T) -> Option<usize> {
        self.by_address
            .get(&std::ptr::from_ref(node).addr())
            .copied()
    }
    fn at(&self, span: Span) -> impl Iterator<Item = &'a T> + '_ {
        self.by_span
            .get(&span)
            .into_iter()
            .flatten()
            .map(|index| self.nodes[*index])
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DefinitionSource<'a> {
    Intrinsic,
    File { file: FileId, program: &'a Program },
    Module(&'a SubDeclaration),
    Function(&'a Function),
    Type(&'a TypeDeclaration),
    Effect(&'a EffectDeclaration),
    Variant { owner: DefId, syntax: &'a Variant },
    Binding(&'a Binding),
    Parameter(&'a Parameter),
    GenericParameter(&'a GenericParameter),
    Pattern(&'a Pattern),
    Row(&'a TypeExpr),
    MappedCoordinate(&'a TypeExpr),
    EffectProjection { alias: DefId },
}

/// This indexes resolved source; construction does not establish type correctness.
pub struct SourceIndex<'a> {
    pub hir: &'a Hir,
    definitions: BTreeMap<DefId, DefinitionSource<'a>>,
    types: Sites<'a, TypeExpr>,
    expressions: Sites<'a, Expr>,
    references: BTreeMap<Span, Vec<&'a Reference>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexError {
    FrontendRejected,
    MissingDefinition(DefId),
    MissingTypeScope(Span),
    MissingExpressionScope(Span),
}

impl fmt::Display for IndexError {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FrontendRejected => {
                output.write_str("checking inputs require a successful frontend")
            }
            Self::MissingDefinition(definition) => {
                write!(output, "missing source for definition {definition:?}")
            }
            Self::MissingTypeScope(span) => write!(output, "missing type scope at {span:?}"),
            Self::MissingExpressionScope(span) => {
                write!(output, "missing expression scope at {span:?}")
            }
        }
    }
}

impl Error for IndexError {}

impl<'a> SourceIndex<'a> {
    pub fn new(frontend: &'a Frontend) -> Result<Self, IndexError> {
        let hir = frontend.hir.as_ref().ok_or(IndexError::FrontendRejected)?;
        let mut statements = BTreeMap::new();
        let mut functions = BTreeMap::new();
        let mut bindings = BTreeMap::new();
        let mut parameters = BTreeMap::new();
        let mut generics = BTreeMap::new();
        let mut patterns = BTreeMap::new();
        let mut mapped = BTreeMap::new();
        let mut types = Sites::new();
        let mut expressions = Sites::new();
        for parse in frontend.files.values() {
            for node in walk(&parse.program) {
                match node {
                    Node::Statement(statement) => {
                        statements.insert(statement.span, statement);
                        if let StmtKind::Binding(binding) = &statement.kind {
                            bindings.insert(binding.pattern.span, binding.as_ref());
                        }
                    }
                    Node::Function(function) => {
                        functions.insert(function.span, function);
                    }
                    Node::Parameter(parameter) => {
                        parameters.insert(parameter.pattern.span, parameter);
                    }
                    Node::GenericParameter(parameter) => {
                        generics.insert(parameter.span, parameter);
                    }
                    Node::Pattern(pattern) => {
                        patterns.insert(pattern.span, pattern);
                    }
                    Node::Type(ty) => {
                        if !hir.type_scopes.contains_key(&ty.span) {
                            return Err(IndexError::MissingTypeScope(ty.span));
                        }
                        types.insert(ty, ty.span);
                        if let TypeKind::Mapped { value, .. } = &ty.kind {
                            mapped.insert(value.span, ty);
                        }
                    }
                    Node::Expression(expression) => {
                        if !hir.expression_scopes.contains_key(&expression.span) {
                            return Err(IndexError::MissingExpressionScope(expression.span));
                        }
                        expressions.insert(expression, expression.span);
                    }
                    Node::TypeDeclaration(_)
                    | Node::Block(_)
                    | Node::ValueTest(_)
                    | Node::Annotation(_) => {}
                }
            }
        }
        let mut definitions = BTreeMap::new();
        let mut variants = BTreeMap::new();
        for (index, definition) in hir.definitions.iter().enumerate() {
            let id = DefId(index);
            let Some(span) = definition.span else {
                continue;
            };
            if let Some(Stmt {
                kind: StmtKind::Type(ty),
                ..
            }) = statements.get(&span)
            {
                for variant in &ty.variants {
                    variants.insert(variant.span, (id, variant));
                }
            }
        }
        for (index, definition) in hir.definitions.iter().enumerate() {
            let id = DefId(index);
            if let Some(EffectMember::Projection { alias, .. }) = hir.effect_members.get(&id) {
                definitions.insert(id, DefinitionSource::EffectProjection { alias: *alias });
                continue;
            }
            let Some(span) = definition.span else {
                definitions.insert(id, DefinitionSource::Intrinsic);
                continue;
            };
            let source = match definition.kind {
                DefinitionKind::Function
                | DefinitionKind::Primitive
                | DefinitionKind::MetaFunction
                | DefinitionKind::ForeignFunction => {
                    match statements.get(&span).map(|statement| &statement.kind) {
                        Some(StmtKind::Function(function)) => {
                            Some(DefinitionSource::Function(function))
                        }
                        _ => None,
                    }
                }
                DefinitionKind::EffectOperation => functions
                    .get(&span)
                    .copied()
                    .map(DefinitionSource::Function),
                DefinitionKind::Type
                | DefinitionKind::NominalType
                | DefinitionKind::OpaqueType
                | DefinitionKind::ForeignType => {
                    match statements.get(&span).map(|statement| &statement.kind) {
                        Some(StmtKind::Type(ty)) => Some(DefinitionSource::Type(ty)),
                        _ => None,
                    }
                }
                DefinitionKind::Effect | DefinitionKind::EffectAlias => {
                    match statements.get(&span).map(|statement| &statement.kind) {
                        Some(StmtKind::Effect(effect)) => Some(DefinitionSource::Effect(effect)),
                        _ => None,
                    }
                }
                DefinitionKind::Constructor => {
                    variants
                        .get(&span)
                        .map(|(owner, syntax)| DefinitionSource::Variant {
                            owner: *owner,
                            syntax,
                        })
                }
                DefinitionKind::Binding | DefinitionKind::ForeignConstant => {
                    bindings.get(&span).copied().map(DefinitionSource::Binding)
                }
                DefinitionKind::GenericParameter => generics
                    .get(&span)
                    .copied()
                    .map(DefinitionSource::GenericParameter),
                DefinitionKind::RowParameter => types.at(span).next().map(DefinitionSource::Row),
                DefinitionKind::Parameter => parameters
                    .get(&span)
                    .copied()
                    .map(DefinitionSource::Parameter)
                    .or_else(|| patterns.get(&span).copied().map(DefinitionSource::Pattern))
                    .or_else(|| {
                        mapped
                            .get(&span)
                            .copied()
                            .map(DefinitionSource::MappedCoordinate)
                    }),
                DefinitionKind::Module => {
                    match statements.get(&span).map(|statement| &statement.kind) {
                        Some(StmtKind::Sub(sub)) => Some(DefinitionSource::Module(sub)),
                        _ => hir.units.iter().find_map(|(file, unit)| {
                            (unit.namespace == Some(id)).then(|| DefinitionSource::File {
                                file: *file,
                                program: &frontend.files[file].program,
                            })
                        }),
                    }
                }
                DefinitionKind::Builtin | DefinitionKind::EffectProjection => None,
            };
            definitions.insert(id, source.ok_or(IndexError::MissingDefinition(id))?);
        }
        let mut references: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for reference in &hir.references {
            references
                .entry(reference.span)
                .or_default()
                .push(reference);
        }
        Ok(Self {
            hir,
            definitions,
            types,
            expressions,
            references,
        })
    }

    pub fn definition(&self, definition: DefId) -> Option<DefinitionSource<'a>> {
        self.definitions.get(&definition).copied()
    }
    pub fn definitions(&self) -> impl Iterator<Item = (DefId, DefinitionSource<'a>)> + '_ {
        self.definitions.iter().map(|(id, syntax)| (*id, *syntax))
    }
    pub fn definition_scope(&self, definition: DefId) -> Option<ScopeId> {
        self.hir
            .definition_scopes
            .get(&definition)
            .copied()
            .or_else(|| {
                self.hir
                    .definitions
                    .get(definition.0)
                    .map(|definition| definition.scope)
            })
    }
    pub fn type_id(&self, syntax: &TypeExpr) -> Option<TypeSiteId> {
        self.types.id(syntax).map(TypeSiteId)
    }
    pub fn expression_id(&self, syntax: &Expr) -> Option<ExpressionSiteId> {
        self.expressions.id(syntax).map(ExpressionSiteId)
    }
    pub fn type_syntax(&self, id: TypeSiteId) -> Option<&'a TypeExpr> {
        self.types.nodes.get(id.0).copied()
    }
    pub fn expression(&self, id: ExpressionSiteId) -> Option<&'a Expr> {
        self.expressions.nodes.get(id.0).copied()
    }
    pub fn types_at(&self, span: Span) -> impl Iterator<Item = (TypeSiteId, &'a TypeExpr)> + '_ {
        self.types
            .by_span
            .get(&span)
            .into_iter()
            .flatten()
            .map(|index| (TypeSiteId(*index), self.types.nodes[*index]))
    }
    pub fn type_nodes(&self) -> impl Iterator<Item = (TypeSiteId, &'a TypeExpr)> + '_ {
        self.types
            .nodes
            .iter()
            .enumerate()
            .map(|(index, syntax)| (TypeSiteId(index), *syntax))
    }
    pub fn expression_nodes(&self) -> impl Iterator<Item = (ExpressionSiteId, &'a Expr)> + '_ {
        self.expressions
            .nodes
            .iter()
            .enumerate()
            .map(|(index, syntax)| (ExpressionSiteId(index), *syntax))
    }
    pub fn type_scope(&self, span: Span) -> Option<ScopeId> {
        self.hir.type_scopes.get(&span).copied()
    }
    pub fn expression_scope(&self, span: Span) -> Option<ScopeId> {
        self.hir.expression_scopes.get(&span).copied()
    }
    pub fn references_at(&self, span: Span) -> impl Iterator<Item = &'a Reference> + '_ {
        self.references
            .get(&span)
            .into_iter()
            .flat_map(|references| references.iter().copied())
    }
}
