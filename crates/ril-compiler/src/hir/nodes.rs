//! Owned semantic syntax with occurrence identities and explicit child edges.
//!
//! This is an uncertified phase input, available even for recovery syntax.
//! Node IDs belong to this program/revision, never to a source span or dynamic
//! invocation. Existing AST-based checking is migrated separately; constructing
//! this arena, adding a type reference, or minting generated syntax grants no
//! capability proof and cannot construct a `VerifiedProgram`.
use ril_compiler_core::{
    ids::{ExprId, GenericParamId, PatternId, StmtId, TypeExprId, TypeId},
    source::Span,
};
use ril_syntax::ast::{
    self, AnnotationKind, BindingMode, ControlOperation, ParameterMode, Visibility,
};

mod identify;
mod lower;
mod walk;
pub use walk::WalkError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeId {
    Expr(ExprId),
    Stmt(StmtId),
    Pattern(PatternId),
    Generic(GenericParamId),
    Type(TypeExprId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LexicalOwner {
    Module,
    Declaration(StmtId),
    Lambda(ExprId),
    TypeFunction(TypeExprId),
    CallableType(TypeExprId),
    Variant { declaration: StmtId, index: u32 },
    HandlerArm { statement: StmtId, index: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneratedKind {
    IteratorAdapter,
    StaticMaterialization,
    Desugaring,
    /// Reading the expected value of a Name, literal, or nullary tag pattern.
    PatternValue,
}

/// The selected input phase, before any semantic authorization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputOrigin {
    Source,
    Transformed(GeneratedKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeOrigin {
    Source,
    /// A transformed AST was lowered before the transforming pass could retain
    /// original node IDs. This is explicitly not a source occurrence or a
    /// generated receipt with a proven anchor.
    Transformed {
        kind: GeneratedKind,
    },
    Generated {
        generation: u32,
        anchor: NodeId,
        kind: GeneratedKind,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NodeInfo {
    pub span: Span,
    pub owner: LexicalOwner,
    pub origin: NodeOrigin,
    /// A reference supplied by the analysis that owns the corresponding type
    /// table. None means unanalysed/unknown, including recovery nodes.
    pub analyzed_type: Option<TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub info: NodeInfo,
    pub kind: ExprKind,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
    pub info: NodeInfo,
    pub kind: StmtKind,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern {
    pub info: NodeInfo,
    pub kind: PatternKind,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeExpr {
    pub info: NodeInfo,
    pub kind: TypeKind,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericParam {
    pub info: NodeInfo,
    pub name: String,
    pub bound: Option<TypeExprId>,
    pub default: Option<TypeExprId>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    pub kind: AnnotationKind,
    pub text: String,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub pattern: PatternId,
    pub mode: ParameterMode,
    pub ty: Option<TypeExprId>,
    pub default: Option<ExprId>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub statements: Vec<StmtId>,
    pub where_items: Vec<StmtId>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub visibility: Visibility,
    pub is_meta: bool,
    pub is_halt: bool,
    pub name: String,
    pub generics: Vec<GenericParamId>,
    pub parameters: Vec<Parameter>,
    pub return_type: Option<TypeExprId>,
    pub annotations: Vec<Annotation>,
    pub signature_where: Vec<StmtId>,
    pub body: Option<Block>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    pub name: String,
    pub generics: Vec<GenericParamId>,
    pub payload: Option<TypeExprId>,
    pub result: Option<TypeExprId>,
    pub annotations: Vec<Annotation>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportMember {
    pub name: String,
    pub alias: Option<String>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind {
    Binding {
        visibility: Visibility,
        is_meta: bool,
        mode: BindingMode,
        pattern: PatternId,
        ty: Option<TypeExprId>,
        value: ExprId,
        fallback: Option<ExprId>,
    },
    Function(Function),
    Type {
        visibility: Visibility,
        is_halt: bool,
        name: String,
        generics: Vec<GenericParamId>,
        value: Option<TypeExprId>,
        variants: Vec<Variant>,
        opaque: bool,
        nominal: bool,
    },
    Effect {
        visibility: Visibility,
        name: String,
        generics: Vec<GenericParamId>,
        operations: Vec<StmtId>,
        members: Vec<TypeExprId>,
    },
    Use {
        visibility: Visibility,
        path: Vec<String>,
        alias: Option<String>,
        members: Vec<ImportMember>,
        glob: bool,
    },
    Handler(Vec<HandlerArm>),
    HandlerApplication(ExprId),
    Assignment {
        target: ExprId,
        operator: String,
        value: ExprId,
    },
    Expr {
        expression: ExprId,
        terminated: bool,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandlerArm {
    pub operation: ExprId,
    pub parameters: Vec<Parameter>,
    pub body: ExprId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Argument {
    pub label: Option<String>,
    pub mode: ParameterMode,
    pub value: ExprId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringPart {
    Text(String),
    Interpolation {
        expression: ExprId,
        format: Option<String>,
        span: Span,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordMember {
    Field {
        name: String,
        value: ExprId,
        span: Span,
    },
    Spread(ExprId),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub pattern: PatternId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccessorSegment {
    pub field: String,
    pub safe: bool,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Literal(ast::Literal),
    Interpolated(Vec<StringPart>),
    Name(String),
    Path(Vec<String>),
    Generic {
        base: ExprId,
        arguments: Vec<TypeExprId>,
    },
    Tuple(Vec<ExprId>),
    Array(Vec<ExprId>),
    Map(Vec<(ExprId, ExprId)>),
    /// Members are the single ordered semantic representation. Legacy AST
    /// fields/spread mirrors are used only when ordered members are absent.
    Record {
        ty: Option<TypeExprId>,
        members: Vec<RecordMember>,
    },
    Unary {
        operator: String,
        operand: ExprId,
    },
    Binary {
        operator: String,
        left: ExprId,
        right: ExprId,
    },
    Call {
        callee: ExprId,
        arguments: Vec<Argument>,
    },
    Field {
        base: ExprId,
        field: String,
        safe: bool,
    },
    ComputedField {
        base: ExprId,
        key: ExprId,
    },
    Index {
        base: ExprId,
        index: ExprId,
        safe: bool,
    },
    Lambda {
        parameters: Vec<Parameter>,
        return_type: Option<TypeExprId>,
        annotations: Vec<Annotation>,
        body: ExprId,
    },
    Accessor(Vec<AccessorSegment>),
    Block(Block),
    If {
        condition: ExprId,
        then_branch: ExprId,
        else_branch: Option<ExprId>,
    },
    Match {
        value: ExprId,
        arms: Vec<MatchArm>,
        type_match: bool,
    },
    Is {
        value: ExprId,
        pattern: PatternId,
    },
    Loop(Block),
    While {
        condition: ExprId,
        body: Block,
    },
    For {
        iterable: ExprId,
        pattern: PatternId,
        body: Block,
    },
    Control {
        operation: ControlOperation,
        value: Option<ExprId>,
    },
    TypeValue(TypeExprId),
    KeyOf(TypeExprId),
    Derive {
        base: Option<ExprId>,
        recipe: ExprId,
    },
    Range {
        start: Option<ExprId>,
        end: Option<ExprId>,
        inclusive: bool,
    },
    Ambient,
    Error,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeField {
    pub name: String,
    pub mutable: bool,
    pub ty: TypeExprId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Name {
        path: Vec<String>,
        arguments: Vec<TypeExprId>,
    },
    Optional(TypeExprId),
    Array {
        length: Option<ExprId>,
        element: TypeExprId,
    },
    Map {
        key: TypeExprId,
        value: TypeExprId,
    },
    Tuple(Vec<TypeExprId>),
    Record {
        fields: Vec<TypeField>,
        row: Option<TypeExprId>,
    },
    Callable {
        parameters: Vec<Parameter>,
        result: Option<TypeExprId>,
        annotations: Vec<Annotation>,
    },
    TypeFunction {
        parameters: Vec<GenericParamId>,
        body: ExprId,
    },
    Projection {
        base: TypeExprId,
        field: String,
    },
    ComputedProjection {
        base: TypeExprId,
        key: ExprId,
    },
    KeyOf(TypeExprId),
    Computation(ExprId),
    Mapped {
        binder: String,
        keys: ExprId,
        value: TypeExprId,
        tuple: bool,
    },
    Rest(TypeExprId),
    KindArrow {
        parameter: TypeExprId,
        result: TypeExprId,
    },
    Error,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatternField {
    pub name: String,
    pub pattern: PatternId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternKind {
    Name(String),
    Wildcard,
    Literal(ast::Literal),
    Tuple(Vec<PatternId>),
    Record {
        ty: Option<TypeExprId>,
        fields: Vec<PatternField>,
        rest: bool,
        rest_binding: Option<String>,
    },
    Constructor {
        path: Vec<String>,
        arguments: Vec<PatternId>,
        parenthesized: bool,
    },
    Alternative(Vec<PatternId>),
    Mode {
        mode: BindingMode,
        pattern: PatternId,
    },
    Type {
        ty: TypeExprId,
        binder: Option<String>,
    },
    Value(ExprId),
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HirLimits {
    pub nodes: usize,
    pub depth: usize,
    pub text_bytes: usize,
    /// Auxiliary spellings (including empty names/annotations) must be bounded
    /// independently of their byte length and the number of arena nodes.
    pub text_items: usize,
}
impl Default for HirLimits {
    fn default() -> Self {
        Self {
            nodes: 262_144,
            depth: 256,
            text_bytes: 16 * 1024 * 1024,
            text_items: 262_144,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum LowerError {
    #[error("HIR {0} budget exhausted")]
    Budget(&'static str),
    #[error("HIR arena identity space exhausted")]
    IdentitySpace,
    #[error("generated HIR anchor or lexical owner is absent")]
    MissingAnchor,
    #[error("AST and HIR structural correspondence differs")]
    Correspondence,
}

#[derive(Debug, Clone, Default)]
pub struct HirProgram {
    roots: Vec<StmtId>,
    expressions: Vec<Expr>,
    statements: Vec<Stmt>,
    patterns: Vec<Pattern>,
    generics: Vec<GenericParam>,
    types: Vec<TypeExpr>,
    generated_roots: Vec<ExprId>,
}
impl HirProgram {
    pub fn lower(source: &ast::Program) -> Result<Self, LowerError> {
        Self::lower_with_limits(source, HirLimits::default())
    }
    pub fn lower_with_limits(source: &ast::Program, limits: HirLimits) -> Result<Self, LowerError> {
        lower::program(source, limits)
    }
    /// Assign static occurrence IDs to this exact AST by following typed HIR
    /// edges. Existing IDs are ignored. A bounded read-only pairing pass must
    /// succeed before any identity is written; failure preserves the input.
    pub fn lower_identified(
        source: &mut ast::Program,
        origin: InputOrigin,
    ) -> Result<Self, LowerError> {
        Self::lower_identified_with_limits(source, origin, HirLimits::default())
    }
    pub fn lower_identified_with_limits(
        source: &mut ast::Program,
        origin: InputOrigin,
        limits: HirLimits,
    ) -> Result<Self, LowerError> {
        let mut hir = Self::lower_with_limits(source, limits)?;
        if let InputOrigin::Transformed(kind) = origin {
            hir.mark_transformed(kind);
        }
        identify::program(&hir, source, limits)?;
        Ok(hir)
    }
    /// Transitional input from a pass that has not yet migrated to identity-
    /// preserving HIR transformations. Every node records the missing original
    /// correspondence; no source anchor is invented from a matching span.
    pub fn lower_transformed(
        source: &ast::Program,
        kind: GeneratedKind,
    ) -> Result<Self, LowerError> {
        let mut hir = Self::lower(source)?;
        hir.mark_transformed(kind);
        Ok(hir)
    }
    fn mark_transformed(&mut self, kind: GeneratedKind) {
        for info in self
            .expressions
            .iter_mut()
            .map(|node| &mut node.info)
            .chain(self.statements.iter_mut().map(|node| &mut node.info))
            .chain(self.patterns.iter_mut().map(|node| &mut node.info))
            .chain(self.generics.iter_mut().map(|node| &mut node.info))
            .chain(self.types.iter_mut().map(|node| &mut node.info))
        {
            info.origin = NodeOrigin::Transformed { kind };
        }
    }
    pub fn roots(&self) -> &[StmtId] {
        &self.roots
    }
    pub fn generated_roots(&self) -> &[ExprId] {
        &self.generated_roots
    }
    pub fn expression(&self, id: ExprId) -> Option<&Expr> {
        self.expressions.get(id.0 as usize)
    }
    pub fn statement(&self, id: StmtId) -> Option<&Stmt> {
        self.statements.get(id.0 as usize)
    }
    pub(crate) fn statements(&self) -> impl ExactSizeIterator<Item = (StmtId, &Stmt)> {
        self.statements
            .iter()
            .enumerate()
            .map(|(index, node)| (StmtId(index as u32), node))
    }
    pub(crate) fn generics(&self) -> impl ExactSizeIterator<Item = &GenericParam> {
        self.generics.iter()
    }
    pub fn pattern(&self, id: PatternId) -> Option<&Pattern> {
        self.patterns.get(id.0 as usize)
    }
    pub fn generic(&self, id: GenericParamId) -> Option<&GenericParam> {
        self.generics.get(id.0 as usize)
    }
    pub fn type_expression(&self, id: TypeExprId) -> Option<&TypeExpr> {
        self.types.get(id.0 as usize)
    }
    pub fn node_count(&self) -> usize {
        self.expressions.len()
            + self.statements.len()
            + self.patterns.len()
            + self.generics.len()
            + self.types.len()
    }
    pub fn info(&self, id: NodeId) -> Option<&NodeInfo> {
        match id {
            NodeId::Expr(id) => self.expression(id).map(|n| &n.info),
            NodeId::Stmt(id) => self.statement(id).map(|n| &n.info),
            NodeId::Pattern(id) => self.pattern(id).map(|n| &n.info),
            NodeId::Generic(id) => self.generic(id).map(|n| &n.info),
            NodeId::Type(id) => self.type_expression(id).map(|n| &n.info),
        }
    }
    /// Analysis attaches references by occurrence ID, never by matching spans.
    /// The caller owns the referenced type table; this does not certify a node.
    pub fn set_analyzed_type(&mut self, id: NodeId, ty: TypeId) -> bool {
        let info = match id {
            NodeId::Expr(id) => self.expressions.get_mut(id.0 as usize).map(|n| &mut n.info),
            NodeId::Stmt(id) => self.statements.get_mut(id.0 as usize).map(|n| &mut n.info),
            NodeId::Pattern(id) => self.patterns.get_mut(id.0 as usize).map(|n| &mut n.info),
            NodeId::Generic(id) => self.generics.get_mut(id.0 as usize).map(|n| &mut n.info),
            NodeId::Type(id) => self.types.get_mut(id.0 as usize).map(|n| &mut n.info),
        };
        if let Some(info) = info {
            info.analyzed_type = Some(ty);
            true
        } else {
            false
        }
    }
    /// Append a distinct generated syntax occurrence tied to a real prior node.
    /// Failure is transactional: no IDs or partial roots escape. All descendants
    /// carry this generation; synthetic file numbers alone confer no origin.
    pub fn mint_generated_expr(
        &mut self,
        source: &ast::Expr,
        anchor: NodeId,
        kind: GeneratedKind,
        owner: LexicalOwner,
        limits: HirLimits,
    ) -> Result<ExprId, LowerError> {
        lower::generated(self, source, anchor, kind, owner, limits)
    }
    /// Register and identify the generated AST as one transaction. The original
    /// AST is untouched if allocation or structural admission fails. Canonical
    /// record members and their controlled AST mirrors share occurrence IDs.
    pub fn mint_generated_identified_expr(
        &mut self,
        source: &mut ast::Expr,
        anchor: NodeId,
        kind: GeneratedKind,
        owner: LexicalOwner,
        limits: HirLimits,
    ) -> Result<ExprId, LowerError> {
        let before = (
            self.expressions.len(),
            self.statements.len(),
            self.patterns.len(),
            self.generics.len(),
            self.types.len(),
            self.generated_roots.len(),
        );
        let id = self.mint_generated_expr(source, anchor, kind, owner, limits)?;
        if let Err(error) = identify::expression(self, source, id, limits) {
            self.expressions.truncate(before.0);
            self.statements.truncate(before.1);
            self.patterns.truncate(before.2);
            self.generics.truncate(before.3);
            self.types.truncate(before.4);
            self.generated_roots.truncate(before.5);
            return Err(error);
        }
        Ok(id)
    }
}
