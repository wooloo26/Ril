//! Owned source syntax. Names are unresolved and every node retains byte spans.
use crate::SyntaxNode;
use ril_compiler_core::{
    ids::{ExprId, GenericParamId, PatternId, StmtId, TypeExprId},
    source::Span,
};

pub trait AstNode: Sized {
    fn cast(node: SyntaxNode) -> Option<Self>;
    fn syntax(&self) -> &SyntaxNode;
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub statements: Vec<Stmt>,
}

#[derive(Clone, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    /// Assigned by identified HIR lowering. Clones retain the occurrence;
    /// source structural equality deliberately does not compare this identity.
    pub hir_id: Option<StmtId>,
}
impl PartialEq for Stmt {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.span == other.span
    }
}
impl std::fmt::Debug for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Stmt")
            .field("kind", &self.kind)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(
    clippy::large_enum_variant,
    reason = "Keep owned declaration payloads uniform for frontend consumers"
)]
pub enum StmtKind {
    Binding(Binding),
    Function(Function),
    Type(TypeDeclaration),
    Effect(EffectDeclaration),
    Use(UseDeclaration),
    Handler(Vec<HandlerArm>),
    HandlerApplication(Expr),
    Assignment {
        target: Expr,
        operator: String,
        value: Expr,
    },
    Expr {
        expression: Expr,
        terminated: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Visibility {
    #[default]
    Private,
    Public,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingMode {
    Let,
    LetMut,
    View,
    Var,
    VarMut,
    Scoped,
    ScopedMut,
}

impl BindingMode {
    pub fn is_mutable(self) -> bool {
        matches!(self, Self::LetMut | Self::VarMut | Self::ScopedMut)
    }
    pub fn is_reassignable(self) -> bool {
        matches!(self, Self::Var | Self::VarMut)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub visibility: Visibility,
    pub is_meta: bool,
    pub mode: BindingMode,
    pub pattern: Pattern,
    pub ty: Option<TypeExpr>,
    pub value: Expr,
    pub fallback: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub visibility: Visibility,
    pub is_meta: bool,
    pub is_halt: bool,
    pub name: String,
    pub generics: Vec<GenericParameter>,
    pub parameters: Vec<Parameter>,
    pub return_type: Option<TypeExpr>,
    pub annotations: Vec<Annotation>,
    pub signature_where: Vec<Stmt>,
    pub body: Option<Block>,
    pub span: Span,
}

#[derive(Clone, Eq)]
pub struct GenericParameter {
    pub name: String,
    pub bound: Option<TypeExpr>,
    pub default: Option<TypeExpr>,
    pub span: Span,
    pub hir_id: Option<GenericParamId>,
}
impl PartialEq for GenericParameter {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.bound == other.bound
            && self.default == other.default
            && self.span == other.span
    }
}
impl std::fmt::Debug for GenericParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GenericParameter")
            .field("name", &self.name)
            .field("bound", &self.bound)
            .field("default", &self.default)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ParameterMode {
    #[default]
    Read,
    Mut,
    SharedMut,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub pattern: Pattern,
    pub mode: ParameterMode,
    pub ty: Option<TypeExpr>,
    pub default: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationKind {
    Effect,
    Capability,
}

/// Exact annotation spelling including @ or &; semantic resolution interprets
/// storage names, closure layers, provider references and effect rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    pub kind: AnnotationKind,
    pub text: String,
    pub span: Span,
}

#[derive(Clone, Eq)]
pub struct TypeExpr {
    pub text: String,
    pub kind: TypeKind,
    pub span: Span,
    pub hir_id: Option<TypeExprId>,
}
impl PartialEq for TypeExpr {
    fn eq(&self, other: &Self) -> bool {
        self.text == other.text && self.kind == other.kind && self.span == other.span
    }
}
impl std::fmt::Debug for TypeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeExpr")
            .field("text", &self.text)
            .field("kind", &self.kind)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Name {
        path: Vec<String>,
        arguments: Vec<TypeExpr>,
    },
    Optional(Box<TypeExpr>),
    Array {
        length: Option<Box<Expr>>,
        element: Box<TypeExpr>,
    },
    Map {
        key: Box<TypeExpr>,
        value: Box<TypeExpr>,
    },
    Tuple(Vec<TypeExpr>),
    Record {
        fields: Vec<TypeField>,
        row: Option<Box<TypeExpr>>,
    },
    Callable {
        parameters: Vec<Parameter>,
        result: Option<Box<TypeExpr>>,
        annotations: Vec<Annotation>,
    },
    TypeFunction {
        parameters: Vec<GenericParameter>,
        body: Box<Expr>,
    },
    Projection {
        base: Box<TypeExpr>,
        field: String,
    },
    ComputedProjection {
        base: Box<TypeExpr>,
        key: Box<Expr>,
    },
    KeyOf(Box<TypeExpr>),
    Computation(Box<Expr>),
    Mapped {
        binder: String,
        keys: Box<Expr>,
        value: Box<TypeExpr>,
        tuple: bool,
    },
    Rest(Box<TypeExpr>),
    KindArrow {
        parameter: Box<TypeExpr>,
        result: Box<TypeExpr>,
    },
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeField {
    pub name: String,
    pub mutable: bool,
    pub ty: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDeclaration {
    pub visibility: Visibility,
    pub is_halt: bool,
    pub name: String,
    pub generics: Vec<GenericParameter>,
    pub value: Option<TypeExpr>,
    pub variants: Vec<Variant>,
    pub opaque: bool,
    /// `type W(T)` / bare `type W`, as distinct from `type W = T`.
    pub nominal: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    pub name: String,
    pub generics: Vec<GenericParameter>,
    pub payload: Option<TypeExpr>,
    pub result: Option<TypeExpr>,
    pub annotations: Vec<Annotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectDeclaration {
    pub visibility: Visibility,
    pub name: String,
    pub generics: Vec<GenericParameter>,
    pub operations: Vec<Function>,
    pub members: Vec<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDeclaration {
    pub visibility: Visibility,
    pub path: Vec<String>,
    pub alias: Option<String>,
    pub members: Vec<ImportMember>,
    pub glob: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportMember {
    pub name: String,
    pub alias: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub statements: Vec<Stmt>,
    pub where_items: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub hir_id: Option<ExprId>,
}
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.span == other.span
    }
}
impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Expr")
            .field("kind", &self.kind)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Literal(Literal),
    Interpolated(Vec<StringPart>),
    Name(String),
    Path(Vec<String>),
    Generic {
        base: Box<Expr>,
        arguments: Vec<TypeExpr>,
    },
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    Record {
        ty: Option<TypeExpr>,
        fields: Vec<RecordField>,
        spread: Option<Box<Expr>>,
        members: Vec<RecordMember>,
    },
    Unary {
        operator: String,
        operand: Box<Expr>,
    },
    Binary {
        operator: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        arguments: Vec<Argument>,
    },
    Field {
        base: Box<Expr>,
        field: String,
        safe: bool,
    },
    ComputedField {
        base: Box<Expr>,
        key: Box<Expr>,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
        safe: bool,
    },
    Lambda {
        parameters: Vec<Parameter>,
        return_type: Option<TypeExpr>,
        annotations: Vec<Annotation>,
        body: Box<Expr>,
    },
    Accessor(Vec<AccessorSegment>),
    Block(Block),
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    Match {
        value: Box<Expr>,
        arms: Vec<MatchArm>,
        type_match: bool,
    },
    Is {
        value: Box<Expr>,
        pattern: Pattern,
    },
    Loop(Block),
    While {
        condition: Box<Expr>,
        body: Block,
    },
    For {
        iterable: Box<Expr>,
        pattern: Pattern,
        body: Block,
    },
    Control {
        operation: ControlOperation,
        value: Option<Box<Expr>>,
    },
    TypeValue(TypeExpr),
    KeyOf(TypeExpr),
    Derive {
        base: Option<Box<Expr>>,
        recipe: Box<Expr>,
    },
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },
    Ambient,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Integer(String),
    Float(String),
    String(String),
    RawString(String),
    Bytes(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringPart {
    Text(String),
    Interpolation {
        expression: Box<Expr>,
        format: Option<String>,
        span: Span,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlOperation {
    Return,
    Last,
    Next,
    Resume,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordMember {
    Field(RecordField),
    Spread(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Argument {
    pub label: Option<String>,
    pub mode: ParameterMode,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccessorSegment {
    pub field: String,
    pub safe: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandlerArm {
    pub operation: Expr,
    pub parameters: Vec<Parameter>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Eq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
    pub hir_id: Option<PatternId>,
}
impl PartialEq for Pattern {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.span == other.span
    }
}
impl std::fmt::Debug for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Pattern")
            .field("kind", &self.kind)
            .field("span", &self.span)
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternKind {
    Name(String),
    Wildcard,
    Literal(Literal),
    Tuple(Vec<Pattern>),
    Record {
        ty: Option<TypeExpr>,
        fields: Vec<PatternField>,
        rest: bool,
        rest_binding: Option<String>,
    },
    Constructor {
        path: Vec<String>,
        arguments: Vec<Pattern>,
        /// Distinguishes a nullary tag `None` from the invalid tag call `None()`.
        parenthesized: bool,
    },
    Alternative(Vec<Pattern>),
    Mode {
        mode: BindingMode,
        pattern: Box<Pattern>,
    },
    Type {
        ty: TypeExpr,
        binder: Option<String>,
    },
    Value(Box<Expr>),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatternField {
    pub name: String,
    pub pattern: Pattern,
    pub span: Span,
}
