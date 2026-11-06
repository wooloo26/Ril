//! Owned source syntax. Names are unresolved and every node retains byte spans.
use crate::source::Span;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub statements: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

impl Stmt {
    pub(crate) fn item_name(&self) -> Option<&str> {
        match &self.kind {
            StmtKind::Function(item) => Some(&item.name),
            StmtKind::Type(item) => Some(&item.name),
            StmtKind::Effect(item) => Some(&item.name),
            StmtKind::Sub(item) => Some(&item.name),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind {
    Binding(Box<Binding>),
    Function(Function),
    Type(TypeDeclaration),
    Effect(EffectDeclaration),
    Use(UseDeclaration),
    Sub(SubDeclaration),
    Handler(Vec<HandlerArm>),
    HandlerApplication(Expr),
    Expr { expression: Expr, terminated: bool },
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
    Ref,
    VarRef,
    LetSharedMut,
    VarSharedMut,
    Via,
    Var,
    VarMut,
    Scoped,
    ScopedMut,
}

impl BindingMode {
    pub fn is_mutable(self) -> bool {
        matches!(
            self,
            Self::LetMut | Self::VarMut | Self::ScopedMut | Self::LetSharedMut | Self::VarSharedMut
        )
    }
    pub fn is_reassignable(self) -> bool {
        matches!(
            self,
            Self::Var | Self::VarMut | Self::VarRef | Self::VarSharedMut
        )
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
    pub return_mode: ReturnMode,
    pub annotations: Vec<Annotation>,
    pub signature_where: Vec<Stmt>,
    pub body: Option<Block>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericParameter {
    pub name: String,
    pub bound: Option<TypeExpr>,
    pub guards: Vec<TypeExpr>,
    pub default: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ParameterMode {
    #[default]
    Read,
    Mut,
    SharedMut,
    Ref,
    New,
    Via,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub pattern: Pattern,
    pub mode: ParameterMode,
    pub ty: Option<TypeExpr>,
    pub default: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnMode {
    Plain,
    Infer(Span),
    New,
    Ref(Vec<ReturnSource>),
    SharedMut(Vec<ReturnSource>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnSource {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationKind {
    Effect,
    State,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationScope {
    Lexical,
    Module,
    Enclosing,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnnotationReference {
    pub scope: AnnotationScope,
    pub name: TypeExpr,
}

/// Exact annotation spelling including @ or &; semantic resolution interprets
/// storage names, closure layers, provider references and effect rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    pub kind: AnnotationKind,
    pub references: Vec<AnnotationReference>,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeExpr {
    pub text: String,
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Name {
        path: Vec<String>,
        arguments: Vec<TypeExpr>,
    },
    Optional(Box<TypeExpr>),
    Array {
        access: Option<StorageMode>,
        element: Box<TypeExpr>,
    },
    ArrayPattern {
        length: Option<Box<Expr>>,
        element: Box<TypeExpr>,
    },
    Map {
        key: Box<TypeExpr>,
        access: Option<StorageMode>,
        value: Box<TypeExpr>,
    },
    Tuple(Vec<TypeExpr>),
    Alternatives(Vec<TypeExpr>),
    VariantPayload(Vec<VariantField>),
    Record {
        fields: Vec<TypeField>,
        row: Option<Box<TypeExpr>>,
    },
    Callable {
        parameters: Vec<Parameter>,
        result: Option<Box<TypeExpr>>,
        return_mode: ReturnMode,
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
        mode: Option<ModeExpression>,
        binder: String,
        keys: Box<Expr>,
        value: Box<TypeExpr>,
        tuple: bool,
    },
    Rest(Box<TypeExpr>),
    Member {
        mode: String,
        ty: Box<TypeExpr>,
    },
    OpenRow,
    PatternRest(Option<String>),
    PatternMode {
        binder: String,
        ty: Box<TypeExpr>,
    },
    TypeBinder(String),
    ModeLiteral,
    QualifiedMemberMode,
    KindArrow {
        parameter: Box<TypeExpr>,
        result: Box<TypeExpr>,
    },
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StorageMode {
    pub kind: StorageModeKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageModeKind {
    Mut,
    SharedMut,
    Ref,
    Via,
    Parameter(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModeExpression {
    Concrete(String),
    Static(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeField {
    pub name: String,
    pub mode: Option<String>,
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
    pub signature_where: Vec<Stmt>,
    pub opaque: bool,
    /// `type W(T)` / bare `type W`, as distinct from `type W = T`.
    pub nominal: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantField {
    pub label: Option<String>,
    pub mode: Option<String>,
    pub ty: TypeExpr,
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
pub struct SubDeclaration {
    pub visibility: Visibility,
    pub name: String,
    pub items: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDeclaration {
    pub visibility: Visibility,
    pub path: Vec<String>,
    pub namespaces: Vec<String>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
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
    TupleMember {
        mode: String,
        value: Box<Expr>,
    },
    Array(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    Record {
        ty: Option<TypeExpr>,
        /// The single source-ordered list of evaluated fields and spreads.
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
    Assignment {
        target: Box<Expr>,
        operator: String,
        value: Box<Expr>,
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
    EffectOperation {
        effect: Box<Expr>,
        name: String,
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
    IfLet {
        pattern: Pattern,
        value: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    Match {
        value: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Is {
        value: Box<Expr>,
        test: ValueTest,
    },
    Loop(Block),
    While {
        condition: Box<Expr>,
        body: Block,
    },
    WhileLet {
        pattern: Pattern,
        value: Box<Expr>,
        body: Block,
    },
    For {
        iterable: Box<Expr>,
        pattern: Pattern,
        body: Block,
    },
    Control {
        operation: ControlOperation,
        operator_span: Span,
        value: Option<Box<Expr>>,
    },
    TypeValue(TypeExpr),
    KeyOf(TypeExpr),
    ModeOf(TypeExpr),
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },
    Ambient,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueTest {
    pub kind: ValueTestKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueTestKind {
    Wildcard,
    Value(Box<Expr>),
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },
    Constructor {
        path: Vec<String>,
        head: Span,
        arguments: Option<Vec<ValueTest>>,
    },
    Tuple(Vec<ValueTest>),
    Record {
        ty: Option<TypeExpr>,
        fields: Vec<ValueTestField>,
    },
    Alternative(Vec<ValueTest>),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueTestField {
    pub name: String,
    pub test: ValueTest,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Integer(String),
    Float(String),
    String(String),
    RawString(String),
    Bytes(String),
    Bool(bool),
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
    Propagate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub mode: Option<String>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

impl Pattern {
    pub(crate) fn binding_names(&self, names: &mut Vec<String>) {
        match &self.kind {
            PatternKind::Name(name) | PatternKind::Rest(Some(name)) if name != "_" => {
                names.push(name.clone());
            }
            PatternKind::Tuple(items)
            | PatternKind::Array(items)
            | PatternKind::Alternative(items)
            | PatternKind::Constructor {
                arguments: items, ..
            } => {
                for item in items {
                    item.binding_names(names);
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    field.pattern.binding_names(names);
                }
                if let Some(name) = rest_binding {
                    names.push(name.clone());
                }
            }
            PatternKind::Mode { pattern, .. } => pattern.binding_names(names),
            PatternKind::Type(ty) => ty.pattern_binding_names(names),
            _ => {}
        }
    }
}

impl TypeExpr {
    fn pattern_binding_names(&self, names: &mut Vec<String>) {
        match &self.kind {
            TypeKind::TypeBinder(name) | TypeKind::PatternRest(Some(name)) if name != "_" => {
                names.push(name.clone());
            }
            TypeKind::PatternMode { binder, ty } => {
                names.push(binder.clone());
                ty.pattern_binding_names(names);
            }
            TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                for arg in arguments {
                    arg.pattern_binding_names(names);
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    field.ty.pattern_binding_names(names);
                }
                if let Some(row) = row {
                    row.pattern_binding_names(names);
                }
            }
            TypeKind::Map { key, value, .. } => {
                key.pattern_binding_names(names);
                value.pattern_binding_names(names);
            }
            TypeKind::Array { element: ty, .. }
            | TypeKind::ArrayPattern { element: ty, .. }
            | TypeKind::Member { ty, .. }
            | TypeKind::Optional(ty) => ty.pattern_binding_names(names),
            _ => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternKind {
    Name(String),
    Wildcard,
    Literal(Literal),
    Range {
        start: Literal,
        end: Literal,
        inclusive: bool,
    },
    Tuple(Vec<Pattern>),
    Array(Vec<Pattern>),
    /// Only a directly enclosing tuple or array may introduce a rest. Tuples
    /// discard their remainder; arrays may bind its read-only window.
    Rest(Option<String>),
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
    Type(TypeExpr),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatternField {
    pub name: String,
    pub pattern: Pattern,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentSort {
    Type,
    Value,
    Mode,
}

impl GenericParameter {
    pub(crate) fn sort_for(name: &str, bound: Option<&TypeExpr>) -> ArgumentSort {
        match bound.map(|ty| &ty.kind) {
            Some(TypeKind::KeyOf(_)) => ArgumentSort::Value,
            Some(TypeKind::QualifiedMemberMode) => ArgumentSort::Mode,
            Some(TypeKind::Name { path, .. })
                if path.last().is_some_and(|name| name == "MemberMode") =>
            {
                ArgumentSort::Mode
            }
            _ if name.as_bytes().first().is_some_and(u8::is_ascii_uppercase) => ArgumentSort::Type,
            _ => ArgumentSort::Value,
        }
    }
}
