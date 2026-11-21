use std::collections::HashSet;

use ril_base::span::Span;

#[derive(Clone, Debug)]
pub struct Spanned<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub const fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }
}

pub type Name = Spanned<String>;

macro_rules! arenas {
    ($(($id:ident, $node:ty, $field:ident, $push:ident, $get:ident)),* $(,)?) => {
        $(
            #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
            pub struct $id(usize);
        )*
        #[derive(Debug, Default)]
        pub struct Ast {
            $( $field: Vec<Spanned<$node>>, )*
            grouped: HashSet<ExprId>,
            pub items: Vec<StmtId>,
        }

        impl Ast {
            $(
                pub(crate) fn $push(&mut self, span: Span, value: $node) -> $id {
                    let id = $id(self.$field.len());
                    self.$field.push(Spanned::new(value, span));
                    id
                }

                pub fn $get(&self, id: $id) -> &Spanned<$node> {
                    self.$field.get(id.0).unwrap_or_else(|| ril_base::ice!("invalid syntax node {:?}", id))
                }
            )*
        }
    };
}

arenas! {
    (ExprId, Expr, exprs, add_expr, expr),
    (TypeId, Type, types, add_ty, ty),
    (PatternId, Pattern, patterns, add_pattern, pattern),
    (StmtId, Stmt, statements, add_stmt, stmt),
}

impl Ast {
    pub(crate) fn add_group(&mut self, span: Span, inner: ExprId) -> ExprId {
        let id = self.add_expr(span, self.expr(inner).value.clone());
        self.grouped.insert(id);
        id
    }

    pub fn navigation_chain(&self, root: ExprId) -> Option<(ExprId, Vec<ExprId>)> {
        let mut steps = Vec::new();
        let mut current = root;
        let mut safe = false;
        loop {
            if current != root && self.grouped.contains(&current) {
                break;
            }
            match self.expr(current).value {
                Expr::Member {
                    base, safe: step, ..
                }
                | Expr::Index {
                    base, safe: step, ..
                } => {
                    safe |= step;
                    steps.push(current);
                    current = base;
                }
                _ => break,
            }
        }
        steps.reverse();
        safe.then_some((current, steps))
    }

    pub fn statements(&self) -> impl Iterator<Item = &Spanned<Stmt>> {
        self.statements.iter()
    }

    pub fn expressions(&self) -> impl Iterator<Item = &Spanned<Expr>> {
        self.exprs.iter()
    }
}

#[derive(Clone, Debug)]
pub struct Path {
    pub segments: Vec<Segment>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Segment {
    pub name: Name,
    pub arguments: Vec<GenericArg>,
}

#[derive(Clone, Debug)]
pub enum GenericArg {
    Type(TypeId),
    Value(ExprId),
    Mode(Storage),
}

#[derive(Clone, Debug)]
pub struct GenericParam {
    pub name: Name,
    pub bound: Vec<TypeId>,
    pub guards: Vec<Path>,
    pub default: Option<GenericArg>,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Visibility {
    #[default]
    Private,
    Package,
    Public,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Mode {
    #[default]
    Plain,
    Ref,
    Mut,
    Shared,
    New,
    Via,
    Infer,
}

#[derive(Clone, Debug, Default)]
pub struct Storage {
    pub variable: bool,
    pub mode: Mode,
    pub mode_path: Option<Path>,
}

#[derive(Clone, Debug)]
pub struct Argument {
    pub name: Option<Name>,
    pub mode: Mode,
    pub value: ExprId,
}

#[derive(Clone, Debug)]
pub struct Parameter {
    pub name: Option<Name>,
    pub pattern: Option<PatternId>,
    pub is_meta: bool,
    pub mode: Mode,
    pub ty: Option<TypeId>,
    pub guards: Vec<ExprId>,
    pub default: Option<ExprId>,
}

#[derive(Clone, Debug, Default)]
pub struct Obligations {
    pub effects: Vec<Path>,
    pub open_effects: bool,
    pub state: Vec<StateClause>,
    pub open_state: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateKind {
    Write,
    Share,
    Capture,
    Environment,
    Return,
}

#[derive(Clone, Debug)]
pub struct StateClause {
    pub kind: StateKind,
    pub bindings: Vec<(Storage, Path)>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub params: Vec<Parameter>,
    pub obligations: Obligations,
    pub result_mode: Mode,
    pub result_sources: Vec<Name>,
    pub result: TypeId,
    pub guards: Vec<ExprId>,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: Name,
    pub is_meta: bool,
    pub generics: Vec<GenericParam>,
    pub signature: Signature,
    pub helpers: Vec<StmtId>,
    pub body: Option<ExprId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeKind {
    Alias,
    Nominal,
    Opaque,
}

#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub name: Name,
    pub kind: TypeKind,
    pub generics: Vec<GenericParam>,
    pub cleanup: Option<Name>,
    pub definition: TypeDefinition,
}

#[derive(Clone, Debug)]
pub enum TypeDefinition {
    Data(TypeId),
    Function(Vec<GenericParam>, ExprId),
    Sum(Vec<Variant>),
    Opaque,
}

#[derive(Clone, Debug)]
pub enum Variant {
    Constructor {
        name: Name,
        payload: Option<Vec<TypeId>>,
        attrs: Vec<ExprId>,
    },
    Spread(TypeId),
    Extensible,
}

#[derive(Clone, Debug)]
pub struct Import {
    pub file: Option<Vec<Name>>,
    pub modules: Vec<Name>,
    pub target: ImportTarget,
}

#[derive(Clone, Debug)]
pub enum ImportTarget {
    Module(Option<Name>),
    Items(Vec<(Name, Option<Name>)>),
    Glob,
}

#[derive(Clone, Debug)]
pub struct Handler {
    pub operation: Path,
    pub mode: Mode,
    pub value: ExprId,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub visibility: Visibility,
    pub attrs: Vec<ExprId>,
    pub kind: StmtKind,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Function(Box<Function>),
    Type(Box<TypeDecl>),
    Effect {
        name: Name,
        generics: Vec<GenericParam>,
        operations: Vec<StmtId>,
        spreads: Vec<TypeId>,
    },
    Sub {
        name: Name,
        items: Vec<StmtId>,
    },
    Import(Import),
    Binding {
        storage: Storage,
        pattern: PatternId,
        ty: Option<TypeId>,
        value: Option<ExprId>,
        fallback: Option<ExprId>,
        is_meta: bool,
        resource: bool,
    },
    With(Vec<Handler>),
    Expr(ExprId),
}

#[derive(Clone, Debug)]
pub struct TypeField {
    pub name: Name,
    pub storage: Storage,
    pub ty: TypeId,
    pub default: Option<ExprId>,
    pub attrs: Vec<ExprId>,
}

#[derive(Clone, Debug)]
pub enum FieldTail {
    Open,
    Named(Name),
}

#[derive(Clone, Debug)]
pub enum Type {
    PatternBinding(Name),
    PatternWildcard,
    PatternLiteral(Literal),
    Named(Path),
    Unit,
    Tuple(Vec<(Storage, TypeId)>),
    Array(Storage, TypeId),
    Map(TypeId, Storage, TypeId),
    Result(TypeId, TypeId),
    Option(TypeId),
    Record {
        fields: Vec<TypeField>,
        tail: Option<FieldTail>,
    },
    Mapped {
        storage: Storage,
        pattern: PatternId,
        iterable: ExprId,
        field: TypeId,
    },
    Callable(Box<Signature>),
    Unquote(ExprId),
    TypeOf(ExprId),
    Project {
        base: TypeId,
        field: Member,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LiteralKind {
    Bool,
    Int,
    F64,
    String,
    RawString,
    Bytes,
    RawBytes,
}

#[derive(Clone, Debug)]
pub struct Literal {
    pub kind: LiteralKind,
    pub text: String,
}

#[derive(Clone, Debug)]
pub enum Member {
    Name(Name),
    Index(Name),
    Computed(ExprId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Transfer {
    Return,
    Break,
    Continue,
}

#[derive(Clone, Debug)]
pub enum StringPart {
    Text(String),
    Interpolation(ExprId),
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pattern: PatternId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

#[derive(Clone, Debug)]
pub enum Condition {
    Expr(ExprId),
    Binding {
        mode: Mode,
        pattern: PatternId,
        value: ExprId,
    },
}

#[derive(Clone, Debug)]
pub struct ValueField {
    pub name: Name,
    pub storage: Storage,
    pub value: Option<ExprId>,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Path(Path),
    Unit,
    Literal(Literal),
    Interpolated(Vec<StringPart>),
    Block {
        statements: Vec<StmtId>,
        helpers: Vec<StmtId>,
    },
    Unary {
        op: Name,
        value: ExprId,
    },
    Binary {
        op: Name,
        left: ExprId,
        right: ExprId,
    },
    Cast {
        value: ExprId,
        target: TypeId,
    },
    Pipeline {
        value: ExprId,
        mode: Mode,
        target: ExprId,
        propagate: bool,
    },
    Member {
        base: ExprId,
        member: Member,
        safe: bool,
    },
    Index {
        base: ExprId,
        index: ExprId,
        safe: bool,
    },
    Range {
        start: Option<ExprId>,
        end: Option<ExprId>,
        inclusive: bool,
    },
    Call {
        callee: ExprId,
        args: Vec<Argument>,
    },
    Record {
        name: Option<Path>,
        fields: Vec<ValueField>,
    },
    Array(Vec<ExprId>),
    Tuple(Vec<ExprId>),
    Map(Vec<(ExprId, ExprId)>),
    Quote(TypeId),
    If {
        condition: Condition,
        yes: ExprId,
        no: Option<ExprId>,
    },
    While {
        condition: Condition,
        body: ExprId,
    },
    For {
        mode: Mode,
        iterable: ExprId,
        pattern: PatternId,
        body: ExprId,
    },
    Match {
        mode: Mode,
        value: ExprId,
        arms: Vec<MatchArm>,
    },
    Closure {
        params: Vec<Parameter>,
        obligations: Obligations,
        body: ExprId,
    },
    Accessor(Vec<(bool, Member)>),
    Transfer {
        kind: Transfer,
        value: Option<ExprId>,
    },
    Hole,
}

#[derive(Clone, Debug)]
pub struct PatternField {
    pub name: Name,
    pub storage: Storage,
    pub pattern: Option<PatternId>,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard,
    Unit,
    Binding(Storage, Name),
    Literal(Literal),
    Or(Vec<PatternId>),
    Tuple(Vec<PatternId>),
    Slice {
        text: bool,
        elements: Vec<PatternId>,
    },
    Rest(Option<Name>),
    Constructor(Path, Option<Vec<PatternId>>),
    Record {
        name: Option<Path>,
        fields: Vec<PatternField>,
        rest: bool,
    },
    Range {
        low: Literal,
        high: Literal,
        inclusive: bool,
    },
    Subset {
        ty: TypeId,
        binding: Option<PatternId>,
    },
    Type(TypeId),
    TypeBinding(Name),
}
