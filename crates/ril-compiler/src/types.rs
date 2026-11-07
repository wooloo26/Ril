//! Resolved type templates. Static evaluation and constraint solving reduce these terms.
use crate::{
    ast::*,
    hir::{DefId, ModeParameterId, ScopeId},
    input::{DefinitionSource, ExpressionSiteId, SourceIndex, TypeSiteId},
    library::{LibraryTypeId, OperationPhase},
    source::Span,
};
use ril_ir::layout::{FloatType, IntegerType, ValueRepr};
use std::{collections::BTreeMap, error::Error, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    Unit,
    Never,
    Bool,
    Integer(IntegerType),
    Float(FloatType),
    Text,
    Bytes,
}

impl PrimitiveType {
    pub const fn representation(self) -> ValueRepr {
        match self {
            Self::Unit => ValueRepr::Unit,
            Self::Never => ValueRepr::Never,
            Self::Bool => ValueRepr::Bool,
            Self::Integer(integer) => ValueRepr::Integer(integer),
            Self::Float(float) => ValueRepr::Float(float),
            Self::Text => ValueRepr::Text,
            Self::Bytes => ValueRepr::Bytes,
        }
    }
    fn named(name: &str) -> Option<Self> {
        Some(match name {
            "never" => Self::Never,
            "bool" => Self::Bool,
            "str" => Self::Text,
            "bytes" => Self::Bytes,
            "i8" => Self::Integer(IntegerType::I8),
            "i16" => Self::Integer(IntegerType::I16),
            "i32" => Self::Integer(IntegerType::I32),
            "i64" => Self::Integer(IntegerType::I64),
            "u8" => Self::Integer(IntegerType::U8),
            "u16" => Self::Integer(IntegerType::U16),
            "u32" => Self::Integer(IntegerType::U32),
            "u64" => Self::Integer(IntegerType::U64),
            "bigint" => Self::Integer(IntegerType::BigInt),
            "f32" => Self::Float(FloatType::F32),
            "f64" => Self::Float(FloatType::F64),
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeHead {
    Primitive(PrimitiveType),
    Definition(DefId),
    Wildcard,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixedAccess {
    Immutable,
    Ref,
    Mut,
    SharedMut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessTerm {
    Fixed(FixedAccess),
    Inferred(ModeParameterId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemberModeTerm {
    pub replaceable: bool,
    pub access: AccessTerm,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageAccessTerm {
    Access(AccessTerm),
    /// A member-mode parameter still requires a fixed-slot proof at selection.
    Parameter(DefId),
}

#[derive(Debug)]
pub enum MappedModeTerm {
    Concrete(MemberModeTerm),
    Computed(ExpressionSiteId),
}

#[derive(Debug)]
pub enum ParameterAccess {
    Read,
    Ref,
    Mut,
    SharedMut,
    New,
    Inferred(ModeParameterId),
}

#[derive(Debug)]
pub struct ParameterTerm {
    pub formal: FormalId,
    pub binding: Option<DefId>,
    pub label: Option<String>,
    pub access: ParameterAccess,
    pub ty: Option<TypeSiteId>,
    pub default: Option<ExpressionSiteId>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FormalId {
    pub callable: ScopeId,
    pub position: usize,
}

#[derive(Debug)]
pub enum ReturnTerm {
    Plain,
    New,
    Infer(Span),
    Ref(Vec<DefId>),
    SharedMut(Vec<DefId>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StateGroupId(pub usize);

#[derive(Debug)]
pub enum StateTerm {
    Open,
    Empty,
    Mut,
    SharedMut,
    Capture,
    Environment,
    Sources(StateGroupId),
    Return(Vec<(ReturnDependencyMode, DefId)>),
    Provider(DefId),
}

#[derive(Debug)]
pub enum ClauseTerm {
    OpenEffects,
    Effects(Vec<TypeSiteId>),
    State(StateTerm),
}

#[derive(Debug)]
pub struct CallableTerm {
    pub scope: ScopeId,
    pub parameters: Vec<ParameterTerm>,
    pub result: Option<TypeSiteId>,
    pub result_access: ReturnTerm,
    pub clauses: Vec<ClauseTerm>,
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub generics: Vec<DefId>,
    pub phase: OperationPhase,
    pub callable: CallableTerm,
}

#[derive(Debug)]
pub struct GenericTerm {
    pub sort: ArgumentSort,
    pub bound: Option<TypeSiteId>,
    pub guards: Vec<TypeSiteId>,
    pub default: Option<TypeSiteId>,
}

#[derive(Debug)]
pub struct FieldTerm {
    pub name: String,
    pub mode: Option<MemberModeTerm>,
    pub ty: TypeSiteId,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantFieldTerm {
    pub label: Option<String>,
    pub mode: Option<MemberModeTerm>,
    pub ty: TypeSiteId,
}

#[derive(Debug)]
pub enum TypeTermKind {
    Apply {
        head: TypeHead,
        arguments: Vec<TypeSiteId>,
    },
    Array {
        access: Option<StorageAccessTerm>,
        element: TypeSiteId,
    },
    ArrayPattern {
        length: Option<ExpressionSiteId>,
        element: TypeSiteId,
    },
    Map {
        key: TypeSiteId,
        access: Option<StorageAccessTerm>,
        value: TypeSiteId,
    },
    Tuple(Vec<TypeSiteId>),
    TypeSet(Vec<TypeSiteId>),
    VariantPayload(Vec<VariantFieldTerm>),
    Record {
        fields: Vec<FieldTerm>,
        row: Option<TypeSiteId>,
    },
    Callable(CallableTerm),
    TypeFunction {
        scope: ScopeId,
        parameters: Vec<DefId>,
        body: ExpressionSiteId,
    },
    Projection {
        base: TypeSiteId,
        field: String,
    },
    ComputedProjection {
        base: TypeSiteId,
        key: ExpressionSiteId,
    },
    KeyOf(TypeSiteId),
    Computation(ExpressionSiteId),
    Mapped {
        scope: ScopeId,
        mode: Option<MappedModeTerm>,
        binder: DefId,
        keys: ExpressionSiteId,
        value: TypeSiteId,
        tuple: bool,
    },
    Rest(TypeSiteId),
    Member {
        mode: MemberModeTerm,
        ty: TypeSiteId,
    },
    OpenRow {
        parameter: Option<DefId>,
    },
    PatternRest(Option<DefId>),
    PatternMode {
        binder: DefId,
        ty: TypeSiteId,
    },
    PatternBinder(Option<DefId>),
    ModeLiteral(MemberModeTerm),
    KindArrow {
        parameter: TypeSiteId,
        result: TypeSiteId,
    },
}

#[derive(Debug)]
pub struct TypeTerm {
    pub scope: ScopeId,
    pub span: Span,
    pub kind: TypeTermKind,
}

pub struct TypeTemplates {
    pub nodes: Vec<TypeTerm>,
    pub signatures: BTreeMap<DefId, FunctionSignature>,
    pub generics: BTreeMap<DefId, GenericTerm>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateError {
    MissingSyntax(Span),
    MissingReference(Span),
    MissingBinding(Span),
    InvalidSyntax(Span),
}

impl fmt::Display for TemplateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "incomplete resolved type template: {self:?}")
    }
}
impl Error for TemplateError {}

struct Lower<'a, 'source> {
    input: &'a SourceIndex<'source>,
    modes: BTreeMap<Span, ModeParameterId>,
    parameters: BTreeMap<Span, DefId>,
    generics: BTreeMap<Span, DefId>,
}

impl TypeTemplates {
    pub fn lower(input: &SourceIndex<'_>) -> Result<Self, TemplateError> {
        let mut lower = Lower {
            input,
            modes: BTreeMap::new(),
            parameters: BTreeMap::new(),
            generics: BTreeMap::new(),
        };
        for (index, mode) in input.hir.mode_parameters.iter().enumerate() {
            lower.modes.insert(mode.span, ModeParameterId(index));
        }
        for (id, source) in input.definitions() {
            match source {
                DefinitionSource::Parameter(parameter) => {
                    lower.parameters.insert(parameter.pattern.span, id);
                }
                DefinitionSource::GenericParameter(parameter) => {
                    lower.generics.insert(parameter.span, id);
                }
                _ => {}
            }
        }
        let nodes = input
            .type_nodes()
            .map(|(_, ty)| lower.ty(ty))
            .collect::<Result<_, _>>()?;
        let mut signatures = BTreeMap::new();
        let mut generics = BTreeMap::new();
        for (id, source) in input.definitions() {
            match source {
                DefinitionSource::Function(function) => {
                    let phase = if let Some(primitive) = input.hir.primitives.get(&id) {
                        primitive.phase()
                    } else if let Some(body) = input.hir.library_bodies.get(&id) {
                        body.phase()
                    } else if function.is_meta {
                        OperationPhase::Static
                    } else {
                        OperationPhase::Runtime
                    };
                    signatures.insert(
                        id,
                        FunctionSignature {
                            generics: lower.generic_bindings(&function.generics)?,
                            phase,
                            callable: lower.callable(
                                input
                                    .definition_scope(id)
                                    .ok_or(TemplateError::MissingBinding(function.span))?,
                                &function.parameters,
                                function.return_type.as_ref(),
                                &function.return_mode,
                                &function.annotations,
                            )?,
                        },
                    );
                }
                DefinitionSource::GenericParameter(parameter) => {
                    generics.insert(
                        id,
                        GenericTerm {
                            sort: GenericParameter::sort_for(
                                &parameter.name,
                                parameter.bound.as_ref(),
                            ),
                            bound: lower.optional_ty(parameter.bound.as_ref())?,
                            guards: lower.type_list(&parameter.guards)?,
                            default: lower.optional_ty(parameter.default.as_ref())?,
                        },
                    );
                }
                _ => {}
            }
        }
        Ok(Self {
            nodes,
            signatures,
            generics,
        })
    }
    pub fn get(&self, id: TypeSiteId) -> Option<&TypeTerm> {
        self.nodes.get(id.0)
    }
}

impl Lower<'_, '_> {
    fn tid(&self, ty: &TypeExpr) -> Result<TypeSiteId, TemplateError> {
        self.input
            .type_id(ty)
            .ok_or(TemplateError::MissingSyntax(ty.span))
    }
    fn eid(&self, expression: &Expr) -> Result<ExpressionSiteId, TemplateError> {
        self.input
            .expression_id(expression)
            .ok_or(TemplateError::MissingSyntax(expression.span))
    }
    fn optional_ty(&self, ty: Option<&TypeExpr>) -> Result<Option<TypeSiteId>, TemplateError> {
        ty.map(|ty| self.tid(ty)).transpose()
    }
    fn type_list(&self, types: &[TypeExpr]) -> Result<Vec<TypeSiteId>, TemplateError> {
        types.iter().map(|ty| self.tid(ty)).collect()
    }
    fn name(&self, span: Span, path: &[String]) -> Result<DefId, TemplateError> {
        self.input
            .references_at(span)
            .find(|reference| reference.path == path)
            .map(|reference| reference.definition)
            .ok_or(TemplateError::MissingReference(span))
    }
    fn inferred(&self, span: Span) -> Result<ModeParameterId, TemplateError> {
        self.modes
            .get(&span)
            .copied()
            .ok_or(TemplateError::MissingBinding(span))
    }
    fn binding_scope(&self, ty: &TypeExpr) -> Result<ScopeId, TemplateError> {
        self.input
            .hir
            .type_binding_scopes
            .get(&ty.span)
            .copied()
            .ok_or(TemplateError::MissingBinding(ty.span))
    }
    fn generic_bindings(
        &self,
        parameters: &[GenericParameter],
    ) -> Result<Vec<DefId>, TemplateError> {
        parameters
            .iter()
            .map(|parameter| {
                self.generics
                    .get(&parameter.span)
                    .copied()
                    .ok_or(TemplateError::MissingBinding(parameter.span))
            })
            .collect()
    }
    fn member_mode(&self, mode: MemberMode) -> Result<MemberModeTerm, TemplateError> {
        let access = match mode.access {
            MemberAccess::Default => AccessTerm::Fixed(FixedAccess::Immutable),
            MemberAccess::Ref => AccessTerm::Fixed(FixedAccess::Ref),
            MemberAccess::Mut => AccessTerm::Fixed(FixedAccess::Mut),
            MemberAccess::SharedMut => AccessTerm::Fixed(FixedAccess::SharedMut),
            MemberAccess::Via => AccessTerm::Inferred(self.inferred(mode.span)?),
        };
        Ok(MemberModeTerm {
            replaceable: mode.replaceable,
            access,
        })
    }
    fn storage(
        &self,
        mode: Option<&StorageMode>,
    ) -> Result<Option<StorageAccessTerm>, TemplateError> {
        mode.map(|mode| {
            Ok(match &mode.kind {
                StorageModeKind::Mut => {
                    StorageAccessTerm::Access(AccessTerm::Fixed(FixedAccess::Mut))
                }
                StorageModeKind::SharedMut => {
                    StorageAccessTerm::Access(AccessTerm::Fixed(FixedAccess::SharedMut))
                }
                StorageModeKind::Ref => {
                    StorageAccessTerm::Access(AccessTerm::Fixed(FixedAccess::Ref))
                }
                StorageModeKind::Via => {
                    StorageAccessTerm::Access(AccessTerm::Inferred(self.inferred(mode.span)?))
                }
                StorageModeKind::Parameter(name) => {
                    StorageAccessTerm::Parameter(self.name(mode.span, std::slice::from_ref(name))?)
                }
            })
        })
        .transpose()
    }
    fn pattern_binding(&self, name: &str, span: Span) -> Result<Option<DefId>, TemplateError> {
        if name == "_" {
            return Ok(None);
        }
        self.input
            .definitions()
            .filter_map(|(id, source)| {
                if self.input.hir.definitions[id.0].name != name {
                    return None;
                }
                let pattern = match source {
                    DefinitionSource::Pattern(pattern) => pattern,
                    DefinitionSource::Parameter(parameter) => &parameter.pattern,
                    DefinitionSource::Binding(binding) => &binding.pattern,
                    _ => return None,
                };
                let root = pattern.span;
                (root.file == span.file && root.start <= span.start && root.end >= span.end)
                    .then_some((root.end - root.start, id))
            })
            .min_by_key(|(width, _)| *width)
            .map(|(_, id)| Some(id))
            .ok_or(TemplateError::MissingBinding(span))
    }
    fn callable(
        &self,
        scope: ScopeId,
        parameters: &[Parameter],
        result: Option<&TypeExpr>,
        mode: &ReturnMode,
        annotations: &[Annotation],
    ) -> Result<CallableTerm, TemplateError> {
        let parameters = parameters
            .iter()
            .enumerate()
            .map(|(position, parameter)| {
                let access = match parameter.mode {
                    ParameterMode::Read => ParameterAccess::Read,
                    ParameterMode::Ref => ParameterAccess::Ref,
                    ParameterMode::Mut => ParameterAccess::Mut,
                    ParameterMode::SharedMut => ParameterAccess::SharedMut,
                    ParameterMode::New => ParameterAccess::New,
                    ParameterMode::Via => ParameterAccess::Inferred(
                        self.inferred(
                            parameter
                                .mode_span
                                .ok_or(TemplateError::MissingBinding(parameter.span))?,
                        )?,
                    ),
                };
                let label = if let PatternKind::Name(name) = &parameter.pattern.kind {
                    Some(name.clone())
                } else {
                    None
                };
                Ok(ParameterTerm {
                    formal: FormalId {
                        callable: scope,
                        position,
                    },
                    binding: self.parameters.get(&parameter.pattern.span).copied(),
                    label,
                    access,
                    ty: self.optional_ty(parameter.ty.as_ref())?,
                    default: parameter
                        .default
                        .as_ref()
                        .map(|value| self.eid(value))
                        .transpose()?,
                    span: parameter.span,
                })
            })
            .collect::<Result<_, _>>()?;
        let sources = |sources: &[ReturnSource]| {
            sources
                .iter()
                .map(|source| self.name(source.span, std::slice::from_ref(&source.name)))
                .collect::<Result<Vec<_>, _>>()
        };
        let result_access = match mode {
            ReturnMode::Plain => ReturnTerm::Plain,
            ReturnMode::New => ReturnTerm::New,
            ReturnMode::Infer(span) => ReturnTerm::Infer(*span),
            ReturnMode::Ref(names) => ReturnTerm::Ref(sources(names)?),
            ReturnMode::SharedMut(names) => ReturnTerm::SharedMut(sources(names)?),
        };
        let clauses = annotations
            .iter()
            .map(|annotation| {
                Ok(match &annotation.kind {
                    AnnotationKind::Effects(EffectRow::Open) => ClauseTerm::OpenEffects,
                    AnnotationKind::Effects(EffectRow::Closed(effects)) => {
                        ClauseTerm::Effects(self.type_list(effects)?)
                    }
                    AnnotationKind::State(clause) => ClauseTerm::State(match clause {
                        StateClause::Open => StateTerm::Open,
                        StateClause::Empty => StateTerm::Empty,
                        StateClause::Mut => StateTerm::Mut,
                        StateClause::SharedMut => StateTerm::SharedMut,
                        StateClause::Capture => StateTerm::Capture,
                        StateClause::Environment => StateTerm::Environment,
                        StateClause::Sources { .. } => StateTerm::Sources(StateGroupId(
                            self.input
                                .hir
                                .state_source_groups
                                .iter()
                                .position(|group| group.span == annotation.span)
                                .ok_or(TemplateError::MissingReference(annotation.span))?,
                        )),
                        StateClause::Provider(name) => {
                            StateTerm::Provider(self.name(name.span, &name.path)?)
                        }
                        StateClause::Return(sources) => StateTerm::Return(
                            sources
                                .iter()
                                .map(|source| {
                                    Ok((
                                        source.mode,
                                        self.name(source.name.span, &source.name.path)?,
                                    ))
                                })
                                .collect::<Result<_, _>>()?,
                        ),
                    }),
                })
            })
            .collect::<Result<_, TemplateError>>()?;
        Ok(CallableTerm {
            scope,
            parameters,
            result: self.optional_ty(result)?,
            result_access,
            clauses,
        })
    }
    fn ty(&self, ty: &TypeExpr) -> Result<TypeTerm, TemplateError> {
        let kind = match &ty.kind {
            TypeKind::Name { path, arguments } => {
                let head = if let [name] = path.as_slice() {
                    if let Some(primitive) = PrimitiveType::named(name) {
                        TypeHead::Primitive(primitive)
                    } else if name == "_" {
                        TypeHead::Wildcard
                    } else {
                        TypeHead::Definition(self.name(ty.span, path)?)
                    }
                } else {
                    TypeHead::Definition(self.name(ty.span, path)?)
                };
                TypeTermKind::Apply {
                    head,
                    arguments: self.type_list(arguments)?,
                }
            }
            TypeKind::QualifiedMemberMode => TypeTermKind::Apply {
                head: TypeHead::Definition(
                    self.name(ty.span, &["ril/reflect".into(), "MemberMode".into()])?,
                ),
                arguments: vec![],
            },
            TypeKind::Optional(inner) => TypeTermKind::Apply {
                head: TypeHead::Definition(
                    self.input
                        .hir
                        .library_types
                        .iter()
                        .find_map(|(definition, ty)| {
                            (*ty == LibraryTypeId::Option).then_some(*definition)
                        })
                        .ok_or(TemplateError::MissingBinding(ty.span))?,
                ),
                arguments: vec![self.tid(inner)?],
            },
            TypeKind::Array { access, element } => TypeTermKind::Array {
                access: self.storage(access.as_ref())?,
                element: self.tid(element)?,
            },
            TypeKind::ArrayPattern { length, element } => TypeTermKind::ArrayPattern {
                length: length.as_ref().map(|value| self.eid(value)).transpose()?,
                element: self.tid(element)?,
            },
            TypeKind::Map { key, access, value } => TypeTermKind::Map {
                key: self.tid(key)?,
                access: self.storage(access.as_ref())?,
                value: self.tid(value)?,
            },
            TypeKind::Tuple(types) if types.is_empty() => TypeTermKind::Apply {
                head: TypeHead::Primitive(PrimitiveType::Unit),
                arguments: vec![],
            },
            TypeKind::Tuple(types) => TypeTermKind::Tuple(self.type_list(types)?),
            TypeKind::Alternatives(types) => TypeTermKind::TypeSet(self.type_list(types)?),
            TypeKind::VariantPayload(fields) => TypeTermKind::VariantPayload(
                fields
                    .iter()
                    .map(|field| {
                        Ok(VariantFieldTerm {
                            label: field.label.clone(),
                            mode: field.mode.map(|mode| self.member_mode(mode)).transpose()?,
                            ty: self.tid(&field.ty)?,
                        })
                    })
                    .collect::<Result<_, _>>()?,
            ),
            TypeKind::Record { fields, row } => TypeTermKind::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(FieldTerm {
                            name: field.name.clone(),
                            mode: field.mode.map(|mode| self.member_mode(mode)).transpose()?,
                            ty: self.tid(&field.ty)?,
                            span: field.span,
                        })
                    })
                    .collect::<Result<_, _>>()?,
                row: self.optional_ty(row.as_deref())?,
            },
            TypeKind::Callable {
                parameters,
                result,
                return_mode,
                annotations,
            } => TypeTermKind::Callable(self.callable(
                self.binding_scope(ty)?,
                parameters,
                result.as_deref(),
                return_mode,
                annotations,
            )?),
            TypeKind::TypeFunction { parameters, body } => TypeTermKind::TypeFunction {
                scope: self.binding_scope(ty)?,
                parameters: self.generic_bindings(parameters)?,
                body: self.eid(body)?,
            },
            TypeKind::Projection { base, field } => TypeTermKind::Projection {
                base: self.tid(base)?,
                field: field.clone(),
            },
            TypeKind::ComputedProjection { base, key } => TypeTermKind::ComputedProjection {
                base: self.tid(base)?,
                key: self.eid(key)?,
            },
            TypeKind::KeyOf(base) => TypeTermKind::KeyOf(self.tid(base)?),
            TypeKind::Computation(value) => TypeTermKind::Computation(self.eid(value)?),
            TypeKind::Mapped {
                mode,
                binder,
                keys,
                value,
                tuple,
            } => {
                let scope = self.binding_scope(ty)?;
                let binding = self
                    .input
                    .hir
                    .definitions
                    .iter()
                    .enumerate()
                    .find(|(_, definition)| definition.scope == scope && definition.name == *binder)
                    .map(|(index, _)| DefId(index))
                    .ok_or(TemplateError::MissingBinding(ty.span))?;
                TypeTermKind::Mapped {
                    scope,
                    mode: mode
                        .as_ref()
                        .map(|mode| match mode {
                            ModeExpression::Concrete(mode) => {
                                self.member_mode(*mode).map(MappedModeTerm::Concrete)
                            }
                            ModeExpression::Static(value) => {
                                self.eid(value).map(MappedModeTerm::Computed)
                            }
                        })
                        .transpose()?,
                    binder: binding,
                    keys: self.eid(keys)?,
                    value: self.tid(value)?,
                    tuple: *tuple,
                }
            }
            TypeKind::Rest(inner) => TypeTermKind::Rest(self.tid(inner)?),
            TypeKind::Member { mode, ty } => TypeTermKind::Member {
                mode: self.member_mode(*mode)?,
                ty: self.tid(ty)?,
            },
            TypeKind::OpenRow => TypeTermKind::OpenRow {
                parameter: self
                    .input
                    .definitions()
                    .find_map(|(id, source)| match source {
                        DefinitionSource::Row(row) if std::ptr::eq(row, ty) => Some(id),
                        _ => None,
                    }),
            },
            TypeKind::PatternRest(name) => TypeTermKind::PatternRest(
                name.as_ref()
                    .map(|name| self.pattern_binding(name, ty.span))
                    .transpose()?
                    .flatten(),
            ),
            TypeKind::PatternMode { binder, ty: inner } => TypeTermKind::PatternMode {
                binder: self
                    .pattern_binding(binder, ty.span)?
                    .ok_or(TemplateError::MissingBinding(ty.span))?,
                ty: self.tid(inner)?,
            },
            TypeKind::TypeBinder(name) => {
                TypeTermKind::PatternBinder(self.pattern_binding(name, ty.span)?)
            }
            TypeKind::ModeLiteral(mode) => TypeTermKind::ModeLiteral(self.member_mode(*mode)?),
            TypeKind::KindArrow { parameter, result } => TypeTermKind::KindArrow {
                parameter: self.tid(parameter)?,
                result: self.tid(result)?,
            },
            TypeKind::Error => return Err(TemplateError::InvalidSyntax(ty.span)),
        };
        Ok(TypeTerm {
            scope: self
                .input
                .type_scope(ty.span)
                .ok_or(TemplateError::MissingSyntax(ty.span))?,
            span: ty.span,
            kind,
        })
    }
}
