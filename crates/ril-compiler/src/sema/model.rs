use super::facts::{NodeId, Participant, Permission, Publication, ScopeId};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use ril_syntax::ast::{Annotation, BindingMode, Expr, Function, Parameter, TypeExpr};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
pub(crate) mod iteration;
pub mod rows;

/// Discard correlations after a may-join whose alternatives are no longer
/// represented by a live branch identity. Descendant identities and duties stay.
pub(crate) fn forget_choices(value: &mut Value) {
    value.origins.choices.clear();
    for nested in [
        &mut value.option_payload,
        &mut value.variant_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        forget_choices(nested);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    NumericHole(ril_compiler_core::ids::NumericHoleId),
    Unknown,
    Never,
    Unit,
    Bool,
    Int(String),
    Float(String),
    Str,
    Bytes,
    Named(String),
    Applied {
        constructor: String,
        arguments: Vec<TypeArgument>,
    },
    Generic(String),
    StaticKey(String),
    Projection {
        base: Box<Ty>,
        key: String,
    },
    Immutable(Box<Ty>),
    Optional(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    Array(Box<Ty>),
    Set(Box<Ty>),
    Range(Box<Ty>),
    Map(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Record(BTreeMap<String, (bool, Ty)>),
    OpenRecord {
        fields: BTreeMap<String, (bool, Ty)>,
        row: rows::OpenTail,
    },
    Callable(Vec<Ty>, Box<Ty>),
}
/// Instantiation identity keeps each admitted sort. Static keys are produced by
/// symbolic normalization, and binders use their owning declaration identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeArgument {
    Type(Box<Ty>),
    /// The complete normalized source type identity supplements the runtime
    /// shape, whose array and callable forms intentionally omit qualifiers.
    CanonicalType {
        ty: Box<Ty>,
        key: String,
    },
    Static(String),
    Symbolic(String),
}

/// Complete source type identity. This carries no graph, permission, resource,
/// lifetime, Result-inspection or termination evidence.
#[derive(Debug, Clone)]
pub struct SourceTypeWitness {
    pub syntax: TypeExpr,
    pub key: String,
}
impl PartialEq for SourceTypeWitness {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl Eq for SourceTypeWitness {}
impl SourceTypeWitness {
    /// Admit the closed compatibility validator before it scans syntax or
    /// allocates normalized keys. This does not authorize the witness's origin.
    pub(crate) fn validate_closed_with_work(&self, work: &mut usize) -> Option<bool> {
        *work = work.checked_sub(1 + self.key.len())?;
        // The validator walks the syntax, builds its argument key and then
        // builds its normalized comparison key. Each walk spends shared work.
        for _ in 0..3 {
            crate::static_eval::charge_type_syntax_clone(&self.syntax, work)?;
        }
        Some(self.validate_closed())
    }

    /// Pure consistency check for current values and frozen historical snapshots.
    /// Named state/effect bounds require a separately frozen lexical identity;
    /// the initial witness producer therefore leaves those schemas unresolved.
    pub fn validate_closed(&self) -> bool {
        use ril_syntax::ast::{ExprKind, Literal, TypeKind};
        if self.key.len() > 1024 * 1024 {
            return false;
        }
        let mut pending = vec![(&self.syntax, 0)];
        let mut nodes = 0usize;
        let mut bytes = 0usize;
        while let Some((ty, depth)) = pending.pop() {
            nodes += 1;
            if depth >= 64 || nodes > 4096 {
                return false;
            }
            match &ty.kind {
                TypeKind::Name { path, arguments } => {
                    if path.is_empty() || path.len() > 4096 || arguments.len() > 4096 - nodes {
                        return false;
                    }
                    for name in path {
                        if name.starts_with('\0') || name.starts_with('$') || name == "_" {
                            return false;
                        }
                        bytes = bytes.saturating_add(name.len());
                    }
                    pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
                }
                TypeKind::Optional(inner) => pending.push((inner, depth + 1)),
                TypeKind::Array { length, element } => {
                    if let Some(length) = length {
                        let ExprKind::Literal(Literal::Integer(text)) = &length.kind else {
                            return false;
                        };
                        bytes = bytes.saturating_add(text.len());
                    }
                    pending.push((element, depth + 1));
                }
                TypeKind::Map { key, value } => {
                    pending.push((key, depth + 1));
                    pending.push((value, depth + 1));
                }
                TypeKind::Tuple(items) => {
                    if items.len() > 4096 - nodes {
                        return false;
                    }
                    pending.extend(items.iter().map(|item| (item, depth + 1)));
                }
                TypeKind::Record { fields, row } => {
                    if row.is_some() || fields.len() > 4096 - nodes {
                        return false;
                    }
                    for field in fields {
                        bytes = bytes.saturating_add(field.name.len());
                        pending.push((&field.ty, depth + 1));
                    }
                }
                TypeKind::Callable {
                    parameters,
                    result,
                    annotations,
                } => {
                    if parameters.len() > 4096 - nodes || annotations.len() > 4096 {
                        return false;
                    }
                    for parameter in parameters {
                        if parameter.default.is_some() {
                            return false;
                        }
                        let Some(ty) = &parameter.ty else {
                            return false;
                        };
                        pending.push((ty, depth + 1));
                    }
                    if let Some(result) = result {
                        pending.push((result, depth + 1));
                    }
                    for annotation in annotations {
                        bytes = bytes.saturating_add(annotation.text.len());
                        if bytes > 1024 * 1024
                            || !matches!(
                                annotation.text.replace(' ', "").as_str(),
                                "@{}" | "&{}" | "&mut" | "&^mut" | "&closure" | "&capture"
                            )
                        {
                            return false;
                        }
                    }
                }
                TypeKind::Computation(expression) => {
                    let ExprKind::Literal(literal) = &expression.kind else {
                        return false;
                    };
                    bytes = bytes.saturating_add(match literal {
                        Literal::Integer(text)
                        | Literal::Float(text)
                        | Literal::String(text)
                        | Literal::RawString(text)
                        | Literal::Bytes(text) => text.len(),
                        _ => 0,
                    });
                }
                _ => return false,
            }
            if bytes > 1024 * 1024 || nodes.saturating_add(pending.len()) > 4096 {
                return false;
            }
        }
        crate::static_eval::effects::argument_key(&self.syntax, &BTreeMap::new()).is_closed()
            && self.key == crate::static_eval::normalized_argument_key(&self.syntax)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticCoordinate {
    Label(String),
    Index(i128),
}
/// Fill inference holes without changing any already selected nominal or
/// instantiated identity. Known mismatches remain for ordinary typing to reject.
pub fn join_type_holes(left: &Ty, right: &Ty) -> Ty {
    if left == right {
        return left.clone();
    }
    if matches!(left, Ty::Unknown | Ty::Never) {
        return right.clone();
    }
    if matches!(right, Ty::Unknown | Ty::Never) {
        return left.clone();
    }
    match (left, right) {
        (Ty::Optional(a), Ty::Optional(b)) => Ty::Optional(Box::new(join_type_holes(a, b))),
        (Ty::Immutable(a), Ty::Immutable(b)) => Ty::Immutable(Box::new(join_type_holes(a, b))),
        (Ty::Array(a), Ty::Array(b)) => Ty::Array(Box::new(join_type_holes(a, b))),
        (Ty::Set(a), Ty::Set(b)) => Ty::Set(Box::new(join_type_holes(a, b))),
        (Ty::Range(a), Ty::Range(b)) => Ty::Range(Box::new(join_type_holes(a, b))),
        (Ty::Result(a, b), Ty::Result(c, d)) => Ty::Result(
            Box::new(join_type_holes(a, c)),
            Box::new(join_type_holes(b, d)),
        ),
        (Ty::Map(a, b), Ty::Map(c, d)) => Ty::Map(
            Box::new(join_type_holes(a, c)),
            Box::new(join_type_holes(b, d)),
        ),
        (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => Ty::Tuple(
            a.iter()
                .zip(b)
                .map(|(a, b)| join_type_holes(a, b))
                .collect(),
        ),
        (Ty::Record(a), Ty::Record(b))
            if a.keys().eq(b.keys())
                && a.iter().all(|(name, (mutable, _))| *mutable == b[name].0) =>
        {
            Ty::Record(
                a.iter()
                    .map(|(name, (mutable, ty))| {
                        (name.clone(), (*mutable, join_type_holes(ty, &b[name].1)))
                    })
                    .collect(),
            )
        }
        (Ty::OpenRecord { fields: a, row: ar }, Ty::OpenRecord { fields: b, row: br })
            if ar == br
                && a.keys().eq(b.keys())
                && a.iter().all(|(name, (mutable, _))| *mutable == b[name].0) =>
        {
            Ty::OpenRecord {
                fields: a
                    .iter()
                    .map(|(name, (mutable, ty))| {
                        (name.clone(), (*mutable, join_type_holes(ty, &b[name].1)))
                    })
                    .collect(),
                row: ar.clone(),
            }
        }
        (Ty::Callable(a, b), Ty::Callable(c, d)) if a.len() == c.len() => Ty::Callable(
            a.iter()
                .zip(c)
                .map(|(a, c)| join_type_holes(a, c))
                .collect(),
            Box::new(join_type_holes(b, d)),
        ),
        _ => left.clone(),
    }
}
impl Ty {
    pub fn generic_names(&self, names: &mut BTreeSet<String>) {
        match self {
            Self::Generic(identity) | Self::StaticKey(identity) => {
                names.insert(identity.clone());
            }
            Self::Projection { base, key } => {
                base.generic_names(names);
                names.insert(key.clone());
            }
            Self::Immutable(inner)
            | Self::Optional(inner)
            | Self::Array(inner)
            | Self::Set(inner)
            | Self::Range(inner) => inner.generic_names(names),
            Self::Result(left, right) | Self::Map(left, right) => {
                left.generic_names(names);
                right.generic_names(names);
            }
            Self::Tuple(items) => {
                for item in items {
                    item.generic_names(names)
                }
            }
            Self::Record(fields) => {
                for (_, ty) in fields.values() {
                    ty.generic_names(names)
                }
            }
            Self::OpenRecord { fields, row } => {
                for (_, ty) in fields.values() {
                    ty.generic_names(names);
                }
                if let rows::RowIdentity::Binder(identity) = &row.identity {
                    names.insert(identity.clone());
                }
            }
            Self::Callable(parameters, result) => {
                for parameter in parameters {
                    parameter.generic_names(names)
                }
                result.generic_names(names);
            }
            Self::Applied { arguments, .. } => {
                for argument in arguments {
                    match argument {
                        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                            ty.generic_names(names)
                        }
                        TypeArgument::Symbolic(identity) => {
                            names.insert(identity.clone());
                        }
                        TypeArgument::Static(_) => {}
                    }
                }
            }
            _ => {}
        }
    }
    pub fn scalar(&self) -> bool {
        if let Self::Optional(inner) = self {
            return inner.scalar();
        }
        if let Self::Result(ok, error) = self {
            return ok.scalar() && error.scalar();
        }
        if let Self::Immutable(inner) = self {
            return inner.scalar();
        }
        if let Self::Named(name) = self {
            if ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(name).is_some() {
                return true;
            }
            return matches!(
                name.as_str(),
                "Time::Duration"
                    | "Time::Instant"
                    | "Time::TimeError"
                    | "Binary::ByteOrder"
                    | "Binary::BinaryError"
                    | "Num::NumError"
                    | "Io::ErrorKind"
                    | "File::OpenMode"
                    | "File::SeekFrom"
                    | "File::FileKind"
            );
        }
        matches!(
            self,
            Self::Never
                | Self::Unit
                | Self::Bool
                | Self::Int(_)
                | Self::Float(_)
                | Self::Str
                | Self::Bytes
                | Self::Range(_)
                | Self::StaticKey(_)
        )
    }
    pub fn contains_open_row(&self) -> bool {
        match self {
            Self::OpenRecord { .. } => true,
            Self::Immutable(inner)
            | Self::Optional(inner)
            | Self::Array(inner)
            | Self::Set(inner)
            | Self::Range(inner) => inner.contains_open_row(),
            Self::Map(a, b) | Self::Result(a, b) => a.contains_open_row() || b.contains_open_row(),
            Self::Tuple(items) => items.iter().any(Self::contains_open_row),
            Self::Record(fields) => fields.values().any(|(_, ty)| ty.contains_open_row()),
            Self::Callable(parameters, result) => {
                parameters.iter().any(Self::contains_open_row) || result.contains_open_row()
            }
            Self::Applied { arguments, .. } => arguments.iter().any(|argument| match argument {
                TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                    ty.contains_open_row()
                }
                _ => false,
            }),
            Self::Projection { base, .. } => base.contains_open_row(),
            _ => false,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constant {
    Bool(bool),
    Integer(i128),
    Unit,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Origins {
    pub nodes: BTreeSet<NodeId>,
    /// Correlated alternatives share a finite source-branch identity.
    pub choices: BTreeMap<u32, Vec<BTreeSet<NodeId>>>,
}
impl Origins {
    pub fn one(node: NodeId) -> Self {
        Self {
            nodes: [node].into(),
            choices: BTreeMap::new(),
        }
    }
    pub fn join(&self, other: &Self, branch: u32) -> Self {
        if self == other || self.nodes.is_empty() && other.nodes.is_empty() {
            return self.clone();
        }
        let mut choices = BTreeMap::new();
        for (&key, left) in &self.choices {
            if let Some(right) = other.choices.get(&key)
                && left == right
            {
                choices.insert(key, left.clone());
            }
        }
        choices.insert(branch, vec![self.nodes.clone(), other.nodes.clone()]);
        Self {
            nodes: self.nodes.union(&other.nodes).copied().collect(),
            choices,
        }
    }
    pub fn remap(&mut self, from: NodeId, to: NodeId) {
        if self.nodes.remove(&from) {
            self.nodes.insert(to);
        }
        for branches in self.choices.values_mut() {
            for nodes in branches {
                if nodes.remove(&from) {
                    nodes.insert(to);
                }
            }
        }
    }
}
pub type BindingId = usize;
pub type Env = BTreeMap<String, BindingId>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Callable {
    Constructor(String),
    Named(usize),
    Closure(usize),
    Symbolic(u32, Vec<String>),
    Builtin(String),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableBound {
    pub annotations: Vec<Annotation>,
    pub source: Option<ril_compiler_core::ids::CallableContractSource>,
    pub typing_environment: super::context::FrozenEnvironment,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableReturnBound {
    /// A raw branch has no ascription; its other fields are inert placeholders.
    pub raw: bool,
    /// Alternative prior contracts for this value, before this ascription.
    pub predecessors: Vec<Arc<CallableReturnBound>>,
    pub target: Ty,
    pub syntax: TypeExpr,
    pub span: Span,
    pub callables: Vec<Callable>,
    pub typing_environment: super::context::FrozenEnvironment,
}
impl CallableReturnBound {
    pub fn raw(callable: Callable, span: Span) -> Self {
        Self {
            raw: true,
            predecessors: vec![],
            target: Ty::Unknown,
            syntax: TypeExpr {
                hir_id: None,
                text: String::new(),
                kind: ril_syntax::ast::TypeKind::Tuple(vec![]),
                span,
            },
            span,
            callables: vec![callable],
            typing_environment: Default::default(),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub numeric: super::numeric_selection::NumericDependencies,
    /// Conditional copy qualification follows values until an actual
    /// invocation discharges the producing boundaries with complete witnesses.
    pub pending_copies: BTreeSet<super::copy_contract::CopyBoundaryId>,
    pub ty: Ty,
    pub source_type_witness: Option<Arc<SourceTypeWitness>>,
    pub origins: Origins,
    pub permission: Permission,
    pub publication: Publication,
    pub constant: Option<Constant>,
    pub static_coordinate: Option<StaticCoordinate>,
    pub unsuffixed_numeric: bool,
    pub literal_number: bool,
    pub callables: Vec<Callable>,
    pub callable_bounds: Vec<CallableBound>,
    pub callable_returns: Vec<Arc<CallableReturnBound>>,
    pub signature: Option<Vec<Parameter>>,
    pub participants: BTreeSet<Participant>,
    pub sources: BTreeSet<BindingId>,
    pub callback_parameters: BTreeSet<BindingId>,
    /// Authority received through a scoped binding; ordinary detached copies clear it.
    pub scoped: BTreeSet<BindingId>,
    pub stable: bool,
    pub marker: bool,
    pub retention_result: bool,
    pub through_return: bool,
    pub readonly_spread: bool,
    pub temporary: bool,
    pub requires_inference: bool,
    /// Only unresolved binders owned by the producing invocation may be solved
    /// from its result context. Caller and enclosing binders remain rigid.
    pub pending_inference: BTreeSet<String>,
    pub construction: bool,
    pub internal_aliases: bool,
    pub mutable_environment: bool,
    pub observer_environment: bool,
    pub cause: CauseId,
    pub results: BTreeSet<u32>,
    pub outer_results: BTreeSet<u32>,
    pub must_outer_results: BTreeSet<u32>,
    pub must_results: BTreeSet<u32>,
    pub condition_inspections: super::result_conditions::ConditionInspections,
    pub result_payload: Option<Box<Value>>,
    /// Complete tag-specific payload witnesses; absence means unknown shape.
    pub result_success: Option<Box<Value>>,
    pub result_error: Option<Box<Value>>,
    pub result_tag: Option<bool>,
    pub option_payload: Option<Box<Value>>,
    pub option_tag: Option<bool>,
    /// Immutable tag equality only. This carries no Result inspection or
    /// storage/freshness authority.
    pub option_identity: Option<ril_compiler_core::ids::OptionalTagId>,
    pub abnormal: bool,
    pub variant_tag: Option<String>,
    /// Legacy known-tag payload, used only when `variant_witnesses` is empty.
    /// New construction and joins keep one owner in `variant_witnesses`.
    pub variant_payload: Option<Box<Value>>,
    /// Actual tag-specific payloads. Missing entries prove no shape, and may
    /// never be filled using another constructor's payload or a fresh object.
    pub variant_witnesses: BTreeMap<String, Box<Value>>,
}
impl Value {
    /// Rebase node references only. Access, retention, Result and type duties
    /// belong to the original value and are never reconstructed by transport.
    pub(crate) fn remap_origins(&mut self, recent: NodeId, older: NodeId) {
        self.origins.remap(recent, older);
        for payload in [
            &mut self.variant_payload,
            &mut self.option_payload,
            &mut self.result_payload,
            &mut self.result_success,
            &mut self.result_error,
        ]
        .into_iter()
        .flatten()
        .chain(self.variant_witnesses.values_mut())
        {
            payload.remap_origins(recent, older);
        }
    }
    pub fn inherit_copy_dependencies(
        &mut self,
        dependencies: &BTreeSet<super::copy_contract::CopyBoundaryId>,
    ) {
        self.pending_copies.extend(dependencies);
        for payload in [
            &mut self.option_payload,
            &mut self.result_payload,
            &mut self.result_success,
            &mut self.result_error,
            &mut self.variant_payload,
        ]
        .into_iter()
        .flatten()
        .chain(self.variant_witnesses.values_mut())
        {
            payload.inherit_copy_dependencies(dependencies);
        }
    }
    pub fn nested_copy_dependencies(&self) -> BTreeSet<super::copy_contract::CopyBoundaryId> {
        let mut dependencies = self.pending_copies.clone();
        for payload in [
            &self.option_payload,
            &self.result_payload,
            &self.result_success,
            &self.result_error,
            &self.variant_payload,
        ]
        .into_iter()
        .flatten()
        .chain(self.variant_witnesses.values())
        {
            dependencies.extend(payload.nested_copy_dependencies());
        }
        dependencies
    }
    pub fn variant_witness(&self, tag: &str) -> Option<&Value> {
        self.variant_witnesses
            .get(tag)
            .map(Box::as_ref)
            .or_else(|| {
                (self.variant_witnesses.is_empty() && self.variant_tag.as_deref() == Some(tag))
                    .then_some(self.variant_payload.as_deref())
                    .flatten()
            })
    }
    pub fn same_abstract_value(&self, other: &Self) -> bool {
        self.pending_copies == other.pending_copies
            && self.same_source_schema(other)
            && self.option_identity == other.option_identity
            && self.ty == other.ty
            && self.origins == other.origins
            && self.permission == other.permission
            && self.publication == other.publication
            && self.constant == other.constant
            && self.static_coordinate == other.static_coordinate
            && self.callables == other.callables
            && self.callable_bounds == other.callable_bounds
            && self.callable_returns == other.callable_returns
            && self.signature == other.signature
            && self.pending_inference == other.pending_inference
            && self.requires_inference == other.requires_inference
            && self.stable == other.stable
            && self.mutable_environment == other.mutable_environment
            && self.observer_environment == other.observer_environment
            && self.temporary == other.temporary
            && self.scoped == other.scoped
            && self.variant_tag == other.variant_tag
            && self
                .variant_witnesses
                .keys()
                .eq(other.variant_witnesses.keys())
            && self
                .variant_witnesses
                .iter()
                .all(|(tag, payload)| payload.same_abstract_value(&other.variant_witnesses[tag]))
    }
    /// An incomplete carrier's root witness cannot hide a change in one of
    /// its known payload schemas. Causes and obligation identities are not
    /// schema coordinates and do not affect this fixed-point component.
    fn same_source_schema(&self, other: &Self) -> bool {
        self.ty == other.ty
            && self.source_type_witness == other.source_type_witness
            && [
                (&self.option_payload, &other.option_payload),
                (&self.result_payload, &other.result_payload),
                (&self.result_success, &other.result_success),
                (&self.result_error, &other.result_error),
                (&self.variant_payload, &other.variant_payload),
            ]
            .into_iter()
            .all(|(left, right)| match (left, right) {
                (Some(left), Some(right)) => left.same_source_schema(right),
                (None, None) => true,
                _ => false,
            })
            && self
                .variant_witnesses
                .keys()
                .eq(other.variant_witnesses.keys())
            && self
                .variant_witnesses
                .iter()
                .all(|(tag, left)| left.same_source_schema(&other.variant_witnesses[tag]))
    }
    pub fn scalar(ty: Ty, constant: Option<Constant>, cause: CauseId) -> Self {
        Self {
            numeric: Default::default(),
            pending_copies: BTreeSet::new(),
            ty,
            source_type_witness: None,
            origins: Origins::default(),
            permission: Permission::Read,
            publication: Publication::Immutable,
            constant,
            static_coordinate: None,
            unsuffixed_numeric: false,
            literal_number: false,
            callables: vec![],
            callable_bounds: vec![],
            callable_returns: vec![],
            signature: None,
            participants: BTreeSet::new(),
            sources: BTreeSet::new(),
            callback_parameters: BTreeSet::new(),
            scoped: BTreeSet::new(),
            stable: false,
            marker: false,
            retention_result: false,
            through_return: false,
            readonly_spread: false,
            temporary: false,
            requires_inference: false,
            pending_inference: BTreeSet::new(),
            construction: false,
            internal_aliases: false,
            mutable_environment: false,
            observer_environment: false,
            cause,
            results: BTreeSet::new(),
            outer_results: BTreeSet::new(),
            must_outer_results: BTreeSet::new(),
            must_results: BTreeSet::new(),
            condition_inspections: Default::default(),
            result_payload: None,
            result_success: None,
            result_error: None,
            result_tag: None,
            option_payload: None,
            option_tag: None,
            option_identity: None,
            abnormal: false,
            variant_tag: None,
            variant_payload: None,
            variant_witnesses: BTreeMap::new(),
        }
    }
    pub fn reference(ty: Ty, node: NodeId, cause: CauseId) -> Self {
        Self {
            origins: Origins::one(node),
            permission: Permission::Write,
            publication: Publication::Unpublished,
            stable: true,
            construction: true,
            ..Self::scalar(ty, None, cause)
        }
    }
    pub fn join(&self, other: &Self, branch: u32, cause: CauseId) -> Self {
        let mut value = self.clone();
        if self.source_type_witness != other.source_type_witness {
            value.source_type_witness = None;
        }
        value.numeric.include(&other.numeric);
        // Payload witnesses can disappear at a join. Their still-unproved
        // producers must survive at the containing value even in that case.
        value.pending_copies = self.nested_copy_dependencies();
        value
            .pending_copies
            .extend(other.nested_copy_dependencies());
        value.ty = join_type_holes(&self.ty, &other.ty);
        value.origins = self.origins.join(&other.origins, branch);
        value.permission = self.permission.meet(other.permission);
        value.publication = self.publication.join(other.publication);
        value.constant = if self.constant == other.constant {
            self.constant.clone()
        } else {
            None
        };
        if self.static_coordinate != other.static_coordinate {
            value.static_coordinate = None;
        }
        value.unsuffixed_numeric &= other.unsuffixed_numeric;
        value.literal_number &= other.literal_number;
        for callable in &other.callables {
            if !value.callables.contains(callable) {
                value.callables.push(callable.clone());
            }
        }
        for bound in &other.callable_bounds {
            if !value.callable_bounds.contains(bound) {
                value.callable_bounds.push(bound.clone());
            }
        }
        for bound in &other.callable_returns {
            if !value.callable_returns.contains(bound) {
                value.callable_returns.push(bound.clone());
            }
        }
        // The same descriptor may reach the join with and without an
        // ascription. Preserve the raw path explicitly; a contract on the
        // other branch must never become evidence for this one.
        for callable in self
            .callables
            .iter()
            .filter(|callable| other.callables.contains(callable))
        {
            let left = self
                .callable_returns
                .iter()
                .find(|bound| bound.callables.contains(callable));
            let right = other
                .callable_returns
                .iter()
                .find(|bound| bound.callables.contains(callable));
            let bound = match (left, right) {
                (Some(bound), None) | (None, Some(bound)) => bound,
                _ => continue,
            };
            if !value
                .callable_returns
                .iter()
                .any(|bound| bound.raw && bound.callables.contains(callable))
            {
                value
                    .callable_returns
                    .push(Arc::new(CallableReturnBound::raw(
                        callable.clone(),
                        bound.span,
                    )));
            }
        }
        value.participants.extend(&other.participants);
        value.sources.extend(&other.sources);
        value.callback_parameters.extend(&other.callback_parameters);
        value.scoped.extend(&other.scoped);
        value.stable &= other.stable;
        value.marker &= other.marker;
        value.retention_result &= other.retention_result;
        value.through_return |= other.through_return;
        value.readonly_spread |= other.readonly_spread;
        value.temporary |= other.temporary;
        value.requires_inference |= other.requires_inference;
        value
            .pending_inference
            .extend(other.pending_inference.iter().cloned());
        value.construction &= other.construction;
        value.internal_aliases |= other.internal_aliases;
        value.mutable_environment |= other.mutable_environment;
        value.observer_environment |= other.observer_environment;
        value.cause = cause;
        value.results.extend(&other.results);
        value.outer_results.extend(&other.outer_results);
        value.must_outer_results = self
            .must_outer_results
            .intersection(&other.must_outer_results)
            .copied()
            .collect();
        value.must_results = self
            .must_results
            .intersection(&other.must_results)
            .copied()
            .collect();
        value.condition_inspections = self.condition_inspections.branch_join(
            match self.constant {
                Some(Constant::Bool(value)) => Some(value),
                _ => None,
            },
            &other.condition_inspections,
            match other.constant {
                Some(Constant::Bool(value)) => Some(value),
                _ => None,
            },
        );
        value.result_tag = if self.result_tag == other.result_tag {
            self.result_tag
        } else {
            None
        };
        value.option_tag = if self.option_tag == other.option_tag {
            self.option_tag
        } else {
            None
        };
        value.option_identity = if self.option_identity == other.option_identity {
            self.option_identity
        } else {
            None
        };
        value.abnormal = self.abnormal && other.abnormal;
        value.variant_tag = if self.variant_tag == other.variant_tag {
            self.variant_tag.clone()
        } else {
            None
        };
        value.variant_witnesses = self
            .variant_witnesses
            .keys()
            .chain(other.variant_witnesses.keys())
            .chain(
                self.variant_tag
                    .iter()
                    .filter(|_| self.variant_payload.is_some()),
            )
            .chain(
                other
                    .variant_tag
                    .iter()
                    .filter(|_| other.variant_payload.is_some()),
            )
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|tag| {
                let payload = match (self.variant_witness(&tag), other.variant_witness(&tag)) {
                    (Some(a), Some(b)) => Some(Box::new(a.join(b, branch, cause))),
                    (Some(a), None)
                        if other
                            .variant_tag
                            .as_ref()
                            .is_some_and(|other| other != &tag) =>
                    {
                        Some(Box::new(a.clone()))
                    }
                    (None, Some(b))
                        if self.variant_tag.as_ref().is_some_and(|other| other != &tag) =>
                    {
                        Some(Box::new(b.clone()))
                    }
                    _ => None,
                }?;
                Some((tag, payload))
            })
            .collect();
        value.variant_payload = None;
        value.result_success = join_result_witness(
            &self.result_success,
            &other.result_success,
            self.result_tag,
            other.result_tag,
            true,
            branch,
            cause,
        );
        value.result_error = join_result_witness(
            &self.result_error,
            &other.result_error,
            self.result_tag,
            other.result_tag,
            false,
            branch,
            cause,
        );
        value.result_payload = match (&self.result_payload, &other.result_payload) {
            (Some(a), Some(b)) => Some(Box::new(a.join(b, branch, cause))),
            _ => None,
        };
        value.option_payload = match (&self.option_payload, &other.option_payload) {
            (Some(a), Some(b)) => Some(Box::new(a.join(b, branch, cause))),
            (Some(a), None) if other.option_tag == Some(false) => Some(a.clone()),
            (None, Some(b)) if self.option_tag == Some(false) => Some(b.clone()),
            _ => None,
        };
        if self.origins.nodes.is_empty() != other.origins.nodes.is_empty() {
            let reference = if self.origins.nodes.is_empty() {
                other
            } else {
                self
            };
            value.permission = reference.permission;
            value.publication = reference.publication;
            value.construction = reference.construction;
            value.stable = reference.stable;
            value.marker = reference.marker;
            value.retention_result = reference.retention_result;
        }
        value
    }
}

#[derive(Debug, Clone)]
pub struct BindingInfo {
    /// Canonical function statement that created a hoisted declaration binding.
    pub declaration: Option<ril_compiler_core::ids::StmtId>,
    /// Actual HIR pattern introducing this binding, independent of its span.
    pub pattern: Option<ril_compiler_core::ids::PatternId>,
    /// Actual initializer or pattern-receiver activation selecting this birth.
    /// Source identity and physical occurrence are checked together on replay.
    pub birth: Option<super::application_effect::OccurrenceIdentity>,
    /// Declaration interpretation belongs to this binding's own activation,
    /// including when a later closure or handler reads the captured binding.
    pub context: super::effect_identity::InvocationContext,
    pub typing_environment: super::context::FrozenEnvironment,
    pub name: String,
    pub value: Value,
    pub mode: BindingMode,
    pub owner: ScopeId,
    pub lexical_scope: u32,
    pub span: Span,
    pub root: super::facts::RootId,
    pub cell: Option<NodeId>,
    pub alive: bool,
    pub slot_used: bool,
    pub write_used: bool,
    pub used: bool,
    pub forwarded: BTreeSet<BindingId>,
    pub parameter: bool,
}
#[derive(Debug, Clone)]
pub struct FunctionInfo {
    pub hir_id: Option<ril_compiler_core::ids::StmtId>,
    pub definition: ril_compiler_core::ids::DefinitionId,
    pub lexical_owner: Option<ril_compiler_core::ids::CallableOwner>,
    /// Complete declaration-time interpretation; never merged with a caller.
    pub typing_environment: super::context::FrozenEnvironment,
    pub syntax: Function,
    pub lexical: Env,
    pub owner: Option<ScopeId>,
    pub handler_context: Vec<usize>,
    pub lexical_scope: u32,
    pub environment: Option<NodeId>,
    pub captures: BTreeSet<BindingId>,
    pub writes: BTreeSet<BindingId>,
    pub environment_published: bool,
}
#[derive(Debug, Clone)]
pub struct LambdaContract {
    pub source: Option<ril_compiler_core::ids::CallableContractSource>,
    pub return_type: Option<TypeExpr>,
    pub annotations: Vec<Annotation>,
    pub span: Span,
    pub typing_environment: super::context::FrozenEnvironment,
}

#[derive(Debug, Clone)]
pub struct ClosureInfo {
    pub contract: Arc<LambdaContract>,
    pub hir_id: Option<ril_compiler_core::ids::ExprId>,
    pub site: Option<ril_compiler_core::ids::ClosureSiteId>,
    pub creation_invocation: Option<super::copy_templates::InstanceId>,
    pub creation_closure: Option<super::effect_identity::ClosureInvocationId>,
    pub creation_default: Option<super::default_uses::DefaultUseId>,
    pub handler_context: Vec<usize>,
    pub parameters: Vec<Parameter>,
    pub body: Expr,
    pub lexical: Env,
    pub captures: BTreeSet<BindingId>,
    pub writes: BTreeSet<BindingId>,
    pub owner: ScopeId,
    pub node: NodeId,
}
#[derive(Debug, Clone)]
pub struct ClosureSite {
    pub id: ril_compiler_core::ids::ClosureSiteId,
    pub owner: ril_compiler_core::ids::CallableOwner,
    pub source: ril_compiler_core::ids::ExprId,
    pub span: Span,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Read,
    Write,
    Retain,
}
#[derive(Debug, Clone)]
pub struct AccessFact {
    /// Immutable observation epoch. Access facts are never coalesced across
    /// observations; recency below is the current transport cursor.
    pub observed_recency: usize,
    /// Allocation history at observation time. Before consulting the current
    /// heap, transport exactly the transitions after this cursor.
    pub recency: usize,
    /// Historical ownership of precisely the origins observed by this access.
    /// This is not an ownership or singleton proof for the current heap node.
    pub origin_owners: BTreeMap<NodeId, AccessOwners>,
    pub origins: Origins,
    pub slot: Option<super::facts::Slot>,
    pub mode: Mode,
    pub participants: BTreeSet<Participant>,
    pub cause: CauseId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccessOwners {
    Known(BTreeSet<ScopeId>),
    Unknown,
}
impl AccessOwners {
    fn include(&mut self, other: Self) {
        match (&mut *self, other) {
            (Self::Known(left), Self::Known(right)) if !left.is_empty() && !right.is_empty() => {
                left.extend(right);
            }
            _ => *self = Self::Unknown,
        }
    }
}
impl AccessFact {
    pub fn transport(&mut self, moves: &[(NodeId, NodeId)]) {
        self.origin_owners
            .retain(|node, _| self.origins.nodes.contains(node));
        for node in &self.origins.nodes {
            let owners = self
                .origin_owners
                .entry(*node)
                .or_insert(AccessOwners::Unknown);
            if matches!(owners, AccessOwners::Known(values) if values.is_empty()) {
                *owners = AccessOwners::Unknown;
            }
        }
        for &(recent, older) in &moves[self.recency..] {
            if let Some(owners) = self.origin_owners.remove(&recent) {
                if let Some(previous) = self.origin_owners.get_mut(&older) {
                    previous.include(owners);
                } else {
                    self.origin_owners.insert(older, owners);
                }
            }
            self.origins.remap(recent, older);
        }
        self.recency = moves.len();
    }
}
#[derive(Debug, Clone, Default)]
pub struct Obligations {
    pub copy_boundaries: BTreeSet<super::copy_contract::CopyBoundaryId>,
    pub performed_operations: BTreeSet<u64>,
    /// Concrete handler definitions selected by invocation, distinct from the
    /// operation identities that multiple lexical handlers may implement.
    pub selected_handlers: BTreeSet<usize>,
    pub handler_environment: bool,
    pub named: BTreeMap<BindingId, Mode>,
    pub concrete: BTreeMap<BindingId, Mode>,
    pub direct: BTreeMap<BindingId, Mode>,
    pub effects: BTreeSet<String>,
    pub concrete_effects: BTreeSet<String>,
    pub parameter_write: bool,
    pub retention: bool,
    pub capture: bool,
    pub symbolic: bool,
    /// Actual unknown-callback callee occurrences. These can justify a named
    /// upper-bound use, but never stand in for a concrete access or effect.
    pub symbolic_uses: BTreeSet<ril_compiler_core::ids::EvaluationOccurrenceId>,
    pub accesses: Vec<AccessFact>,
}
impl Obligations {
    pub fn include(&mut self, other: &Self, direct: bool) {
        self.copy_boundaries.extend(&other.copy_boundaries);
        self.performed_operations
            .extend(&other.performed_operations);
        self.selected_handlers.extend(&other.selected_handlers);
        self.handler_environment |= other.handler_environment;
        for (&binding, &mode) in &other.named {
            self.named
                .entry(binding)
                .and_modify(|m| *m = (*m).max(mode))
                .or_insert(mode);
        }
        if direct {
            for (&binding, &mode) in &other.direct {
                self.direct
                    .entry(binding)
                    .and_modify(|m| *m = (*m).max(mode))
                    .or_insert(mode);
            }
        }
        self.effects.extend(other.effects.iter().cloned());
        self.concrete_effects
            .extend(other.concrete_effects.iter().cloned());
        for (&binding, &mode) in &other.concrete {
            self.concrete
                .entry(binding)
                .and_modify(|old| *old = (*old).max(mode))
                .or_insert(mode);
        }
        self.parameter_write |= other.parameter_write;
        self.retention |= other.retention;
        self.capture |= other.capture;
        self.symbolic |= other.symbolic;
        self.symbolic_uses.extend(&other.symbolic_uses);
        self.accesses.extend(other.accesses.iter().cloned());
    }
}
#[derive(Debug, Clone)]
pub struct OperationFact {
    pub source: Option<OperationSource>,
    pub(crate) signature: Option<super::source_types::SourceSchema>,
    pub identity: u64,
    pub name: String,
    pub effect: String,
    pub span: Span,
    pub parameters: Vec<(ril_syntax::ast::ParameterMode, Ty)>,
    pub result: Ty,
}
#[derive(Debug, Clone)]
pub struct OperationSource {
    pub effect: ril_compiler_core::ids::StmtId,
    pub index: u32,
    pub environment: super::context::FrozenEnvironment,
    pub scope: ScopeId,
    pub context: super::effect_identity::InvocationContext,
}
#[derive(Debug, Clone)]
pub struct HandlerFact {
    pub site: Option<ril_compiler_core::ids::HandlerSiteId>,
    pub callable_owner: Option<ril_compiler_core::ids::CallableOwner>,
    pub id: usize,
    pub boundary: u32,
    pub span: Span,
    pub operations: Vec<u64>,
    pub arm_spans: Vec<Span>,
    pub lexical: Env,
    pub typing_environment: super::context::FrozenEnvironment,
    pub answer: Option<Ty>,
    pub arms: Vec<ril_syntax::ast::HandlerArm>,
    pub outer: Vec<usize>,
}
#[derive(Debug, Clone)]
pub struct RetainedHandlerFact {
    pub callable: Callable,
    pub span: Span,
    pub handlers: Vec<usize>,
    pub answer: Ty,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct RetainedHandlerAnswerFact {
    pub handler: usize,
    pub operation: u64,
    pub declaration: Ty,
    pub invocation: Ty,
    pub parametric: bool,
    pub transport: AnswerTransport,
    pub span: Span,
    pub cause: CauseId,
    pub activation: ScopeId,
    pub resumption_steps: Vec<usize>,
}
/// Eligibility of the continuation-answer handoff, not a request to copy it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnswerTransport {
    CopyChecked,
    /// The exact answer binder is returned; ordinary reception still applies.
    Identity,
    /// This invocation checked the ordinary answer graph through its suffix.
    OrdinaryChecked,
}
#[derive(Debug, Clone)]
pub struct ConstructorInfo {
    /// Declaration or normalized instance interpretation, captured once.
    pub typing_environment: super::context::FrozenEnvironment,
    pub source: Option<super::source_types::SourceView>,
    /// Original source and compatibility cache; structural queries use source.
    pub source_syntax: Option<Arc<TypeExpr>>,
    pub source_type_witness: Option<Arc<SourceTypeWitness>>,
    pub tag: String,
    pub owner: Ty,
    pub payload: Ty,
    pub nominal: bool,
    pub has_payload: bool,
    pub payload_syntax: Option<ril_syntax::ast::TypeExpr>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Frame {
    /// Signature interpretation for formals whose declaration environment
    /// differs from the receiver body's lexical environment.
    pub(crate) input_environment: Option<super::context::FrozenEnvironment>,
    pub(crate) copy_call_event: Option<super::copy_contract::CopyCallEventId>,
    /// Actual closure objects present in parameter graphs at reception.
    /// Forwarding one does not create another lexical environment.
    /// Values are the environment origin and receipt cause at that instant.
    /// Origin recency may change; it never changes or merges a ClosureInfo ID.
    pub(crate) received_closures: BTreeMap<usize, (NodeId, CauseId)>,
    pub callable_owner: Option<ril_compiler_core::ids::CallableOwner>,
    pub definition: Option<ril_compiler_core::ids::DefinitionId>,
    pub env: Env,
    pub owner: ScopeId,
    pub obligations: Obligations,
    pub locals: Vec<BindingId>,
    pub returned: Vec<Value>,
    pub(crate) foreign_return_states: Vec<usize>,
    pub anonymous: bool,
    pub callback_call: bool,
    pub expected_return: Option<Ty>,
    pub(crate) expected_return_source: Option<super::source_reception::Target>,
    /// Monotone failure state, never an authorization for unchecked returns.
    pub(crate) return_source_valid: bool,
}

#[derive(Debug, Clone)]
pub struct ResultDuty {
    pub id: u32,
    /// Immutable producer scope; current ownership may later be transferred.
    pub creation_owner: ScopeId,
    pub owner: ScopeId,
    pub span: Span,
    pub cause: CauseId,
    pub inspected: bool,
    pub returned: bool,
    pub abnormal: bool,
    pub covered: bool,
}

fn join_result_witness(
    left: &Option<Box<Value>>,
    right: &Option<Box<Value>>,
    left_tag: Option<bool>,
    right_tag: Option<bool>,
    tag: bool,
    branch: u32,
    cause: CauseId,
) -> Option<Box<Value>> {
    match (left, right) {
        (Some(a), Some(b)) => Some(Box::new(a.join(b, branch, cause))),
        (Some(a), None) if right_tag == Some(!tag) => Some(a.clone()),
        (None, Some(b)) if left_tag == Some(!tag) => Some(b.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod source_schema_fixed_point_tests {
    use super::*;

    fn payload(value: &mut Value, slot: usize) -> &mut Option<Box<Value>> {
        match slot {
            0 => &mut value.option_payload,
            1 => &mut value.result_payload,
            2 => &mut value.result_success,
            3 => &mut value.result_error,
            _ => &mut value.variant_payload,
        }
    }

    fn array(schema: &str) -> Value {
        let parsed = ril_syntax::parse(&format!("type Shape={schema}"));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let ril_syntax::ast::StmtKind::Type(declaration) = &parsed.program.statements[0].kind
        else {
            panic!("type fixture");
        };
        let syntax = declaration.value.clone().unwrap();
        let witness = SourceTypeWitness {
            key: crate::static_eval::normalized_argument_key(&syntax),
            syntax,
        };
        assert!(witness.validate_closed());
        let mut value = Value::scalar(
            Ty::Array(Box::new(Ty::Array(Box::new(Ty::Int("int".into()))))),
            None,
            CauseId(0),
        );
        value.source_type_witness = Some(std::sync::Arc::new(witness));
        value
    }

    #[test]
    fn incomplete_carriers_keep_nested_source_changes_in_the_fixed_point() {
        for slot in 0..5 {
            let mut before = Value::scalar(Ty::Unknown, None, CauseId(0));
            let mut after = before.clone();
            *payload(&mut before, slot) = Some(Box::new(array("[0][2]int")));
            *payload(&mut after, slot) = Some(Box::new(array("[0][3]int")));
            assert!(!before.same_abstract_value(&after));
            *payload(&mut after, slot) = None;
            assert!(!before.same_abstract_value(&after));
        }
    }

    #[test]
    fn equal_canonical_schema_does_not_depend_on_allocation_or_cause() {
        let before = array("[0][2]int");
        let mut same = array("[0][2]int");
        same.cause = CauseId(1);
        assert!(before.same_abstract_value(&same));
    }
}

#[cfg(test)]
mod callable_return_tests {
    use super::*;
    use ril_compiler_core::source::FileId;
    use ril_syntax::ast::TypeKind;

    fn bounded(callable: Callable, file: u32, identity: &str) -> Value {
        let span = Span {
            file: FileId(file),
            start: 10,
            end: 20,
        };
        let target = Ty::Generic(identity.into());
        let mut value = Value::scalar(
            Ty::Callable(vec![], Box::new(target.clone())),
            None,
            CauseId(0),
        );
        value.callables.push(callable.clone());
        value.callable_returns.push(Arc::new(CallableReturnBound {
            raw: false,
            predecessors: vec![],
            target,
            syntax: TypeExpr {
                hir_id: None,
                text: "T".into(),
                kind: TypeKind::Name {
                    path: vec!["T".into()],
                    arguments: vec![],
                },
                span,
            },
            span,
            callables: vec![callable],
            typing_environment: super::super::context::TypingEnvironment {
                types: super::super::context::StaticEnvironment {
                    generic_context: [("T".into(), identity.into())].into(),
                    generic_substitutions: [(identity.into(), Ty::Int("int".into()))].into(),
                    generic_sources: BTreeMap::new(),
                    bound_row_context: BTreeMap::new(),
                    bound_row_selections: BTreeMap::new(),
                    static_key_arguments: [(
                        format!("{identity}:key"),
                        StaticCoordinate::Label("value".into()),
                    )]
                    .into(),
                },
                contract_bindings: [("source".into(), file as usize)].into(),
            }
            .freeze(),
        }));
        value
    }

    #[test]
    fn joins_keep_independent_return_contracts_even_for_the_same_callable() {
        // One closure may receive different ascriptions on different paths.
        // A later invocation must inspect both contracts with their own scope.
        let left = bounded(Callable::Closure(3), 1, "left:T");
        let right = bounded(Callable::Closure(3), 2, "right:T");
        for joined in [
            left.join(&right, 1, CauseId(1)),
            right.join(&left, 1, CauseId(1)),
        ] {
            assert_eq!(joined.callables, vec![Callable::Closure(3)]);
            assert_eq!(joined.callable_returns.len(), 2);
            for original in [&left.callable_returns[0], &right.callable_returns[0]] {
                assert!(joined.callable_returns.contains(original));
            }
            assert_eq!(
                joined.join(&joined, 2, CauseId(2)).callable_returns,
                joined.callable_returns
            );
        }
    }

    #[test]
    fn nested_payload_joins_keep_callable_selection_and_return_contracts_together() {
        let left = bounded(Callable::Named(1), 1, "left:T");
        let right = bounded(Callable::Named(2), 2, "right:T");
        let wrap = |payload: Value| {
            let mut value =
                Value::scalar(Ty::Optional(Box::new(payload.ty.clone())), None, CauseId(0));
            value.option_tag = Some(true);
            value.option_payload = Some(Box::new(payload));
            value
        };
        let joined = wrap(left.clone()).join(&wrap(right.clone()), 1, CauseId(1));
        let payload = joined.option_payload.unwrap();
        assert_eq!(
            payload.callables,
            vec![Callable::Named(1), Callable::Named(2)]
        );
        assert_eq!(
            payload.callable_returns,
            [left.callable_returns, right.callable_returns].concat()
        );
    }

    #[test]
    fn a_contract_on_one_branch_does_not_replace_the_other_branches_raw_result() {
        let contracted = bounded(Callable::Closure(3), 1, "T");
        let mut raw = contracted.clone();
        raw.callable_returns.clear();
        for joined in [
            contracted.join(&raw, 1, CauseId(1)),
            raw.join(&contracted, 1, CauseId(1)),
        ] {
            assert_eq!(joined.callable_returns.len(), 2);
            assert!(
                joined
                    .callable_returns
                    .contains(&contracted.callable_returns[0])
            );
            let raw = joined
                .callable_returns
                .iter()
                .find(|bound| bound.raw)
                .unwrap();
            assert_eq!(raw.callables, [Callable::Closure(3)]);
            assert!(raw.predecessors.is_empty());
            assert!(raw.typing_environment.generic_substitutions.is_empty());
            assert_eq!(
                joined.join(&joined, 2, CauseId(2)).callable_returns,
                joined.callable_returns
            );
        }
    }

    #[test]
    fn different_callable_branches_do_not_invent_raw_paths_for_contracted_descriptors() {
        let contracted = bounded(Callable::Closure(3), 1, "T");
        let mut raw = bounded(Callable::Closure(4), 1, "T");
        raw.callable_returns.clear();
        let joined = contracted.join(&raw, 1, CauseId(1));
        assert_eq!(joined.callable_returns, contracted.callable_returns);
        assert_eq!(
            joined.callables,
            [Callable::Closure(3), Callable::Closure(4)]
        );
    }

    #[test]
    fn repeated_diamond_ascriptions_share_prior_proofs_instead_of_cloning_path_trees() {
        let mut value = bounded(Callable::Closure(3), 1, "T");
        for level in 0..64 {
            let mut left = (*value.callable_returns[0]).clone();
            left.predecessors = value.callable_returns.clone();
            left.span.start = level * 2;
            let mut right = left.clone();
            right.span.start += 1;
            value.callable_returns = vec![Arc::new(left), Arc::new(right)];
        }
        let cloned = value.clone();
        assert!(value.same_abstract_value(&cloned));
        assert!(Arc::ptr_eq(
            &value.callable_returns[0],
            &cloned.callable_returns[0]
        ));
        let mut seen = BTreeSet::new();
        let mut work = value.callable_returns.clone();
        while let Some(bound) = work.pop() {
            if seen.insert(Arc::as_ptr(&bound) as usize) {
                work.extend(bound.predecessors.iter().cloned());
            }
        }
        assert_eq!(
            seen.len(),
            129,
            "64 diamonds expanded into their exponential set of paths"
        );
    }
}

#[cfg(test)]
mod variant_witness_tests {
    use super::*;

    fn tagged(tag: &str, payload: Value) -> Value {
        let mut value = payload.clone();
        value.ty = Ty::Named("Example".into());
        value.variant_tag = Some(tag.into());
        value.variant_payload = None;
        value.variant_witnesses = [(tag.into(), Box::new(payload))].into();
        value
    }

    #[test]
    fn nested_payloads_have_one_owner_and_legacy_joins_normalize_to_that_form() {
        fn size(value: &Value) -> usize {
            1 + value
                .variant_witnesses
                .values()
                .map(|payload| size(payload))
                .sum::<usize>()
                + value.variant_payload.as_deref().map_or(0, size)
        }
        let mut nested = Value::scalar(Ty::Unit, None, CauseId(0));
        for _ in 0..96 {
            nested = tagged("Nested", nested);
        }
        assert_eq!(
            size(&nested.clone()),
            97,
            "nested proof payloads grew exponentially"
        );
        let mut legacy = tagged(
            "Value",
            Value::reference(Ty::Record(BTreeMap::new()), NodeId(1), CauseId(1)),
        );
        legacy.variant_payload = legacy.variant_witnesses.remove("Value");
        let canonical = tagged(
            "Value",
            Value::reference(Ty::Record(BTreeMap::new()), NodeId(2), CauseId(2)),
        );
        let joined = legacy.join(&canonical, 1, CauseId(3));
        assert!(joined.variant_payload.is_none());
        assert_eq!(
            joined.variant_witness("Value").unwrap().origins.nodes,
            [NodeId(1), NodeId(2)].into()
        );
    }

    #[test]
    fn a_known_different_tag_preserves_only_the_original_payload_for_each_alternative() {
        let done = tagged(
            "Done",
            Value::scalar(Ty::Unit, Some(Constant::Unit), CauseId(0)),
        );
        let yielded = tagged(
            "Yielded",
            Value::reference(Ty::Record(BTreeMap::new()), NodeId(7), CauseId(1)),
        );
        let joined = done.join(&yielded, 1, CauseId(2));
        assert!(joined.variant_tag.is_none());
        assert!(joined.variant_payload.is_none());
        assert_eq!(
            joined
                .variant_witnesses
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["Done", "Yielded"]
        );
        assert!(joined.variant_witnesses["Done"].origins.nodes.is_empty());
        assert_eq!(
            joined.variant_witnesses["Yielded"].origins.nodes,
            BTreeSet::from([NodeId(7)])
        );
        assert_eq!(
            joined.variant_witnesses["Yielded"].permission,
            Permission::Write
        );
    }

    #[test]
    fn missing_unknown_tag_witnesses_are_not_empty_or_fresh_payload_proofs() {
        let yielded = tagged(
            "Yielded",
            Value::reference(Ty::Record(BTreeMap::new()), NodeId(7), CauseId(1)),
        );
        let unknown = Value::scalar(Ty::Named("Example".into()), None, CauseId(2));
        for joined in [
            unknown.join(&yielded, 1, CauseId(3)),
            yielded.join(&unknown, 1, CauseId(3)),
        ] {
            assert!(joined.variant_witnesses.is_empty());
            assert!(joined.variant_payload.is_none());
        }
    }

    #[test]
    fn same_tag_joins_keep_every_origin_and_meet_payload_authority() {
        let mut writable = Value::reference(Ty::Record(BTreeMap::new()), NodeId(1), CauseId(1));
        writable.publication = Publication::Live;
        let mut readonly = Value::reference(Ty::Record(BTreeMap::new()), NodeId(2), CauseId(2));
        readonly.permission = Permission::Read;
        readonly.construction = false;
        readonly.publication = Publication::Immutable;
        let joined = tagged("Value", writable).join(&tagged("Value", readonly), 1, CauseId(3));
        let payload = &joined.variant_witnesses["Value"];
        assert_eq!(payload.origins.nodes, [NodeId(1), NodeId(2)].into());
        assert_eq!(payload.permission, Permission::Read);
        assert!(!payload.construction);
        assert_eq!(payload.publication, Publication::Live);
    }
}
