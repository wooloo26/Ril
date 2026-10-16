//! Structural constraints retain type identity and existing value authority.
use super::{
    copy_contract::CopyValueSnapshot,
    effect_identity::{ArgumentKey, InvocationContext},
    facts::{ScopeId, Slot},
    model::{
        SourceTypeWitness, Ty,
        rows::{Row, RowIdentity, RowTail},
    },
};
use ril_compiler_core::{diagnostic::CauseId, ids::DefinitionId, source::Span};
use ril_syntax::ast::TypeExpr;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

pub use ril_compiler_core::ids::{BoundRowId, GenericBoundCheckId, GenericBoundId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundPathStep {
    Bound,
    Field(String),
    RowTail,
    TypeArgument(u32),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundDeclarationPath {
    pub generic_index: u32,
    pub path: Vec<BoundPathStep>,
}

/// R is not a fake function generic parameter at T's source index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundRowRole {
    ImplicitResidual,
    /// A real explicitly declared Type parameter also used as a row.
    DeclaredTypeParameter {
        binder: String,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundRowDeclaration {
    pub id: BoundRowId,
    pub definition: DefinitionId,
    pub ordinal: u32,
    pub name: String,
    pub role: BoundRowRole,
    pub declaration_paths: Vec<BoundDeclarationPath>,
    pub identity: RowIdentity,
    /// Union of all required absences for this one shared row in its owner.
    pub lacks: BTreeSet<String>,
    pub span: Span, // diagnostic only
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BoundScope {
    /// Entries point to real GenericBinder records and their genuine indices.
    pub types: BTreeMap<String, String>,
    /// Separate typed namespace/capture for row residuals.
    pub rows: BTreeMap<String, BoundRowId>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordBoundField {
    pub label: String,
    pub mutable: bool,
    pub ty: Ty,
    pub syntax: TypeExpr,
    pub key: ArgumentKey,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclaredBoundTail {
    Closed,
    Row(BoundRowId),
    /// An already resolved concrete/named record tail, not an implicit binder.
    Concrete {
        syntax: TypeExpr,
        key: ArgumentKey,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericRecordBound {
    pub id: GenericBoundId,
    pub definition: DefinitionId,
    pub binder: String,
    pub generic_index: u32,
    pub syntax: TypeExpr,
    pub scope: BoundScope,
    pub fields: Vec<RecordBoundField>,
    pub tail: DeclaredBoundTail,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StructuralSchemaSource {
    Closed(Arc<SourceTypeWitness>),
    CallerBound(GenericBoundId),
    /// Legitimate rigid OpenRecord parameters need no GenericBoundId and no
    /// closed root. The owner/index freeze the declaration supporting fields.
    RigidParameter {
        definition: DefinitionId,
        parameter_index: u32,
        syntax: TypeExpr,
        scope: BoundScope,
    },
}
#[derive(Debug, Clone)]
pub struct StructuralSchema {
    pub source: StructuralSchemaSource,
    pub fields: Vec<RecordBoundField>,
    pub tail: RowTail,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundRowSelection {
    pub row: BoundRowId,
    pub remainder: Row<Ty>,
    pub fields: Vec<RecordBoundField>,
    /// Some only for an actually closed, independently verified remainder.
    pub source_type_witness: Option<Arc<SourceTypeWitness>>,
}
#[derive(Debug, Clone)]
pub enum BoundTypeSelectionStep {
    ArrayElement,
    MapKey,
    MapValue,
    Tuple(u32),
    Field(String),
    OptionalPayload,
    ResultSuccess,
    ResultError,
    AppliedArgument(u32),
    ImmutableInner,
    CallableParameter(u32),
    CallableResult,
}
#[derive(Debug, Clone)]
pub struct GenericBoundCheck {
    pub id: GenericBoundCheckId,
    pub required: GenericBoundId,
    pub context: InvocationContext,
    pub activation: ScopeId,
    pub allocation_epoch: usize,
    /// The snapshot is the real whole argument, including when this path has
    /// no runtime element (such as an empty array). It never fabricates T.
    pub argument_index: u32,
    pub selection_path: Vec<BoundTypeSelectionStep>,
    pub actual: CopyValueSnapshot,
    pub actual_schema: StructuralSchema,
    pub substitutions: BTreeMap<String, ArgumentKey>,
    pub rows: Vec<BoundRowSelection>,
    pub cause: CauseId,
    pub span: Span,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundAccess {
    Read,
    Write,
    /// read=false projection alone is not evidence that a write was authorized.
    ValueOnly,
}
#[derive(Debug, Clone)]
pub struct GenericBoundProjection {
    pub required: GenericBoundId,
    /// None is a universal declaration projection; Some pins a real call check.
    pub check: Option<GenericBoundCheckId>,
    pub context: InvocationContext,
    pub activation: ScopeId,
    pub allocation_epoch: usize,
    pub source: CopyValueSnapshot,
    pub slot: Slot,
    pub output: CopyValueSnapshot,
    pub access: BoundAccess,
    pub cause: CauseId,
    pub span: Span,
}

/// Certify the declared sort only. A registered structural promise never
/// substitutes for an application's complete selected type or capability graph.
pub(crate) fn certifies_type_sort(
    identity: &str,
    binder: &super::GenericBinder,
    parameter: &ril_syntax::ast::GenericParameter,
    bounds: &[GenericRecordBound],
) -> bool {
    if binder.identity != identity
        || binder.name != parameter.name
        || !parameter
            .name
            .chars()
            .next()
            .is_some_and(char::is_uppercase)
    {
        return false;
    }
    match parameter.bound.as_ref().map(|bound| &bound.kind) {
        None => true,
        Some(ril_syntax::ast::TypeKind::Name { path, arguments }) => {
            path == &["Type"] && arguments.is_empty()
        }
        Some(ril_syntax::ast::TypeKind::Record { .. }) => {
            bounds.iter().enumerate().any(|(index, bound)| {
                bound.id.0 as usize == index
                    && bound.binder == identity
                    && bound.definition == binder.definition
                    && bound.generic_index == binder.index
            })
        }
        _ => false,
    }
}
