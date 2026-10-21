//! Structural type evidence retained with its scoped identities and snapshots.
//! These records carry no independent capability authority.
use super::{
    ContractSyntax, CopyValueSnapshot, OpenTail, Projection, ResumptionContext, RowIdentity,
    SourceTypeWitness,
};
pub use ril_compiler_core::ids::{BoundRowId, GenericBoundCheckId, GenericBoundId};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{DefinitionId, TypeId},
    source::Span,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordBoundKey {
    GenericBuiltin(ril_compiler_core::builtin_calls::GenericBuiltin),
    Closed(String),
    Binder {
        identity: String,
    },
    Name {
        name: String,
        arguments: Vec<Self>,
    },
    Array {
        length: Option<String>,
        element: Box<Self>,
    },
    Map {
        key: Box<Self>,
        value: Box<Self>,
    },
    Tuple(Vec<Self>),
    Record {
        fields: Vec<(String, bool, Self)>,
        row: Option<Box<Self>>,
    },
    Callable {
        parameters: Vec<(super::Access, Self)>,
        result: Box<Self>,
        annotations: Vec<String>,
    },
}
#[derive(Debug, Clone)]
pub enum BoundRowTail {
    Closed,
    Open(OpenTail),
}
#[derive(Debug, Clone)]
pub struct BoundRowShape {
    pub fields: BTreeMap<String, (bool, TypeId)>,
    pub tail: BoundRowTail,
}
#[derive(Debug, Clone)]
pub enum BoundPathStep {
    Bound,
    Field(String),
    RowTail,
    TypeArgument(u32),
}
#[derive(Debug, Clone)]
pub struct BoundDeclarationPath {
    pub generic_index: u32,
    pub path: Vec<BoundPathStep>,
}

/// R is not a fake function generic parameter at T's source index.
#[derive(Debug, Clone)]
pub enum BoundRowRole {
    ImplicitResidual,
    /// A real explicitly declared Type parameter also used as a row.
    DeclaredTypeParameter {
        binder: String,
    },
}
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone, Default)]
pub struct BoundScope {
    /// Entries point to real GenericBinder records and their genuine indices.
    pub types: BTreeMap<String, String>,
    /// Separate typed namespace/capture for row residuals.
    pub rows: BTreeMap<String, BoundRowId>,
}
#[derive(Debug, Clone)]
pub struct RecordBoundField {
    pub label: String,
    pub mutable: bool,
    pub ty: TypeId,
    pub syntax: ContractSyntax,
    pub key: RecordBoundKey,
}
#[derive(Debug, Clone)]
pub enum DeclaredBoundTail {
    Closed,
    Row(BoundRowId),
    /// An already resolved concrete/named record tail, not an implicit binder.
    Concrete {
        syntax: ContractSyntax,
        key: RecordBoundKey,
    },
}
#[derive(Debug, Clone)]
pub struct GenericRecordBound {
    pub id: GenericBoundId,
    pub definition: DefinitionId,
    pub binder: String,
    pub generic_index: u32,
    pub syntax: ContractSyntax,
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
        syntax: ContractSyntax,
        scope: BoundScope,
    },
}
#[derive(Debug, Clone)]
pub struct StructuralSchema {
    pub source: StructuralSchemaSource,
    pub fields: Vec<RecordBoundField>,
    pub tail: BoundRowTail,
}
#[derive(Debug, Clone)]
pub struct BoundRowSelection {
    pub row: BoundRowId,
    pub remainder: BoundRowShape,
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
    pub context: ResumptionContext,
    pub activation: u32,
    pub allocation_epoch: u64,
    pub argument_index: u32,
    pub selection_path: Vec<BoundTypeSelectionStep>,
    pub actual: CopyValueSnapshot,
    pub actual_schema: StructuralSchema,
    pub substitutions: BTreeMap<String, RecordBoundKey>,
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
    pub context: ResumptionContext,
    pub activation: u32,
    pub allocation_epoch: u64,
    pub source: CopyValueSnapshot,
    pub slot: Projection,
    pub output: CopyValueSnapshot,
    pub access: BoundAccess,
    pub cause: CauseId,
    pub span: Span,
}
