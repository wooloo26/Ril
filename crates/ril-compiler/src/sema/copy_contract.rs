//! Frozen evidence for a particular copy use. These records describe proofs;
//! neither allocation freshness nor an output template discharges a condition.
use super::{
    copy_eligibility::Constituent,
    facts::*,
    model::{Ty, Value},
    relations::Relation,
};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{CallableOwner, DefinitionId},
    source::Span,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CopyBoundaryId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyMode {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CopyProjection {
    Storage(Slot),
    OptionPayload,
    ResultSuccess,
    ResultError,
    Variant(String),
}

#[derive(Debug, Clone)]
pub struct CopyConstituent {
    /// None denotes the boundary's root value, not an invented heap object.
    pub parent: Option<NodeId>,
    pub path: Vec<CopyProjection>,
    /// None is a type-only potential member, without observed permissions or origins.
    pub source: Option<Value>,
    pub ty: Ty,
    pub cause: CauseId,
    pub qualification: Constituent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyRequirementKind {
    DeferredTransfer,
    PriorBoundary(CopyBoundaryId),
    Eligibility,
    WindowGraph,
    ResultMembership,
    Transfer,
}

#[derive(Debug, Clone)]
pub struct CopyRequirement {
    /// Index in this boundary's frozen constituent table.
    pub constituent: u32,
    pub kind: CopyRequirementKind,
}

#[derive(Debug, Clone)]
pub struct CopyNode {
    pub origin: NodeId,
    pub fact: HeapNode,
    pub fields: Vec<(Slot, Value)>,
    pub length: Option<Option<u64>>,
    pub fixed: bool,
}

#[derive(Debug, Clone)]
pub struct CopyBoundary {
    pub id: CopyBoundaryId,
    pub input_allocation_epoch: usize,
    pub output_allocation_epoch: Option<usize>,
    pub owner: Option<DefinitionId>,
    pub activation: ScopeId,
    pub span: Span,
    pub mode: CopyMode,
    pub cause: CauseId,
    pub source: Value,
    pub nodes: Vec<CopyNode>,
    pub relations: Vec<(NodeId, NodeId, Relation)>,
    pub constituents: Vec<CopyConstituent>,
    pub requirements: Vec<CopyRequirement>,
    /// Present only when both eligibility and graph transfer were established.
    pub output: Option<Value>,
    /// The output graph is frozen too: later mutation or recency must not
    /// reinterpret an earlier copy template through the final global heap.
    pub output_nodes: Vec<CopyNode>,
    pub output_relations: Vec<(NodeId, NodeId, Relation)>,
    pub invocation: Option<super::copy_templates::InstanceId>,
    pub source_event: Option<CopyCallEventId>,
    /// Conditional declaration evidence; its requirements remain unproved.
    pub template: bool,
    pub template_root: Option<super::copy_templates::InstanceId>,
}

#[derive(Debug, Clone)]
pub struct CopyValueSnapshot {
    pub value: Value,
    pub nodes: Vec<CopyNode>,
    pub relations: Vec<(NodeId, NodeId, Relation)>,
}

/// Heap evidence accompanies the shared packet and cannot supply another root.
#[derive(Debug, Clone)]
pub struct CopyHeapSnapshot {
    pub allocation_epoch: usize,
    pub nodes: Vec<CopyNode>,
    pub relations: Vec<(NodeId, NodeId, Relation)>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CopyValueView<'a> {
    pub(crate) value: &'a Value,
    pub(crate) nodes: &'a [CopyNode],
    pub(crate) relations: &'a [(NodeId, NodeId, Relation)],
}

impl CopyValueSnapshot {
    pub(crate) fn as_view(&self) -> CopyValueView<'_> {
        CopyValueView {
            value: &self.value,
            nodes: &self.nodes,
            relations: &self.relations,
        }
    }
}

impl<'a> From<&'a CopyValueSnapshot> for CopyValueView<'a> {
    fn from(snapshot: &'a CopyValueSnapshot) -> Self {
        snapshot.as_view()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyInvocationStatus {
    Incomplete,
    Completed,
    Rejected,
    Unsupported,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CopyReferenceId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CopyCallEventId(pub u32);
/// One evaluated expression occurrence, including repeated default expressions.
#[derive(Debug, Clone)]
pub struct CopyReference {
    pub id: CopyReferenceId,
    pub expression: usize,
    pub owner: Option<CallableOwner>,
    pub parent: Option<super::copy_templates::InstanceId>,
    pub target: DefinitionId,
    pub span: Span,
    pub direct_call: Option<CopyCallEventId>,
}
#[derive(Debug, Clone)]
pub struct CopyCallEvent {
    pub id: CopyCallEventId,
    pub source_id: Option<ril_compiler_core::ids::ExprId>,
    pub callee_expression: Option<usize>,
    /// The actual root emission, including a Never result. This is an
    /// observation edge, not proof that arguments or a body completed.
    pub result_expression: Option<usize>,
    pub owner: Option<CallableOwner>,
    /// Dynamic named invocation; lexical owner may instead be a handler arm.
    pub parent: Option<super::copy_templates::InstanceId>,
    pub span: Span,
    pub target: Option<DefinitionId>,
    pub direct: bool,
    pub copy_operation: Option<CopyMode>,
    pub references: Vec<CopyReferenceId>,
}
impl CopyCallEvent {
    /// Lexical identity comes from the actual labeled syntax occurrence.
    /// A missing identity never matches another missing identity.
    pub(crate) fn matches_source(&self, expression: &ril_syntax::ast::Expr) -> bool {
        self.source_id.is_some() && self.source_id == expression.hir_id
    }
}
#[derive(Debug, Clone)]
pub struct CopyInvocation {
    pub id: super::copy_templates::InstanceId,
    pub summary: Option<ril_compiler_core::ids::InvocationSummaryId>,
    pub entry: super::application_effect::CallableEntry,
    pub parent: Option<super::copy_templates::InstanceId>,
    pub caller: Option<DefinitionId>,
    pub caller_owner: Option<CallableOwner>,
    pub caller_activation: Option<super::facts::ScopeId>,
    pub target: DefinitionId,
    pub span: Span,
    pub declaration_probe: bool,
    pub direct: bool,
    pub source_event: Option<CopyCallEventId>,
    pub boundaries: std::collections::BTreeSet<CopyBoundaryId>,
    pub result: Option<CopyValueSnapshot>,
    pub resource_copies: Vec<super::resource_copy::ResourceCloneId>,
    pub status: CopyInvocationStatus,
}
#[derive(Debug, Clone)]
pub struct CopyTemplateClosure {
    pub templates: std::collections::BTreeMap<DefinitionId, super::copy_templates::Template>,
    pub certificate: super::copy_templates::Certificate,
    pub discharges: std::collections::BTreeMap<
        (super::copy_templates::InstanceId, CopyBoundaryId),
        super::resource_copy::CopyDischarge,
    >,
}
