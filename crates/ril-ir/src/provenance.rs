//! Presentation-independent semantic evidence retained alongside executable IR.
//! Consumers may inspect facts, but constructing this graph grants no authority.
use ril_compiler_core::{
    diagnostic::{Cause, CauseId},
    ids::{
        CallableOwner, ClosureCheckId, ClosureDiscardId, ClosureInvocationId, ClosureObjectId,
        ClosureSiteId, DefinitionId, HandlerSiteId, OriginId, TypeId,
    },
    source::Span,
};
mod channel_messages;
pub use channel_messages::*;
mod call_arguments;
pub use call_arguments::*;
mod generated_sources;
pub use generated_sources::*;
mod storage_sources;
pub use storage_sources::*;
mod record_bounds;
pub use record_bounds::*;
mod bound_writes;
mod scoped_source_identity;
pub use bound_writes::*;
pub use ril_compiler_core::ids::OptionalTagId;
pub use scoped_source_identity::*;

#[derive(Debug, Clone, Default)]
pub struct Graph {
    /// Static HIR identities indexed exactly like `values`. Dynamic invocation
    /// identity remains in `invocation_expressions` and call records.
    pub expression_sources: Vec<Option<ril_compiler_core::ids::ExprId>>,
    pub call_arguments: Vec<CallArguments>,
    pub invocation_expressions: Vec<InvocationExpression>,
    pub builtin_source_observations: Vec<BuiltinSourceObservation>,
    pub generated_sources: Vec<GeneratedSource>,
    pub binding_sources: Vec<BindingSource>,
    pub storage_writes: Vec<StorageWrite>,
    pub default_uses: Vec<DefaultUse>,
    pub optional_tags: Vec<OptionalTagFact>,
    pub channel_repetitions: Vec<ChannelRepetition>,
    pub target_layout: Option<ril_compiler_core::target::TargetLayout>,
    pub record_bounds: Vec<GenericRecordBound>,
    pub bound_rows: Vec<BoundRowDeclaration>,
    pub generic_bound_checks: Vec<GenericBoundCheck>,
    pub generic_bound_projections: Vec<GenericBoundProjection>,
    pub scoped_source_identities: Vec<ScopedSourceIdentity>,
    pub observed_accesses: Vec<ObservedAccess>,
    pub bound_field_writes: Vec<BoundFieldWrite>,
    pub channel_messages: Vec<ChannelMessageFact>,
    pub channel_exits: Vec<ChannelExitFact>,
    pub channel_message_sequence: u64,
    pub invocation_loan_starts: Vec<InvocationLoanStart>,
    pub invocation_loan_ends: Vec<InvocationLoanEnd>,
    pub closure_invocations: Vec<ClosureInvocation>,
    pub closure_exclusivity_checks: Vec<ClosureExclusivityCheck>,
    pub closure_exposures: Vec<ClosureExposure>,
    pub closure_discards: Vec<ClosureDiscard>,
    pub closure_exclusivity_certificate: Option<ClosureExclusivityCertificate>,
    pub numeric_selections: Vec<NumericSelection>,
    pub condition_evaluations: Vec<ConditionEvaluation>,
    pub specializations: Vec<crate::specialization::Instance>,
    pub constant_values: Vec<(ril_compiler_core::ids::ConstRef, Value)>,
    pub copy_invocations: Vec<CopyInvocation>,
    pub copy_references: Vec<CopyReference>,
    pub copy_call_events: Vec<CopyCallEvent>,
    pub resource_clones: Vec<ResourceCloneEvent>,
    pub copy_template_closure: Option<CopyTemplateClosure>,
    pub copy_boundaries: Vec<CopyBoundary>,
    pub types: Vec<Type>,
    pub contextual_types: Vec<(Span, TypeId)>,
    pub generic_binders: Vec<GenericBinder>,
    pub static_definitions: Vec<StaticDefinition>,
    pub result_duties: Vec<ResultDuty>,
    pub operations: Vec<Operation>,
    pub handlers: Vec<Handler>,
    pub retained_handlers: Vec<RetainedHandler>,
    pub closure_sites: Vec<ClosureSite>,
    pub nonretaining_adapters: Vec<NonRetainingAdapter>,
    pub retained_handler_answers: Vec<RetainedHandlerAnswer>,
    pub operation_loan_ends: Vec<(u32, CauseId)>,
    pub operation_loan_starts: Vec<OperationLoanStart>,
    pub allocation_history: Vec<(OriginId, OriginId)>,
    pub implicit_unwraps: Vec<ImplicitUnwrap>,
    pub variant_projections: Vec<VariantProjection>,
    pub constructors: Vec<Constructor>,
    pub origins: Vec<Origin>,
    pub values: Vec<Value>,
    pub fields: Vec<Field>,
    pub uncertain_slots: Vec<(OriginId, Projection)>,
    pub array_lengths: Vec<(OriginId, Option<u64>)>,
    pub fixed_arrays: Vec<OriginId>,
    pub bindings: Vec<Binding>,
    pub callables: Vec<Environment>,
    pub conditions: Vec<Decision>,
    pub relations: Vec<Relation>,
    pub invocations: Vec<Invocation>,
    pub termination: Vec<Termination>,
    pub static_termination: Vec<Termination>,
    pub loan_parents: Vec<(u32, Vec<Participant>)>,
    pub scope_parents: Vec<(u32, u32)>,
    pub concurrent_boundaries: Vec<ConcurrentBoundary>,
    pub parallel_boundaries: Vec<ParallelBoundary>,
    pub storage_types: Vec<(OriginId, TypeId)>,
    pub static_key_checks: Vec<StaticKeyCheck>,
    pub static_key_parameters: Vec<StaticKeyParameter>,
    pub result_families: Vec<(u32, Vec<u32>)>,
    pub inference_resolutions: Vec<InferenceResolution>,
    pub budget_proofs: Vec<BudgetProof>,
    pub budget_termination: Vec<BudgetTermination>,
    pub iter_steps: Vec<IterStep>,
    pub callable_return_contracts: Vec<CallableReturnBound>,
    pub windows: Vec<Window>,
    pub cleanup_events: Vec<CleanupEvent>,
    pub definition_checks: Vec<DefinitionCheck>,
    pub resumption_steps: Vec<ResumptionStep>,
    pub causes: Vec<Cause>,
}
#[derive(Debug, Clone)]
pub struct InvocationLoanStart {
    pub loan: u32,
    pub activation: u32,
    pub owner: Option<CallableOwner>,
    pub named: Option<CopyInstanceId>,
    pub closure: Option<ClosureInvocationId>,
    pub parameter: u32,
    pub retained: bool,
    pub source: Value,
    pub bindings: Vec<u32>,
    pub allocation_epoch: u64,
    pub cause: CauseId,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct InvocationLoanEnd {
    pub activation: u32,
    pub owner: Option<CallableOwner>,
    pub named: Option<CopyInstanceId>,
    pub closure: Option<ClosureInvocationId>,
    pub loans: Vec<(u32, Vec<Participant>)>,
    pub cause: CauseId,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct ClosureInvocation {
    pub id: ClosureInvocationId,
    pub source_event: Option<CopyCallEventId>,
    pub caller_activation: u32,
    pub activation: Option<u32>,
    pub closure: ClosureObjectId,
    pub parent_named: Option<CopyInstanceId>,
    pub parent_closure: Option<ClosureInvocationId>,
    pub caller_owner: Option<CallableOwner>,
    pub site: Span,
    pub probe: bool,
    pub budget_validation: bool,
    pub status: CopyInvocationStatus,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClosureConflict {
    ReadWrite,
    WriteWrite,
}
#[derive(Debug, Clone)]
pub struct ClosureRequirement {
    pub left: u32,
    pub right: u32,
    pub conflict: ClosureConflict,
}
#[derive(Debug, Clone)]
pub enum ClosureResolution {
    Proved,
    Pending,
    Discharged {
        calls: Vec<ClosureInvocationId>,
        discards: Vec<ClosureDiscardId>,
    },
    Rejected,
    Unsupported,
}
#[derive(Debug, Clone)]
pub struct ClosureExclusivityCheck {
    pub id: ClosureCheckId,
    pub closure: ClosureObjectId,
    pub site: Option<ClosureSiteId>,
    pub invocation: ClosureInvocationId,
    pub creation_named: Option<CopyInstanceId>,
    pub creation_closure: Option<ClosureInvocationId>,
    pub creation_default: Option<crate::specialization::DefaultUseId>,
    pub probe: bool,
    pub body_complete: bool,
    pub span: Span,
    pub allocation_epoch: u64,
    pub accesses: Vec<ConditionalAccess>,
    /// Origin observations and queried relations frozen at this check.
    pub nodes: Vec<Origin>,
    pub relations: Vec<Relation>,
    pub requirements: Vec<ClosureRequirement>,
    pub resolution: ClosureResolution,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClosureExposureKind {
    Returned,
    Stored,
}
#[derive(Debug, Clone)]
pub struct ClosureExposure {
    pub closure: ClosureObjectId,
    pub kind: ClosureExposureKind,
    pub owner: Option<CallableOwner>,
    pub named: Option<CopyInstanceId>,
    pub invocation: Option<ClosureInvocationId>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct ClosureExclusivityCertificate {
    pub objects: Vec<(ClosureObjectId, Vec<ClosureInvocationId>)>,
    pub templates: Vec<(ClosureObjectId, Vec<ClosureObjectId>)>,
    pub discarded: Vec<(ClosureObjectId, ClosureDiscardId)>,
}
#[derive(Debug, Clone)]
pub struct ClosureDiscard {
    pub id: ClosureDiscardId,
    pub closure: ClosureObjectId,
    pub created_start: ClosureObjectId,
    pub created_end: ClosureObjectId,
    pub named_start: CopyInstanceId,
    pub named_end: CopyInstanceId,
    pub owner: Option<CallableOwner>,
    pub named: Option<CopyInstanceId>,
    pub invocation: Option<ClosureInvocationId>,
    pub span: Span,
    pub allocation_epoch: u64,
    pub value: CopyValueSnapshot,
}
#[derive(Debug, Clone)]
pub struct RetainedHandler {
    pub callable: Option<CallableOwner>,
    pub span: Span,
    pub handlers: Vec<u32>,
    pub definitions: Option<Vec<HandlerSiteId>>,
    pub answer: TypeId,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct ClosureSite {
    pub id: ClosureSiteId,
    pub owner: CallableOwner,
    pub span: Span,
}
/// A certified forwarding adapter selects no creation-site user handlers.
/// Its captured receiver retains all ordinary borrow/resource obligations.
#[derive(Debug, Clone)]
pub struct NonRetainingAdapter {
    pub owner: CallableOwner,
    pub span: Span,
    pub builtin: NonRetainingBuiltin,
    pub causes: Vec<CauseId>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonRetainingBuiltin {
    ConcurrentFork,
    ConcurrentJoin,
}
#[derive(Debug, Clone)]
pub struct RetainedHandlerAnswer {
    pub handler: u32,
    pub operation: u64,
    pub declaration: TypeId,
    pub invocation: TypeId,
    pub parametric: bool,
    pub transport: AnswerTransport,
    pub span: Span,
    pub cause: CauseId,
    pub activation: u32,
    pub resumption_steps: Vec<u32>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnswerTransport {
    CopyChecked,
    Identity,
    OrdinaryChecked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResumptionContext {
    pub invocation: Option<CopyInstanceId>,
    pub owner: Option<CallableOwner>,
    pub closure: Option<ClosureObjectId>,
    pub closure_invocation: Option<ClosureInvocationId>,
    pub budget_validation: bool,
    pub default_use: Option<crate::specialization::DefaultUseId>,
}

#[derive(Debug, Clone)]
pub struct OperationLoanStart {
    pub loan: u32,
    pub activation: u32,
    pub boundary: u32,
    pub handler: u32,
    pub operation: u64,
    pub parameter: u32,
    pub temporary: bool,
    pub context: ResumptionContext,
    pub source: CopyValueSnapshot,
    pub allocation_epoch: u64,
    pub span: Span,
    pub cause: CauseId,
}

#[derive(Debug, Clone)]
pub struct OperationReception {
    pub parameter: u32,
    pub mode: Access,
    pub loan: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct ScopeBindingObservation {
    pub binding: u32,
    pub value: Value,
    pub cell: Option<OriginId>,
    pub forwarded: Vec<u32>,
    pub alive: bool,
}

#[derive(Debug, Clone)]
pub struct ContinuationScopeExit {
    pub activation: u32,
    pub boundary: u32,
    pub epoch: u64,
    pub binding_frontier: u32,
    pub retired_bindings: Vec<u32>,
    pub protected_bindings: Vec<u32>,
    pub alive_bindings: Vec<u32>,
    pub bindings: Vec<ScopeBindingObservation>,
    pub nodes: Vec<CopyNode>,
    pub answer_before: CopyValueSnapshot,
    pub answer_received: CopyValueSnapshot,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcurrentBoundaryKind {
    Scope,
    Fork,
    Join,
    ChannelCreate,
    Send,
    Receive,
    Detach,
    Attach,
    Close,
    CloneSender,
}
#[derive(Debug, Clone)]
pub struct ConcurrentBoundary {
    pub span: Span,
    pub scope: OriginId,
    pub task: Option<OriginId>,
    pub kind: ConcurrentBoundaryKind,
    pub cause: CauseId,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParallelOperation {
    Map,
    MapBounded,
    Find,
    First,
    Any,
    Fold,
    Join,
    Join3,
    ForEach,
}
#[derive(Debug, Clone)]
pub struct ParallelBoundary {
    pub span: Span,
    pub operation: ParallelOperation,
    pub callbacks: Vec<ParallelCallbackProof>,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct ParallelCallbackProof {
    pub cause: CauseId,
    pub accesses: Vec<ConditionalAccess>,
    pub selected_handlers: Vec<u32>,
    pub termination: ComputationJudgment,
}
/// The full conditional footprint, including access paths and authority roots.
#[derive(Debug, Clone)]
pub struct ConditionalAccess {
    /// Analysis allocation-history indices, not executable time. Historical
    /// ownership describes this access only and grants no current heap authority.
    pub observed_allocation_epoch: u64,
    pub allocation_epoch: u64,
    pub origin_owners: Vec<(OriginId, AccessOwners)>,
    pub origins: Vec<OriginId>,
    pub choices: Vec<(u32, Vec<Vec<OriginId>>)>,
    pub slot: Option<Projection>,
    pub access: Access,
    pub participants: Vec<Participant>,
    pub cause: CauseId,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccessOwners {
    Known(Vec<u32>),
    Unknown,
}
#[derive(Debug, Clone)]
pub struct Handler {
    pub definition: Option<HandlerSiteId>,
    pub callable_owner: Option<CallableOwner>,
    pub id: u32,
    pub boundary: u32,
    pub span: Span,
    pub operations: Vec<u64>,
    pub arm_spans: Vec<Span>,
    pub lexical: Vec<(String, u32)>,
    pub answer: Option<TypeId>,
}
#[derive(Debug, Clone)]
pub struct ImplicitUnwrap {
    pub span: Span,
    pub cause: CauseId,
    pub depth: u32,
    pub tags: Vec<String>,
}
#[derive(Debug, Clone)]
pub struct VariantProjection {
    pub span: Span,
    pub tag: String,
    pub cause: CauseId,
    pub direct: bool,
}
#[derive(Debug, Clone)]
pub struct Constructor {
    pub name: String,
    /// Runtime tag is declaration identity; an instantiated registry key may differ.
    pub tag: String,
    pub owner: TypeId,
    pub payload: TypeId,
    pub nominal: bool,
    pub has_payload: bool,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Operation {
    pub identity: u64,
    pub name: String,
    pub effect: String,
    pub span: Span,
    pub parameters: Vec<(Access, TypeId)>,
    pub result: TypeId,
}
#[derive(Debug, Clone)]
pub enum StaticFamily {
    Meta,
    Type,
}
#[derive(Debug, Clone)]
pub struct StaticDefinition {
    pub name: String,
    pub span: Span,
    pub family: StaticFamily,
    pub parameters: Vec<Parameter>,
    pub generic_names: Vec<String>,
    pub result_annotation: Option<String>,
}
#[derive(Debug, Clone)]
pub struct ResultDuty {
    pub id: u32,
    pub creation_owner: u32,
    pub owner: u32,
    pub span: Span,
    pub cause: CauseId,
    pub inspected: bool,
    pub returned: bool,
    pub abnormal: bool,
    pub covered: bool,
}
#[derive(Debug, Clone)]
pub struct GenericBinder {
    pub identity: String,
    pub definition: ril_compiler_core::ids::DefinitionId,
    /// Diagnostic location only.
    pub owner: Span,
    pub index: u32,
    pub name: String,
    pub ty: TypeId,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Unknown,
    Never,
    Unit,
    Bool,
    Integer(String),
    Float(String),
    String,
    Bytes,
    Named(String),
    Applied {
        constructor: String,
        arguments: Vec<TypeArgument>,
    },
    Generic(String),
    StaticKey(String),
    Projection {
        base: TypeId,
        key: String,
    },
    Immutable(TypeId),
    Optional(TypeId),
    Result(TypeId, TypeId),
    Array(TypeId),
    Set(TypeId),
    Range(TypeId),
    Map(TypeId, TypeId),
    Tuple(Vec<TypeId>),
    Record(Vec<(String, bool, TypeId)>),
    OpenRecord {
        fields: Vec<(String, bool, TypeId)>,
        row: OpenTail,
    },
    Callable(Vec<TypeId>, TypeId),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeArgument {
    Type(TypeId),
    CanonicalType { ty: TypeId, key: String },
    Static(String),
    Symbolic(String),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RowIdentity {
    Binder(String),
    Fresh { owner: String, ordinal: u64 },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenTail {
    pub identity: RowIdentity,
    pub lacks: Vec<String>,
}
#[derive(Debug, Clone)]
pub enum OriginKind {
    Formal(u32),
    Global,
    Fresh(u32),
    Older(u32),
    Environment,
    Opaque,
}
#[derive(Debug, Clone)]
pub struct Origin {
    pub id: OriginId,
    pub kind: OriginKind,
    pub multiplicity: Multiplicity,
    pub owner: u32,
    pub edges: Vec<(Projection, Vec<OriginId>)>,
    pub writable_roots: Vec<u32>,
    pub escaping: bool,
    pub cause: CauseId,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Multiplicity {
    One,
    MayMany,
}
#[derive(Debug, Clone)]
pub enum Projection {
    Field(String),
    /// A symbolic record tail carries all unknown members without authorizing
    /// an arbitrary concrete field projection.
    RowTail(RowIdentity),
    Tuple(u32),
    Index(i64),
    AnyIndex,
    Capture(u32),
}
#[derive(Debug, Clone, Copy)]
pub enum Permission {
    Read,
    Write,
}
#[derive(Debug, Clone, Copy)]
pub enum Publication {
    Immutable,
    Live,
    Unpublished,
}
#[derive(Debug, Clone, Copy)]
pub enum Participant {
    Loan(u32),
    Root(u32),
}
#[derive(Debug, Clone)]
pub enum Callable {
    Constructor(String),
    Named(DefinitionId),
    Closure(u32),
    Symbolic(u32, Vec<String>),
    Builtin(String),
}
#[derive(Debug, Clone)]
pub enum Constant {
    Integer(i128),
    Bool(bool),
    Unit,
}
#[derive(Debug, Clone, Default)]
pub struct NumericDependencies {
    pub uses: Vec<ril_compiler_core::ids::NumericUseId>,
    pub selections: Vec<ril_compiler_core::ids::NumericSelectionId>,
}
#[derive(Debug, Clone)]
pub enum NumericEncoding {
    Integer { value: i128, bits: u8, signed: bool },
    BigInteger(String),
    Float { bits: u8, payload: u64 },
}
#[derive(Debug, Clone)]
pub struct NumericSelection {
    pub id: ril_compiler_core::ids::NumericSelectionId,
    pub literal: ril_compiler_core::ids::NumericUseId,
    pub span: Span,
    pub invocation: Option<CopyInstanceId>,
    pub owner: Option<CallableOwner>,
    pub closure: Option<u32>,
    pub closure_invocation: Option<u32>,
    pub default_use: Option<u32>,
    pub budget_validation: bool,
    pub ty: TypeId,
    pub layout: ril_compiler_core::target::TargetLayout,
    pub encoded: NumericEncoding,
    pub cause: CauseId,
}

#[derive(Debug, Clone)]
pub struct SourceTypeWitness {
    /// Canonical source identity, independent of its runtime representation.
    pub key: String,
    pub shape: crate::specialization::ArgumentKey,
}

#[derive(Debug, Clone)]
pub struct OptionalTagFact {
    pub id: OptionalTagId,
    pub creation_owner: u32,
    pub cause: CauseId,
    pub payload_type: TypeId,
}

#[derive(Debug, Clone)]
pub struct Value {
    /// Identity metadata only; this never grants storage or path authority.
    pub source_type_witness: Option<std::sync::Arc<SourceTypeWitness>>,
    pub numeric: NumericDependencies,
    pub condition_inspections: ConditionInspections,
    pub pending_copies: Vec<CopyBoundaryId>,
    pub span: Span,
    pub ty: TypeId,
    pub origins: Vec<OriginId>,
    pub choices: Vec<(u32, Vec<Vec<OriginId>>)>,
    pub permission: Permission,
    pub publication: Publication,
    pub participants: Vec<Participant>,
    pub sources: Vec<u32>,
    pub callback_parameters: Vec<u32>,
    pub results: Vec<u32>,
    pub outer_results: Vec<u32>,
    pub must_results: Vec<u32>,
    pub must_outer_results: Vec<u32>,
    pub scoped_bindings: Vec<u32>,
    pub result_payload: Option<Box<Value>>,
    pub result_success: Option<Box<Value>>,
    pub result_error: Option<Box<Value>>,
    pub result_tag: Option<bool>,
    pub option_payload: Option<Box<Value>>,
    pub option_tag: Option<bool>,
    pub option_identity: Option<OptionalTagId>,
    pub variant_tag: Option<String>,
    pub variant_payload: Option<Box<Value>>,
    pub variant_witnesses: std::collections::BTreeMap<String, Box<Value>>,
    pub abnormal: bool,
    pub callables: Vec<Callable>,
    pub callable_bounds: Vec<CallableBound>,
    pub callable_returns: Vec<ReturnContractId>,
    pub signature: Option<Vec<Parameter>>,
    pub constant: Option<Constant>,
    pub static_coordinate: Option<StaticCoordinate>,
    pub pending_inference: Vec<String>,
    pub flags: ValueFlags,
    pub cause: CauseId,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConditionEvaluationId(pub u32);
#[derive(Debug, Clone, Default)]
pub struct ConditionInspections {
    pub channel_when_true: ChannelGuard,
    pub channel_when_false: ChannelGuard,
    pub when_true: Vec<u32>,
    pub when_false: Vec<u32>,
    pub versions: Vec<(u32, u32)>,
    pub evaluations: Vec<ConditionEvaluationId>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionKind {
    Plain,
    Pattern,
    Negation,
    Conjunction,
    Disjunction,
}
#[derive(Debug, Clone)]
pub struct ConditionEvaluation {
    pub id: ConditionEvaluationId,
    pub invocation: Option<CopyInstanceId>,
    pub owner: Option<CallableOwner>,
    pub closure: Option<u32>,
    pub closure_invocation: Option<u32>,
    pub default_use: Option<u32>,
    pub budget_validation: bool,
    pub span: Span,
    pub cause: CauseId,
    pub kind: ConditionKind,
    pub constant: Option<bool>,
    pub inspections: ConditionInspections,
}
#[derive(Debug, Clone, Default)]
pub struct ValueFlags {
    pub stable: bool,
    pub marker: bool,
    pub retained_return: bool,
    pub through_return: bool,
    pub construction: bool,
    pub internal_aliases: bool,
    pub mutable_environment: bool,
    pub observer_environment: bool,
    pub unsuffixed_numeric: bool,
    pub temporary: bool,
    pub readonly_spread: bool,
    pub requires_inference: bool,
}
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: Option<String>,
    pub mode: Access,
    pub type_annotation: Option<String>,
    pub default: Option<Span>,
}
#[derive(Debug, Clone)]
pub struct CallableBound {
    pub annotations: Vec<Annotation>,
    pub lexical: Vec<(String, u32)>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct CallableReturnBound {
    pub raw: bool,
    pub predecessors: Vec<ReturnContractId>,
    pub target: TypeId,
    pub syntax: ContractSyntax,
    pub span: Span,
    pub callables: Vec<Callable>,
    pub lexical: Vec<(String, u32)>,
    pub generic_context: Vec<(String, String)>,
    pub generic_substitutions: Vec<(String, TypeId)>,
    pub generic_type_witnesses: Vec<(String, std::sync::Arc<SourceTypeWitness>)>,
    pub bound_row_context: Vec<(String, BoundRowId)>,
    pub bound_row_selections: Vec<BoundRowSelection>,
    pub static_key_arguments: Vec<(String, StaticCoordinate)>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReturnContractId(pub u32);
/// Owned type-contract structure. Static expressions and binding patterns
/// reference the complete verified HIR; resolved types are stored separately.
#[derive(Debug, Clone)]
pub struct ContractSyntax {
    pub text: String,
    pub span: Span,
    pub kind: ContractKind,
}
#[derive(Debug, Clone)]
pub enum ContractKind {
    Name {
        path: Vec<String>,
        arguments: Vec<ContractSyntax>,
    },
    Optional(Box<ContractSyntax>),
    Array {
        length: Option<Span>,
        element: Box<ContractSyntax>,
    },
    Map {
        key: Box<ContractSyntax>,
        value: Box<ContractSyntax>,
    },
    Tuple(Vec<ContractSyntax>),
    Record {
        fields: Vec<ContractField>,
        row: Option<Box<ContractSyntax>>,
    },
    Callable {
        parameters: Vec<ContractParameter>,
        result: Option<Box<ContractSyntax>>,
        annotations: Vec<Annotation>,
    },
    TypeFunction {
        parameters: Vec<ContractGeneric>,
        body: Span,
    },
    Projection {
        base: Box<ContractSyntax>,
        field: String,
    },
    ComputedProjection {
        base: Box<ContractSyntax>,
        key: Span,
    },
    KeyOf(Box<ContractSyntax>),
    Computation(Span),
    Mapped {
        binder: String,
        keys: Span,
        value: Box<ContractSyntax>,
        tuple: bool,
    },
    Rest(Box<ContractSyntax>),
    KindArrow {
        parameter: Box<ContractSyntax>,
        result: Box<ContractSyntax>,
    },
    Error,
}
#[derive(Debug, Clone)]
pub struct ContractField {
    pub name: String,
    pub mutable: bool,
    pub ty: ContractSyntax,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct ContractParameter {
    pub pattern: Span,
    pub mode: Access,
    pub ty: Option<ContractSyntax>,
    pub default: Option<Span>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct ContractGeneric {
    pub name: String,
    pub bound: Option<ContractSyntax>,
    pub default: Option<ContractSyntax>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct Annotation {
    pub kind: AnnotationKind,
    pub text: String,
    pub span: Span,
}
#[derive(Debug, Clone, Copy)]
pub enum AnnotationKind {
    Effect,
    Capability,
}
#[derive(Debug, Clone)]
pub enum StaticCoordinate {
    Label(String),
    Index(i128),
}
#[derive(Debug, Clone)]
pub struct StaticKeyCheck {
    pub binder: String,
    pub argument: Span,
    pub receiver: TypeId,
    pub coordinate: StaticCoordinate,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct StaticKeyParameter {
    pub binder: String,
    pub owner: Span,
    pub parameter: u32,
    pub name: String,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct InferenceResolution {
    pub binder: String,
    pub selected: TypeId,
    pub site: Span,
    pub origin: CauseId,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct BudgetProof {
    pub span: Span,
    pub exhaustion_operation: u64,
    pub callee_coverage: Vec<CauseId>,
    pub cleanup_coverage: Vec<CauseId>,
    pub cause: CauseId,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputationJudgment {
    pub may_diverge: bool,
    pub unresolved: bool,
    pub callable_parameters: Vec<u32>,
}
#[derive(Debug, Clone)]
pub struct BudgetTermination {
    pub span: Span,
    pub cause: CauseId,
    pub exhaustion_operation: u64,
    pub callee_coverage: Vec<CauseId>,
    pub cleanup_coverage: Vec<CauseId>,
    pub explicit_evaluation: ComputationJudgment,
    pub action_invocation: ComputationJudgment,
    pub recovery: ComputationJudgment,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IterAdapterKind {
    Indexed,
    Map,
    Filter,
    Take,
}
#[derive(Debug, Clone)]
pub struct IterStep {
    pub identity: String,
    pub closure: u32,
    pub kind: IterAdapterKind,
    pub state: TypeId,
    pub item: TypeId,
    pub span: Span,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct Window {
    pub origin: OriginId,
    pub backing: Vec<OriginId>,
    pub choices: Vec<(u32, Vec<Vec<OriginId>>)>,
    pub lower: Option<u64>,
    pub length: Option<u64>,
    pub span: Span,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct CleanupEvent {
    pub binding: u32,
    pub owner: u32,
    pub span: Span,
    pub resumed_boundary: Option<u32>,
    pub cause: CauseId,
}
#[derive(Debug, Clone)]
pub struct DefinitionCheck {
    pub function: u32,
    pub span: Span,
    pub returned: TypeId,
    pub declared: TypeId,
    pub invocation: Option<u32>,
}
#[derive(Debug, Clone)]
pub struct ResumptionStep {
    pub span: Span,
    pub owner: u32,
    pub handler: u32,
    pub operation: u64,
    pub body_answer: TypeId,
    pub arm_answer: TypeId,
    pub continuation: CauseId,
    pub cause: CauseId,
    pub boundary: u32,
    pub context: ResumptionContext,
    pub continuation_value: CopyValueSnapshot,
    pub arm_value: CopyValueSnapshot,
    pub continuation_epoch: u64,
    pub completion_epoch: u64,
    pub ended_operation_loans: Vec<u32>,
    pub operation_receptions: Vec<OperationReception>,
    pub continuation_expression: u32,
    pub arm_expression: u32,
    pub transport: AnswerTransport,
    pub scope_exit: Option<ContinuationScopeExit>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Access {
    Read,
    Write,
    Retain,
}
#[derive(Debug, Clone)]
pub struct Field {
    pub origin: OriginId,
    pub projection: Projection,
    pub value: Value,
}
#[derive(Debug, Clone)]
pub struct Binding {
    pub id: u32,
    pub name: String,
    pub root: u32,
    pub cell: Option<OriginId>,
    pub owner: u32,
    pub lexical_scope: u32,
    pub reassignable: bool,
    pub writable: bool,
    pub alive: bool,
    pub slot_used: bool,
    pub write_used: bool,
    pub used: bool,
    pub forwarded: Vec<u32>,
    pub parameter: bool,
    pub value: Value,
}
#[derive(Debug, Clone)]
pub struct Environment {
    pub callable: Callable,
    pub span: Span,
    pub owner: Option<u32>,
    pub lexical_scope: Option<u32>,
    pub published: bool,
    pub origin: Option<OriginId>,
    pub lexical: Vec<(String, u32)>,
    pub captures: Vec<u32>,
    pub writes: Vec<u32>,
    pub handler_context: Vec<u32>,
}
#[derive(Debug, Clone, Copy)]
pub enum Atom {
    Equal(u32, u32),
    Disjoint(u32, u32),
}
#[derive(Debug, Clone)]
pub struct Decision {
    pub id: u32,
    pub atom: Atom,
    pub low: u32,
    pub high: u32,
}
#[derive(Debug, Clone)]
pub struct Relation {
    pub left: OriginId,
    pub right: OriginId,
    pub equal: u32,
    pub disjoint: u32,
}
#[derive(Debug, Clone)]
pub struct Invocation {
    pub activation: Option<u32>,
    pub context: Option<ResumptionContext>,
    pub channel_messages: Vec<ChannelMessageId>,
    pub copy_boundaries: Vec<CopyBoundaryId>,
    pub selected_handlers: Vec<u32>,
    pub handler_environment: bool,
    pub accesses: Vec<(OriginId, Participant, Access)>,
    pub concrete_state: Vec<(u32, Access)>,
    pub effects: Vec<String>,
    pub performed_operations: Vec<u64>,
    pub callbacks: Vec<(u32, Vec<String>)>,
    pub escaped_origins: Vec<OriginId>,
    pub retained_origins: Vec<OriginId>,
    pub new_environments: Vec<OriginId>,
    pub owners: Vec<u32>,
    pub unresolved: Vec<u32>,
}
#[derive(Debug, Clone)]
pub struct Termination {
    pub function: String,
    pub may_diverge: bool,
    pub unresolved: bool,
    pub callable_parameters: Vec<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CopyBoundaryId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyMode {
    Mutable,
    Immutable,
}
#[derive(Debug, Clone)]
pub enum CopyProjection {
    Storage(Projection),
    OptionPayload,
    ResultSuccess,
    ResultError,
    Variant(String),
}
#[derive(Debug, Clone)]
pub enum CopyQualification {
    Ordinary,
    EnvironmentFreeCallable,
    DeferredData(String),
    DeferredRow(RowIdentity),
    DeferredCallableEnvironment,
    Resource,
    RetainedEnvironment,
    Incomplete,
}
#[derive(Debug, Clone)]
pub struct CopyConstituent {
    pub parent: Option<OriginId>,
    pub path: Vec<CopyProjection>,
    pub source: Option<Value>,
    pub ty: TypeId,
    pub cause: CauseId,
    pub qualification: CopyQualification,
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
    pub constituent: u32,
    pub kind: CopyRequirementKind,
}
#[derive(Debug, Clone)]
pub struct CopyNode {
    /// Snapshot at this boundary; later recency updates cannot alter it.
    pub origin: Origin,
    pub fields: Vec<(Projection, Value)>,
    pub length: Option<Option<u64>>,
    pub fixed: bool,
}
#[derive(Debug, Clone)]
pub struct CopyBoundary {
    pub id: CopyBoundaryId,
    pub owner: Option<DefinitionId>,
    pub activation: u32,
    pub span: Span,
    pub mode: CopyMode,
    pub cause: CauseId,
    pub source: Value,
    pub nodes: Vec<CopyNode>,
    pub relations: Vec<Relation>,
    pub constituents: Vec<CopyConstituent>,
    pub requirements: Vec<CopyRequirement>,
    /// None is an unverified transfer, never an implicit fresh allocation.
    pub output: Option<Value>,
    pub output_nodes: Vec<CopyNode>,
    pub output_relations: Vec<Relation>,
    pub invocation: Option<CopyInstanceId>,
    pub source_event: Option<CopyCallEventId>,
    pub template: bool,
    pub template_root: Option<CopyInstanceId>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CopyInstanceId(pub u32);
#[derive(Debug, Clone)]
pub struct CopyValueSnapshot {
    pub value: Value,
    pub nodes: Vec<CopyNode>,
    pub relations: Vec<Relation>,
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
#[derive(Debug, Clone)]
pub struct CopyReference {
    pub id: CopyReferenceId,
    pub expression: usize,
    pub owner: Option<CallableOwner>,
    pub parent: Option<CopyInstanceId>,
    pub target: DefinitionId,
    pub span: Span,
    pub direct_call: Option<CopyCallEventId>,
}
#[derive(Debug, Clone)]
pub struct CopyCallEvent {
    pub id: CopyCallEventId,
    pub source_id: Option<ril_compiler_core::ids::ExprId>,
    pub callee_expression: Option<usize>,
    pub result_expression: Option<usize>,
    pub owner: Option<CallableOwner>,
    pub parent: Option<CopyInstanceId>,
    pub span: Span,
    pub target: Option<DefinitionId>,
    pub direct: bool,
    pub copy_operation: Option<CopyMode>,
    pub references: Vec<CopyReferenceId>,
}
#[derive(Debug, Clone)]
pub struct CopyInvocation {
    pub id: CopyInstanceId,
    pub parent: Option<CopyInstanceId>,
    pub caller: Option<DefinitionId>,
    pub caller_owner: Option<CallableOwner>,
    pub caller_activation: Option<u32>,
    pub entry_allocation_epoch: u64,
    pub target: DefinitionId,
    pub span: Span,
    pub declaration_probe: bool,
    pub direct: bool,
    pub source_event: Option<CopyCallEventId>,
    pub arguments: Vec<(Access, CopyValueSnapshot)>,
    pub boundaries: Vec<CopyBoundaryId>,
    pub result: Option<CopyValueSnapshot>,
    pub resource_copies: Vec<ResourceCloneId>,
    pub status: CopyInvocationStatus,
}
#[derive(Debug, Clone)]
pub struct CopyCallSite {
    pub owner: Option<DefinitionId>,
    pub target: DefinitionId,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct CopyTemplate {
    pub owner: DefinitionId,
    pub public: bool,
    pub escaped: bool,
    pub sites: Vec<CopyCallSite>,
    pub dependencies: Vec<DefinitionId>,
}
#[derive(Debug, Clone)]
pub struct CopyTemplateClosure {
    pub templates: Vec<CopyTemplate>,
    pub instances: Vec<(DefinitionId, Vec<CopyInstanceId>)>,
    pub dependency_order: Vec<DefinitionId>,
    pub discharges: Vec<(CopyInstanceId, CopyBoundaryId, CopyDischarge)>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyDischarge {
    Ordinary(CopyBoundaryId),
    Sender(ResourceCloneId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResourceCloneId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceCloneContract {
    Sender,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceCloneEffect {
    Fiber,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceChannel {
    Known(OriginId),
    FromSourceDescriptor(OriginId),
}
#[derive(Debug, Clone)]
pub struct ResourceDescriptor {
    pub origin: OriginId,
    pub scope: OriginId,
    pub task: Option<OriginId>,
    pub channel: Option<OriginId>,
    pub formal: bool,
}
#[derive(Debug, Clone)]
pub struct ResourceCloneEvent {
    pub id: ResourceCloneId,
    pub owner: Option<DefinitionId>,
    pub lexical_owner: Option<CallableOwner>,
    pub invocation: Option<CopyInstanceId>,
    pub source_event: Option<CopyCallEventId>,
    pub span: Span,
    pub contract: ResourceCloneContract,
    pub required_effect: ResourceCloneEffect,
    pub effect_registered: bool,
    pub source: CopyValueSnapshot,
    pub source_descriptor: Option<ResourceDescriptor>,
    pub output: CopyValueSnapshot,
    pub output_descriptor: Option<ResourceDescriptor>,
    pub channel: Option<ResourceChannel>,
    pub boundary: Option<ConcurrentBoundary>,
    pub anchors: Vec<CopyNode>,
}
