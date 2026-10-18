//! Semantic checking entry point. Individual phases are implemented here as needed.
use crate::hir::VerifiedProgram;
use ril_compiler_core::{
    diagnostic::Diagnostic,
    source::{FileId, Span},
};

pub mod bound_writes;
pub mod builtin_sources;
pub(crate) mod checker;
pub(crate) use checker::parallel_parameter_labels;
#[cfg(test)]
mod call_input_source_review_tests;
mod channel_message_validation;
pub mod channel_messages;
mod channel_production;
pub mod closure_exclusivity;
pub mod context;
pub mod copy_contract;
pub mod copy_eligibility;
pub mod copy_template_closure;
pub mod copy_templates;
pub mod default_uses;
pub mod effect_identity;
mod evaluation_identity;
pub mod facts;
pub mod generated_sources;
pub mod invocation_loans;
pub mod model;
pub mod numeric_selection;
pub mod optional_tags;
pub(crate) mod record_bound_shapes;
mod record_bound_validation;
pub mod record_bounds;
pub mod recursive;
pub mod relations;
pub mod resource_copy;
pub mod result_conditions;
pub mod resumption;
pub mod scoped_source_identity;
pub(crate) mod source_reception;
#[cfg(test)]
mod source_reception_review_tests;
mod source_type_validation;
pub mod source_types;
mod static_argument_validation;
pub mod storage_sources;
pub mod summary;
pub mod validate;
pub use checker::iter::{AdapterKind as IterAdapterKind, StepFact as IterStepFact};
#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Default)]
pub struct SemanticFacts {
    pub source_types: source_types::SourceTypeIndex,
    pub semantic_hir: Option<std::sync::Arc<crate::hir::HirProgram>>,
    /// The actual analyzed source tree supplies complete lexical declarations.
    /// A missing tree cannot establish a new Source-dependent proof.
    pub source_program: Option<std::sync::Arc<ril_syntax::ast::Program>>,
    pub optional_tags: Vec<optional_tags::OptionalTagFact>,
    pub channel_repetitions: Vec<channel_messages::ChannelRepetition>,
    pub target_layout: Option<ril_compiler_core::target::TargetLayout>,
    pub record_bounds: Vec<record_bounds::GenericRecordBound>,
    pub bound_rows: Vec<record_bounds::BoundRowDeclaration>,
    pub generic_bound_checks: Vec<record_bounds::GenericBoundCheck>,
    pub generic_bound_projections: Vec<record_bounds::GenericBoundProjection>,
    pub scoped_source_identities: Vec<scoped_source_identity::ScopedSourceIdentity>,
    pub observed_accesses: Vec<bound_writes::ObservedAccess>,
    pub bound_field_writes: Vec<bound_writes::BoundFieldWrite>,
    pub channel_messages: Vec<channel_messages::ChannelMessageFact>,
    pub channel_exits: Vec<channel_messages::ChannelExitFact>,
    pub channel_message_sequence: u64,
    pub invocation_loan_starts: Vec<invocation_loans::InvocationLoanStart>,
    pub invocation_loan_ends: Vec<invocation_loans::InvocationLoanEnd>,
    pub closure_exclusivity_checks: Vec<closure_exclusivity::ClosureExclusivityCheck>,
    pub closure_exclusivity_certificate: Option<closure_exclusivity::ClosureExclusivityCertificate>,
    pub closure_exposures: Vec<closure_exclusivity::ClosureExposure>,
    pub closure_discards: Vec<closure_exclusivity::ClosureDiscard>,
    /// Real allocation transitions produced by this analysis, in epoch order.
    pub allocation_history: Vec<(facts::NodeId, facts::NodeId)>,
    /// Scope identities allocated by the checker. The formal MAX sentinel is
    /// deliberately absent and must be admitted only by a formal fact's rule.
    pub allocated_scopes: std::collections::BTreeSet<facts::ScopeId>,
    pub numeric_uses: Vec<numeric_selection::NumericUse>,
    pub numeric_selections: Vec<numeric_selection::NumericSelection>,
    pub condition_evaluations: Vec<result_conditions::ConditionEvaluation>,
    pub effect_instances: Vec<effect_identity::EffectInstance>,
    pub effect_invocations: Vec<effect_identity::EffectInvocation>,
    pub invocation_expressions: Vec<effect_identity::InvocationExpression>,
    pub builtin_source_observations: Vec<builtin_sources::BuiltinSourceObservation>,
    pub generated_sources: Vec<generated_sources::GeneratedSource>,
    pub binding_sources: Vec<storage_sources::BindingSource>,
    pub storage_writes: Vec<storage_sources::StorageWrite>,
    pub invocation_calls: Vec<effect_identity::InvocationCall>,
    pub invocation_witnesses: Vec<effect_identity::InvocationWitness>,
    pub closure_invocations: Vec<effect_identity::ClosureInvocation>,
    pub default_uses: Vec<default_uses::DefaultUse>,
    pub call_arguments: Vec<default_uses::CallArguments>,
    pub(crate) constant_pool: crate::static_eval::constants::ConstantPool,
    pub constant_values: Vec<ConstantValue>,
    pub external_instances: Vec<ExternalInstance>,
    pub external_type_witnesses: Vec<ExternalTypeWitness>,
    pub external_type_declarations:
        std::collections::BTreeMap<String, ril_syntax::ast::TypeDeclaration>,
    /// Checked transparent type expansions needed by external exchange schemas.
    pub external_type_expansions: Vec<(model::Ty, model::Ty)>,
    pub external_resource_types: Vec<model::Ty>,
    pub copy_boundaries: Vec<copy_contract::CopyBoundary>,
    pub copy_invocations: Vec<copy_contract::CopyInvocation>,
    pub copy_references: Vec<copy_contract::CopyReference>,
    pub copy_call_events: Vec<copy_contract::CopyCallEvent>,
    pub resource_clones: Vec<resource_copy::ResourceCloneEvent>,
    pub copy_template_closure: Option<copy_contract::CopyTemplateClosure>,
    pub parallel_boundaries: Vec<ParallelBoundary>,
    pub concurrent_boundaries: Vec<ConcurrentBoundary>,
    pub iter_steps: Vec<IterStepFact>,
    pub windows: std::collections::BTreeMap<facts::NodeId, WindowInfo>,
    pub budget_proofs: Vec<BudgetProof>,
    pub budget_termination: Vec<crate::termination::BudgetTerminationWitness>,
    pub inference_resolutions: Vec<InferenceResolution>,
    pub static_key_parameters: Vec<StaticKeyParameter>,
    pub resumption_steps: Vec<ResumptionStep>,
    pub definition_checks: Vec<DefinitionCheck>,
    pub cleanup_events: Vec<CleanupEvent>,
    pub static_key_checks: Vec<StaticKeyCheck>,
    pub storage_types: std::collections::BTreeMap<facts::NodeId, model::Ty>,
    pub scope_parents: std::collections::BTreeMap<facts::ScopeId, facts::ScopeId>,
    pub variant_projections: std::collections::BTreeMap<(u32, u32, u32), VariantProjection>,
    pub array_lengths: std::collections::BTreeMap<facts::NodeId, Option<u64>>,
    pub fixed_arrays: std::collections::BTreeSet<facts::NodeId>,
    pub uncertain_slots: std::collections::BTreeSet<(facts::NodeId, facts::Slot)>,
    pub constructors: std::collections::BTreeMap<String, model::ConstructorInfo>,
    pub implicit_unwraps: std::collections::BTreeMap<(u32, u32, u32), ImplicitUnwrap>,
    pub operations: std::collections::BTreeMap<String, model::OperationFact>,
    pub handlers: Vec<model::HandlerFact>,
    pub retained_handlers: Vec<model::RetainedHandlerFact>,
    pub retained_handler_answers: Vec<model::RetainedHandlerAnswerFact>,
    pub operation_loan_ends:
        std::collections::BTreeMap<facts::LoanId, ril_compiler_core::diagnostic::CauseId>,
    pub operation_loan_starts: Vec<resumption::OperationLoanStart>,
    pub contextual_types: std::collections::BTreeMap<(u32, u32, u32), model::Ty>,
    pub generic_binders: std::collections::BTreeMap<String, GenericBinder>,
    pub result_duties: Vec<model::ResultDuty>,
    pub result_families: std::collections::BTreeMap<u32, std::collections::BTreeSet<u32>>,
    pub recursive_summaries: recursive::Analysis,
    pub file: Option<FileId>,
    pub explanations: facts::Explanations,
    pub invocations: Vec<summary::InvocationSummary>,
    pub heap: facts::Heap,
    pub fields: std::collections::BTreeMap<(facts::NodeId, facts::Slot), model::Value>,
    pub bindings: Vec<model::BindingInfo>,
    pub functions: Vec<model::FunctionInfo>,
    pub closures: Vec<model::ClosureInfo>,
    pub closure_sites: Vec<model::ClosureSite>,
    pub expressions: Vec<ExpressionFact>,
    pub termination: std::collections::BTreeMap<String, crate::termination::Judgment>,
    pub loan_parents:
        std::collections::BTreeMap<facts::LoanId, std::collections::BTreeSet<facts::Participant>>,
}
#[derive(Debug, Clone)]
pub struct ConstantValue {
    pub reference: ril_compiler_core::ids::ConstRef,
    pub value: model::Value,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub struct ExternalInstance {
    pub declaration_name: String,
    pub syntax: ril_syntax::ast::Function,
    pub callable_type: model::Ty,
    pub arguments: Vec<(String, ril_syntax::ast::TypeExpr)>,
    pub sites: std::collections::BTreeSet<(u32, u32, u32)>,
    pub callable: usize,
}
/// The checked source shape accompanies value-level types because fixed array
/// cardinalities and explicit qualifications are not stored in `model::Ty`.
#[derive(Debug, Clone)]
pub struct ExternalTypeWitness {
    pub syntax: ril_syntax::ast::TypeExpr,
    pub value_type: model::Ty,
}
/// Evidence for the actual invocations admitted at a deterministic parallel
/// boundary. Accesses retain conditional origins and selected handler identity.
#[derive(Debug, Clone)]
pub struct ParallelBoundary {
    pub span: Span,
    pub operation: ParallelOperation,
    pub callbacks: Vec<ParallelCallbackProof>,
    pub cause: ril_compiler_core::diagnostic::CauseId,
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
impl ParallelOperation {
    pub fn canonical_name(self) -> &'static str {
        match self {
            Self::Map => "Parallel::map",
            Self::MapBounded => "Parallel::map_bounded",
            Self::Find => "Parallel::find",
            Self::First => "Parallel::first",
            Self::Any => "Parallel::any",
            Self::Fold => "Parallel::fold",
            Self::Join => "Parallel::join",
            Self::Join3 => "Parallel::join3",
            Self::ForEach => "Parallel::for_each",
        }
    }
}
#[derive(Debug, Clone)]
pub struct ParallelCallbackProof {
    pub cause: ril_compiler_core::diagnostic::CauseId,
    pub accesses: Vec<model::AccessFact>,
    pub selected_handlers: std::collections::BTreeSet<usize>,
    pub termination: crate::termination::Judgment,
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
    pub scope: facts::NodeId,
    pub task: Option<facts::NodeId>,
    pub kind: ConcurrentBoundaryKind,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct WindowInfo {
    pub backing: model::Origins,
    pub lower: Option<u64>,
    pub length: Option<u64>,
    pub span: Span,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct BudgetProof {
    pub span: Span,
    pub exhaustion_operation: u64,
    pub callee_coverage: Vec<ril_compiler_core::diagnostic::CauseId>,
    pub cleanup_coverage: Vec<ril_compiler_core::diagnostic::CauseId>,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct InferenceResolution {
    pub binder: String,
    pub selected: model::Ty,
    pub site: Span,
    pub origin: ril_compiler_core::diagnostic::CauseId,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct StaticKeyParameter {
    pub binder: String,
    pub owner: Span,
    pub parameter: u32,
    pub name: String,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct ResumptionStep {
    pub span: Span,
    pub owner: facts::ScopeId,
    pub handler: usize,
    pub operation: u64,
    pub body_answer: model::Ty,
    pub arm_answer: model::Ty,
    pub continuation: ril_compiler_core::diagnostic::CauseId,
    pub cause: ril_compiler_core::diagnostic::CauseId,
    pub boundary: u32,
    pub context: effect_identity::InvocationContext,
    pub continuation_value: copy_contract::CopyValueSnapshot,
    pub arm_value: copy_contract::CopyValueSnapshot,
    pub continuation_epoch: usize,
    pub completion_epoch: usize,
    pub ended_operation_loans: std::collections::BTreeSet<facts::LoanId>,
    pub operation_receptions: Vec<resumption::OperationReception>,
    pub continuation_expression: usize,
    pub arm_expression: usize,
    pub transport: model::AnswerTransport,
    pub scope_exit: Option<resumption::ContinuationScopeExit>,
}
/// The universally checked body of one declaration. Actual caller-specific
/// instantiations do not replace this entry or erase its residual effects.
#[derive(Debug, Clone)]
pub struct DefinitionCheck {
    pub function: usize,
    pub span: Span,
    pub declared: model::Ty,
    pub returned: model::Ty,
    pub invocation: summary::InvocationSummary,
}
#[derive(Debug, Clone)]
pub struct CleanupEvent {
    pub binding: usize,
    pub owner: facts::ScopeId,
    pub span: Span,
    pub resumed_boundary: Option<u32>,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct StaticKeyCheck {
    pub binder: String,
    pub argument: Span,
    pub receiver: model::Ty,
    pub coordinate: model::StaticCoordinate,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}
#[derive(Debug, Clone)]
pub struct ImplicitUnwrap {
    pub cause: ril_compiler_core::diagnostic::CauseId,
    pub depth: u32,
    pub tags: Vec<String>,
}
#[derive(Debug, Clone)]
pub struct VariantProjection {
    pub tag: String,
    pub cause: ril_compiler_core::diagnostic::CauseId,
    pub direct: bool,
}
#[derive(Debug, Clone)]
pub struct GenericBinder {
    pub identity: String,
    /// Canonical named declaration. Repeated activations keep this owner;
    /// specialized declarations with the same source span have different IDs.
    pub definition: ril_compiler_core::ids::DefinitionId,
    /// Diagnostic location only; never an identity or lookup key.
    pub owner: Span,
    pub index: u32,
    pub name: String,
}
#[derive(Debug, Clone)]
pub struct ExpressionFact {
    pub source_id: Option<ril_compiler_core::ids::ExprId>,
    /// The node identities in `value` belong to this immutable observation epoch.
    pub allocation_epoch: usize,
    pub span: Span,
    pub value: model::Value,
}
impl ExpressionFact {
    /// Obtain a later view without rewriting this historical observation.
    pub fn value_at(
        &self,
        epoch: usize,
        history: &[(facts::NodeId, facts::NodeId)],
    ) -> Option<model::Value> {
        if self.allocation_epoch > epoch || epoch > history.len() {
            return None;
        }
        let mut value = self.value.clone();
        for &(recent, older) in &history[self.allocation_epoch..epoch] {
            value.remap_origins(recent, older);
        }
        Some(value)
    }
}
impl SemanticFacts {
    pub fn expressions_at(&self, span: Span) -> impl Iterator<Item = &ExpressionFact> {
        self.expressions
            .iter()
            .filter(move |fact| fact.span == span)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsupportedFeature {
    pub span: Span,
    pub description: String,
}
#[derive(Debug)]
pub struct AnalyzeOutcome {
    pub program: Option<VerifiedProgram>,
    /// Available observations remain inspectable when semantic verification fails.
    pub facts: Option<std::sync::Arc<SemanticFacts>>,
    pub hir: Option<std::sync::Arc<crate::hir::HirProgram>>,
    pub diagnostics: Vec<Diagnostic>,
    pub unsupported: Vec<UnsupportedFeature>,
}
pub fn analyze(syntax: &ril_syntax::ast::Program, file: FileId) -> AnalyzeOutcome {
    let diagnostics = ril_syntax::validate_program(syntax);
    if !diagnostics.is_empty() {
        return AnalyzeOutcome {
            program: None,
            facts: None,
            hir: None,
            diagnostics,
            unsupported: vec![],
        };
    }
    let resolved = crate::modules::resolve(
        vec![crate::modules::ModuleUnit {
            path: std::path::PathBuf::from("/ril-memory-source.ril"),
            file,
            program: syntax.clone(),
            is_declaration: false,
        }],
        file,
    );
    if !resolved.diagnostics.is_empty() || !resolved.unsupported.is_empty() {
        return AnalyzeOutcome {
            program: None,
            facts: None,
            hir: None,
            diagnostics: resolved.diagnostics,
            unsupported: resolved.unsupported,
        };
    }
    let layout = ril_compiler_core::target::TargetLayout::POINTER64;
    let evaluated = crate::static_eval::evaluate(&resolved.program, layout);
    if !evaluated.diagnostics.is_empty() || !evaluated.unsupported.is_empty() {
        return AnalyzeOutcome {
            program: None,
            facts: None,
            hir: None,
            diagnostics: evaluated.diagnostics,
            unsupported: evaluated.unsupported,
        };
    }
    let mut outcome =
        checker::analyze_constants(&evaluated.program, file, &[], layout, &evaluated.constants);
    if let Some(program) = &mut outcome.program {
        program.attach_resolved_source(resolved.program);
        program.attach_static_metadata(
            evaluated.static_definitions,
            evaluated.type_functions,
            evaluated.static_termination,
        );
    }
    outcome
}
#[cfg(test)]
pub(crate) fn analyze_project(
    syntax: &ril_syntax::ast::Program,
    file: FileId,
    declaration_files: &[FileId],
) -> AnalyzeOutcome {
    checker::analyze(
        syntax,
        file,
        declaration_files,
        ril_compiler_core::target::TargetLayout::POINTER64,
    )
}
pub(crate) fn analyze_project_for(
    syntax: &ril_syntax::ast::Program,
    file: FileId,
    declaration_files: &[FileId],
    layout: ril_compiler_core::target::TargetLayout,
    constants: &crate::static_eval::constants::ConstantPool,
) -> AnalyzeOutcome {
    checker::analyze_constants(syntax, file, declaration_files, layout, constants)
}
