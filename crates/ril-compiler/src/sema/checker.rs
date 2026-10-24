use super::{
    AnalyzeOutcome, SemanticFacts, UnsupportedFeature,
    facts::*,
    model::*,
    relations::{Condition, Pivot, Relation},
};
use crate::hir::{Definition, VerifiedProgram};
use ril_compiler_core::{
    diagnostic::{CauseId, Diagnostic, Label, Severity},
    ids::{CallableOwner, ClosureSiteId, DefinitionId, HandlerSiteId, StmtId},
    source::{FileId, Span},
};
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
mod allocation_tests;
mod applications;
pub(crate) mod arrays;
mod bindings;
mod budget;
mod builtin_source_observations;
mod builtin_source_types;
mod call_input_source;
mod calls;
mod cancellation;
mod canonical_copy;
mod cleanup;
mod closure_exclusivity;
mod closure_invocations;
mod collection_types;
mod concurrent;
mod constants;
mod context;
mod contract_types;
mod contracts;
pub(crate) use contracts::state_group;
mod copy;
mod copy_classes;
mod copy_contracts;
mod copy_invocations;
mod default_uses;
mod effect_instances;
mod effect_invocations;
mod effects;
mod entry_arguments;
mod environments;
mod evaluated;
#[cfg(test)]
mod execution_oracle;
mod explicit_named;
mod formal_values;
mod generated_sources;
mod symbolic_rows;
use super::evaluated::EvaluatedValue;
mod bound_writes;
mod expressions;
mod external_calls;
mod external_exits;
mod external_generics;
mod external_types;
mod file_callback;
mod flow;
mod havoc;
mod invocation_loans;
mod io_buffered;
mod io_callback;
mod io_types;
pub(super) mod iter;
mod iter_types;
mod keys;
mod loop_graph;
mod loop_results;
mod loop_shapes;
mod multiplicity;
mod narrowing;
mod numeric;
mod numeric_application;
mod numeric_pending;
mod parallel;
mod parallel_signatures;
mod patterns;
mod post_resume;
mod post_resume_scope;
mod propagation;
mod record_bounds;
mod recursive_calls;
mod repeated;
mod resources;
mod result_conditions;
mod results;
mod retained_answers;
mod rows;
mod source_receiving;
mod source_types;
mod static_source_context;
pub(crate) use source_types::normalize_closed_source_syntax;
mod standard;
mod storage;
mod storage_sources;
mod sums;
mod termination_queries;
mod type_source;
mod types;
mod windows;

pub(crate) fn parallel_parameter_labels(name: &str) -> Option<&'static [&'static str]> {
    parallel_signatures::labels(name)
}

#[cfg(test)]
pub(super) fn analyze(
    syntax: &Program,
    file: FileId,
    declaration_files: &[FileId],
    layout: ril_compiler_core::target::TargetLayout,
) -> AnalyzeOutcome {
    analyze_constants(syntax, file, declaration_files, layout, &Default::default())
}

pub(super) fn analyze_constants(
    syntax: &Program,
    file: FileId,
    declaration_files: &[FileId],
    layout: ril_compiler_core::target::TargetLayout,
    constants: &crate::static_eval::constants::ConstantPool,
) -> AnalyzeOutcome {
    std::thread::scope(|scope| {
        match std::thread::Builder::new()
            .name("ril-semantic-analysis".into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, move || {
                analyze_inner(syntax, file, declaration_files, layout, constants)
            }) {
            Ok(worker) => worker
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
            Err(error) => AnalyzeOutcome {
                program: None,
                facts: None,
                hir: None,
                diagnostics: Vec::new(),
                unsupported: vec![UnsupportedFeature {
                    span: Span {
                        file,
                        start: 0,
                        end: 0,
                    },
                    description: format!("semantic analysis worker could not be started: {error}"),
                }],
            },
        }
    })
}

fn freeze_formal_value(value: &mut Value) {
    value.permission = Permission::Read;
    value.publication = Publication::Immutable;
    value.construction = false;
    value.marker = false;
    value.retention_result = false;
    value.mutable_environment = false;
    value.observer_environment = false;
    for payload in [
        &mut value.option_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        freeze_formal_value(payload);
    }
}
fn analyze_inner(
    syntax: &Program,
    file: FileId,
    declaration_files: &[FileId],
    layout: ril_compiler_core::target::TargetLayout,
    constants: &crate::static_eval::constants::ConstantPool,
) -> AnalyzeOutcome {
    let ambiguous_sites = crate::syntax_sites::ambiguous(syntax);
    let mut checker = Checker::new(file);
    // Remaining span-indexed consumers cannot certify ambiguous syntax. Keep
    // their obligation while still building the uncertified analysis snapshot.
    checker.unsupported.extend(ambiguous_sites);
    checker.declare_system_operations();
    checker.layout = layout;
    checker.declaration_files = declaration_files.iter().map(|file| file.0).collect();
    checker.install_constants(constants);
    checker.run(syntax);
    if checker.application_effect.exhausted {
        checker.unsupported(
            Span {
                file,
                start: 0,
                end: 0,
            },
            "semantic occurrence budget exhausted before recording a value",
        );
    }
    if let Some(span) = checker.numeric.incomplete() {
        checker.unsupported(
            span,
            "numeric choices must be committed before issuing a semantic certificate",
        );
    }
    checker.finish_copy_templates();
    checker.finish_retained_answer_contracts();
    checker.finish_constant_types(constants);
    checker.finish_closure_exclusivity();
    let termination = crate::termination::analyze_with_budgets(syntax, &checker.budget_proofs);
    checker.diagnostics.extend(termination.diagnostics);
    checker.unsupported.extend(termination.unsupported);
    let handlers = checker.handler_facts();
    let external_type_expansions = checker.external_type_expansions();
    let external_type_witnesses = checker.external_type_witnesses(syntax);
    let external_resource_types = external_type_expansions
        .iter()
        .map(|(ty, _)| ty)
        .chain(
            external_type_witnesses
                .iter()
                .map(|witness| &witness.value_type),
        )
        .filter(|ty| checker.resource_type(ty))
        .cloned()
        .collect();
    if checker.type_source.exhausted.get() {
        checker.unsupported(Span { file, start: 0, end: 0 },
            "typing environment clone work or depth budget exhausted; captured contracts are unresolved");
    }
    let (binding_sources, storage_writes, source_types) = checker.type_source.storage.into_parts();
    let checked_syntax = checker
        .checked_source
        .clone()
        .unwrap_or_else(|| std::sync::Arc::new(syntax.clone()));
    let hir = std::sync::Arc::new(std::mem::take(&mut checker.semantic_hir));
    let facts = SemanticFacts {
        activations: checker.application_effect.activations,
        source_types,
        semantic_hir: Some(hir.clone()),
        binding_sources,
        storage_writes,
        source_program: Some(checked_syntax.clone()),
        channel_repetitions: checker.channel_repetitions,
        channel_messages: checker.channel_message_facts,
        channel_exits: checker.channel_exit_facts,
        channel_message_sequence: checker.channel_message_sequence,
        closure_exclusivity_checks: checker.closure_exclusivity_checks,
        closure_exclusivity_certificate: checker.closure_exclusivity_certificate,
        closure_exposures: checker.closure_exposures,
        closure_discards: checker.closure_discards,
        allocation_history: checker.recency_moves.clone(),
        allocation_events: checker.allocation_events,
        allocation_poisoned: checker.allocation_poisoned,
        pattern_window_sites: checker
            .pattern_window_sites
            .into_iter()
            .map(
                |((rest, loop_owner), site)| super::allocation::PatternWindowSite {
                    rest,
                    loop_owner,
                    site,
                },
            )
            .collect(),
        scopes: checker.scopes,
        numeric_uses: checker.numeric.uses,
        numeric_holes: checker.numeric.holes,
        numeric_selections: checker.numeric.selections,
        constant_pool: checker.constant_pool,
        constant_values: checker.constant_values,
        external_instances: checker.external_instances,
        external_type_witnesses,
        external_type_declarations: checker.types.clone(),
        external_type_expansions,
        external_resource_types,
        copy_boundaries: checker.copy_boundaries,
        copy_invocations: checker.copy_invocations,
        copy_references: checker.copy_references,
        copy_call_events: checker.copy_call_events,
        resource_clones: checker.resource_clones,
        copy_template_closure: checker.copy_template_closure,
        parallel_boundaries: checker.parallel_boundaries,
        concurrent_boundaries: checker.concurrent_boundaries,
        windows: checker.windows,
        pattern_windows: checker.pattern_windows,
        iter_steps: checker.iter_steps.into_values().collect(),
        budget_proofs: checker.budget_proofs,
        budget_termination: termination.budget_witnesses,
        inference_resolutions: checker.inference_resolutions,
        resumption_steps: checker.resumption_steps,
        definition_checks: checker.definition_checks,
        file: Some(checker.file),

        storage_types: checker.storage_types,
        static_key_checks: checker.static_key_checks,
        static_key_parameters: checker.static_key_parameters,
        cleanup_events: checker.cleanup_events,
        explanations: checker.explanations,
        invocations: checker.invocations,
        heap: checker.heap,
        fields: checker.fields,
        bindings: checker.bindings,
        functions: checker.functions,
        closures: checker.closures,
        closure_sites: checker.application_effect.closure_sites,
        expressions: checker.application_effect.expressions,
        termination: termination.judgments,
        loan_parents: checker.loan_parents,
        invocation_loan_starts: checker.invocation_loan_starts,
        invocation_loan_ends: checker.invocation_loan_ends,
        target_layout: Some(checker.layout),
        generic_binders: checker.generic_binders,
        record_bounds: checker.record_bounds,
        bound_rows: checker.bound_rows,
        generic_bound_checks: checker.generic_bound_checks,
        generic_bound_projections: checker.generic_bound_projections,
        scoped_source_identities: checker.scoped_source_identities,
        observed_accesses: checker.observed_accesses,
        bound_field_writes: checker.bound_field_writes,
        result_duties: checker.result_duties,
        optional_tags: checker.optional_tags,
        result_families: checker.result_families,
        operations: checker.operations,
        effect_instances: checker.effect_instances,
        effect_invocations: checker.effect_invocations,
        invocation_expressions: checker.application_effect.contexts,
        evaluations: checker.application_effect.evaluations,
        builtin_source_observations: checker.builtin_sources.into_observations(),
        generated_sources: checker.generated_sources,
        invocation_calls: checker.invocation_calls,
        invocation_witnesses: checker.invocation_witnesses,
        closure_invocations: checker.closure_invocations,
        condition_evaluations: checker.condition_evaluations,
        default_uses: checker.default_uses,
        call_arguments: checker.call_arguments,
        handlers,
        retained_handlers: checker.retained_handlers,
        retained_handler_answers: checker.retained_handler_answers,
        implicit_unwraps: checker.implicit_unwraps,
        constructors: checker.constructors,
        uncertain_slots: checker.uncertain_slots,
        array_lengths: checker.array_lengths,
        variant_projections: checker.variant_projections,
        fixed_arrays: checker.fixed_arrays,
        operation_loan_ends: checker.operation_loan_ends,
        operation_loan_starts: checker.operation_loan_starts,
        recursive_summaries: checker.recursive_analysis,
    };
    // Finalizing the owned type arena is part of primary analysis, not a
    // replay of declarations or evaluation histories.
    if let Err(error) = facts
        .source_types
        .validate(&mut super::source_types::WorkLimit::new(4_000_000))
    {
        checker.unsupported.push(super::UnsupportedFeature {
            span: Span {
                file: checker.file,
                start: 0,
                end: 0,
            },
            description: format!("type store could not be finalized: {error}"),
        });
    }
    let accepted = checker
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.severity != Severity::Error)
        && checker.unsupported.is_empty();
    let facts = std::sync::Arc::new(facts);
    let program = accepted.then(|| {
        VerifiedProgram::verified(
            checked_syntax,
            checker.definitions,
            facts.clone(),
            hir.clone(),
            checker.diagnostics.clone(),
        )
    });
    AnalyzeOutcome {
        program,
        facts: Some(facts),
        hir: Some(hir),
        diagnostics: checker.diagnostics,
        unsupported: checker.unsupported,
    }
}
pub(super) fn is_known_builtin_source_type(name: &str) -> bool {
    super::source_types::standard_data::Nominal::lookup(name).is_some()
        || standard::file_type(name).is_some()
}

struct Checker {
    type_source: type_source::TypeSourceDomain,
    semantic_hir: crate::hir::HirProgram,
    pattern_value_sources:
        BTreeMap<ril_compiler_core::ids::PatternId, ril_compiler_core::ids::ExprId>,
    checked_source: Option<std::sync::Arc<Program>>,
    explicit_named: explicit_named::State,
    call_input_source: call_input_source::State,
    invocation_loan_starts: Vec<super::invocation_loans::InvocationLoanStart>,
    invocation_loan_ends: Vec<super::invocation_loans::InvocationLoanEnd>,
    ended_invocation_loans: BTreeMap<LoanId, BTreeSet<Participant>>,
    closure_exclusivity_checks: Vec<super::closure_exclusivity::ClosureExclusivityCheck>,
    closure_exclusivity_certificate:
        Option<super::closure_exclusivity::ClosureExclusivityCertificate>,
    closure_exposures: Vec<super::closure_exclusivity::ClosureExposure>,
    closure_discards: Vec<super::closure_exclusivity::ClosureDiscard>,
    numeric: super::numeric_selection::State,
    constant_pool: std::sync::Arc<crate::static_eval::constants::ConstantPool>,
    constant_values: Vec<super::ConstantValue>,
    foreign_callback_depth: usize,
    foreign_return_states: Vec<external_exits::ReturnExit>,
    foreign_abort_exits: Vec<external_exits::AbortExit>,
    external_instances: Vec<super::ExternalInstance>,
    copy_boundaries: Vec<super::copy_contract::CopyBoundary>,
    copy_invocations: Vec<super::copy_contract::CopyInvocation>,
    copy_template_closure: Option<super::copy_contract::CopyTemplateClosure>,
    copy_invocation_stack: Vec<super::copy_templates::InstanceId>,
    copy_references: Vec<super::copy_contract::CopyReference>,
    copy_call_events: Vec<super::copy_contract::CopyCallEvent>,
    resource_clones: Vec<super::resource_copy::ResourceCloneEvent>,
    descriptor_sites: BTreeMap<concurrent::DescriptorContext, SiteId>,
    parallel_boundaries: Vec<super::ParallelBoundary>,
    concurrent_boundaries: Vec<super::ConcurrentBoundary>,
    concurrency: concurrent::State,
    channel_message_facts: Vec<super::channel_messages::ChannelMessageFact>,
    channel_repetitions: Vec<super::channel_messages::ChannelRepetition>,
    active_channel_repetitions: Vec<super::channel_messages::ChannelRepetitionId>,
    channel_exit_facts: Vec<super::channel_messages::ChannelExitFact>,
    channel_message_sequence: u64,
    channel_return_states: BTreeMap<(ScopeId, u32), concurrent::messages::Flow>,
    file: FileId,
    layout: ril_compiler_core::target::TargetLayout,
    budget_proofs: Vec<super::BudgetProof>,
    budget_coverage: Vec<budget::Coverage>,
    budget_recoveries: Vec<budget::Recovery>,
    heap: Heap,
    fields: BTreeMap<(NodeId, Slot), Value>,
    bindings: Vec<BindingInfo>,
    functions: Vec<FunctionInfo>,
    type_contract_environments:
        BTreeMap<ril_compiler_core::ids::TypeExprId, contracts::ContractEnvironment>,
    completed_invocation: Option<contracts::CompletedInvocation>,
    definition_checks: Vec<super::DefinitionCheck>,
    resumption_steps: Vec<super::ResumptionStep>,
    completed_cleanups: BTreeSet<BindingId>,
    cleanup_events: Vec<super::CleanupEvent>,
    suspended_cleanups: BTreeMap<ScopeId, Vec<BindingId>>,
    deferred_arm_cleanups: Vec<cleanup::DeferredArmCleanup>,
    probing_contracts: BTreeSet<(u32, u32, u32, u32)>,
    nested_contracts: BTreeSet<(u32, u32, u32, u32)>,
    closures: Vec<ClosureInfo>,
    types: BTreeMap<String, TypeDeclaration>,
    effects: BTreeMap<String, effects::EffectInfo>,
    local_effects: BTreeSet<String>,
    callable_local_effects: BTreeMap<(bool, usize), BTreeSet<String>>,
    callable_dependencies: BTreeMap<(bool, usize), Obligations>,
    global: Env,
    diagnostics: Vec<Diagnostic>,
    unsupported: Vec<UnsupportedFeature>,
    definitions: Vec<Definition>,
    explanations: Explanations,
    next_loan: u32,
    loan_parents: BTreeMap<LoanId, BTreeSet<Participant>>,
    next_choice: u32,
    loop_depth: usize,
    loop_allocation_owners: Vec<ScopeId>,
    fallback_boundaries: Vec<(ScopeId, usize)>,
    call_stack: Vec<usize>,
    sites: BTreeMap<(u32, u32, u32), SiteId>,
    next_site: u32,
    copy_classes: copy_classes::Classes,
    formal_family_parents: BTreeMap<NodeId, BTreeSet<NodeId>>,
    recency_moves: Vec<(NodeId, NodeId)>,
    active_iterations: Vec<Origins>,
    active_drafts: BTreeSet<NodeId>,
    checked_closures: BTreeSet<usize>,
    application_effect: super::application_effect::ApplicationEffectDomain,
    invocations: Vec<super::summary::InvocationSummary>,
    literal_negative: bool,
    scope_names: BTreeMap<ScopeId, Option<String>>,
    scopes: super::scopes::ScopeIndex,
    storage_types: BTreeMap<NodeId, Ty>,
    declaration_files: BTreeSet<u32>,
    recursive_analysis: super::recursive::Analysis,
    static_value_bindings: BTreeSet<BindingId>,
    cancellation_contexts: Vec<cancellation::Context>,
    generic_row_lacks: BTreeMap<super::model::rows::RowIdentity, BTreeSet<String>>,
    generic_key_bounds: BTreeMap<String, TypeExpr>,
    generic_key_contexts: BTreeMap<String, BTreeMap<String, String>>,
    static_key_checks: Vec<super::StaticKeyCheck>,
    static_key_parameters: Vec<super::StaticKeyParameter>,
    inference_resolutions: Vec<super::InferenceResolution>,
    inference_metas: BTreeSet<String>,
    generic_binders: BTreeMap<String, super::GenericBinder>,
    record_bounds: Vec<super::record_bounds::GenericRecordBound>,
    bound_rows: Vec<super::record_bounds::BoundRowDeclaration>,
    generic_bound_checks: Vec<super::record_bounds::GenericBoundCheck>,
    generic_bound_projections: Vec<super::record_bounds::GenericBoundProjection>,
    scoped_source_identities: Vec<super::scoped_source_identity::ScopedSourceIdentity>,
    observed_accesses: Vec<super::bound_writes::ObservedAccess>,
    bound_field_writes: Vec<super::bound_writes::BoundFieldWrite>,
    record_bounds_by_binder: BTreeMap<String, ril_compiler_core::ids::GenericBoundId>,
    rigid_record_parameters:
        BTreeMap<(DefinitionId, u32), Vec<super::record_bounds::StructuralSchema>>,
    universal: bool,
    result_duties: Vec<ResultDuty>,
    optional_tags: Vec<super::optional_tags::OptionalTagFact>,
    result_families: BTreeMap<u32, BTreeSet<u32>>,
    result_sites: BTreeMap<(u32, u32, u32, u32), u32>,
    operations: BTreeMap<String, OperationFact>,
    effect_type_binders: BTreeMap<String, String>,
    effect_instances: Vec<super::effect_identity::EffectInstance>,
    effect_invocations: Vec<super::effect_identity::EffectInvocation>,
    builtin_sources: builtin_source_observations::State,
    generated_sources: Vec<super::generated_sources::GeneratedSource>,
    invocation_calls: Vec<super::effect_identity::InvocationCall>,
    invocation_witnesses: Vec<super::effect_identity::InvocationWitness>,
    closure_invocations: Vec<super::effect_identity::ClosureInvocation>,
    condition_evaluations: Vec<super::result_conditions::ConditionEvaluation>,
    result_inspection_versions: BTreeMap<u32, u32>,
    closure_invocation_stack: Vec<super::effect_identity::ClosureInvocationId>,
    default_uses: Vec<super::default_uses::DefaultUse>,
    default_use_stack: Vec<super::default_uses::DefaultUseId>,
    call_arguments: Vec<super::default_uses::CallArguments>,
    budget_validation_depth: u32,
    expression_owners: Vec<Option<CallableOwner>>,
    effect_callback_uses: Vec<super::effect_identity::CallbackInvocation>,
    handler_definitions: Vec<effects::HandlerDefinition>,
    retained_handlers: Vec<RetainedHandlerFact>,
    retained_answer_uses: Vec<retained_answers::PendingUse>,
    retained_handler_answers: Vec<RetainedHandlerAnswerFact>,
    immediate_scope_arguments: BTreeSet<(super::copy_contract::CopyCallEventId, u32)>,
    immediate_scope_closures: BTreeSet<usize>,
    active_handlers: Vec<usize>,
    block_boundaries: Vec<u32>,
    next_boundary: u32,
    resume_contexts: Vec<effects::ResumeContext>,
    ended_operation_loans: BTreeSet<LoanId>,
    operation_loan_ends: BTreeMap<LoanId, CauseId>,
    operation_loan_starts: Vec<super::resumption::OperationLoanStart>,
    pending_abort: Option<(u32, Value)>,
    effect_answer_probe: bool,
    checked_definitions: BTreeSet<DefinitionId>,
    type_alternatives: BTreeMap<u32, Vec<Value>>,
    pending_handler_obligations: BTreeMap<ScopeId, Obligations>,
    loop_breaks: Vec<(ScopeId, Vec<Value>)>,
    loop_continuations: Vec<(ScopeId, bool)>,
    loop_unit: Vec<bool>,
    refinements: BTreeMap<narrowing::Place, narrowing::Refinement>,
    implicit_unwraps: BTreeMap<(u32, u32, u32), super::ImplicitUnwrap>,
    suppress_refinement: usize,
    constructors: BTreeMap<String, ConstructorInfo>,
    invalid_refinement_values: BTreeMap<u32, &'static str>,
    write_events: Vec<narrowing::WriteEvent>,
    read_epochs: BTreeMap<(ril_compiler_core::ids::ExprId, ScopeId), usize>,
    uncertain_slots: BTreeSet<(NodeId, Slot)>,
    source_type_intern: BTreeMap<String, std::sync::Arc<SourceTypeWitness>>,
    source_type_bytes: usize,
    variant_projections: BTreeMap<(u32, u32, u32), super::VariantProjection>,
    result_loop_starts: Vec<usize>,
    result_exit_checks: BTreeMap<(u32, u32, u32, u32), bool>,
    result_return_checks: BTreeMap<(u32, u32), bool>,
    lexical_declarations:
        BTreeMap<(ScopeId, u32, String), Option<ril_compiler_core::ids::PatternId>>,
    array_lengths: BTreeMap<NodeId, Option<u64>>,
    fixed_arrays: BTreeSet<NodeId>,
    analysis_depth: usize,
    analysis_visits: usize,
    windows: BTreeMap<NodeId, super::WindowInfo>,
    pattern_windows: Vec<super::pattern_windows::PatternWindowCreation>,
    pattern_window_sites: BTreeMap<(ril_compiler_core::ids::PatternId, ScopeId), SiteId>,
    allocation_events: Vec<super::allocation::AllocationEvent>,
    allocation_poisoned: bool,
    iter_steps: BTreeMap<String, iter::StepFact>,
    window_blocks: Vec<windows::WindowBlockUses>,
    window_expression_uses: Vec<windows::WindowExpressionUses>,
}
fn declaration_definition(
    functions: &[FunctionInfo],
    owner: Option<CallableOwner>,
    source: Option<StmtId>,
) -> Option<DefinitionId> {
    let (Some(owner), Some(source)) = (owner, source) else {
        return None;
    };
    functions
        .iter()
        .find(|info| info.lexical_owner == Some(owner) && info.hir_id == Some(source))
        .map(|info| info.definition)
}

impl Checker {
    fn new(file: FileId) -> Self {
        let mut checker = Self {
            type_source: Default::default(),
            semantic_hir: Default::default(),
            pattern_value_sources: Default::default(),
            checked_source: None,
            explicit_named: Default::default(),
            call_input_source: Default::default(),
            numeric: Default::default(),
            constant_pool: std::sync::Arc::default(),
            constant_values: vec![],
            foreign_callback_depth: 0,
            foreign_return_states: Vec::new(),
            foreign_abort_exits: Vec::new(),
            external_instances: Vec::new(),
            concurrent_boundaries: Vec::new(),
            copy_boundaries: Vec::new(),
            copy_invocations: Vec::new(),
            copy_template_closure: None,
            copy_invocation_stack: Vec::new(),
            copy_references: Vec::new(),
            copy_call_events: Vec::new(),
            resource_clones: Vec::new(),
            descriptor_sites: BTreeMap::new(),
            parallel_boundaries: Vec::new(),
            concurrency: concurrent::State::default(),
            channel_message_facts: vec![],
            channel_exit_facts: vec![],
            channel_message_sequence: 0,
            channel_return_states: BTreeMap::new(),
            channel_repetitions: Vec::new(),
            active_channel_repetitions: Vec::new(),
            file,
            budget_proofs: Vec::new(),
            budget_coverage: Vec::new(),
            budget_recoveries: Vec::new(),
            windows: BTreeMap::new(),
            pattern_windows: Vec::new(),
            pattern_window_sites: BTreeMap::new(),
            allocation_events: Vec::new(),
            allocation_poisoned: false,
            iter_steps: BTreeMap::new(),
            window_blocks: Vec::new(),
            window_expression_uses: Vec::new(),
            layout: ril_compiler_core::target::TargetLayout::POINTER64,
            heap: Heap::default(),
            fields: BTreeMap::new(),
            bindings: vec![],
            functions: vec![],
            type_contract_environments: BTreeMap::new(),
            completed_invocation: None,
            definition_checks: Vec::new(),
            resumption_steps: Vec::new(),
            completed_cleanups: BTreeSet::new(),
            cleanup_events: Vec::new(),
            suspended_cleanups: BTreeMap::new(),
            deferred_arm_cleanups: Vec::new(),
            probing_contracts: BTreeSet::new(),
            nested_contracts: BTreeSet::new(),
            closures: vec![],
            types: BTreeMap::new(),
            effects: BTreeMap::new(),
            local_effects: BTreeSet::new(),
            callable_local_effects: BTreeMap::new(),
            callable_dependencies: BTreeMap::new(),
            global: Env::new(),
            diagnostics: vec![],
            unsupported: vec![],
            definitions: vec![],
            explanations: Explanations::default(),
            next_loan: 0,
            loan_parents: BTreeMap::new(),
            invocation_loan_starts: Vec::new(),
            invocation_loan_ends: Vec::new(),
            ended_invocation_loans: BTreeMap::new(),
            next_choice: 0,
            loop_depth: 0,
            loop_allocation_owners: Vec::new(),
            fallback_boundaries: Vec::new(),
            call_stack: vec![],
            sites: BTreeMap::new(),
            next_site: 0,
            copy_classes: copy_classes::Classes::default(),
            formal_family_parents: BTreeMap::new(),
            recency_moves: Vec::new(),
            active_iterations: vec![],
            active_drafts: BTreeSet::new(),
            checked_closures: BTreeSet::new(),
            closure_exclusivity_checks: Vec::new(),
            closure_exclusivity_certificate: None,
            closure_exposures: Vec::new(),
            closure_discards: Vec::new(),
            application_effect: Default::default(),
            invocations: vec![],
            literal_negative: false,
            scope_names: BTreeMap::new(),
            scopes: [ScopeId(0)].into_iter().collect(),
            storage_types: BTreeMap::new(),
            declaration_files: BTreeSet::new(),
            recursive_analysis: super::recursive::Analysis::default(),
            static_value_bindings: BTreeSet::new(),
            cancellation_contexts: Vec::new(),
            generic_row_lacks: BTreeMap::new(),
            generic_key_bounds: BTreeMap::new(),
            generic_key_contexts: BTreeMap::new(),
            static_key_checks: Vec::new(),
            static_key_parameters: Vec::new(),
            inference_resolutions: Vec::new(),
            inference_metas: BTreeSet::new(),
            generic_binders: BTreeMap::new(),
            record_bounds: Vec::new(),
            bound_rows: Vec::new(),
            generic_bound_checks: Vec::new(),
            generic_bound_projections: Vec::new(),
            scoped_source_identities: Vec::new(),
            observed_accesses: Vec::new(),
            bound_field_writes: Vec::new(),
            record_bounds_by_binder: BTreeMap::new(),
            rigid_record_parameters: BTreeMap::new(),
            effect_type_binders: BTreeMap::new(),
            effect_instances: Vec::new(),
            effect_invocations: Vec::new(),
            builtin_sources: builtin_source_observations::State::default(),
            generated_sources: Vec::new(),
            invocation_calls: Vec::new(),
            invocation_witnesses: Vec::new(),
            closure_invocations: Vec::new(),
            condition_evaluations: Vec::new(),
            result_inspection_versions: BTreeMap::new(),
            closure_invocation_stack: Vec::new(),
            default_uses: Vec::new(),
            default_use_stack: Vec::new(),
            call_arguments: Vec::new(),
            budget_validation_depth: 0,
            expression_owners: Vec::new(),
            effect_callback_uses: Vec::new(),
            universal: false,
            result_duties: vec![],
            optional_tags: vec![],
            result_families: BTreeMap::new(),
            result_sites: BTreeMap::new(),
            operations: BTreeMap::new(),
            handler_definitions: Vec::new(),
            retained_handlers: Vec::new(),
            retained_answer_uses: Vec::new(),
            retained_handler_answers: Vec::new(),
            immediate_scope_arguments: BTreeSet::new(),
            immediate_scope_closures: BTreeSet::new(),
            active_handlers: Vec::new(),
            block_boundaries: Vec::new(),
            next_boundary: 0,
            resume_contexts: Vec::new(),
            ended_operation_loans: BTreeSet::new(),
            operation_loan_ends: BTreeMap::new(),
            operation_loan_starts: Vec::new(),
            pending_abort: None,
            effect_answer_probe: false,
            checked_definitions: BTreeSet::new(),
            type_alternatives: BTreeMap::new(),
            pending_handler_obligations: BTreeMap::new(),
            loop_breaks: Vec::new(),
            loop_continuations: Vec::new(),
            loop_unit: Vec::new(),
            refinements: BTreeMap::new(),
            implicit_unwraps: BTreeMap::new(),
            suppress_refinement: 0,
            constructors: BTreeMap::new(),
            invalid_refinement_values: BTreeMap::new(),
            write_events: Vec::new(),
            read_epochs: BTreeMap::new(),
            uncertain_slots: BTreeSet::new(),
            source_type_intern: BTreeMap::new(),
            source_type_bytes: 0,
            variant_projections: BTreeMap::new(),
            result_loop_starts: Vec::new(),
            result_exit_checks: BTreeMap::new(),
            result_return_checks: BTreeMap::new(),
            lexical_declarations: BTreeMap::new(),
            array_lengths: BTreeMap::new(),
            fixed_arrays: BTreeSet::new(),
            analysis_depth: 0,
            analysis_visits: 0,
        };
        checker.register_standard_process_types();
        checker.register_standard_iter_types();
        checker.register_standard_concurrent_types();
        checker
    }
    fn scope(&mut self) -> ScopeId {
        self.scopes.allocate().unwrap_or_else(|| {
            self.application_effect.exhausted = true;
            ScopeId(u32::MAX)
        })
    }
    fn choice(&mut self) -> u32 {
        let choice = self.next_choice;
        self.next_choice += 1;
        choice
    }
    fn frame(&mut self, env: Env, anonymous: bool) -> Frame {
        Frame {
            input_environment: None,
            copy_call_event: None,
            received_closures: BTreeMap::new(),
            callable_owner: None,
            env,
            owner: self.scope(),
            obligations: Obligations::default(),
            locals: vec![],
            returned: vec![],
            foreign_return_states: vec![],
            definition: None,
            anonymous,
            callback_call: false,
            expected_return: None,
            expected_return_source: None,
            return_source_valid: true,
        }
    }
    fn closure_site(
        &mut self,
        owner: Option<CallableOwner>,
        source: Option<ril_compiler_core::ids::ExprId>,
        span: Span,
    ) -> Option<ClosureSiteId> {
        let site =
            owner.zip(source).and_then(|(owner, source)| {
                if !self.semantic_hir.expression(source).is_some_and(|node| {
                    matches!(node.kind, crate::hir::nodes::ExprKind::Lambda { .. })
                }) {
                    return None;
                }
                self.application_effect.closure_site(owner, source, span)
            });
        if site.is_none() {
            self.unsupported(
                span,
                "closure site has no original HIR lambda identity or exhausted its work bound",
            );
        }
        site
    }
    fn scope_is_within(&self, mut candidate: ScopeId, ancestor: ScopeId) -> bool {
        let mut seen = BTreeSet::new();
        while seen.insert(candidate) {
            if candidate == ancestor {
                return true;
            }
            let Some(parent) = self.scopes.parent(&candidate) else {
                return false;
            };
            candidate = *parent;
        }
        false
    }
    fn generic_scope(&mut self, id: usize) -> super::context::FrozenEnvironment {
        let info = self.functions[id].clone();
        let function = &info.syntax;
        let previous = self.enter_typing_environment(&info.typing_environment);
        let mut context = self.type_source.environment.generic_context.clone();
        let mut owned_keys = Vec::new();
        for (index, generic) in function.generics.iter().enumerate() {
            self.type_source
                .environment
                .bound_row_context
                .remove(&generic.name);
            let identity = format!("function:{}:generic:{index}", info.definition.0);
            self.generic_binders
                .entry(identity.clone())
                .or_insert_with(|| super::GenericBinder {
                    identity: identity.clone(),
                    definition: info.definition,
                    owner: function.span,
                    index: index as u32,
                    name: generic.name.clone(),
                });
            if let Some(bound) = &generic.bound
                && let TypeKind::KeyOf(base) = &bound.kind
            {
                self.generic_key_bounds
                    .insert(identity.clone(), *base.clone());
                owned_keys.push(identity.clone());
            }
            context.insert(generic.name.clone(), identity);
        }
        let captured_rows: BTreeSet<_> = self
            .type_source
            .environment
            .bound_row_context
            .values()
            .copied()
            .collect();
        self.type_source
            .environment
            .bound_row_selections
            .retain(|id, _| {
                captured_rows.contains(id)
                    && self
                        .bound_rows
                        .get(id.0 as usize)
                        .is_some_and(|row| row.definition != info.definition)
            });
        for identity in owned_keys {
            self.generic_key_contexts.insert(identity, context.clone());
        }
        self.type_source.environment.generic_context = context;
        self.declare_record_bounds(id);
        self.declare_row_contract(function);
        previous
    }
    fn cause(
        &mut self,
        kind: CauseKind,
        span: Span,
        text: impl Into<String>,
        parents: impl IntoIterator<Item = CauseId>,
    ) -> CauseId {
        self.explanations.add(kind, Some(span), text, parents)
    }
    fn error(
        &mut self,
        code: &str,
        span: Span,
        message: impl Into<String>,
        parents: impl IntoIterator<Item = CauseId>,
    ) {
        self.fail_copy_invocations(true);
        self.fail_closure_invocations(true);
        self.fail_default_uses(true);
        if self
            .diagnostics
            .iter()
            .any(|d| d.code == code && d.labels.first().is_some_and(|l| l.span == span))
        {
            return;
        }
        let message = message.into();
        let cause = self.cause(CauseKind::MissingProof, span, message.clone(), parents);
        self.diagnostics.push(Diagnostic {
            code: code.into(),
            severity: Severity::Error,
            message: message.clone(),
            labels: vec![Label { span, message }],
            causes: self.explanations.chain(cause),
        });
    }
    fn unsupported(&mut self, span: Span, description: impl Into<String>) {
        self.fail_copy_invocations(false);
        self.fail_closure_invocations(false);
        self.fail_default_uses(false);
        let description = description.into();
        if !self
            .unsupported
            .iter()
            .any(|u| u.span == span && u.description == description)
        {
            self.unsupported
                .push(UnsupportedFeature { span, description });
        }
    }
    fn run(&mut self, program: &Program) {
        let mut identified = program.clone();
        let mut hir = match crate::hir::HirProgram::lower_identified(
            &mut identified,
            crate::hir::nodes::InputOrigin::Transformed(
                crate::hir::nodes::GeneratedKind::StaticMaterialization,
            ),
        ) {
            Ok(hir) => hir,
            Err(error) => {
                self.unsupported(
                    Span {
                        file: self.file,
                        start: 0,
                        end: 0,
                    },
                    format!("semantic HIR construction is incomplete: {error}"),
                );
                return;
            }
        };
        if let Err(error) = hir.classify_declaration_units(&self.declaration_files, &mut 1_000_000)
        {
            self.unsupported(
                Span {
                    file: self.file,
                    start: 0,
                    end: 0,
                },
                format!("semantic input classification is incomplete: {error}"),
            );
            return;
        }
        self.type_source.reset_header_queries();
        self.semantic_hir = hir;
        let program = std::sync::Arc::new(identified);
        self.checked_source = Some(program.clone());
        let mut frame = Frame {
            input_environment: None,
            copy_call_event: None,
            received_closures: BTreeMap::new(),
            callable_owner: Some(CallableOwner::Global),
            env: Env::new(),
            owner: ScopeId(0),
            obligations: Obligations::default(),
            locals: vec![],
            returned: vec![],
            foreign_return_states: vec![],
            definition: None,
            anonymous: true,
            callback_call: false,
            expected_return: None,
            expected_return_source: None,
            return_source_valid: true,
        };
        self.declarations(&program.statements, &mut frame);
        for stmt in &program.statements {
            if !matches!(
                stmt.kind,
                StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
            ) {
                let mut previous = std::mem::take(&mut frame.obligations);
                self.statement(stmt, &mut frame);
                self.flush_handler_obligations(&mut frame);
                let module_write = frame.obligations.accesses.iter().any(|access| {
                    access.mode == Mode::Write
                        && access
                            .participants
                            .iter()
                            .any(|participant| match participant {
                                Participant::Root(root) => {
                                    self.bindings.get(root.0 as usize).is_some_and(|binding| {
                                        binding.owner == ScopeId(0)
                                            && binding.lexical_scope == u32::MAX
                                    })
                                }
                                _ => false,
                            })
                });
                if !frame.obligations.effects.is_empty()
                    || frame.obligations.parameter_write
                    || frame
                        .obligations
                        .named
                        .values()
                        .any(|mode| *mode != Mode::Read)
                    || module_write
                {
                    let causes = frame
                        .obligations
                        .accesses
                        .iter()
                        .filter(|access| access.mode == Mode::Write)
                        .map(|access| access.cause)
                        .collect::<Vec<_>>();
                    self.error(
                        "E0202",
                        stmt.span,
                        "top-level initialization must have no observable effects or state writes",
                        causes,
                    );
                }
                previous.include(&frame.obligations, true);
                frame.obligations = previous;
            }
        }
        self.global = frame.env.clone();
        self.flush_handler_obligations(&mut frame);
        let module_tail = self.unit(Span {
            file: self.file,
            start: 0,
            end: 0,
        });
        self.finish_results(frame.owner, &module_tail);
        for function in &mut self.functions {
            if function.owner.is_none() {
                function.lexical = self.global.clone();
                function.typing_environment = self
                    .type_source
                    .derive_environment(&function.typing_environment, &function.lexical);
            }
        }
        let functions = self.functions.len();
        self.recursive_analysis = super::recursive::analyze(
            self.functions
                .iter()
                .map(|info| (info.definition, &info.syntax)),
        );
        for id in 0..functions {
            let function = self.functions[id].syntax.clone();
            self.checked_definitions
                .insert(self.functions[id].definition);
            let previous_typing = self.generic_scope(id);
            self.validate_defaults(id, self.functions[id].lexical.clone());
            if function.body.is_none() {
                for annotation in &function.annotations {
                    if annotation.kind == AnnotationKind::Effect {
                        self.effect_row(annotation);
                    }
                }
                if !self.declaration_files.contains(&function.span.file.0) {
                    self.unsupported(
                        function.span,
                        "bodyless declaration outside a checked foreign declaration unit",
                    );
                }
                self.restore_typing_environment(previous_typing);
                continue;
            }
            let mut arguments = Vec::new();
            for (index, parameter) in function.parameters.iter().enumerate() {
                let ty = parameter
                    .ty
                    .as_ref()
                    .map(|t| self.ty(t))
                    .unwrap_or(Ty::Unknown);
                let mut value =
                    self.formal_value(ty, index as u32, parameter.span, &mut BTreeSet::new());
                if parameter.mode != ParameterMode::Read && !self.formal_is_immutable(&value.ty) {
                    value.permission = Permission::Write;
                    if !value.callables.is_empty() {
                        value.mutable_environment = true;
                    }
                }
                if let Some(syntax) = &parameter.ty {
                    self.promise_array_shape(&value, syntax, &mut frame);
                }
                self.register_formal_record_schema(id, index as u32, &value, &mut frame);
                arguments.push((parameter.mode, value, parameter.span));
            }
            for a in 0..arguments.len() {
                for b in a + 1..arguments.len() {
                    if arguments[a].0 == ParameterMode::Mut || arguments[b].0 == ParameterMode::Mut
                    {
                        let left = self
                            .heap
                            .reachable(arguments[a].1.origins.nodes.iter().copied());
                        let right = self
                            .heap
                            .reachable(arguments[b].1.origins.nodes.iter().copied());
                        for x in &left {
                            for y in &right {
                                self.heap.set_relation(*x, *y, Relation::DISJOINT);
                            }
                        }
                    }
                }
            }
            let preview = self.snapshot_flow();
            let _ = self.invoke_named_declaration_probe(id, arguments, function.span);
            self.restore_definition_state(&preview);
            self.restore_typing_environment(previous_typing);
        }
        for id in frame.locals {
            self.check_authority_use(id);
        }
        for id in 0..self.closures.len() {
            if !self.checked_closures.contains(&id) {
                let span = self.closures[id].body.span;
                self.unsupported(
                    span,
                    "anonymous parameter types require a checked invocation or callable context",
                );
            }
        }
    }
    fn declarations(&mut self, statements: &[Stmt], frame: &mut Frame) {
        self.declare_lexical_bindings(statements, frame);
        let functions_before = self.functions.len();
        // Types are collected before function signatures, independent of order.
        for stmt in statements {
            if let StmtKind::Effect(effect) = &stmt.kind {
                let declaration = std::sync::Arc::new(effect.clone());
                let info = effects::EffectInfo {
                    source: stmt.hir_id,
                    syntax: declaration.clone(),
                    declaration,
                    arguments: Vec::new().into(),
                    environment: self.capture_typing_environment_with_bindings(&frame.env),
                    scope: frame.owner,
                    context: self.invocation_context(frame.callable_owner),
                };
                self.effects.insert(effect.name.clone(), info);
            }
            if let StmtKind::Type(decl) = &stmt.kind {
                self.register_type_contract_environments(decl, frame);
                self.types.insert(decl.name.clone(), decl.clone());
            }
            if let StmtKind::Function(function) = &stmt.kind {
                for item in &function.signature_where {
                    if let StmtKind::Type(decl) = &item.kind {
                        self.types.insert(decl.name.clone(), decl.clone());
                    }
                }
            }
        }
        for stmt in statements {
            match &stmt.kind {
                StmtKind::Type(decl) => {
                    let previous = self.type_source.environment.generic_context.clone();
                    for (index, generic) in decl.generics.iter().enumerate() {
                        self.type_source.environment.generic_context.insert(
                            generic.name.clone(),
                            format!(
                                "{}:{}:type:{}:{}",
                                decl.span.file.0, decl.span.start, index, generic.name
                            ),
                        );
                    }
                    self.declare_constructors(decl);
                    if let Some(ty) = &decl.value {
                        let _ = self.ty(ty);
                    }
                    self.type_source.environment.generic_context = previous;
                    if (!decl.generics.is_empty()
                        && !self.structural_alias_contract(decl)
                        && !self.external_shape_template(decl)
                        && !self.generic_constructor_contract(decl))
                        || (decl.opaque
                            && decl.value.is_none()
                            && !self.declaration_files.contains(&decl.span.file.0))
                    {
                        self.unsupported(decl.span, "generic, opaque, or sum type declaration");
                    }
                }
                StmtKind::Effect(decl) => {
                    if matches!(decl.name.as_str(), "Fiber" | "Concurrent" | "Div" | "Async") {
                        self.unsupported(decl.span,"user and system effect names require distinct canonical declaration identities");
                    }
                    if !decl.members.is_empty() && decl.generics.is_empty() {
                        let annotation = Annotation {
                            kind: AnnotationKind::Effect,
                            text: format!("@{}", decl.name),
                            span: decl.span,
                        };
                        self.effect_row(&annotation);
                    }
                    if frame.owner != ScopeId(0) {
                        self.local_effects.insert(decl.name.clone());
                    }
                    let declaration = std::sync::Arc::new(decl.clone());
                    let info = effects::EffectInfo {
                        source: stmt.hir_id,
                        syntax: declaration.clone(),
                        declaration,
                        arguments: Vec::new().into(),
                        environment: self.capture_typing_environment_with_bindings(&frame.env),
                        scope: frame.owner,
                        context: self.invocation_context(frame.callable_owner),
                    };
                    self.effects.insert(decl.name.clone(), info.clone());
                    self.declare_operations(&info);
                }
                StmtKind::Function(function) => {
                    if function.is_meta {
                        self.unsupported(function.span,"compile-time function definitions require static-family verification before runtime semantic analysis");
                    }
                    let typing_environment =
                        self.capture_typing_environment_with_bindings(&frame.env);
                    let id = self.functions.len();
                    if frame.callable_owner.is_some()
                        && stmt.hir_id.is_some()
                        && !self.application_effect.admit(1 + self.functions.len())
                    {
                        self.unsupported(
                            stmt.span,
                            "function declaration identity lookup exhausted its shared work bound",
                        );
                        return;
                    }
                    let definition =
                        declaration_definition(&self.functions, frame.callable_owner, stmt.hir_id)
                            .unwrap_or(DefinitionId(id as u32));
                    self.functions.push(FunctionInfo {
                        hir_id: stmt.hir_id,
                        definition,
                        lexical_owner: frame.callable_owner,
                        typing_environment,
                        syntax: function.clone(),
                        lexical: frame.env.clone(),
                        owner: (frame.owner != ScopeId(0)).then_some(frame.owner),
                        handler_context: self.active_handlers.clone(),
                        lexical_scope: self.block_boundaries.last().copied().unwrap_or(u32::MAX),
                        environment: None,
                        captures: BTreeSet::new(),
                        writes: BTreeSet::new(),
                        environment_published: false,
                    });
                    let previous_typing = self.generic_scope(id);
                    for item in &function.signature_where {
                        if let StmtKind::Type(decl) = &item.kind {
                            self.declare_constructors(decl);
                        }
                    }
                    for generic in &function.generics {
                        if generic.default.is_some() {
                            self.error(
                                "E0317",
                                generic.span,
                                "function generic parameters cannot declare defaults",
                                [],
                            );
                        }
                    }
                    if !self
                        .definitions
                        .iter()
                        .any(|existing| existing.id == definition)
                    {
                        self.definitions.push(Definition {
                            id: definition,
                            span: function.span,
                        });
                    }
                    let cause = self.cause(
                        CauseKind::Source,
                        function.span,
                        format!("function {}", function.name),
                        [],
                    );
                    let ty = Ty::Callable(
                        function
                            .parameters
                            .iter()
                            .map(|p| p.ty.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unknown))
                            .collect(),
                        Box::new(
                            function
                                .return_type
                                .as_ref()
                                .map(|t| self.ty(t))
                                .unwrap_or(Ty::Unit),
                        ),
                    );
                    let mut value = Value::scalar(ty, None, cause);
                    value.callables.push(Callable::Named(id));
                    value.signature = Some(self.callable_signature(function.parameters.clone()));
                    self.bind_name(
                        &function.name,
                        BindingMode::Let,
                        value,
                        bindings::BindingSite::declaration(function.span, stmt.hir_id),
                        frame,
                        false,
                    );
                    self.restore_typing_environment(previous_typing);
                }
                _ => {}
            }
        }
        if self.functions.len() != functions_before {
            self.recursive_analysis = super::recursive::analyze(
                self.functions
                    .iter()
                    .map(|info| (info.definition, &info.syntax)),
            );
        }
    }
    fn allocate(&mut self, span: Span, discriminator: u32, owner: ScopeId) -> NodeId {
        let key = (span.file.0, span.start, discriminator);
        let site = if let Some(site) = self.sites.get(&key) {
            *site
        } else {
            let site = SiteId(self.next_site);
            self.next_site = self
                .next_site
                .checked_add(1)
                .expect("semantic allocation site identity exhausted");
            self.sites.insert(key, site);
            site
        };
        self.allocate_site(span, site, owner)
    }
    pub(super) fn allocate_site(&mut self, span: Span, site: SiteId, owner: ScopeId) -> NodeId {
        // Admission precedes cause, heap and ledger growth. The infallible
        // analysis API may finish its failed branch, but poison prevents any
        // unrecorded birth from subsequently authenticating semantic evidence.
        let admitted = !self.allocation_poisoned
            && self.allocation_events.len() < u32::MAX as usize
            && self.application_effect.admit(10);
        if !admitted && !self.allocation_poisoned {
            self.allocation_poisoned = true;
            self.unsupported(
                span,
                "allocation event recording exhausted its shared work bound",
            );
        }
        let epoch_before = self.recency_moves.len();
        let cause = self.cause(CauseKind::Allocation, span, "fresh storage allocation", []);
        let (id, remap) = self.heap.fresh_in_scopes(site, owner, cause, &self.scopes);
        if admitted {
            self.allocation_events
                .push(super::allocation::AllocationEvent {
                    id: super::allocation::AllocationEventId(self.allocation_events.len() as u32),
                    site,
                    recent: id,
                    remap,
                    epoch_before,
                    cause,
                    owner,
                    anchor: self.application_effect.current_activation(),
                    position: self.application_effect.expressions.len(),
                });
        }
        if let Some((recent, older)) = remap {
            self.recency_moves.push((recent, older));
            self.remap_concurrent_identity(recent, older);
            for invocation in &mut self.invocations {
                copy::remap_summary(invocation, recent, older);
            }
            for definition in &mut self.definition_checks {
                copy::remap_summary(&mut definition.invocation, recent, older);
            }
            for origins in &mut self.active_iterations {
                origins.remap(recent, older);
            }
            if let Some(contracts::CompletedInvocation::Intrinsic(summary)) =
                &mut self.completed_invocation
            {
                copy::remap_summary(summary, recent, older);
            }
            for obligations in self.pending_handler_obligations.values_mut() {
                for access in &mut obligations.accesses {
                    access.transport(&self.recency_moves);
                }
            }
            for boundary in &mut self.parallel_boundaries {
                for callback in &mut boundary.callbacks {
                    for access in &mut callback.accesses {
                        access.transport(&self.recency_moves);
                    }
                }
            }
            for window in self.windows.values_mut() {
                window.backing.remap(recent, older);
            }
            if let Some(mut window) = self.windows.remove(&recent) {
                if let Some(previous) = self.windows.get(&older) {
                    window.backing.nodes.extend(&previous.backing.nodes);
                    window.backing.choices.clear();
                    if window.lower != previous.lower {
                        window.lower = None;
                    }
                    if window.length != previous.length {
                        window.length = None;
                    }
                }
                self.windows.insert(older, window);
            }
            if let Some(ty) = self.storage_types.remove(&recent) {
                if let Some(previous) = self.storage_types.get(&older).cloned() {
                    if !types::unify_call_types(
                        &previous,
                        &ty,
                        &BTreeSet::new(),
                        &mut BTreeMap::new(),
                    ) {
                        self.unsupported(span,"one older allocation summary contains incompatible collection instantiations");
                    }
                    self.storage_types
                        .insert(older, join_type_holes(&previous, &ty));
                } else {
                    self.storage_types.insert(older, ty);
                }
            }
            let moved: Vec<_> = self
                .fields
                .iter()
                .filter(|((node, _), _)| *node == recent)
                .map(|((_, slot), value)| (slot.clone(), value.clone()))
                .collect();
            for (slot, mut value) in moved {
                copy::remap_value_origins(&mut value, recent, older);
                if let Some(previous) = self.fields.get(&(older, slot.clone())).cloned() {
                    let cause = self.cause(
                        CauseKind::BranchJoin,
                        span,
                        "older allocation summary retains all earlier field origins",
                        [previous.cause, value.cause],
                    );
                    value = previous.join(&value, self.choice(), cause);
                }
                self.fields.insert((older, slot), value);
            }
            self.fields.retain(|(node, _), _| *node != recent);
            for value in self.fields.values_mut() {
                copy::remap_value_origins(value, recent, older);
            }
            for binding in &mut self.bindings {
                copy::remap_value_origins(&mut binding.value, recent, older);
                if binding.cell == Some(recent) {
                    binding.cell = Some(older);
                }
            }
            for (_, values) in &mut self.loop_breaks {
                for value in values {
                    copy::remap_value_origins(value, recent, older);
                }
            }
            if let Some(length) = self.array_lengths.remove(&recent) {
                let merged = match self.array_lengths.get(&older) {
                    Some(previous) if *previous != length => None,
                    _ => length,
                };
                self.array_lengths.insert(older, merged);
            }
            if self.fixed_arrays.remove(&recent) {
                self.fixed_arrays.insert(older);
            }
            for function in &mut self.functions {
                if function.environment == Some(recent) {
                    function.environment = Some(older);
                }
            }
            for closure in &mut self.closures {
                if closure.node == recent {
                    closure.node = older;
                }
            }
        }
        id
    }
    /// Used immediately after allocation; equal node IDs from another birth
    /// never select an older receipt. Exhaustion has no authenticated fallback.
    pub(super) fn last_allocation_event(
        &self,
        node: NodeId,
    ) -> Option<super::allocation::AllocationEventId> {
        let event = self.allocation_events.last()?;
        (!self.allocation_poisoned
            && event.recent == node
            && event.epoch_after() == self.recency_moves.len()
            && self
                .heap
                .nodes
                .get(node.0 as usize)
                .is_some_and(|registered| registered.cause == event.cause))
        .then_some(event.id)
    }
    fn formal_value(
        &mut self,
        ty: Ty,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) -> Value {
        if let Some(representation) = self.top_representation_type(&ty)
            && seen.insert(format!("representation:{ty:?}"))
        {
            let mut value = self.formal_value(representation, index, span, seen);
            value.ty = ty;
            return value;
        }
        if let Ty::Immutable(inner) = &ty {
            let mut value = self.formal_value(*inner.clone(), index, span, seen);
            let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
            for ((node, _), child) in &mut self.fields {
                if reachable.contains(node) {
                    freeze_formal_value(child);
                }
            }
            freeze_formal_value(&mut value);
            value.ty = ty;
            return value;
        }
        if matches!(ty, Ty::StaticKey(_)) {
            let cause = self.cause(CauseKind::Source, span, "formal static coordinate", []);
            return Value::scalar(ty, None, cause);
        }
        if let Some(value) = self.constructor_formal(&ty, index, span, seen) {
            return value;
        }
        if matches!(&ty, Ty::Result(..)) {
            return self.formal_result_graph(ty, index, span, seen);
        }
        if matches!(&ty, Ty::Optional(..)) {
            return self.formal_optional_graph(ty, index, span, seen);
        }
        let cause = self.cause(
            CauseKind::Source,
            span,
            format!("formal parameter {index}"),
            [],
        );
        if ty.scalar() {
            return Value::scalar(ty, None, cause);
        }
        let node = self
            .heap
            .symbolic(Pivot(self.heap.nodes.len() as u32), ScopeId(0), cause);
        let mut value = Value::reference(ty.clone(), node, cause);
        if matches!(&ty,Ty::Named(name)if name=="File::Handle") {
            // File state is an opaque resource identity, never a Ril variable
            // cell. It may still alias every other compatible file handle.
            for cell in self.bindings.iter().filter_map(|binding| binding.cell) {
                self.heap.set_relation(node, cell, Relation::DISJOINT);
            }
        }
        value.construction = false;
        value.publication = Publication::Live;
        self.concurrent_formal(&mut value, index, span, seen);
        if let Ty::Callable(_, _) = self.expanded(&ty, &mut BTreeSet::new()) {
            value.callables.push(Callable::Symbolic(index, vec![]));
            value.permission = Permission::Read;
        }
        let bounded_view = self.record_bound_formal_view(&ty).filter(|_| {
            let Ty::Generic(identity) = &ty else {
                return true;
            };
            seen.insert(format!("record-bound:{identity}"))
        });
        match bounded_view.unwrap_or_else(|| self.expanded(&ty, &mut seen.clone())) {
            Ty::OpenRecord { fields, row } => {
                let tail = self.formal_row_tail(&row, span);
                value.results.extend(&tail.results);
                value.must_results.extend(&tail.must_results);
                self.store_field(node, Slot::RowTail(row.identity.clone()), tail);
                for (i, (name, (_, ty))) in fields.into_iter().enumerate() {
                    let child = self.formal_value(
                        ty,
                        index.wrapping_mul(31) + i as u32 + 1,
                        span,
                        &mut seen.clone(),
                    );
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    self.store_field(node, Slot::Field(name), child);
                }
            }
            Ty::Record(fields) => {
                for (i, (name, (_, ty))) in fields.into_iter().enumerate() {
                    let mut branch = seen.clone();
                    if branch.insert(format!("{ty:?}")) {
                        let child = self.formal_value(
                            ty,
                            index.wrapping_mul(31) + i as u32 + 1,
                            span,
                            &mut branch,
                        );
                        value.results.extend(&child.results);
                        value.must_results.extend(&child.must_results);
                        self.store_field(node, Slot::Field(name), child);
                    }
                }
            }
            Ty::Tuple(items) => {
                for (i, ty) in items.into_iter().enumerate() {
                    let child = self.formal_value(
                        ty,
                        index.wrapping_mul(31) + i as u32 + 1,
                        span,
                        &mut seen.clone(),
                    );
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                    self.store_field(node, Slot::Tuple(i as u32), child);
                }
            }
            Ty::Array(ty) | Ty::Set(ty) if seen.insert(format!("{ty:?}")) => {
                let mut family = seen.clone();
                family.insert("\0optional-member-family".into());
                let child = self.formal_value(*ty, index.wrapping_mul(31) + 1, span, &mut family);
                self.mark_formal_member_family(node, &child);
                // The element family can be absent for an empty collection.
                // Its possible duties still belong to the whole carrier.
                value.results.extend(&child.results);
                self.store_field(node, Slot::AnyIndex, child);
            }
            Ty::Map(key, ty) => {
                let mut family = seen.clone();
                family.insert("\0optional-member-family".into());
                let key = self.formal_value(*key, index, span, &mut family.clone());
                let child = self.formal_value(*ty, index, span, &mut family);
                self.mark_formal_member_family(node, &key);
                self.mark_formal_member_family(node, &child);
                value.results.extend(&key.results);
                value.results.extend(&child.results);
                self.store_field(node, Slot::Field("key".into()), key);
                self.store_field(node, Slot::AnyIndex, child);
            }
            _ => {}
        }
        value
    }
    fn formal_is_immutable(&self, ty: &Ty) -> bool {
        matches!(self.representation_graph_type(ty), Ty::Immutable(_))
    }
    fn store_field(&mut self, node: NodeId, slot: Slot, value: Value) {
        self.heap.nodes[node.0 as usize]
            .fields
            .insert(slot.clone(), value.origins.nodes.clone());
        self.fields.insert((node, slot), value);
        self.refresh_window_fields();
        self.refresh_writable_roots();
    }
    fn unit(&mut self, span: Span) -> Value {
        let cause = self.cause(CauseKind::Source, span, "unit value", []);
        Value::scalar(Ty::Unit, Some(Constant::Unit), cause)
    }
    fn statement(&mut self, statement: &Stmt, frame: &mut Frame) -> Value {
        self.statement_expected(statement, frame, None)
    }
    fn statement_expected(
        &mut self,
        statement: &Stmt,
        frame: &mut Frame,
        expected: Option<&Ty>,
    ) -> Value {
        match &statement.kind {
            StmtKind::Binding(binding) => {
                if !matches!(binding.pattern.kind, PatternKind::Wildcard)
                    && expressions::binding_count(&binding.pattern) == 0
                {
                    self.error(
                        "E0309",
                        binding.pattern.span,
                        "binding pattern must introduce a variable or use the discard wildcard",
                        [],
                    );
                }
                if binding.is_meta {
                    self.unsupported(statement.span, "meta binding evaluation");
                }
                let guarded = binding.fallback.is_some()
                    || matches!(
                        binding.pattern.kind,
                        PatternKind::Constructor { .. }
                            | PatternKind::Literal(_)
                            | PatternKind::Alternative(_)
                            | PatternKind::Value(_)
                    );
                if guarded {
                    self.suppress_refinement += 1;
                }
                self.set_contract_environment(&frame.env);
                let source_target = binding
                    .ty
                    .as_ref()
                    .map(|syntax| self.freeze_source_receiving_target(syntax));
                let (value, source_valid, initializer) =
                    if matches!(binding.value.kind, ExprKind::Ambient)
                        && statement
                            .hir_id
                            .is_some_and(|id| self.semantic_hir.declaration_roots().contains(&id))
                        && binding.mode == BindingMode::Let
                        && let Some(syntax) = &binding.ty
                    {
                        let ty = self.ty(syntax);
                        self.check_external_result_shape(
                            &ty,
                            true,
                            binding.value.span,
                            &mut BTreeSet::new(),
                        );
                        let mut value = self.formal_value(
                            ty,
                            binding.value.span.start,
                            binding.value.span,
                            &mut BTreeSet::new(),
                        );
                        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
                        for ((node, _), child) in &mut self.fields {
                            if reachable.contains(node) {
                                child.permission = Permission::Read;
                                child.publication = Publication::Immutable;
                                child.construction = false;
                            }
                        }
                        value.permission = Permission::Read;
                        value.publication = Publication::Immutable;
                        value.construction = false;
                        self.promise_array_shape(&value, syntax, frame);
                        // This actual external declaration introduces its schema;
                        // it is not a cast of existing storage or a later view.
                        self.ascribe_source_type(&mut value, syntax);
                        let evaluation_context = self.invocation_context(frame.callable_owner);
                        self.record_copy_references(&value, binding.value.span, frame);
                        let environment = self.physical_evaluation_environment(binding.value.span);
                        let mut emitted = Some(value);
                        let observation = self.application_effect.observe(
                            || super::application_effect::ObservationInput {
                                allocation_epoch: self.recency_moves.len(),
                                source_id: binding.value.hir_id,
                                span: binding.value.span,
                                value: emitted.take().expect("ambient output moves once"),
                            },
                            evaluation_context,
                            frame.owner,
                            environment,
                            None,
                        );
                        let value = if let Some(observation) = observation {
                            match self.application_effect.packet_at(observation).and_then(
                                |packet| self.read_evaluation_packet(&packet, binding.value.span),
                            ) {
                                Ok(value) => value,
                                Err(error) => {
                                    self.unsupported(
                                        binding.value.span,
                                        format!("ambient physical packet admission: {error}"),
                                    );
                                    Value::scalar(Ty::Unknown, None, CauseId(0))
                                }
                            }
                        } else {
                            emitted.unwrap_or_else(|| Value::scalar(Ty::Unknown, None, CauseId(0)))
                        };
                        (value, observation.is_some(), observation)
                    } else {
                        self.set_contract_environment(&frame.env);
                        let expected = binding.ty.as_ref().map(|syntax| self.ty(syntax));
                        let received = self.expression_expected_source(
                            &binding.value,
                            frame,
                            expected.as_ref(),
                            source_target.as_ref(),
                        );
                        let observation = received.observation;
                        (received.value, received.source_valid, observation)
                    };
                let initializer =
                    initializer.map(|expression| super::storage_sources::StorageObservation {
                        expression,
                        allocation_epoch: self.recency_moves.len(),
                    });
                if guarded {
                    self.suppress_refinement -= 1;
                }
                if value.ty == Ty::Never {
                    if binding.ty.is_none()
                        && (value.requires_inference
                            || !self.pending_result_binders(&value).is_empty())
                    {
                        self.error(
                            "E0344",
                            binding.value.span,
                            "abrupt initializer has unresolved result type variables",
                            [value.cause],
                        );
                    }
                    return value;
                }
                self.receive_binding(
                    binding,
                    value,
                    initializer,
                    source_target.as_ref(),
                    source_valid,
                    frame,
                )
            }
            StmtKind::Assignment {
                target,
                operator,
                value,
            } => {
                let (evaluated, rhs_expression) = self.expression_observed(value, frame);
                if evaluated.ty == Ty::Never {
                    return evaluated;
                }
                let rhs =
                    rhs_expression.map(|expression| super::storage_sources::StorageObservation {
                        expression,
                        allocation_epoch: self.recency_moves.len(),
                    });
                if let Some(abrupt) = self.assign(target, operator, value, evaluated, rhs, frame) {
                    return abrupt;
                }
                self.unit(statement.span)
            }
            StmtKind::Expr {
                expression,
                terminated,
            } => {
                let created_closures = self.closures.len();
                let created_named = self.copy_invocations.len();
                let value = self.expression_expected(
                    expression,
                    frame,
                    if *terminated { None } else { expected },
                );
                if *terminated {
                    let pending = self.pending_result_binders(&value);
                    if (value.requires_inference && pending.is_empty())
                        || !self.unresolved_inference_metas(pending).is_empty()
                        || self.unresolved_empty_map_keys(&value)
                    {
                        self.error(
                            "E0344",
                            expression.span,
                            "discarded expression has unresolved result type variables",
                            [value.cause],
                        );
                    }
                }
                if *terminated && value.ty != Ty::Never {
                    self.record_closure_discard(
                        &value,
                        created_closures,
                        created_named,
                        frame,
                        expression.span,
                    );
                    self.unit(statement.span)
                } else {
                    value
                }
            }
            StmtKind::Use(_) => {
                self.unsupported(statement.span, "module import resolution");
                self.unit(statement.span)
            }
            StmtKind::Handler(arms) => {
                self.register_handler(arms, statement.span, frame);
                self.unit(statement.span)
            }
            StmtKind::HandlerApplication(_) => {
                self.unsupported(
                    statement.span,
                    "parameterized handler application requires continuation typing",
                );
                self.unit(statement.span)
            }
            _ => self.unit(statement.span),
        }
    }
    fn block(&mut self, block: &Block, frame: &mut Frame) -> Value {
        self.block_expected(block, frame, None)
    }
    fn statement_expected_source(
        &mut self,
        statement: &Stmt,
        frame: &mut Frame,
        expected: Option<&Ty>,
        source: Option<&super::source_reception::Target>,
    ) -> expressions::SourceExpression {
        if source.is_some()
            && let StmtKind::Expr {
                expression,
                terminated: false,
            } = &statement.kind
        {
            return self.expression_expected_source(expression, frame, expected, source);
        }
        expressions::SourceExpression::unobserved(
            self.statement_expected(statement, frame, expected),
            self.recency_moves.len(),
            true,
        )
    }

    fn block_expected(&mut self, block: &Block, frame: &mut Frame, expected: Option<&Ty>) -> Value {
        self.block_expected_source(block, frame, expected, None)
            .value
    }

    fn block_expected_source(
        &mut self,
        block: &Block,
        frame: &mut Frame,
        expected: Option<&Ty>,
        source: Option<&super::source_reception::Target>,
    ) -> expressions::SourceExpression {
        let definitions = self.functions.len();
        let boundary = self.next_boundary;
        self.next_boundary += 1;
        self.block_boundaries.push(boundary);
        let handlers = self.active_handlers.len();
        let old_env = frame.env.clone();
        let start = frame.locals.len();
        self.declarations(&block.statements, frame);
        self.declarations(&block.where_items, frame);
        self.window_blocks.push(windows::WindowBlockUses {
            statements: block.statements.clone(),
            next: 0,
            environment: frame.env.clone(),
            repeated: self.loop_depth > 0,
        });
        let mut value = self.unit(block.span);
        let mut source_valid = true;
        for (position, statement) in block.statements.iter().enumerate() {
            if let Some(context) = self.window_blocks.last_mut() {
                context.next = position + 1;
                context.environment = frame.env.clone();
            }
            if !matches!(
                statement.kind,
                StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
            ) {
                let before = (!self.active_handlers.is_empty() && !self.effect_answer_probe)
                    .then(|| self.snapshot_flow());
                let prior_frame = frame.clone();
                let received = self.statement_expected_source(
                    statement,
                    frame,
                    if position + 1 == block.statements.len() {
                        expected
                    } else {
                        None
                    },
                    if position + 1 == block.statements.len() {
                        source
                    } else {
                        None
                    },
                );
                value = received.value;
                source_valid &= received.source_valid;
                if value.ty == Ty::Never {
                    if let Some(before) = before
                        && self
                            .pending_abort
                            .as_ref()
                            .is_some_and(|(target, _)| *target == boundary)
                    {
                        self.probe_handler_answer(
                            &before,
                            &prior_frame,
                            &block.statements[position..],
                            frame,
                            block.span,
                        );
                    }
                    let remaining: Vec<_> = block.statements[position + 1..]
                        .iter()
                        .filter(|statement| {
                            !matches!(
                                statement.kind,
                                StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
                            )
                        })
                        .cloned()
                        .collect();
                    if !remaining.is_empty()
                        && (self.universal || !matches!(statement.kind, StmtKind::Binding(_)))
                    {
                        // Unreachable source still receives static checks.
                        // Use the complete preview transaction so it cannot
                        // change this activation's continuing runtime state.
                        self.preview_block_source(
                            &Block {
                                span: block.span,
                                statements: remaining,
                                where_items: Vec::new(),
                            },
                            frame,
                            expected,
                            source,
                        );
                    }
                    break;
                }
            }
        }
        let mut received_value = EvaluatedValue::new(value.clone(), self.recency_moves.len());
        self.verify_local_definitions(definitions, frame);
        self.check_local_effect_boundary(block, &old_env, &value, frame);
        self.window_blocks.pop();
        self.exit_cleanups(start, &value, block.span, frame);
        self.finish_deferred_cleanups(boundary, frame, block.span, &mut value, start);
        self.finish_budget_recoveries(boundary, &mut value);
        self.finish_foreign_abort_exits(boundary, &mut value);
        if self
            .pending_abort
            .as_ref()
            .is_some_and(|(target, _)| *target == boundary)
        {
            value = self.pending_abort.take().unwrap().1;
        }
        if source.is_some_and(|target| {
            target.sensitivity != super::source_reception::SchemaSensitivity::NotRequired
        }) && value.ty != Ty::Never
        {
            let original = received_value.current(&self.recency_moves);
            let same_schema = match (&original.source_type_witness, &value.source_type_witness) {
                (Some(original), Some(current)) => original == current,
                _ => original.same_abstract_value(&value),
            };
            if !same_schema {
                self.unsupported(
                    block.span,
                    "a replaced block answer requires its own original source receiving proof",
                );
                source_valid = false;
                frame.return_source_valid = false;
            }
        }
        self.record_handler_answer(boundary, &value.ty);
        self.active_handlers.truncate(handlers);
        self.block_boundaries.pop();
        if !self.resuming_arm(frame.owner) {
            for &binding in &frame.locals[start..] {
                self.check_authority_use(binding);
                self.bindings[binding].alive = false;
            }
        }
        if value.permission == Permission::Write
            && self.pending_copy_dependencies(&value).is_empty()
            && value.publication != Publication::Immutable
            && !value.origins.nodes.is_empty()
            && !self.has_writer(&value)
            && !value.mutable_environment
            && !value.observer_environment
        {
            value.construction = true;
            value.publication = Publication::Unpublished;
        }
        frame.env = old_env;
        expressions::SourceExpression::unobserved(value, self.recency_moves.len(), source_valid)
    }
    fn access(
        &mut self,
        value: &Value,
        slot: Option<Slot>,
        mode: Mode,
        span: Span,
        frame: &mut Frame,
    ) {
        let pending = self.pending_copy_dependencies(value);
        frame.obligations.copy_boundaries.extend(&pending);
        if !pending.is_empty() && mode != Mode::Read {
            self.require_copy_dependencies(value, span, "write or retention authority");
        }
        if mode == Mode::Write {
            self.note_refinement_write(value, &slot, false);
            self.invalidate_refinement_access(value, &slot, false);
        }
        for &source in &value.sources {
            self.use_binding(source, mode, frame);
        }
        frame.obligations.accesses.push(AccessFact {
            observed_recency: self.recency_moves.len(),
            recency: self.recency_moves.len(),
            origin_owners: self.access_owners(&value.origins),
            origins: value.origins.clone(),
            slot,
            mode,
            participants: value.participants.clone(),
            cause: value.cause,
            span,
        });
    }
    fn deep_read(&mut self, value: &Value, span: Span, frame: &mut Frame) {
        self.check_deep_uncertainty(value, span);
        for node in self.heap.reachable(value.origins.nodes.iter().copied()) {
            let mut nested = value.clone();
            nested.origins = Origins::one(node);
            nested.cause = self.cause(
                CauseKind::Projection,
                span,
                "deep read reaches a possibly shared nested storage origin",
                [value.cause],
            );
            self.access(&nested, None, Mode::Read, span, frame);
        }
    }
    fn origins_disjoint(&self, a: &Origins, b: &Origins) -> bool {
        for (choice, left) in &a.choices {
            if let Some(right) = b.choices.get(choice)
                && left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(a, b)| self.nodes_disjoint(a, b))
            {
                return true;
            }
        }
        self.nodes_disjoint(&a.nodes, &b.nodes)
    }
    fn nodes_disjoint(&self, a: &BTreeSet<NodeId>, b: &BTreeSet<NodeId>) -> bool {
        a.iter().all(|a| {
            b.iter()
                .all(|b| self.heap.relation(*a, *b).disjoint == Condition::TRUE)
        })
    }
    fn project(
        &mut self,
        base: &Value,
        slot: Slot,
        span: Span,
        frame: &mut Frame,
        read: bool,
    ) -> Value {
        let mut value = self.project_copy_source(base, slot.clone(), span, frame, read);
        self.project_source_type(base, &slot, &mut value);
        value.inherit_copy_dependencies(&self.pending_copy_dependencies(base));
        self.record_bound_projection(
            base,
            &slot,
            &value,
            if read {
                super::record_bounds::BoundAccess::Read
            } else {
                super::record_bounds::BoundAccess::ValueOnly
            },
            frame,
            span,
        );
        value
    }
    fn project_copy_source(
        &mut self,
        base: &Value,
        slot: Slot,
        span: Span,
        frame: &mut Frame,
        read: bool,
    ) -> Value {
        if let Some(value) = self.window_projection(base, &slot, span, frame, read) {
            return value;
        }
        if matches!(self.expanded_at(&base.ty, span.file), Ty::Result(..)) {
            let Some(success) = base.result_tag else {
                self.error(
                    "E0337",
                    span,
                    "Result payload projection requires a dominating constructor proof",
                    [base.cause],
                );
                return self.unit(span);
            };
            let payload = self.result_payload(base, success, span, frame);
            let payload_shape = self.expanded(&payload.ty, &mut BTreeSet::new());
            let product = matches!(&payload_shape, Ty::Tuple(_) | Ty::Record(_));
            let valid = match (&payload_shape, &slot) {
                (Ty::Tuple(_), Slot::Tuple(_)) | (Ty::Record(_), Slot::Field(_)) => true,
                (_, Slot::Tuple(0)) if !product => true,
                _ => false,
            };
            if !valid {
                self.error(
                    "E0337",
                    span,
                    "coordinate is absent from the proved Result payload",
                    [base.cause],
                );
                return self.unit(span);
            }
            self.record_variant_projection(
                frame.callable_owner,
                span,
                super::VariantProjection {
                    tag: if success { "Ok".into() } else { "Err".into() },
                    cause: base.cause,
                    direct: !product,
                },
            );
            return if product {
                self.project(&payload, slot, span, frame, read)
            } else {
                payload
            };
        }
        if let Some(value) = self.constructor_projection(base, &slot, span, frame) {
            return value;
        }
        if matches!(self.expanded_at(&base.ty, span.file), Ty::Optional(_)) {
            self.error(
                self.optional_error_code(base),
                span,
                "optional receiver requires a proven Some refinement before projection",
                [base.cause],
            );
            return Value::scalar(Ty::Unknown, None, base.cause);
        }
        if let Ty::Named(name) = &base.ty
            && (self.types.get(name).is_some_and(|decl| decl.opaque)
                || self.foreign_opaque_type(&base.ty))
        {
            self.error(
                "E0907",
                span,
                "opaque foreign storage cannot be structurally inspected",
                [base.cause],
            );
            return Value::scalar(Ty::Unknown, None, base.cause);
        }
        if read {
            self.access(base, Some(slot.clone()), Mode::Read, span, frame);
        }
        let receiver = if let Some(receiver) = self.record_bound_receiver_view(&base.ty) {
            receiver
        } else {
            let Some(shape) = self.projection_shape_at(&base.ty, span.file) else {
                self.unsupported(
                    span,
                    "projection receiver alias expansion work bound exceeded",
                );
                return Value::scalar(Ty::Unknown, None, base.cause);
            };
            self.refine_storage_type(base, shape)
        };
        let valid = match &receiver {
            Ty::Record(_) | Ty::OpenRecord { .. } => matches!(slot, Slot::Field(_)),
            Ty::Tuple(_) => matches!(slot, Slot::Tuple(_)),
            Ty::Array(_) | Ty::Set(_) | Ty::Range(_) => {
                matches!(slot, Slot::Index(_) | Slot::AnyIndex)
            }
            Ty::Map(..) => {
                matches!(&slot, Slot::Index(_) | Slot::AnyIndex)
                    || matches!(&slot,Slot::Field(name)if name=="key")
            }
            _ => false,
        };
        if !valid {
            self.error(
                "E0337",
                span,
                "receiver and projection coordinate kinds do not match",
                [base.cause],
            );
            return Value::scalar(Ty::Unknown, None, base.cause);
        }
        if let (Ty::Tuple(items), Slot::Tuple(index)) = (&receiver, &slot)
            && *index as usize >= items.len()
        {
            self.error(
                "E0312",
                span,
                "tuple projection is outside its arity",
                [base.cause],
            );
            return Value::scalar(Ty::Unknown, None, base.cause);
        }
        let expected = match receiver {
            Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                if let Slot::Field(name) = &slot {
                    fields.get(name).map(|(_, ty)| ty.clone())
                } else {
                    None
                }
            }
            Ty::Tuple(items) => {
                if let Slot::Tuple(i) = slot {
                    items.get(i as usize).cloned()
                } else {
                    None
                }
            }
            Ty::Array(ty) | Ty::Range(ty) | Ty::Set(ty) => Some(*ty),
            Ty::Map(key, value) => Some(if matches!(&slot,Slot::Field(name)if name=="key") {
                *key
            } else {
                *value
            }),
            _ => None,
        };
        let mut values = Vec::new();
        if base.origins.nodes.iter().any(|node| {
            self.uncertain_slots.iter().any(|(parent, changed)| {
                parent == node
                    && (changed == &slot
                        || matches!(changed, Slot::AnyIndex)
                        || matches!(slot, Slot::AnyIndex))
            })
        }) {
            self.unsupported(span,"read of reference-bearing storage changed by an unknown callable requires a heap transfer summary");
        }
        for node in &base.origins.nodes {
            if !matches!(slot, Slot::AnyIndex)
                && let Some(value) = self.fields.get(&(*node, slot.clone()))
            {
                values.push(value.clone());
            } else if matches!(slot, Slot::Index(_) | Slot::AnyIndex) {
                for ((parent, child_slot), value) in &self.fields {
                    if parent == node && matches!(child_slot, Slot::Index(_) | Slot::AnyIndex) {
                        values.push(value.clone());
                    }
                }
            }
        }
        let mut value = if let Some(first) = values.first() {
            let mut joined = first.clone();
            for next in &values[1..] {
                joined = joined.join(next, self.choice(), base.cause);
            }
            joined
        } else if let Some(ty) = expected.clone() {
            let mut value = self.formal_value(ty, span.start, span, &mut BTreeSet::new());
            value.permission = Permission::Read;
            value.construction = false;
            value
        } else {
            self.error("E0336", span, "value has no such member", [base.cause]);
            Value::scalar(Ty::Unknown, None, base.cause)
        };
        if let Some(ty) = expected
            && ty != Ty::Unknown
        {
            value.ty = ty;
        }
        let (immutable, selected) = match &value.ty {
            Ty::Immutable(inner) => (true, *inner.clone()),
            ty => (false, ty.clone()),
        };
        let selected = self.refine_storage_type(&value, selected);
        value.ty = if immutable {
            Ty::Immutable(Box::new(selected))
        } else {
            selected
        };
        for (&choice, branches) in &base.origins.choices {
            let branches: Vec<_> = branches
                .iter()
                .map(|parents| {
                    parents
                        .iter()
                        .flat_map(|node| {
                            self.fields
                                .get(&(*node, slot.clone()))
                                .into_iter()
                                .flat_map(|v| v.origins.nodes.iter().copied())
                        })
                        .collect()
                })
                .collect();
            value.origins.choices.insert(choice, branches);
        }
        value.permission = value.permission.meet(base.permission);
        value.construction &= base.construction;
        value.publication = if value.publication == Publication::Immutable
            || base.publication == Publication::Immutable
        {
            Publication::Immutable
        } else if base.publication == Publication::Live {
            Publication::Live
        } else {
            value.publication
        };
        if !value.origins.nodes.is_empty() {
            value.temporary |= base.temporary;
        }
        value.stable &= base.stable;
        if base.publication == Publication::Immutable {
            value.publication = Publication::Immutable;
        }
        value.sources = base.sources.clone();
        value.static_coordinate = None;
        value.callback_parameters.extend(&base.callback_parameters);
        if !value.ty.scalar() {
            value.scoped.extend(&base.scoped);
        }
        value.participants = base.participants.clone();
        value.marker = base.marker || (base.construction && value.marker);
        value.retention_result =
            base.retention_result || (base.construction && value.retention_result);
        value.through_return |= base.through_return;
        if value.ty.scalar() {
            value.unsuffixed_numeric = false;
            value.participants.clear();
            value.temporary = false;
            value.scoped.clear();
        }
        if !matches!(slot, Slot::AnyIndex) {
            self.project_immutable_result_presence(base, &slot, &mut value);
            value.must_outer_results = value
                .outer_results
                .intersection(&value.must_results)
                .copied()
                .collect();
        }
        value.cause = self.cause(
            CauseKind::Projection,
            span,
            "project stored constituent through its access path",
            [base.cause, value.cause],
        );
        value
    }
}
