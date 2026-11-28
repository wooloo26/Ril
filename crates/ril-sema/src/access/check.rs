use std::collections::{BTreeMap, BTreeSet};

use ril_hir::{DefinitionId, DefinitionKind, Resolution};
use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_syntax::syntax::{
    Ast, Condition, Expr, ExprId, Function, LiteralKind, MatchArm, Member, Mode, Path, Pattern,
    PatternId, Signature, StateKind, StmtId, StmtKind, Storage, Transfer, TypeDefinition,
};

use super::{
    Access, Analysis, CallbackModeCall, EffectUse, Input, Invocation, InvocationMode, ReturnSource,
    StorageUpdate, Summary, ViaDomain,
    flow::{
        AccessConflict, ConflictKind, Coordinate, Datum, Ledger, LinearOccurrence, Origin,
        Reception, Region, Replacement, ResultOccurrence, Slot, StorageFlow, conflicts,
    },
    horn::{self, Rule},
};
use crate::ty::{self, AdtKind, Callable, Ty, TypedProgram, Value};

mod calls;
mod domains;
mod higher_order;
mod results;
mod snapshots;
mod storage;

mod control;
mod effects;
mod expr;
mod functions;
mod places;
mod reception;
mod via_summary;
use via_summary::{collect_axes, member_axes};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Obligation {
    Write(Span),
    WriteExisting(Span),
    Schema(Region, SchemaRequirement),
    Replace(Span),
    SharedReception(Span),
    Retain(Span),
    Share(Span),
    StoreShare(Span),
    NeedsSharing(Span),
    ReadUp(Span),
    Invoke(Span),
    Capture,
    StatefulHandler,
    CtlHandler,
    Effect(String),
    EffectVar(DefinitionId),
    OpenEffect,
    DirectOpenEffect,
    Operation(Operation),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SchemaRequirement {
    Writable,
    Exclusive,
    Shared,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LoopExtent {
    Exact(usize),
    Repeat,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum BindingSite {
    Declaration,
    ScopedPattern,
}

impl SchemaRequirement {
    fn accepts(self, access: Access) -> bool {
        match self {
            Self::Writable => access.writes(),
            Self::Exclusive => access == Access::Mut,
            Self::Shared => access == Access::Shared,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Operation {
    id: DefinitionId,
    effect: String,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Fact {
    owner: Span,
    obligation: Obligation,
}

#[derive(Clone)]
struct DeferredAction {
    expr: ExprId,
    span: Span,
    file: FileId,
    handlers: BTreeMap<Operation, Datum>,
    holds_len: usize,
    ctl_boundary: Option<Span>,
}

#[derive(Clone)]
struct Context {
    owner: Span,
    file: FileId,
    scope: Span,
    hir_scope: Option<ril_hir::ScopeId>,
    formals: Vec<Option<Span>>,
    caller_slots: BTreeSet<Span>,
    caller_sources: BTreeSet<Span>,
    capture_modes: Option<BTreeMap<Span, Mode>>,
    new_formals: BTreeSet<Span>,
    via: BTreeSet<Span>,
    member_via: bool,
    handlers: BTreeMap<Operation, Datum>,
    local_effects: BTreeSet<String>,
    defers: Vec<DeferredAction>,
    no_ctl: Option<Span>,
    ctl_boundary: Option<Span>,
    loop_defer_depth: Option<usize>,
    expected: Mode,
    returns: Vec<Span>,
    declared_contained: Vec<(Access, Span)>,
    return_values: Vec<Datum>,
    return_guards: Vec<ExprId>,
    loop_owner: Option<Span>,
    reachable: bool,
    shadow: bool,
    in_function: bool,
    runtime: bool,
}

impl Context {
    fn new(owner: Span) -> Self {
        Self {
            owner,
            file: owner.file,
            scope: owner,
            hir_scope: None,
            formals: Vec::new(),
            caller_slots: BTreeSet::new(),
            caller_sources: BTreeSet::new(),
            capture_modes: None,
            new_formals: BTreeSet::new(),
            via: BTreeSet::new(),
            member_via: false,
            handlers: BTreeMap::new(),
            local_effects: BTreeSet::new(),
            defers: Vec::new(),
            no_ctl: None,
            ctl_boundary: None,
            loop_defer_depth: None,
            expected: Mode::Plain,
            returns: Vec::new(),
            declared_contained: Vec::new(),
            return_values: Vec::new(),
            return_guards: Vec::new(),
            loop_owner: None,
            reachable: true,
            shadow: false,
            in_function: false,
            runtime: true,
        }
    }

    fn set_caller_storage(&mut self, outer: &Ledger) {
        self.caller_slots.extend(outer.slots.keys().copied());
        for slot in outer.slots.values() {
            self.caller_sources.extend(
                outer
                    .loop_snapshot(&slot.value)
                    .origins()
                    .map(|origin| origin.region.source),
            );
        }
    }

    fn mark_capture(&self, slot: &Slot, value: &mut Datum) {
        if !self.caller_slots.contains(&slot.decl) {
            return;
        }
        let mode = match &self.capture_modes {
            Some(modes) => modes.get(&slot.decl).copied(),
            None => Some(slot.mode),
        };
        if let Some(mode @ (Mode::Mut | Mode::Shared)) = mode {
            value.enter_capture(
                self.owner,
                slot.decl,
                mode,
                self.capture_modes.is_none(),
                &self.caller_sources,
            );
        }
    }
}

struct Requirement {
    fact: Fact,
    span: Span,
    message: &'static str,
}

struct CaptureConflict {
    conditions: Vec<(Fact, bool)>,
    code: Code,
    span: Span,
    message: &'static str,
}

struct DefinitionCheck {
    owner: Span,
    id: DefinitionId,
    formals: Vec<Option<Span>>,
    declared: Callable,
    return_sources: Vec<ReturnSource>,
    returns: Vec<Datum>,
    updates: BTreeMap<Region, Replacement>,
    storage_flow: Option<StorageFlow>,
    normal_exit: bool,
    via: BTreeSet<Span>,
    member_axes: Vec<(usize, Region)>,
    returned_new: bool,
    capture_names: BTreeSet<Span>,
    outer_slots: BTreeMap<Span, (bool, Mode)>,
    is_meta: bool,
    has_holes: bool,
    has_pruned_meta: bool,
}

#[derive(Clone, Debug)]
struct CallEdge {
    caller_owner: Span,
    callee_owner: Span,
    handled_ops: BTreeSet<Operation>,
}

struct ModeUse {
    span: Span,
    callee: DefinitionId,
    choices: Vec<(usize, Input, Span)>,
}

#[derive(Clone)]
struct ClosureModes {
    formals: Vec<Option<Span>>,
    via: BTreeSet<Span>,
    member_axes: Vec<(usize, Region)>,
    returns: Vec<Datum>,
    updates: BTreeMap<Region, Replacement>,
    storage_flow: Option<StorageFlow>,
    models_publication: bool,
    captures: Vec<(Span, bool)>,
}

#[derive(Default)]
struct LoopTransfers {
    breaks: Vec<Ledger>,
    continues: Vec<Ledger>,
}

struct LoopSyntax {
    owner: Span,
    repeated: Span,
    body: ExprId,
    extent: LoopExtent,
    exact_elements: bool,
}

struct Analyzer<'a> {
    program: &'a TypedProgram,
    diagnostics: Vec<Diagnostic>,
    rules: Vec<Rule<Fact>>,
    requirements: Vec<Requirement>,
    deferred_errors: Vec<(Vec<Fact>, Diagnostic)>,
    capture_conflicts: Vec<CaptureConflict>,
    mode_constraints: Vec<domains::ModeConstraint>,
    mode_applications: Vec<domains::Application>,
    mode_uses: Vec<ModeUse>,
    member_schemas: BTreeMap<Span, Vec<Region>>,
    closure_modes: BTreeMap<Span, ClosureModes>,
    closure_captures: BTreeMap<Span, Vec<(Span, Mode)>>,
    higher_order: higher_order::Calls,
    snapshots: snapshots::Checks,
    snapshot_invocations: Vec<calls::SnapshotInvocation>,
    snapshot_call_summaries: BTreeMap<Span, BTreeSet<super::SnapshotCall>>,
    snapshot_providers: calls::SnapshotProviders,
    invocation_summaries: BTreeMap<Span, BTreeSet<Invocation>>,
    mode_call_summaries: BTreeMap<Span, BTreeSet<CallbackModeCall>>,
    callback_results: Vec<calls::CallbackResult>,
    loop_transfers: BTreeMap<Span, LoopTransfers>,
    binding_scopes: BTreeMap<Span, Span>,
    storage_exits: BTreeMap<Span, Vec<storage::StorageExit>>,
    recursive_storage: BTreeMap<Span, storage::CallStorage>,
    recursive_calls: BTreeSet<Span>,
    resolving_callback_results: BTreeSet<usize>,
    resolving_interface_results: BTreeSet<Span>,
    replaying_storage: BTreeSet<(Span, storage::ReplaySite)>,
    storage_read_sites: BTreeMap<storage::ReadSite, usize>,
    functions: Vec<DefinitionCheck>,
    call_edges: Vec<CallEdge>,
    done: BTreeSet<DefinitionId>,
    checked_defers: BTreeSet<Span>,
    generic_linear_calls: Vec<(DefinitionId, Span)>,
}

fn collect(
    program: &TypedProgram,
    recursive_storage: BTreeMap<Span, storage::CallStorage>,
    storage_read_sites: BTreeMap<storage::ReadSite, usize>,
) -> Analyzer<'_> {
    let mut analyzer = Analyzer {
        program,
        diagnostics: Vec::new(),
        rules: Vec::new(),
        requirements: Vec::new(),
        deferred_errors: Vec::new(),
        capture_conflicts: Vec::new(),
        mode_constraints: Vec::new(),
        mode_applications: Vec::new(),
        mode_uses: Vec::new(),
        member_schemas: BTreeMap::new(),
        closure_modes: BTreeMap::new(),
        closure_captures: BTreeMap::new(),
        higher_order: higher_order::Calls::default(),
        snapshots: snapshots::Checks::default(),
        snapshot_invocations: Vec::new(),
        snapshot_call_summaries: BTreeMap::new(),
        snapshot_providers: calls::SnapshotProviders::default(),
        invocation_summaries: BTreeMap::new(),
        mode_call_summaries: BTreeMap::new(),
        callback_results: Vec::new(),
        loop_transfers: BTreeMap::new(),
        binding_scopes: BTreeMap::new(),
        storage_exits: BTreeMap::new(),
        recursive_storage,
        recursive_calls: BTreeSet::new(),
        resolving_callback_results: BTreeSet::new(),
        resolving_interface_results: BTreeSet::new(),
        replaying_storage: BTreeSet::new(),
        storage_read_sites,
        functions: Vec::new(),
        call_edges: Vec::new(),
        done: BTreeSet::new(),
        checked_defers: BTreeSet::new(),
        generic_linear_calls: Vec::new(),
    };
    analyzer.load_interface_calls();
    for file in program.hir.files() {
        let mut ledger = Ledger::default();
        let mut context = Context::new(Span::new(file.id, 0, 0));
        for &item in &file.ast.items {
            analyzer.statement(&mut context, &mut ledger, item, false);
        }
        analyzer.check_results(&ledger, &BTreeSet::new());
        analyzer.check_linear(&ledger, &BTreeSet::new());
    }
    analyzer
}

pub(super) fn analyze_with_mode(
    program: &TypedProgram,
    mode: super::AnalysisMode,
) -> (Analysis, Vec<Diagnostic>) {
    let mut analyzer = storage::solve_recursive_storage(program);
    analyzer.link_higher_order_calls();
    analyzer.check_snapshot_calls();
    let facts = horn::solve(&analyzer.rules);
    let fix_closure = if mode == super::AnalysisMode::Fix {
        Some(analyzer.solve_fix_effect_closure(&facts))
    } else {
        None
    };
    for conflict in std::mem::take(&mut analyzer.capture_conflicts) {
        if conflict
            .conditions
            .iter()
            .all(|(fact, expected)| facts.contains(fact) == *expected)
        {
            analyzer.error(conflict.code, conflict.span, conflict.message);
        }
    }
    for (premises, diagnostic) in std::mem::take(&mut analyzer.deferred_errors) {
        if premises.iter().all(|fact| facts.contains(fact))
            && !analyzer.diagnostics.iter().any(|reported| {
                reported.code == diagnostic.code && reported.primary == diagnostic.primary
            })
        {
            analyzer.diagnostics.push(diagnostic);
        }
    }
    let mut analysis = Analysis {
        horn_rules: horn::oracle_input(&analyzer.rules),
        ..Analysis::default()
    };
    for (&definition, import) in &program.imported_functions {
        analysis
            .summaries
            .insert(definition, import.summary.clone());
        if !import.domain.is_empty() {
            analysis.via.insert(definition, import.domain.clone());
        }
    }
    for requirement in std::mem::take(&mut analyzer.requirements) {
        if !facts.contains(&requirement.fact) {
            analyzer.error(Code::E0527, requirement.span, requirement.message);
        }
    }
    let mut sharing_inputs = BTreeMap::new();
    let mut domains = domains::Domains::default();
    let functions = std::mem::take(&mut analyzer.functions);
    let owner_names: BTreeMap<Span, String> = if fix_closure.is_some() {
        functions
            .iter()
            .map(|f| (f.owner, program.hir.definition(f.id).name.value.clone()))
            .collect()
    } else {
        BTreeMap::new()
    };
    for function in functions {
        let summary = analyzer.finish_function(&facts, &function);
        if let Some((fix_rules, fix_facts, derived_by)) = &fix_closure
            && !program.hir.is_stdlib_file(function.owner.file)
        {
            let inferred = analyzer.build_inferred_signature(
                &function,
                &summary,
                &facts,
                fix_rules,
                fix_facts,
                derived_by,
                &owner_names,
            );
            analysis
                .fix_meta
                .inferred_sigs
                .insert(function.id, inferred);
        }
        let instances = analyzer.via_table(&function, &summary, &facts);
        let sharing: BTreeSet<_> = function
            .formals
            .iter()
            .enumerate()
            .filter_map(|(index, formal)| {
                formal
                    .filter(|&span| {
                        facts.contains(&Fact {
                            owner: function.owner,
                            obligation: Obligation::NeedsSharing(span),
                        })
                    })
                    .map(|_| index)
            })
            .collect();
        sharing_inputs.insert(function.id, sharing);
        if !instances.is_empty() {
            domains.register_function(program, &function, &instances);
            analysis.via.insert(function.id, instances);
        }
        analysis.summaries.insert(function.id, summary);
    }
    for use_site in std::mem::take(&mut analyzer.mode_uses) {
        if !program.hir.is_stdlib_file(use_site.span.file) {
            analysis.via_calls.push(super::ViaCallSite {
                span: use_site.span,
                callee: use_site.callee,
                choices: use_site
                    .choices
                    .iter()
                    .map(|&(idx, mode, _)| (idx, mode))
                    .collect(),
            });
        }
        let Some(summary) = analysis.summaries.get(&use_site.callee) else {
            continue;
        };
        for (index, mode, span) in use_site.choices {
            if mode != Input::Shared
                && (summary.retained.contains(&index)
                    || sharing_inputs
                        .get(&use_site.callee)
                        .is_some_and(|indices| indices.contains(&index)))
            {
                analyzer.error(
                    Code::E0520,
                    span,
                    "via application requires shared writable reception",
                );
            } else if summary.writes.contains(&index) && matches!(mode, Input::Plain | Input::Ref) {
                analyzer.error(
                    Code::E0520,
                    span,
                    "via application requires a writable source",
                );
            }
        }
    }
    for (callee_id, call_span) in std::mem::take(&mut analyzer.generic_linear_calls) {
        let Some(summary) = analysis.summaries.get(&callee_id) else {
            continue;
        };
        if summary.forbids_linear_drop.is_empty()
            && summary.forbids_linear_dup.is_empty()
            && summary.forbids_linear_suspend.is_empty()
        {
            continue;
        }
        let Some(type_args) = program.type_arguments.get(&call_span) else {
            continue;
        };
        let Some(fun) = analyzer.function_syntax(callee_id) else {
            continue;
        };
        for (idx, param) in fun.generics.iter().enumerate() {
            let Some(param_id) = analyzer.definition(param.name.span) else {
                continue;
            };
            let Some(concrete) = type_args.get(&param_id) else {
                continue;
            };
            if !program.is_must_consume(concrete) {
                continue;
            }
            if summary.forbids_linear_dup.contains(&idx) {
                analyzer.error(
                    Code::E0548,
                    call_span,
                    "cannot instantiate generic parameter with must-consume type where value may be duplicated or projected",
                );
            } else if summary.forbids_linear_drop.contains(&idx) {
                analyzer.error(
                    Code::E0625,
                    call_span,
                    "cannot instantiate generic parameter with must-consume type where value may be dropped",
                );
            } else if summary.forbids_linear_suspend.contains(&idx) {
                analyzer.error(
                    Code::E0625,
                    call_span,
                    "cannot instantiate generic parameter with must-consume type held across unhandled ctl",
                );
            }
        }
    }
    analyzer.restrict_mode_domains(&facts, &mut domains, &mut analysis);
    analysis.closure_captures = std::mem::take(&mut analyzer.closure_captures);
    analysis.behavior = crate::behavior::analyze(program, &analysis);
    for site in &analysis.behavior.defer_panics {
        let mut diag = Diagnostic::error(
            Code::E0627,
            site.defer_span,
            "defer body may panic (risk of uncatchable double-panic abort)",
        );
        if let Some(step) = site.witness.first()
            && let Some(at) = step.at
        {
            let detail = match (&step.call, step.cause) {
                (Some(call), Some(cause)) => {
                    format!("panic originates via `{call}` ({})", cause.as_str())
                }
                (Some(call), None) => format!("panic originates via `{call}`"),
                (None, Some(cause)) => format!("panic originates here ({})", cause.as_str()),
                (None, None) => "panic originates here".into(),
            };
            diag = diag.with_label(at, detail);
        }
        analyzer.error_diag(diag);
    }
    (analysis, analyzer.diagnostics)
}

impl<'a> Analyzer<'a> {
    fn ast(&self, file: FileId) -> &'a Ast {
        &self.program.hir.file(file).ast
    }

    fn ty(&self, span: Span) -> &'a Ty {
        self.program.types.get(&span).unwrap_or(&Ty::Unknown)
    }

    fn definition(&self, span: Span) -> Option<DefinitionId> {
        self.program
            .hir
            .resolve(span)
            .and_then(Resolution::definition)
    }

    fn declaration(&self, span: Span) -> Option<Span> {
        self.definition(span)
            .map(|id| self.program.hir.definition(id).name.span)
    }

    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        self.error_diag(Diagnostic::error(code, span, message));
    }

    fn error_diag(&mut self, diagnostic: Diagnostic) {
        if !self
            .diagnostics
            .iter()
            .any(|diag| diag.code == diagnostic.code && diag.primary == diagnostic.primary)
        {
            self.diagnostics.push(diagnostic);
        }
    }

    fn check_conflict(
        &mut self,
        ctx: &Context,
        conflict: AccessConflict,
        condition: Option<(Fact, bool)>,
        span: Span,
        message: &'static str,
    ) {
        let mut conditions: Vec<_> = condition.into_iter().collect();
        if let Some(capture) = conflict.capture.filter(|capture| capture.inferred) {
            conditions.push((
                Fact {
                    owner: capture.callable,
                    obligation: Obligation::Write(capture.binding),
                },
                true,
            ));
        }
        let code = match conflict.kind {
            ConflictKind::Direct { writable } => {
                if writable {
                    Code::E0523
                } else {
                    Code::E0524
                }
            }
            ConflictKind::Via(via) => {
                if !ctx.reachable || ctx.shadow {
                    return;
                }
                self.mode_constraints.push(domains::ModeConstraint {
                    owner: via.mode_owner().unwrap_or(ctx.owner),
                    conditions,
                    test: domains::ModeTest::Overlap(via),
                    span,
                    message,
                });
                return;
            }
        };
        if conditions.is_empty() {
            self.error(code, span, message);
        } else {
            self.capture_conflicts.push(CaptureConflict {
                conditions,
                code,
                span,
                message,
            });
        }
    }

    fn seed(&mut self, ctx: &Context, obligation: Obligation) {
        if ctx.reachable && !ctx.shadow {
            self.rules.push(Rule {
                premises: Vec::new(),
                conclusion: Fact {
                    owner: ctx.owner,
                    obligation,
                },
            });
        }
    }
}

fn is_assignment(token: &str) -> bool {
    matches!(
        token,
        "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
    )
}
