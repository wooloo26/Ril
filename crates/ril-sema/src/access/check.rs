use std::collections::{BTreeMap, BTreeSet};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_frontend::{
    hir::{DefinitionId, DefinitionKind, Resolution},
    parser::FileKind,
    syntax::{
        Ast, Condition, Expr, ExprId, Function, LiteralKind, MatchArm, Member, Mode, Path, Pattern,
        PatternId, Signature, StateKind, StmtId, StmtKind, Storage, Transfer, TypeDefinition,
    },
};

use super::{
    Access, Analysis, CallbackModeCall, CleanupAction, EffectUse, Input, Instance, Invocation,
    InvocationMode, ReturnSource, StorageUpdate, Summary, ViaDomain,
    flow::{
        AccessConflict, ConflictKind, Coordinate, Datum, Ledger, Origin, Reception, Region,
        Replacement, ResultOccurrence, Revocation, Slot, StorageFlow, conflicts,
    },
    horn::{self, Rule},
};
use crate::ty::{self, AdtKind, Callable, Ty, TypedProgram, Value, reception};

mod calls;
mod domains;
mod higher_order;
mod results;
mod snapshots;
mod storage;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Obligation {
    Write(Span),
    WriteExisting(Span),
    Handoff(Span),
    CallbackHandoff(usize),
    CallbackConsumes(higher_order::Invocation),
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
    Effect(String),
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
    Resource,
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
struct Context {
    owner: Span,
    file: FileId,
    scope: Span,
    formals: Vec<Option<Span>>,
    caller_slots: BTreeSet<Span>,
    caller_sources: BTreeSet<Span>,
    capture_modes: Option<BTreeMap<Span, Mode>>,
    new_formals: BTreeSet<Span>,
    via: BTreeSet<Span>,
    member_via: bool,
    handlers: BTreeMap<Operation, Datum>,
    local_effects: BTreeSet<String>,
    expected: Mode,
    returns: Vec<Span>,
    declared_contained: Vec<(Access, Span)>,
    return_values: Vec<Datum>,
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
            formals: Vec::new(),
            caller_slots: BTreeSet::new(),
            caller_sources: BTreeSet::new(),
            capture_modes: None,
            new_formals: BTreeSet::new(),
            via: BTreeSet::new(),
            member_via: false,
            handlers: BTreeMap::new(),
            local_effects: BTreeSet::new(),
            expected: Mode::Plain,
            returns: Vec::new(),
            declared_contained: Vec::new(),
            return_values: Vec::new(),
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
}

struct ModeUse {
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
    done: BTreeSet<DefinitionId>,
    cleanups: BTreeMap<Span, CleanupAction>,
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
        done: BTreeSet::new(),
        cleanups: BTreeMap::new(),
    };
    analyzer.load_interface_calls();
    for file in program.hir.files() {
        let mut ledger = Ledger::default();
        let mut context = Context::new(Span::new(file.id, 0, 0));
        for &item in &file.ast.items {
            analyzer.statement(&mut context, &mut ledger, item, false);
        }
        analyzer.check_results(&ledger, &BTreeSet::new());
    }
    analyzer
}

pub(super) fn analyze(program: &TypedProgram) -> (Analysis, Vec<Diagnostic>) {
    let mut analyzer = storage::solve_recursive_storage(program);
    analyzer.link_higher_order_calls();
    analyzer.check_snapshot_calls();
    let facts = horn::solve(&analyzer.rules);
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
        cleanups: std::mem::take(&mut analyzer.cleanups),
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
    let mut consuming_inputs = BTreeMap::new();
    let mut sharing_inputs = BTreeMap::new();
    let mut domains = domains::Domains::default();
    for function in std::mem::take(&mut analyzer.functions) {
        let summary = analyzer.finish_function(&facts, &function);
        let consumed: BTreeSet<_> = function
            .formals
            .iter()
            .enumerate()
            .filter_map(|(index, formal)| {
                formal
                    .filter(|decl| {
                        facts.contains(&Fact {
                            owner: function.owner,
                            obligation: Obligation::Handoff(*decl),
                        })
                    })
                    .map(|_| index)
            })
            .collect();
        let instances = analyzer.via_table(&function, &summary, &facts);
        consuming_inputs.insert(function.id, consumed);
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
            domains.register_function(&function, &instances);
            analysis.via.insert(function.id, instances);
        }
        analysis.summaries.insert(function.id, summary);
    }
    for use_site in std::mem::take(&mut analyzer.mode_uses) {
        let Some(summary) = analysis.summaries.get(&use_site.callee) else {
            continue;
        };
        for (index, mode, span) in use_site.choices {
            if mode != Input::New
                && consuming_inputs
                    .get(&use_site.callee)
                    .is_some_and(|owned| owned.contains(&index))
            {
                analyzer.error(
                    Code::E0548,
                    span,
                    "via application requires new qualification",
                );
            } else if mode != Input::Shared
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
    analyzer.restrict_mode_domains(&facts, &mut domains, &mut analysis);
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
        match self.program.hir.resolve(span) {
            Some(Resolution::Definition(id)) => Some(id),
            _ => None,
        }
    }

    fn declaration(&self, span: Span) -> Option<Span> {
        self.definition(span)
            .map(|id| self.program.hir.definition(id).name.span)
    }

    fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        if !self
            .diagnostics
            .iter()
            .any(|diag| diag.code == Some(code) && diag.primary == Some(span))
        {
            self.diagnostics
                .push(Diagnostic::error(code, span, message));
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

    fn effect(&mut self, ctx: &Context, ledger: &Ledger, effect: &str, span: Span) {
        self.use_effect(ctx, ledger, Obligation::Effect(effect.into()), span, None);
    }

    fn operation(&self, id: DefinitionId, path: Span) -> Option<Operation> {
        let definition = self.program.hir.operation_effect(id)?;
        let effect = self
            .program
            .operation_effects
            .get(&path)
            .cloned()
            .unwrap_or_else(|| self.program.hir.effect_label(definition));
        Some(Operation { id, effect })
    }

    fn effect_operations(&self, effect: &str) -> Vec<Operation> {
        let hir = &self.program.hir;
        let Some(definition) = self.program.effect_definition(effect) else {
            return Vec::new();
        };
        let children = self
            .program
            .effect_instances
            .get(effect)
            .map(|instance| &instance.includes);
        hir.effect_operations(definition)
            .filter_map(|id| {
                let original = hir.operation_effect(id)?;
                let instance = if original == definition {
                    effect.to_owned()
                } else if let Some(label) = children
                    .into_iter()
                    .flatten()
                    .find(|label| self.program.effect_definition(label) == Some(original))
                {
                    label.clone()
                } else {
                    hir.effect_label(original)
                };
                Some(Operation {
                    id,
                    effect: instance,
                })
            })
            .collect()
    }

    fn use_effect(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        obligation: Obligation,
        span: Span,
        if_exercised: Option<Fact>,
    ) {
        if ctx.shadow || !ctx.reachable {
            return;
        }
        let (label, operations) = match &obligation {
            Obligation::Operation(operation) => (operation.effect.clone(), vec![operation.clone()]),
            Obligation::Effect(effect) => (effect.clone(), self.effect_operations(effect)),
            _ => ril_base::ice!("expected effect obligation"),
        };
        if !operations.is_empty() && operations.iter().all(|id| ctx.handlers.contains_key(id)) {
            for handler in operations.iter().filter_map(|id| ctx.handlers.get(id)) {
                self.link_invocation_if(ctx, handler, if_exercised.as_ref());
                self.check_handler_iteration(ledger, handler, span, if_exercised.as_ref());
                if handler.live_callable_state
                    || handler
                        .origins()
                        .any(|origin| origin.mode != Access::Immutable)
                {
                    self.rules.push(Rule {
                        premises: if_exercised.iter().cloned().collect(),
                        conclusion: Fact {
                            owner: ctx.owner,
                            obligation: Obligation::StatefulHandler,
                        },
                    });
                }
            }
            return;
        }
        let local_effect = self
            .program
            .effect_definition(&label)
            .is_some_and(|definition| {
                ctx.local_effects
                    .contains(&self.program.hir.effect_label(definition))
            });
        let error = if local_effect {
            Some((
                Code::E0618,
                "effect must be handled in its declaring block".into(),
            ))
        } else if !ctx.in_function {
            Some((
                Code::E0202,
                format!("top-level initialization cannot perform @{label}"),
            ))
        } else {
            None
        };
        if let Some((code, message)) = error {
            if let Some(fact) = if_exercised {
                self.deferred_errors
                    .push((vec![fact], Diagnostic::error(code, span, message)));
            } else {
                self.error(code, span, message);
            }
        } else {
            self.rules.push(Rule {
                premises: if_exercised.into_iter().collect(),
                conclusion: Fact {
                    owner: ctx.owner,
                    obligation,
                },
            });
        }
    }

    fn check_handler_iteration(
        &mut self,
        ledger: &Ledger,
        handler: &Datum,
        span: Span,
        exercised: Option<&Fact>,
    ) {
        if ledger.iteration.is_empty() {
            return;
        }
        for (&owner, captures) in &handler.invocations {
            for (&source, actual) in captures {
                let overlap = handler.origins().any(|origin| {
                    origin.mode.writes()
                        && (actual.contains(&origin.region.source)
                            || origin.dependency_spans().any(|span| span == source))
                        && ledger
                            .iteration
                            .iter()
                            .any(|iterable| iterable.origins().any(|value| value.overlaps(origin)))
                });
                if overlap {
                    let premises = std::iter::once(Fact {
                        owner,
                        obligation: Obligation::Write(source),
                    })
                    .chain(exercised.cloned())
                    .collect();
                    self.deferred_errors.push((
                        premises,
                        Diagnostic::error(
                            Code::E0526,
                            span,
                            "effect handler writes to a collection being iterated",
                        ),
                    ));
                }
            }
        }
    }

    fn requirement(
        &mut self,
        ctx: &Context,
        span: Span,
        obligation: Obligation,
        msg: &'static str,
    ) {
        if ctx.reachable && !ctx.shadow {
            self.requirements.push(Requirement {
                fact: Fact {
                    owner: ctx.owner,
                    obligation,
                },
                span,
                message: msg,
            });
        }
    }

    fn function(&mut self, fun: &Function, outer: &Ledger) {
        let Some(id) = self.definition(fun.name.span) else {
            return;
        };
        if !self.done.insert(id) {
            return;
        }
        let Some(callable) = self.program.callables.get(&id) else {
            return;
        };
        let Some(body) = fun.body else {
            if self.program.hir.file(fun.name.span.file).kind == FileKind::Foreign {
                self.check_foreign(fun, callable);
            }
            return;
        };
        let mut ctx = Context::new(fun.name.span);
        if let Some(statement) = self.program.hir.definition(id).stmt {
            ctx.scope = self.ast(ctx.file).stmt(statement).span;
        }
        ctx.in_function = true;
        ctx.set_caller_storage(outer);
        ctx.runtime = !fun.is_meta;
        ctx.expected = fun.signature.result_mode;
        ctx.formals = fun
            .signature
            .params
            .iter()
            .map(|p| p.name.as_ref().map(|name| name.span))
            .collect();
        ctx.returns = fun
            .signature
            .result_sources
            .iter()
            .filter_map(|name| self.declaration(name.span))
            .collect();
        ctx.declared_contained = self.declared_sources(&fun.signature);
        let capture_modes: BTreeMap<_, _> = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(storage, path)| {
                self.declaration(path.span)
                    .map(|binding| (binding, storage.mode))
            })
            .collect();
        let captures: BTreeSet<_> = capture_modes.keys().copied().collect();
        ctx.capture_modes = Some(capture_modes);
        let mut ledger = outer.clone();
        ledger.enter_capture_storage(ctx.owner, &ctx.formals, |binding| {
            captures.contains(&binding)
        });
        ledger.clear_result_obligations();
        ledger.clear_array_extents();
        ledger.inspected.clear();
        ledger.reset_revocations();
        ledger.no_continuation = false;
        ledger.iteration.clear();
        ledger.holds.clear();
        if callable.open_effects || callable.open_state {
            self.error(
                Code::E0547,
                ctx.owner,
                "named definitions require closed effect and state sets",
            );
        }
        for (ast_param, param) in fun.signature.params.iter().zip(&callable.parameters) {
            let span = ast_param.name.as_ref().map_or(ctx.owner, |name| name.span);
            self.binding_scopes.insert(span, ctx.scope);
            if param.mode == Mode::Via {
                ctx.via.insert(span);
                if param.ty.is_value() {
                    self.error(
                        Code::E0550,
                        span,
                        "via is redundant on a value-type parameter",
                    );
                }
            }
            if param.mode == Mode::New && param.ty.is_value() {
                self.error(Code::E0411, span, "new parameter requires a shared object");
            }
            if param.mode == Mode::New {
                ctx.new_formals.insert(span);
            }
            let mut value = if param.ty.is_value() {
                Datum::default()
            } else {
                Datum::source(span, Access::from_mode(param.mode), param.mode == Mode::New)
            };
            value.transform(&mut |origin| {
                origin.dependencies.insert(span.into());
                origin.enter_formal(ctx.owner, param.mode);
                if matches!(param.ty, Ty::Draft(_)) {
                    origin.draft = true;
                    origin.confined = Some(ctx.scope);
                }
            });
            value = results::receive_results(self.program, &mut ledger, &param.ty, value, span);
            ledger.slots.insert(
                span,
                Slot {
                    decl: span,
                    variable: false,
                    mode: param.mode,
                    value,
                },
            );
            if param.mode == Mode::Mut {
                self.requirement(
                    &ctx,
                    span,
                    Obligation::Write(span),
                    "mut parameter requires reachable write, forwarding, or handoff",
                );
            }
            if param.mode == Mode::Shared {
                self.requirement(
                    &ctx,
                    span,
                    Obligation::Retain(span),
                    "shared parameter must be retained",
                );
            }
        }
        let member_axes = member_axes(callable, &ctx.formals);
        self.register_member_axes(&member_axes);
        ctx.member_via = !member_axes.is_empty();
        for clause in &fun.signature.obligations.state {
            if matches!(clause.kind, StateKind::Environment | StateKind::Return)
                && clause.bindings.is_empty()
            {
                self.error(
                    Code::E0538,
                    clause.span,
                    "named state groups require source bindings",
                );
            }
        }
        for &helper in &fun.helpers {
            self.statement(&mut ctx, &mut ledger, helper, false);
        }
        let value = self.expr(&mut ctx, &mut ledger, body);
        let body_span = self.ast(ctx.file).expr(body).span;
        if ctx.reachable && self.ty(body_span) != &Ty::Never {
            self.returned(&mut ctx, &mut ledger, value, body_span);
            self.check_results(&ledger, &BTreeSet::new());
        }
        let mut return_sources = BTreeSet::new();
        for value in &ctx.return_values {
            value.visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                let Some(formal) = ctx
                    .formals
                    .iter()
                    .position(|param| *param == Some(origin.region.source))
                else {
                    return;
                };
                let access = if result_path.is_empty() {
                    match ctx.expected {
                        Mode::Ref | Mode::Shared => Access::from_mode(ctx.expected),
                        Mode::Infer => origin.mode,
                        _ => return,
                    }
                } else if !origin.new && ctx.expected != Mode::Plain {
                    origin.mode
                } else {
                    return;
                };
                return_sources.insert(ReturnSource {
                    formal,
                    source_path: origin.region.selection.clone(),
                    result_path: result_path.to_vec(),
                    access,
                });
            });
        }
        if ctx.runtime && ctx.expected != Mode::Infer && !ctx.return_values.is_empty() {
            let excess = ctx.declared_contained.iter().any(|&(mode, source)| {
                ctx.formals
                    .iter()
                    .position(|decl| *decl == Some(source))
                    .is_none_or(|index| {
                        !return_sources.iter().any(|entry| {
                            entry.formal == index
                                && entry.access == mode
                                && !entry.result_path.is_empty()
                        })
                    })
            });
            if excess {
                self.error(Code::E0529, ctx.owner, "unused contained return source");
            }
        }
        let exits = self.storage_exits.remove(&ctx.owner).unwrap_or_default();
        let storage::StorageExit {
            mut updates,
            flow: mut storage_flow,
        } = storage::StorageExit::join(&exits);
        calls::seal_call_allocations(
            &mut self.callback_results,
            ctx.return_values
                .iter_mut()
                .filter(|value| {
                    ctx.expected != Mode::Plain
                        || !value.results().is_empty()
                        || value.has_array_layout()
                })
                .chain(updates.values_mut().map(|update| &mut update.value))
                .chain(storage_flow.iter_mut().flat_map(StorageFlow::values_mut)),
            body_span,
        );
        self.functions.push(DefinitionCheck {
            owner: ctx.owner,
            id,
            formals: ctx.formals,
            declared: (**callable).clone(),
            via: ctx.via,
            member_axes,
            return_sources: return_sources.into_iter().collect(),
            returned_new: !ctx.return_values.is_empty()
                && ctx.return_values.iter().all(|value| value.requires_new),
            returns: ctx.return_values,
            updates,
            storage_flow,
            normal_exit: !exits.is_empty(),
            capture_names: captures,
        });
    }

    fn declared_sources(&self, signature: &Signature) -> Vec<(Access, Span)> {
        signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Return)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(storage, path)| {
                self.declaration(path.span)
                    .map(|span| (Access::from_mode(storage.mode), span))
            })
            .collect()
    }

    fn check_foreign(&mut self, fun: &Function, signature: &Callable) {
        let prohibited = matches!(
            signature.result_mode,
            Mode::Shared | Mode::Via | Mode::Infer
        ) || signature
            .state
            .iter()
            .any(|state| matches!(state.as_str(), "^mut" | "capture"))
            || signature.parameters.iter().any(|parameter| {
                matches!(parameter.mode, Mode::Shared | Mode::Via)
                    || parameter.mode == Mode::Plain
                        && matches!(&parameter.ty, Ty::Adt(adt) if adt.kind == AdtKind::Foreign)
            })
            || signature.result_mode == Mode::Plain
                && matches!(&signature.result, Ty::Adt(adt) if adt.kind == AdtKind::Foreign);
        if prohibited {
            self.error(
                Code::E0908,
                fun.name.span,
                "foreign signature requires non-shared handle authority",
            );
        }
    }

    fn finish_function(&mut self, facts: &BTreeSet<Fact>, fun: &DefinitionCheck) -> Summary {
        let mut summary = Summary {
            return_sources: fun.return_sources.clone(),
            return_allocations: Datum::return_allocations(&fun.returns),
            constructs: fun.returned_new,
            nonreturning: !fun.normal_exit,
            invocations: self
                .invocation_summaries
                .remove(&fun.owner)
                .into_iter()
                .flatten()
                .collect(),
            mode_calls: Some(
                self.mode_call_summaries
                    .remove(&fun.owner)
                    .into_iter()
                    .flatten()
                    .collect(),
            ),
            callback_returns: fun
                .returns
                .iter()
                .flat_map(|value| self.callback_return_contracts(&fun.formals, value))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            storage_updates: self.storage_contracts(fun),
            snapshot_inputs: self.snapshots.inputs(fun.owner, &fun.formals),
            ..Summary::default()
        };
        self.publish_snapshot_contract(fun, &mut summary);
        let mut up = BTreeSet::new();
        for fact in facts.iter().filter(|fact| fact.owner == fun.owner) {
            match &fact.obligation {
                Obligation::Write(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span))
                        && fun
                            .declared
                            .parameters
                            .get(param)
                            .is_some_and(|formal| formal.mode != Mode::New)
                    {
                        summary.writes.push(param);
                    }
                }
                Obligation::WriteExisting(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.writes.push(param);
                    }
                }
                Obligation::Share(span) | Obligation::StoreShare(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.retained.push(param);
                        if matches!(fact.obligation, Obligation::Share(_)) {
                            summary.independent_retention.push(param);
                        }
                    }
                }
                Obligation::ReadUp(span) => {
                    up.insert(*span);
                }
                Obligation::Invoke(span) => {
                    if let Some(formal) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.invoked.push(formal);
                    }
                }
                Obligation::Effect(effect) => {
                    self.record_effect_use(fun, &mut summary, effect, None);
                }
                Obligation::Operation(operation) => {
                    self.record_effect_use(
                        fun,
                        &mut summary,
                        &operation.effect,
                        Some(operation.id),
                    );
                }
                Obligation::Capture => summary.captures = true,
                _ => {}
            }
        }
        summary.writes.sort_unstable();
        summary.writes.dedup();
        summary.retained.sort_unstable();
        summary.retained.dedup();
        summary.independent_retention.sort_unstable();
        summary.invoked.sort_unstable();
        summary.effects.sort();
        summary.effects.dedup();
        summary.effect_uses.sort_unstable();
        summary.effect_uses.dedup();
        summary.normalize_invocations();
        let name = fun.owner;
        let sig = &fun.declared;
        let exercised = |slots: &[usize]| {
            slots.iter().any(|&i| {
                fun.formals
                    .get(i)
                    .and_then(|decl| *decl)
                    .is_some_and(|span| !fun.via.contains(&span))
            })
        };
        for (state, actual) in [
            ("mut", exercised(&summary.writes)),
            ("^mut", exercised(&summary.retained)),
            ("capture", summary.captures),
        ] {
            let declared = sig.state.iter().any(|clause| clause == state);
            if actual && !declared {
                self.error(Code::E0510, name, format!("missing &{state} obligation"));
            } else if !actual && declared && fun.via.is_empty() {
                self.error(Code::E0529, name, format!("unused &{state} obligation"));
            }
        }
        for effect in &summary.effects {
            if !sig
                .effects
                .iter()
                .any(|declared| self.program.effect_covers(declared, effect))
            {
                self.error(Code::E0612, name, format!("unhandled @{effect}"));
            }
        }
        for effect in &sig.effects {
            if !summary
                .effects
                .iter()
                .any(|actual| self.program.effect_covers(effect, actual))
            {
                self.error(
                    Code::E0612,
                    name,
                    format!("declared @{effect} is never exercised"),
                );
            }
        }
        if up.difference(&fun.capture_names).next().is_some() {
            self.error(Code::E0510, name, "missing &up dependency");
        }
        if fun.capture_names.difference(&up).next().is_some() {
            self.error(Code::E0529, name, "unused &up dependency");
        }
        summary
    }

    fn record_effect_use(
        &self,
        function: &DefinitionCheck,
        summary: &mut Summary,
        effect: &str,
        operation: Option<DefinitionId>,
    ) {
        summary.effects.push(effect.to_owned());
        for (declaration, declared) in function.declared.effects.iter().enumerate() {
            if self.program.effect_covers(declared, effect) {
                summary.effect_uses.push(EffectUse {
                    declaration,
                    effect: effect.to_owned(),
                    operation: operation.map(|operation| self.program.hir.export_name(operation)),
                });
            }
        }
    }

    fn storage_contracts(&self, fun: &DefinitionCheck) -> Vec<StorageUpdate> {
        self.describe_storage_updates(&fun.formals, &fun.updates)
    }

    fn describe_storage_updates(
        &self,
        formals: &[Option<Span>],
        entries: &BTreeMap<Region, Replacement>,
    ) -> Vec<StorageUpdate> {
        let formal_index = |source| formals.iter().position(|formal| *formal == Some(source));
        let mut updates: Vec<_> = entries
            .iter()
            .filter_map(|(region, update)| {
                let formal = formal_index(region.source)?;
                let mut sources = BTreeSet::new();
                update
                    .value
                    .visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                        if let Some(formal) = formal_index(origin.region.source) {
                            sources.insert(ReturnSource {
                                formal,
                                source_path: origin.region.selection.clone(),
                                result_path: result_path.to_vec(),
                                access: origin.mode,
                            });
                        }
                    });
                Some(StorageUpdate {
                    formal,
                    path: region.selection.clone(),
                    sources: sources.into_iter().collect(),
                    callback_returns: self.callback_return_contracts(formals, &update.value),
                    snapshot_projections: Vec::new(),
                    allocations: Datum::return_allocations(std::slice::from_ref(&update.value)),
                    definite: update.definite,
                    constructs: update.value.requires_new,
                })
            })
            .collect();
        updates.sort_unstable();
        updates
    }

    fn via_table(
        &mut self,
        fun: &DefinitionCheck,
        summary: &Summary,
        facts: &BTreeSet<Fact>,
    ) -> ViaDomain {
        if fun.via.is_empty() && fun.member_axes.is_empty() {
            return ViaDomain::default();
        }
        let mut permitted = Vec::new();
        let mut formals = BTreeMap::new();
        let mut axes = Vec::new();
        for (index, formal) in fun.formals.iter().enumerate() {
            let Some(source) = formal.filter(|span| fun.via.contains(span)) else {
                continue;
            };
            formals.insert(index, formals.len());
            axes.push(Region::root(source));
            let domain = domains::root_modes(facts, fun.owner, source);
            if domain.is_empty() {
                self.error(
                    Code::E0548,
                    fun.owner,
                    "via source cannot be both handed off as new and retained as shared",
                );
                return ViaDomain::default();
            }
            permitted.push(domain.to_vec());
        }
        for (_, axis) in &fun.member_axes {
            axes.push(axis.clone());
            let domain = domains::member_modes(facts, fun.owner, axis);
            if domain.is_empty() {
                self.error(
                    Code::E0520,
                    fun.owner,
                    "member via template has incompatible access requirements",
                );
                return ViaDomain::default();
            }
            permitted.push(domain);
        }
        if fun.declared.result_mode != Mode::Infer
            && summary
                .invocations
                .iter()
                .all(|invocation| matches!(invocation.mode, InvocationMode::Input(_)))
            && summary.mode_calls.as_ref().is_none_or(Vec::is_empty)
            && summary.callback_returns.is_empty()
            && summary
                .storage_updates
                .iter()
                .all(|update| update.callback_returns.is_empty())
        {
            return ViaDomain::uniform(&permitted, summary);
        }
        let mut rows = vec![Vec::new()];
        for domain in permitted {
            extend_rows(&mut rows, &domain);
        }
        ViaDomain::from_instances(rows.into_iter().map(|modes| {
            let mut summary = summary.clone();
            let input = |formal| {
                formals
                    .get(&formal)
                    .and_then(|&axis| modes.get(axis))
                    .copied()
            };
            for invocation in &mut summary.invocations {
                if let InvocationMode::Formal(formal) = invocation.mode
                    && let Some(input) = input(formal)
                {
                    invocation.mode = InvocationMode::Input(input);
                }
            }
            summary.normalize_invocations();
            let axis_input = |axis: &super::ModeAxis| {
                if axis.path.is_empty() {
                    input(axis.parameter)
                } else {
                    fun.member_axes
                        .iter()
                        .position(|(parameter, region)| {
                            *parameter == axis.parameter && region.selection == axis.path
                        })
                        .and_then(|index| modes.get(formals.len() + index))
                        .copied()
                }
            };
            if let Some(calls) = &mut summary.mode_calls {
                for call in &mut *calls {
                    call.specialize(&axis_input);
                }
                calls.sort_unstable();
                calls.dedup();
            }
            for result in &mut summary.callback_returns {
                result.specialize(&input);
            }
            summary.callback_returns.sort_unstable();
            summary.callback_returns.dedup();
            for update in &mut summary.storage_updates {
                for result in &mut update.callback_returns {
                    result.specialize(&input);
                }
                update.callback_returns.sort_unstable();
                update.callback_returns.dedup();
            }
            if fun.declared.result_mode == Mode::Infer {
                summary.constructs = !fun.returns.is_empty()
                    && fun.returns.iter().all(|value| {
                        value.requires_new
                            || (!value.roots.is_empty()
                                && value.roots.iter().all(|origin| {
                                    origin.inherits_mode
                                        && origin.region.selection.is_empty()
                                        && fun
                                            .formals
                                            .iter()
                                            .position(|formal| {
                                                *formal == Some(origin.region.source)
                                            })
                                            .and_then(|index| formals.get(&index))
                                            .is_some_and(|&position| {
                                                modes.get(position) == Some(&Input::New)
                                            })
                                }))
                    });
                let mut sources = BTreeSet::new();
                for value in &fun.returns {
                    value.visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                        let Some(formal) = fun
                            .formals
                            .iter()
                            .position(|decl| *decl == Some(origin.region.source))
                        else {
                            return;
                        };
                        if !result_path.is_empty() && origin.new {
                            return;
                        }
                        let input = |axis: &Region| {
                            axes.iter()
                                .zip(&modes)
                                .find(|(decl, _)| decl.matches_axis(axis))
                                .map_or(Access::Mut, |(_, mode)| mode.access())
                        };
                        let access = if origin.inherits_mode {
                            input(&origin.region)
                        } else if origin.reception.is_empty() {
                            formals
                                .get(&formal)
                                .and_then(|index| modes.get(*index))
                                .map_or(origin.mode, |mode| mode.access().project(origin.mode))
                        } else {
                            origin
                                .reception
                                .iter()
                                .map(|step| match step {
                                    Reception::Fixed(access) => *access,
                                    Reception::Axis(axis) => input(axis),
                                })
                                .fold(Access::Mut, Access::project)
                        };
                        sources.insert(ReturnSource {
                            formal,
                            source_path: origin.region.selection.clone(),
                            result_path: result_path.to_vec(),
                            access,
                        });
                    });
                }
                summary.return_sources = sources.into_iter().collect();
            }
            Instance { modes, summary }
        }))
    }

    fn statement(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        id: StmtId,
        tail: bool,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let node = ast.stmt(id);
        match &node.value.kind {
            StmtKind::Function(fun) => self.function(fun, ledger),
            StmtKind::Sub { items, .. } => {
                for &item in items {
                    self.statement(ctx, ledger, item, false);
                }
            }
            StmtKind::Binding {
                pattern,
                storage,
                ty,
                value,
                fallback,
                resource,
                ..
            } => {
                if let Some(ty) = ty {
                    self.shadow_type(ctx, ledger, *ty);
                }
                let Some(value_id) = value else {
                    return Datum::default();
                };
                let span = ast.expr(*value_id).span;
                let mut value = self.expr(ctx, ledger, *value_id);
                if let Some(adjustments) = self.program.receptions.get(&span) {
                    for adjustment in adjustments {
                        if !value.requires_new
                            || !Self::retarget(
                                &mut value,
                                &adjustment.path,
                                Access::from_mode(adjustment.mode),
                            )
                        {
                            self.error(
                                Code::E0522,
                                span,
                                "existing container members must retain their access modes",
                            );
                        }
                    }
                }
                if !ctx.reachable {
                    return Datum::default();
                }
                if *resource {
                    self.cleanup(ctx, ledger, &mut value, span, node.span, storage.mode);
                }
                let site = if *resource {
                    BindingSite::Resource
                } else {
                    BindingSite::Declaration
                };
                if let Some(fallback) = fallback {
                    for (mut failed, _) in self.pattern_paths(ctx, ledger, *pattern, &value, false)
                    {
                        let mut failure = ctx.clone();
                        self.expr(&mut failure, &mut failed, *fallback);
                        ctx.return_values = failure.return_values;
                    }
                    if !self.bind_on_match(ctx, ledger, *pattern, storage, &value, site) {
                        ledger.no_continuation = true;
                        ctx.reachable = false;
                    }
                } else {
                    self.pattern_tests(ctx, ledger, *pattern, &value)
                        .inspect(ledger, true);
                    self.bind(ctx, ledger, *pattern, storage, value, site);
                }
            }
            StmtKind::With(handlers) => self.handlers(ctx, ledger, handlers),
            StmtKind::Expr(expr) => {
                let value = self.expr(ctx, ledger, *expr);
                if tail {
                    return value;
                }
                self.discard(ledger, &value);
            }
            StmtKind::Type(decl) => {
                if let TypeDefinition::Data(ty) = decl.definition {
                    self.shadow_type(ctx, ledger, ty);
                }
            }
            StmtKind::Effect { .. } | StmtKind::Import(_) | StmtKind::Error => {}
        }
        Datum::default()
    }

    fn shadow_type(&mut self, ctx: &Context, ledger: &Ledger, ty: ril_frontend::syntax::TypeId) {
        use ril_frontend::syntax::{GenericArg, Type};
        match &self.ast(ctx.file).ty(ty).value {
            Type::TypeOf(expr) => {
                let mut shadow = ctx.clone();
                shadow.shadow = true;
                shadow.loop_owner = None;
                let mut slots = ledger.clone();
                slots.clear_result_obligations();
                let result = self.expr(&mut shadow, &mut slots, *expr);
                self.check_results(&slots, &result.root_results());
            }
            Type::Named(path) => {
                for parameter in path.segments.iter().flat_map(|segment| &segment.arguments) {
                    if let GenericArg::Type(ty) = parameter {
                        self.shadow_type(ctx, ledger, *ty);
                    }
                }
            }
            Type::Array(_, ty) | Type::Option(ty) | Type::Project { base: ty, .. } => {
                self.shadow_type(ctx, ledger, *ty);
            }
            Type::Result(left, right) | Type::Map(left, _, right) => {
                self.shadow_type(ctx, ledger, *left);
                self.shadow_type(ctx, ledger, *right);
            }
            Type::Tuple(items) => {
                for (_, ty) in items {
                    self.shadow_type(ctx, ledger, *ty);
                }
            }
            Type::Record { fields, .. } => {
                for field in fields {
                    self.shadow_type(ctx, ledger, field.ty);
                }
            }
            Type::Callable(call) => {
                for ty in call.params.iter().filter_map(|param| param.ty) {
                    self.shadow_type(ctx, ledger, ty);
                }
                self.shadow_type(ctx, ledger, call.result);
            }
            _ => {}
        }
    }

    fn retarget(value: &mut Datum, path: &[reception::Step], mode: Access) -> bool {
        let Some((step, rest)) = path.split_first() else {
            if value.roots.iter().any(|root| !root.new) {
                return false;
            }
            for root in &mut value.roots {
                root.fix_mode(mode);
                root.clone_member = false;
            }
            return true;
        };
        let coordinate = match step {
            reception::Step::Field(name) => Coordinate::Field(name.clone()),
            reception::Step::Position(index) => Coordinate::Index(index.to_string()),
            reception::Step::Elements => {
                return if value.members.is_empty() {
                    value.roots.iter().all(|root| root.new)
                } else {
                    value
                        .members
                        .values_mut()
                        .all(|member| Self::retarget(member, rest, mode))
                };
            }
        };
        if let Some(member) = value.members.get_mut(&coordinate) {
            Self::retarget(member, rest, mode)
        } else {
            value.origins().all(|origin| origin.new)
        }
    }

    fn receive_member(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        mut value: Datum,
        mode: Access,
        span: Span,
    ) -> Datum {
        if mode != Access::Immutable {
            value.forget_collection_layout();
        }
        if value.roots.is_empty() {
            return value;
        }
        if mode == Access::Shared {
            self.check_shared_reception(&value, span);
        }
        if mode == Access::Immutable
            && self.require_snapshot(
                (ctx, ledger),
                &ledger.snapshot(&value),
                Code::E0535,
                span,
                "live authority cannot enter an immutable member",
            )
        {
            value.specialize_snapshot_sources();
        }
        let inline_closure = value.environments.contains(&span);
        if value.requires_new || inline_closure {
            if mode == Access::Mut
                && inline_closure
                && value
                    .members
                    .values()
                    .flat_map(Datum::origins)
                    .any(|capture| capture.mode.writes())
            {
                self.error(
                    Code::E0510,
                    span,
                    "a closure retaining a writer needs shared writable storage",
                );
            }
            for root in &mut value.roots {
                root.fix_mode(mode);
            }
            return value;
        }
        let valid = value.roots.iter().all(|root| root.mode == mode);
        if !valid {
            let code = match mode {
                Access::Immutable => Code::E0535,
                Access::Ref => Code::E0357,
                Access::Mut if value.writers() => Code::E0510,
                Access::Mut | Access::Shared => Code::E0522,
            };
            self.error(
                code,
                span,
                "existing source does not match the member's access mode",
            );
        }
        if mode == Access::Mut && value.writers() {
            self.error(
                Code::E0510,
                span,
                "mutable member requires an exclusive handoff",
            );
        }
        for root in &mut value.roots {
            root.explicit_share = false;
        }
        value
    }

    fn require_snapshot(
        &mut self,
        (ctx, ledger): (&Context, &Ledger),
        value: &Datum,
        code: Code,
        span: Span,
        message: &'static str,
    ) -> bool {
        let mut conditions = BTreeMap::<_, BTreeSet<_>>::new();
        if !value.accepts_snapshot_sources(&mut |origin| {
            let Some(expression) = origin.forwarded_mode() else {
                return false;
            };
            let owner = origin.entry_callable().unwrap_or(ctx.owner);
            conditions.entry(owner).or_default().insert(expression);
            true
        }) {
            self.error(code, span, message);
            return false;
        }
        // A symbolic path can be treated as immutable after this reception.
        // Keep only the mode assignments for which all such paths are plain.
        if ctx.reachable && !ctx.shadow {
            self.snapshots.freeze(ledger, value);
            self.mode_constraints
                .extend(conditions.into_iter().map(|(owner, expressions)| {
                    domains::ModeConstraint {
                        owner,
                        conditions: Vec::new(),
                        test: domains::ModeTest::Immutable(expressions, code),
                        span,
                        message,
                    }
                }));
        }
        true
    }

    fn freeze_value(&mut self, ctx: &Context, ledger: &Ledger, value: &mut Datum, span: Span) {
        *value = ledger.snapshot(value);
        self.require_snapshot(
            (ctx, ledger),
            value,
            Code::E0535,
            span,
            "live authority cannot be frozen as a plain snapshot",
        );
        value.freeze();
    }

    fn require_shared_replacement(&mut self, value: &Datum, span: Span, allow_new: bool) {
        if value
            .roots
            .iter()
            .any(|root| !(root.explicit_share || allow_new && root.new))
        {
            self.error(
                Code::E0510,
                span,
                "shared replacement requires a '^mut' expression",
            );
        }
    }

    fn check_exclusive_reception(&mut self, value: &Datum, span: Span) {
        // A Draft projection remains confined to the derive callback.
        if value.requires_new || value.writers() && value.roots.iter().all(|root| root.draft) {
            return;
        }
        if value.writers() {
            self.error(
                Code::E0510,
                span,
                "a persistent mutable binding requires an exclusive handoff",
            );
        } else {
            self.error(
                Code::E0520,
                span,
                "binding cannot manufacture write authority",
            );
        }
    }

    fn check_shared_reception(&mut self, value: &Datum, span: Span) {
        if value
            .roots
            .iter()
            .any(|root| root.call_scoped_access && root.mode.writes())
        {
            self.error(Code::E0528, span, "a call-scoped writer cannot be shared");
        }
    }

    fn shared_local_input(&mut self, ctx: &Context, declaration: Span, value: &Datum, span: Span) {
        let closure_with_writer =
            value.creates_environment() && value.origins().any(|origin| origin.mode.writes());
        if !value.writers() && !closure_with_writer {
            self.error(
                Code::E0527,
                span,
                "shared binding requires a writable source",
            );
            return;
        }
        self.check_shared_reception(value, span);
        let existing_writer = value.roots.iter().any(|root| {
            root.mode.writes() && !(root.new && (value.requires_new || root.explicit_share))
        });
        if existing_writer || closure_with_writer {
            self.seed(ctx, Obligation::SharedReception(declaration));
        }
    }

    fn require_shared_local(&mut self, ctx: &Context, declaration: Span, value: &Datum) {
        self.requirement(
            ctx,
            declaration,
            Obligation::SharedReception(declaration),
            "shared binding requires reachable reception of a shared writer",
        );
        self.shared_local_input(ctx, declaration, value, declaration);
    }

    fn check_ref_binding(&mut self, span: Span, value: &Datum, variable: bool) {
        if value.roots.iter().any(|root| root.explicit_share) {
            self.error(
                Code::E0527,
                span,
                "a ref binding does not use a '^mut' marker",
            );
        } else if value.roots.iter().any(|root| root.from_variable) {
            self.error(
                Code::E0531,
                span,
                "a reassignable binding cannot anchor a ref view",
            );
        } else if value.roots.is_empty() {
            self.error(Code::E0531, span, "ref binding has no live object source");
        } else if (value.requires_new
            || value
                .roots
                .iter()
                .any(|root| root.new && root.dependencies.is_empty()))
            && (variable
                || !value
                    .members
                    .values()
                    .flat_map(Datum::origins)
                    .any(|source| source.mode == Access::Ref && !source.new))
        {
            self.error(
                Code::E0543,
                span,
                "temporary has no live ref source to anchor the binding",
            );
        }
    }

    fn check_ref_scope(&mut self, span: Span, value: &Datum, destination: Span) {
        let shorter_scope = value
            .roots
            .iter()
            .flat_map(|root| &root.anchor_scopes)
            .any(|source| {
                source.file != destination.file
                    || source.start > destination.start
                    || source.end < destination.end
            });
        if shorter_scope {
            self.error(
                Code::E0604,
                span,
                "ref source scope must enclose the reassignable binding's scope",
            );
        }
    }

    fn returned(&mut self, ctx: &mut Context, ledger: &mut Ledger, value: Datum, span: Span) {
        let mut value = ledger.snapshot_call_graph(&value);
        ledger.inspect(&value);
        if value.origins().any(|origin| origin.confined.is_some()) {
            self.error(Code::E0604, span, "confined authority cannot be returned");
        }
        if !ctx.runtime || ctx.shadow {
            return;
        }
        self.storage_exit(ctx, ledger);
        if value.creates_environment() {
            self.seed(ctx, Obligation::Capture);
        }
        if value.returns_call_scoped_writer(ctx.expected) {
            self.error(
                Code::E0528,
                span,
                "a call-scoped writer cannot escape in a return",
            );
        }
        match ctx.expected {
            Mode::Plain if value.requires_new => self.error(
                Code::E0544,
                ctx.owner,
                "fresh shared return must declare -> new",
            ),
            Mode::Plain => {
                if self.require_snapshot(
                    (ctx, ledger),
                    &value,
                    Code::E0528,
                    span,
                    "plain return cannot expose live authority",
                ) {
                    value.specialize_snapshot_sources();
                }
            }
            Mode::New if !value.requires_new => {
                self.error(Code::E0546, span, "return does not have new qualification");
            }
            Mode::Ref | Mode::Shared
                if value.roots.is_empty()
                    || value
                        .roots
                        .iter()
                        .any(|root| !ctx.returns.contains(&root.region.source)) =>
            {
                self.error(
                    Code::E0545,
                    span,
                    "return does not select its declared entry source",
                );
            }
            Mode::Shared if value.roots.iter().any(|root| root.mode != Access::Shared) => {
                self.error(
                    Code::E0528,
                    span,
                    "shared return requires an existing shared writer",
                );
            }
            _ => {}
        }
        if ctx.expected == Mode::Shared {
            for origin in &value.roots {
                self.seed(ctx, Obligation::Retain(origin.region.source));
            }
        }
        let actual: BTreeSet<_> = value
            .members
            .values()
            .filter(|_| ctx.expected != Mode::Plain)
            .flat_map(Datum::origins)
            .filter(|origin| !origin.new && ctx.formals.contains(&Some(origin.region.source)))
            .map(|origin| (origin.mode, origin.region.source))
            .collect();
        if ctx.expected != Mode::Infer
            && actual
                .iter()
                .any(|source| !ctx.declared_contained.contains(source))
        {
            self.error(Code::E0510, ctx.owner, "missing contained return source");
        }
        for &(_, source) in actual.iter().filter(|(mode, _)| *mode == Access::Shared) {
            self.seed(ctx, Obligation::Retain(source));
            self.seed(ctx, Obligation::Share(source));
        }
        ctx.return_values.push(value);
    }

    fn storage_exit(&mut self, ctx: &Context, ledger: &Ledger) {
        if !ctx.in_function
            || !ctx.runtime
            || ctx.shadow
            || !ctx.reachable
            || ledger.no_continuation
        {
            return;
        }
        self.publish_at_exit(ctx, ledger, true);
        self.storage_exits
            .entry(ctx.owner)
            .or_default()
            .push(storage::StorageExit {
                updates: ledger.call_updates(ctx.owner, &ctx.formals, &ctx.caller_slots),
                flow: ledger.storage_flow.clone(),
            });
    }

    fn publish_at_exit(&mut self, ctx: &Context, ledger: &Ledger, normal: bool) {
        if !ctx.runtime || ctx.shadow || !ctx.reachable {
            return;
        }
        for &slot in ctx.caller_slots.iter().chain(ctx.formals.iter().flatten()) {
            let Some(slot) = ledger.slots.get(&slot) else {
                continue;
            };
            let caller_root = !ctx.new_formals.contains(&slot.decl);
            let value = ledger.snapshot(&slot.value);
            value.surviving_publications(ctx.owner, caller_root, &mut |stored| {
                if stored.creates_environment() {
                    self.seed(ctx, Obligation::Capture);
                }
                for origin in stored
                    .origins()
                    .filter(|origin| origin.mode == Access::Shared)
                {
                    self.seed(ctx, Obligation::Retain(origin.region.source));
                    let modeled = ctx.formals.contains(&Some(slot.decl))
                        || ledger.replaces_slot(ctx.owner, slot.decl);
                    let effect = if normal && modeled {
                        Obligation::StoreShare(origin.region.source)
                    } else {
                        Obligation::Share(origin.region.source)
                    };
                    self.seed(ctx, effect);
                }
            });
        }
    }

    fn check_publication_source(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
    ) {
        let value = ledger.loop_snapshot(value);
        self.check_stored_views(&value, false, span);
        if value
            .origins()
            .any(|origin| origin.call_scoped_access && origin.mode.writes())
        {
            self.error(
                Code::E0528,
                span,
                "a call-scoped writer cannot be retained in caller storage",
            );
        }
        for origin in value.origins().filter(|origin| {
            origin.mode == Access::Shared
                && origin.region.selection.is_empty()
                && ctx.via.contains(&origin.region.source)
        }) {
            self.seed(ctx, Obligation::NeedsSharing(origin.region.source));
        }
    }

    fn check_stored_views(&mut self, value: &Datum, root_as_ref: bool, span: Span) {
        if value
            .origins()
            .any(|origin| origin.mode == Access::Ref && origin.call_scoped_access)
            || root_as_ref && value.roots.iter().any(|origin| origin.call_scoped_access)
        {
            self.error(
                Code::E0604,
                span,
                "a ref view of a call-scoped writer cannot be stored in existing storage",
            );
        }
    }

    fn check_results(&mut self, ledger: &Ledger, except: &BTreeSet<ResultOccurrence>) {
        let pending: BTreeSet<_> = ledger
            .pending_results()
            .filter(|item| !except.contains(item))
            .map(|item| item.span)
            .chain(ledger.lost_results.iter().copied())
            .collect();
        for span in pending {
            self.error(
                Code::E0720,
                span,
                "fallible result has not been inspected on normal exit",
            );
        }
    }

    fn discard(&mut self, ledger: &Ledger, value: &Datum) {
        for item in value
            .results()
            .iter()
            .filter(|item| !ledger.result_inspected(item))
        {
            self.error(Code::E0720, item.span, "discarded fallible result");
        }
    }

    fn references_scoped_resource(&self, value: &Datum) -> bool {
        value.origins().any(|origin| {
            origin
                .confined
                .is_some_and(|scope| self.cleanups.contains_key(&scope))
        })
    }

    fn check_resource_binding(&mut self, name: Span, value: &Datum, resource: bool) {
        let value_type = self
            .definition(name)
            .and_then(|id| self.program.bindings.get(&id))
            .is_some_and(Ty::is_value);
        if !resource && !value_type && self.references_scoped_resource(value) {
            self.error(Code::E0604, name, "scoped resource cannot be rebound");
        }
    }

    fn cleanup(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &mut Datum,
        value_span: Span,
        binding: Span,
        mode: Mode,
    ) {
        if self.references_scoped_resource(value) {
            self.error(
                Code::E0604,
                binding,
                "scoped resource already has a cleanup binding",
            );
            return;
        }
        if matches!(self.ty(value_span), Ty::Sender(_)) {
            if !value.requires_new {
                self.error(
                    Code::E0548,
                    binding,
                    "cleanup requires a new-qualified sender",
                );
            }
            value.transform(&mut |origin| {
                origin.confined = Some(binding);
                origin.fix_mode(if mode == Mode::Mut {
                    Access::Mut
                } else {
                    Access::Ref
                });
            });
            self.cleanups.insert(binding, CleanupAction::CloseSender);
            return;
        }
        let Ty::Adt(adt) = self.ty(value_span) else {
            self.error(
                Code::E0541,
                binding,
                "resource type has no cleanup declaration",
            );
            return;
        };
        let def = self.program.hir.definition(adt.definition);
        let ast = self.ast(def.name.span.file);
        let cleanup = def
            .stmt
            .and_then(|id| match &ast.stmt(id).value.kind {
                StmtKind::Type(decl) => decl.cleanup.as_ref(),
                _ => None,
            })
            .and_then(|name| self.definition(name.span));
        let Some(cleanup) = cleanup else {
            self.error(
                Code::E0541,
                binding,
                "resource type has no cleanup function",
            );
            return;
        };
        let Some(signature) = self.program.callables.get(&cleanup) else {
            self.error(
                Code::E0541,
                binding,
                "cleanup is not a callable declaration",
            );
            return;
        };
        let [parameter] = signature.parameters.as_slice() else {
            self.error(
                Code::E0541,
                binding,
                "cleanup must take one resource argument",
            );
            return;
        };
        if signature.result != Ty::Unit
            || !matches!(parameter.mode, Mode::Ref | Mode::Mut | Mode::New)
            || signature
                .state
                .iter()
                .any(|clause| matches!(clause.as_str(), "^mut" | "capture" | "up"))
            || (parameter.mode == Mode::Mut) != signature.state.iter().any(|clause| clause == "mut")
            || !matches!(&parameter.ty, Ty::Adt(owner) if owner.definition == adt.definition)
        {
            self.error(
                Code::E0541,
                binding,
                "cleanup must take new, mut, or ref Self and return ()",
            );
        }
        if signature.effects.iter().any(|effect| effect == "fiber") {
            self.error(Code::E0616, binding, "@fiber is prohibited on cleanup");
        }
        if let Some(export) = self.program.imported_functions.get(&cleanup) {
            let owner = self.program.hir.definition(cleanup).name.span;
            self.charge_imported_effects(ctx, ledger, owner, signature, &export.summary, binding);
        } else {
            for effect in &signature.effects {
                self.effect(ctx, ledger, effect, binding);
            }
        }
        if parameter.mode == Mode::New && !value.requires_new {
            self.error(
                Code::E0548,
                binding,
                "cleanup requires a new-qualified resource",
            );
        }
        if parameter.mode == Mode::Mut || mode == Mode::Mut {
            if !value.writers() {
                self.error(
                    Code::E0520,
                    binding,
                    "cleanup requires writable resource authority",
                );
            } else if parameter.mode == Mode::Mut {
                self.mutate(ctx, ledger, value, binding);
            }
        }
        value.transform(&mut |origin| {
            origin.confined = Some(binding);
            origin.fix_mode(if mode == Mode::Mut {
                Access::Mut
            } else {
                Access::Ref
            });
        });
        self.cleanups
            .insert(binding, CleanupAction::Function(cleanup));
    }

    fn bind(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        id: PatternId,
        storage: &Storage,
        mut value: Datum,
        site: BindingSite,
    ) {
        let resource = site == BindingSite::Resource;
        let node = self.ast(ctx.file).pattern(id);
        match &node.value {
            Pattern::Binding(own, name) => {
                self.check_resource_binding(name.span, &value, resource);
                let binding = self
                    .definition(name.span)
                    .unwrap_or_else(|| ril_base::ice!("unresolved binding pattern"));
                let declaration = self.program.hir.definition(binding).name.span;
                if ctx.in_function {
                    self.binding_scopes.insert(declaration, ctx.scope);
                }
                let mode = if own.mode == Mode::Plain {
                    storage.mode
                } else {
                    own.mode
                };
                let variable = own.variable || storage.variable;
                let access = if resource && mode != Mode::Mut {
                    Access::Ref
                } else {
                    Access::from_mode(mode)
                };
                if variable {
                    self.requirement(
                        ctx,
                        name.span,
                        Obligation::Replace(declaration),
                        "var requires reachable slot replacement",
                    );
                }
                if matches!(mode, Mode::Mut | Mode::Shared) {
                    self.require_schema(ctx, &value, SchemaRequirement::Writable);
                    self.requirement(
                        ctx,
                        name.span,
                        Obligation::Write(declaration),
                        "writable binding requires reachable use",
                    );
                }
                match mode {
                    Mode::Mut if site == BindingSite::Declaration => {
                        self.check_exclusive_reception(&value, name.span);
                    }
                    Mode::Mut if !value.requires_new && !value.writers() => self.error(
                        Code::E0520,
                        name.span,
                        "binding cannot manufacture write authority",
                    ),
                    Mode::Shared => self.require_shared_local(ctx, declaration, &value),
                    Mode::Ref if !resource => {
                        self.check_ref_binding(name.span, &value, variable);
                        if variable {
                            self.check_ref_scope(name.span, &value, ctx.scope);
                        }
                    }
                    Mode::Via if ctx.via.is_empty() && !ctx.member_via => {
                        self.error(Code::E0412, name.span, "let via requires a mode template");
                    }
                    Mode::Via
                        if !value.origins().any(|origin| {
                            origin.inherits_mode
                                || origin
                                    .callback_result
                                    .is_some_and(|result| result.cap.is_none())
                                || !origin.reception.is_empty()
                        }) =>
                    {
                        self.error(
                            Code::E0550,
                            name.span,
                            "let via requires mode-dependent provenance",
                        );
                    }
                    _ => {}
                }
                if let Some(ty) = self.program.bindings.get(&binding) {
                    if ty.is_value() && matches!(mode, Mode::Mut | Mode::Shared | Mode::Ref) {
                        self.error(
                            Code::E0402,
                            name.span,
                            "value-type binding cannot carry live access",
                        );
                    } else if matches!(ty, Ty::Adt(adt) if adt.kind == AdtKind::Foreign) && variable
                    {
                        self.error(
                            Code::E0532,
                            name.span,
                            "foreign handle cannot be stored in a reassignable slot",
                        );
                    } else if matches!(ty, Ty::Adt(adt) if adt.kind == AdtKind::Foreign)
                        && mode == Mode::Plain
                        && !resource
                    {
                        self.error(Code::E0535, name.span, "foreign handle cannot be frozen");
                    }
                }
                if mode == Mode::Plain && !resource {
                    self.freeze_value(ctx, ledger, &mut value, name.span);
                } else if mode != Mode::Via {
                    value.receive_binding(access);
                } else {
                    value.forget_collection_layout();
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(declaration.into());
                });
                ledger.stamp(&mut value);
                ledger.slots.insert(
                    declaration,
                    Slot {
                        decl: declaration,
                        variable,
                        mode,
                        value,
                    },
                );
            }
            Pattern::Wildcard => {
                if resource && storage.mode == Mode::Mut {
                    self.error(
                        Code::E0527,
                        node.span,
                        "use mut _ cannot use write authority",
                    );
                }
                self.discard(ledger, &value);
            }
            Pattern::Tuple(items) => {
                for (i, &item) in items.iter().enumerate() {
                    let coordinate = Coordinate::Index(i.to_string());
                    let mode = self.schema_mode(self.ty(node.span), &coordinate).0;
                    let span = self.ast(ctx.file).pattern(item).span;
                    let child =
                        self.project_observed(ctx, ledger, &value, (coordinate, mode, span));
                    if let Pattern::Binding(own, name) = &self.ast(ctx.file).pattern(item).value {
                        let requested = if own.mode == Mode::Plain {
                            storage.mode
                        } else {
                            own.mode
                        };
                        let member_mode = Access::from_mode(mode);
                        if matches!(requested, Mode::Mut | Mode::Shared)
                            && mode != Mode::Via
                            && !member_mode.writes()
                            && !child.origins().any(|origin| origin.draft)
                        {
                            self.error(
                                Code::E0551,
                                name.span,
                                "tuple slot cannot decompose with writable authority",
                            );
                        }
                    }
                    self.bind(ctx, ledger, item, storage, child, site);
                }
            }
            Pattern::Slice { text, elements } => {
                let ast = self.ast(ctx.file);
                let (before, rest, after) = ast.slice_parts(elements);
                let mode = self.schema_mode(self.ty(node.span), &Coordinate::Dynamic).0;
                for (index, &item) in before.iter().enumerate() {
                    let child = self.project_observed(
                        ctx,
                        ledger,
                        &value,
                        (
                            Coordinate::Index(index.to_string()),
                            mode,
                            ast.pattern(item).span,
                        ),
                    );
                    self.bind(ctx, ledger, item, storage, child, site);
                }
                for &item in after {
                    let child = self.project_observed(
                        ctx,
                        ledger,
                        &value,
                        (Coordinate::Dynamic, mode, ast.pattern(item).span),
                    );
                    self.bind(ctx, ledger, item, storage, child, site);
                }
                if let Some(rest) = rest
                    && let Pattern::Rest(Some(name)) = &ast.pattern(rest).value
                {
                    let decl = self.declaration(name.span).unwrap_or(name.span);
                    if ctx.in_function {
                        self.binding_scopes.insert(decl, ctx.scope);
                    }
                    let mut slice = if let Ty::Array(element) = self.ty(node.span) {
                        let end = self
                            .slice_source_length(ledger, &value)
                            .and_then(|len| len.checked_sub(after.len()));
                        self.array_slice(
                            ctx,
                            ledger,
                            &value,
                            element,
                            (Some(before.len()), end),
                            ast.pattern(rest).span,
                        )
                    } else {
                        Datum::default()
                    };
                    self.check_resource_binding(name.span, &slice, resource);
                    slice.transform(&mut |origin| {
                        origin.dependencies.insert(decl.into());
                    });
                    ledger.slots.insert(
                        decl,
                        Slot {
                            decl,
                            variable: false,
                            mode: if *text { Mode::Plain } else { Mode::New },
                            value: slice,
                        },
                    );
                }
            }
            Pattern::Constructor(_, payload) => {
                let items = payload.as_deref().unwrap_or(&[]);
                for (i, &item) in items.iter().enumerate() {
                    let child = self.project_observed(
                        ctx,
                        ledger,
                        &value,
                        (
                            Coordinate::Index(i.to_string()),
                            Mode::Plain,
                            self.ast(ctx.file).pattern(item).span,
                        ),
                    );
                    if items.len() > 1
                        && let Pattern::Binding(own, name) = &self.ast(ctx.file).pattern(item).value
                    {
                        let requested = if own.mode == Mode::Plain {
                            storage.mode
                        } else {
                            own.mode
                        };
                        if matches!(requested, Mode::Mut | Mode::Shared)
                            && !child.origins().any(|origin| origin.draft)
                        {
                            self.error(
                                Code::E0551,
                                name.span,
                                "variant payload slot cannot decompose with writable authority",
                            );
                        }
                    }
                    self.bind(ctx, ledger, item, storage, child, site);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    let coordinate = Coordinate::Field(field.name.value.clone());
                    let mode = self.schema_mode(self.ty(node.span), &coordinate).0;
                    let member_mode = Access::from_mode(mode);
                    let span = field.pattern.map_or(field.name.span, |item| {
                        self.ast(ctx.file).pattern(item).span
                    });
                    let child =
                        self.project_observed(ctx, ledger, &value, (coordinate, mode, span));
                    let mut received = field.storage.clone();
                    if received.mode == Mode::Plain {
                        received.mode = storage.mode;
                    }
                    let requested = field
                        .pattern
                        .and_then(|id| match &self.ast(ctx.file).pattern(id).value {
                            Pattern::Binding(binding, _) if binding.mode != Mode::Plain => {
                                Some(binding.mode)
                            }
                            _ => None,
                        })
                        .unwrap_or(received.mode);
                    if matches!(requested, Mode::Mut | Mode::Shared)
                        && !(child.writers()
                            && (member_mode.writes() || child.origins().any(|origin| origin.draft)))
                    {
                        self.error(
                            Code::E0521,
                            field.name.span,
                            "pattern field cannot receive writable authority",
                        );
                    }
                    if let Some(pattern) = field.pattern {
                        self.bind(ctx, ledger, pattern, &received, child, site);
                    } else {
                        let mut child = child;
                        let decl = self.declaration(field.name.span).unwrap_or(field.name.span);
                        if child.writers() {
                            match requested {
                                Mode::Mut if site == BindingSite::Declaration => {
                                    self.check_exclusive_reception(&child, decl);
                                }
                                Mode::Shared => self.require_shared_local(ctx, decl, &child),
                                _ => {}
                            }
                        }
                        if ctx.in_function {
                            self.binding_scopes.insert(decl, ctx.scope);
                        }
                        self.check_resource_binding(field.name.span, &child, resource);
                        child.transform(&mut |origin| {
                            origin.dependencies.insert(decl.into());
                        });
                        ledger.slots.insert(
                            decl,
                            Slot {
                                decl,
                                variable: received.variable,
                                mode: requested,
                                value: child,
                            },
                        );
                    }
                }
            }
            Pattern::Or(items) => {
                let mut alternatives = Vec::new();
                for (index, &item) in items.iter().enumerate() {
                    let mut branch = ledger.clone();
                    branch.take_choice(node.span, index);
                    let mut value = value.clone();
                    branch.stamp(&mut value);
                    self.bind(ctx, &mut branch, item, storage, value, site);
                    alternatives.push(branch);
                }
                ledger.merge_bindings(&alternatives);
            }
            Pattern::Subset {
                binding: Some(id), ..
            } => self.bind(ctx, ledger, *id, storage, value, site),
            _ => {}
        }
    }

    fn expr(&mut self, ctx: &mut Context, ledger: &mut Ledger, id: ExprId) -> Datum {
        self.expr_with_truth(ctx, ledger, id, None)
    }

    fn expr_with_truth(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        id: ExprId,
        truth: Option<bool>,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let node = ast.expr(id);
        let span = node.span;
        if let Some((base, steps)) = ast.navigation_chain(id) {
            return self.navigate(ctx, ledger, base, &steps, span);
        }
        let mut value = match &node.value {
            Expr::Path(path) => self.read(ctx, ledger, path),
            Expr::Unary { op, value } => {
                let operand_truth = if op.value == "!" {
                    truth.map(|truth| !truth)
                } else {
                    None
                };
                let mut value = self.expr_with_truth(ctx, ledger, *value, operand_truth);
                match op.value.as_str() {
                    "new" => self.handoff(ctx, ledger, &mut value, span),
                    "ref" => {
                        for root in &mut value.roots {
                            root.fix_mode(Access::Ref);
                            root.new &= value.requires_new;
                        }
                        value.requires_new = false;
                    }
                    "^mut" => {
                        if !value.writers() {
                            self.error(Code::E0520, span, "sharing requires writable authority");
                        }
                        self.require_schema(ctx, &value, SchemaRequirement::Writable);
                        for root in &mut value.roots {
                            root.new &= value.requires_new || root.explicit_share;
                            root.fix_mode(Access::Shared);
                            root.explicit_share = true;
                        }
                        value.requires_new = false;
                    }
                    "?" => {
                        value = self.propagated(ctx, ledger, value, op.span);
                    }
                    _ => value = Datum::default(),
                }
                value
            }
            Expr::Binary { op, left, right } => {
                // These predicate outcomes require both operands to be evaluated.
                let both = matches!(
                    (op.value.as_str(), truth),
                    ("&&", Some(true)) | ("||", Some(false))
                );
                let operand_truth = truth.filter(|_| both);
                let lhs = self.expr_with_truth(ctx, ledger, *left, operand_truth);
                let literal = self.literal_bool(ctx, *left);
                let skip = matches!(
                    (op.value.as_str(), literal),
                    ("&&", Some(false)) | ("||", Some(true))
                );
                let fallible = op.value == "??" && self.ty(ast.expr(*left).span).is_result();
                if fallible {
                    ledger.inspect_root(&lhs);
                }
                let optional_rhs = op.value == "??"
                    || !both && matches!((op.value.as_str(), literal), ("&&" | "||", None));
                let rhs = if skip {
                    let mut dead = ctx.clone();
                    dead.reachable = false;
                    self.expr(&mut dead, &mut ledger.clone(), *right)
                } else if optional_rhs {
                    let before = ledger.clone();
                    let mut skipped = before.clone();
                    skipped.take_choice(span, 0);
                    ledger.take_choice(span, 1);
                    let mut rhs_ctx = ctx.clone();
                    let result = if fallible {
                        self.fallback_handler(&mut rhs_ctx, ledger, *right, span)
                    } else {
                        self.expr(&mut rhs_ctx, ledger, *right)
                    };
                    ctx.return_values = rhs_ctx.return_values;
                    let mut taken = ledger.clone();
                    taken.no_continuation |= self.ty(ast.expr(*right).span) == &Ty::Never;
                    ledger.merge(&before, &[skipped, taken]);
                    result
                } else {
                    self.expr_with_truth(ctx, ledger, *right, operand_truth)
                };
                if is_assignment(&op.value) {
                    let place = self.place(ctx, ledger, *left, lhs);
                    self.write(ctx, ledger, *left, &place, rhs, span);
                    Datum::default()
                } else if op.value == "??" {
                    ledger
                        .project(&lhs, Coordinate::Index("0".into()), Access::Immutable)
                        .joined(rhs)
                } else {
                    if matches!(op.value.as_str(), "==" | "!=")
                        && (self.result_constructor(ctx, *right)
                            || self.result_constructor(ctx, *left))
                    {
                        ledger.inspect_root(&lhs);
                        ledger.inspect_root(&rhs);
                    }
                    Datum::default()
                }
            }
            Expr::Record { fields, .. } => {
                let mut record = Datum::source(span, Access::Mut, true);
                for field in fields {
                    let coordinate = Coordinate::Field(field.name.value.clone());
                    let value = if let Some(expr) = field.value {
                        self.expr(ctx, ledger, expr)
                    } else {
                        self.read_span(ctx, ledger, field.name.span)
                    };
                    let access = self.member_schema(span, &coordinate).0;
                    let value = self.receive_member(
                        ctx,
                        ledger,
                        value,
                        access,
                        field.value.map_or(field.name.span, |id| ast.expr(id).span),
                    );
                    record.members.insert(coordinate, value);
                }
                record
            }
            Expr::Tuple(items) | Expr::Array(items) => {
                let mut sequence = Datum::source(span, Access::Mut, true);
                if let Ty::Array(member) = self.ty(span) {
                    if higher_order::carries_callable(self.program, &member.ty) {
                        ledger.record_array_length(span, items.len());
                    }
                    if results::carries_result(self.program, &member.ty) {
                        sequence.array_len = Some(items.len());
                    }
                }
                for (i, &item) in items.iter().enumerate() {
                    let coordinate = Coordinate::Index(i.to_string());
                    let value = self.expr(ctx, ledger, item);
                    let access = self.member_schema(span, &coordinate).0;
                    let value =
                        self.receive_member(ctx, ledger, value, access, ast.expr(item).span);
                    sequence.members.insert(coordinate, value);
                }
                sequence
            }
            Expr::Map(entries) => {
                let mut map = Datum::source(span, Access::Mut, true);
                let keys: Option<Vec<_>> = entries
                    .iter()
                    .map(|&(id, _)| self.constant_map_key(ctx, id))
                    .collect();
                let keys = keys.or_else(|| (entries.len() == 1).then(|| vec![Coordinate::Dynamic]));
                let mut ordered_keys = Vec::new();
                for (index, &(key, value)) in entries.iter().enumerate() {
                    let mut key_value = self.expr(ctx, ledger, key);
                    if !key_value.roots.is_empty() {
                        // A later duplicate replaces the value while retaining the first key.
                        if index > 0 {
                            key_value.forget_results();
                        }
                        let key_value = self.receive_member(
                            ctx,
                            ledger,
                            key_value,
                            Access::Immutable,
                            ast.expr(key).span,
                        );
                        let slot = map.members.entry(Coordinate::MapKey).or_default();
                        *slot = std::mem::take(slot).joined(key_value);
                    }
                    let coordinate = keys
                        .as_ref()
                        .and_then(|keys| keys.get(index))
                        .cloned()
                        .unwrap_or(Coordinate::Dynamic);
                    let access = self.member_schema(span, &coordinate).0;
                    let mut datum = self.expr(ctx, ledger, value);
                    if keys.is_none() && index + 1 < entries.len() {
                        // An unknown later key may replace this occurrence.
                        datum.forget_results();
                    }
                    let datum =
                        self.receive_member(ctx, ledger, datum, access, ast.expr(value).span);
                    if keys.is_some() {
                        if map.members.insert(coordinate.clone(), datum).is_none() {
                            ordered_keys.push(coordinate);
                        }
                    } else {
                        let slot = map.members.entry(coordinate).or_default();
                        *slot = std::mem::take(slot).joined(datum);
                    }
                }
                if results::carries_result(self.program, self.ty(span)) {
                    map.map_keys = keys.map(|_| ordered_keys);
                }
                map
            }
            Expr::Member { base, member, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate = self.coordinate(ctx, ledger, member);
                let (mode, variable) = self.schema_mode(self.ty(ast.expr(*base).span), &coordinate);
                let mode = if variable && self.ty(span).is_value() {
                    Mode::Mut
                } else {
                    mode
                };
                self.project_observed(ctx, ledger, &value, (coordinate, mode, span))
            }
            Expr::Index { base, index, .. } => {
                let value = self.expr(ctx, ledger, *base);
                self.expr(ctx, ledger, *index);
                let ty = self.ty(ast.expr(*base).span);
                self.project_index(ctx, ledger, &value, (ty, *index, span))
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                let mut local_ctx = ctx.clone();
                local_ctx.scope = span;
                for &helper in helpers {
                    if let StmtKind::Effect { name, .. } = &ast.stmt(helper).value.kind
                        && let Some(effect) = self.definition(name.span)
                    {
                        local_ctx
                            .local_effects
                            .insert(self.program.hir.effect_label(effect));
                    }
                }
                let start_returns = local_ctx.return_values.len();
                let prior = ledger.slots.keys().copied().collect::<BTreeSet<_>>();
                let prior_iter = ledger.iteration.len();
                let prior_holds = ledger.holds.len();
                let mut result = Datum::default();
                for (i, &item) in statements.iter().enumerate() {
                    let is_tail = i + 1 == statements.len();
                    result = self.statement(&mut local_ctx, ledger, item, is_tail);
                    if let StmtKind::Expr(expr) = ast.stmt(item).value.kind
                        && self.ty(ast.expr(expr).span) == &Ty::Never
                    {
                        local_ctx.reachable = false;
                    }
                }
                for &helper in helpers {
                    self.statement(&mut local_ctx, ledger, helper, false);
                }
                if result.origins().any(|origin| {
                    origin
                        .confined
                        .is_some_and(|id| span.start <= id.start && id.end <= span.end)
                }) {
                    self.error(Code::E0604, span, "resource or draft escapes its block");
                }
                ledger.slots.retain(|id, _| prior.contains(id));
                ledger.iteration.truncate(prior_iter);
                ledger.holds.truncate(prior_holds);
                ctx.return_values
                    .extend(local_ctx.return_values.into_iter().skip(start_returns));
                result
            }
            Expr::If { condition, yes, no } => {
                let before = ledger.clone();
                let literal = match condition {
                    Condition::Expr(test) => self.literal_bool(ctx, *test),
                    _ => None,
                };
                let mut then_ledger = before.clone();
                then_ledger.take_choice(span, 0);
                let mut yes_ctx = ctx.clone();
                yes_ctx.scope = ast.expr(*yes).span;
                yes_ctx.reachable &= literal != Some(false);
                let takes_yes = self.condition(&mut yes_ctx, &mut then_ledger, condition, true);
                let yes_value = if takes_yes {
                    self.expr(&mut yes_ctx, &mut then_ledger, *yes)
                } else {
                    Datum::default()
                };
                let mut else_ledger = before.clone();
                else_ledger.take_choice(span, 1);
                let mut no_ctx = ctx.clone();
                no_ctx.reachable &= literal != Some(true);
                let takes_no = self.condition(&mut no_ctx, &mut else_ledger, condition, false);
                let no_value = no
                    .filter(|_| takes_no)
                    .map(|expr| self.expr(&mut no_ctx, &mut else_ledger, expr))
                    .unwrap_or_default();
                let count = ctx.return_values.len();
                ctx.return_values
                    .extend(yes_ctx.return_values.into_iter().skip(count));
                ctx.return_values
                    .extend(no_ctx.return_values.into_iter().skip(count));
                let can_yes = literal != Some(false) && self.ty(ast.expr(*yes).span) != &Ty::Never;
                let can_no = literal != Some(true)
                    && no.is_none_or(|no| self.ty(ast.expr(no).span) != &Ty::Never);
                let mut alternatives = Vec::new();
                let can_yes_continue = can_yes && takes_yes && !then_ledger.no_continuation;
                let can_no_continue = can_no && takes_no && !else_ledger.no_continuation;
                if can_yes_continue {
                    alternatives.push(then_ledger);
                }
                if can_no_continue {
                    alternatives.push(else_ledger);
                }
                ledger.merge(&before, &alternatives);
                match (can_yes_continue, can_no_continue) {
                    (true, true) => yes_value.joined(no_value),
                    (true, false) => yes_value,
                    (false, true) => no_value,
                    _ => Datum::default(),
                }
            }
            Expr::While { condition, body } => {
                let literal = match condition {
                    Condition::Expr(test) => self.literal_bool(ctx, *test),
                    Condition::Binding { .. } => None,
                };
                self.check_loop(
                    ctx,
                    ledger,
                    LoopSyntax {
                        owner: span,
                        repeated: span,
                        body: *body,
                        extent: LoopExtent::Repeat,
                        exact_elements: false,
                    },
                    |this, local, inside, _| {
                        if matches!(condition, Condition::Binding { .. }) {
                            let mut failed = inside.clone();
                            let mut failed_ctx = local.clone();
                            let exits =
                                this.condition(&mut failed_ctx, &mut failed, condition, false)
                                    && failed_ctx.reachable;
                            local.reachable &= this.condition(local, inside, condition, true);
                            (exits.then_some(failed), None)
                        } else {
                            this.condition(local, inside, condition, true);
                            let exit =
                                (literal != Some(true) && local.reachable).then(|| inside.clone());
                            local.reachable &= literal != Some(false);
                            (exit, None)
                        }
                    },
                );
                Datum::default()
            }
            Expr::For {
                iterable,
                pattern,
                body,
                mode,
            } => {
                let value = self.expr(ctx, ledger, *iterable);
                let storage = Storage {
                    mode: *mode,
                    ..Storage::default()
                };
                let iterable_type = self.ty(ast.expr(*iterable).span);
                let schema = self.schema_mode(iterable_type, &Coordinate::Dynamic).0;
                let traverse = |this: &mut Self,
                                ctx: &mut Context,
                                ledger: &mut Ledger,
                                value: Datum| {
                    let length = value
                        .array_len
                        .or_else(|| value.map_keys.as_ref().map(Vec::len));
                    let extent = length
                        .map_or_else(|| this.iterable_extent(ctx, *iterable), LoopExtent::Exact);
                    this.check_loop(
                        ctx,
                        ledger,
                        LoopSyntax {
                            owner: span,
                            repeated: ast.pattern(*pattern).span.join(ast.expr(*body).span),
                            body: *body,
                            extent,
                            exact_elements: length.is_some(),
                        },
                        |this, local, inside, index| {
                            let exit = (extent != LoopExtent::Exact(1)).then(|| inside.clone());
                            local.reachable &= extent != LoopExtent::Exact(0);
                            inside.iteration.push(value.clone());
                            let coordinate = match (&value.map_keys, index) {
                                (Some(keys), Some(index)) => {
                                    keys.get(index).cloned().unwrap_or(Coordinate::Dynamic)
                                }
                                (None, Some(index)) => Coordinate::Index(index.to_string()),
                                (_, None) => Coordinate::Dynamic,
                            };
                            let mut child = inside.project_schema(&value, coordinate, schema);
                            let pattern_span = ast.pattern(*pattern).span;
                            if let Ty::Map(key_ty, value_ty) = iterable_type {
                                let key = if key_ty.is_value() {
                                    Datum::default()
                                } else {
                                    inside.project_schema(&value, Coordinate::MapKey, Mode::Plain)
                                };
                                let mut pair = Datum::source(pattern_span, Access::Mut, true);
                                pair.members.insert(Coordinate::Index("0".into()), key);
                                pair.members.insert(
                                    Coordinate::Index("1".into()),
                                    if value_ty.ty.is_value() {
                                        Datum::default()
                                    } else {
                                        child
                                    },
                                );
                                child = pair;
                            }
                            let traversal =
                                if matches!(iterable_type, Ty::Array(_) | Ty::Map(..) | Ty::Set(_))
                                    && local.reachable
                                {
                                    results::CollectionTraversal::enter(
                                        this.program,
                                        inside,
                                        this.ty(pattern_span),
                                        &value,
                                        &mut child,
                                        pattern_span,
                                    )
                                } else {
                                    None
                                };
                            this.pattern_tests(local, inside, *pattern, &child)
                                .inspect(inside, true);
                            this.bind(
                                local,
                                inside,
                                *pattern,
                                &storage,
                                child,
                                BindingSite::ScopedPattern,
                            );
                            (exit, traversal)
                        },
                    );
                };
                let paths = ledger.iterable_result_paths(&value);
                if paths.is_empty() {
                    traverse(self, ctx, ledger, value);
                } else {
                    let before = ledger.clone();
                    let alternatives: Vec<_> = paths
                        .into_iter()
                        .map(|(mut path, selected)| {
                            traverse(self, ctx, &mut path, selected);
                            path
                        })
                        .collect();
                    ledger.merge(&before, &alternatives);
                }
                Datum::default()
            }
            Expr::Match { mode, value, arms } => {
                let value = self.expr(ctx, ledger, *value);
                let paths = ledger.variant_paths(&value);
                if paths.is_empty() {
                    self.match_value(ctx, ledger, *mode, &value, arms, span)
                } else {
                    let before = ledger.clone();
                    let mut alternatives = Vec::with_capacity(paths.len());
                    let mut output = None;
                    for (mut branch, selected) in paths {
                        let value =
                            self.match_value(ctx, &mut branch, *mode, &selected, arms, span);
                        if !branch.no_continuation {
                            output = Some(match output {
                                Some(previous) => value.joined(previous),
                                None => value,
                            });
                            alternatives.push(branch);
                        }
                    }
                    ledger.merge(&before, &alternatives);
                    output.unwrap_or_default()
                }
            }
            Expr::Call { callee, args } => self.call(ctx, ledger, *callee, args, span),
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let mut args = vec![ril_frontend::syntax::Argument {
                    value: *value,
                    mode: *mode,
                    name: None,
                }];
                let callee = if let Expr::Call { callee, args: rest } = &ast.expr(*target).value {
                    args.extend(rest.iter().cloned());
                    *callee
                } else {
                    *target
                };
                let result = self.call(ctx, ledger, callee, &args, span);
                if *propagate {
                    self.propagated(ctx, ledger, result, span)
                } else {
                    result
                }
            }
            Expr::Transfer { kind, value } => {
                let value = value
                    .map(|value| self.expr(ctx, ledger, value))
                    .unwrap_or_default();
                if ctx.reachable {
                    match kind {
                        Transfer::Return => {
                            self.returned(ctx, ledger, value, span);
                            self.check_results(ledger, &BTreeSet::new());
                        }
                        Transfer::Break | Transfer::Continue => {
                            if let Some(owner) = ctx.loop_owner {
                                let exits = self.loop_transfers.entry(owner).or_default();
                                let paths = if *kind == Transfer::Break {
                                    &mut exits.breaks
                                } else {
                                    &mut exits.continues
                                };
                                paths.push(ledger.clone());
                            }
                        }
                    }
                }
                ledger.no_continuation = true;
                Datum::default()
            }
            Expr::Closure { .. } => self.closure(ctx, ledger, id, false),
            Expr::Cast { value, .. } => self.expr(ctx, ledger, *value),
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let ril_frontend::syntax::StringPart::Interpolation(expr) = part {
                        self.expr(ctx, ledger, *expr);
                    }
                }
                Datum::default()
            }
            Expr::Range { start, end, .. } => {
                for &id in start.iter().chain(end) {
                    self.expr(ctx, ledger, id);
                }
                Datum::default()
            }
            Expr::Quote(_) | Expr::Literal(_) | Expr::Unit | Expr::Accessor(_) | Expr::Hole => {
                Datum::default()
            }
        };
        ctx.reachable &= !ledger.no_continuation;
        if ctx.reachable
            && (self.ty(span).is_result()
                || matches!(self.ty(span), Ty::Task(inner) if inner.is_result()))
            && !value.has_root_result()
            && !matches!(node.value, Expr::Path(_))
        {
            ledger.record_result(&mut value, span);
        }
        if self.ty(span).is_value() {
            value.roots.clear();
            value.members.clear();
            value.requires_new = false;
        }
        if matches!(
            node.value,
            Expr::Member { .. } | Expr::Index { .. } | Expr::Call { .. } | Expr::Pipeline { .. }
        ) {
            for root in &mut value.roots {
                root.explicit_share = false;
                root.from_variable = false;
            }
        }
        ledger.stamp(&mut value);
        value
    }

    fn read(&mut self, ctx: &Context, ledger: &Ledger, path: &Path) -> Datum {
        self.read_span(ctx, ledger, path.span)
    }

    fn read_span(&mut self, ctx: &Context, ledger: &Ledger, span: Span) -> Datum {
        let Some(id) = self.definition(span) else {
            return Datum::default();
        };
        if self.program.meta_parameters.contains(&id) {
            return Datum::default();
        }
        let definition = self.program.hir.definition(id);
        let decl = definition.name.span;
        if let Some(slot) = ledger.slots.get(&decl) {
            self.check_live(
                ctx,
                ledger,
                &slot.value,
                span,
                "source path was ended by new handoff",
            );
            if ctx.in_function
                && decl.start < ctx.owner.start
                && !ctx.formals.contains(&Some(decl))
                && self
                    .definition(span)
                    .is_some_and(|id| self.program.hir.definition(id).kind == DefinitionKind::Local)
            {
                self.seed(ctx, Obligation::ReadUp(decl));
            }
            let mut value = slot.value.clone();
            ctx.mark_capture(slot, &mut value);
            for root in &mut value.roots {
                root.explicit_share = false;
                root.from_variable = slot.variable;
                root.anchor_scopes.clear();
                root.anchor_scopes.extend(self.binding_scopes.get(&decl));
            }
            value
        } else if self.program.hir.unit_constructor(id)
            || matches!(definition.kind, DefinitionKind::Primitive(_))
                && definition.name.value == "None"
                && matches!(self.ty(span), Ty::Option(_))
            || matches!(definition.kind, DefinitionKind::Variant(_))
                && matches!(self.ty(span), Ty::Adt(adt) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum))
        {
            let mut value = Datum::source(span, Access::Mut, true);
            value.set_variant(&definition.name.value);
            value
        } else if !self.ty(span).is_value()
            && matches!(
                self.program.hir.definition(id).kind,
                DefinitionKind::Constant | DefinitionKind::Function
            )
        {
            let mut value = Datum::source(decl, Access::Immutable, false);
            if definition.kind == DefinitionKind::Function {
                for root in &mut value.roots {
                    root.snapshot_provider = Some(decl);
                }
                value.live_callable_state = self.named_value_has_live_state(id, ctx, ledger);
            }
            value
        } else {
            Datum::default()
        }
    }

    fn named_value_has_live_state(
        &mut self,
        id: DefinitionId,
        ctx: &Context,
        ledger: &Ledger,
    ) -> bool {
        let function = self.function_syntax(id);
        let mut captured = self
            .function_syntax(id)
            .into_iter()
            .flat_map(|fun| &fun.signature.obligations.state)
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings);
        if captured.any(|(storage, path)| {
            storage.variable
                || storage.mode != Mode::Plain
                || self
                    .declaration(path.span)
                    .and_then(|decl| ledger.slots.get(&decl))
                    .is_some_and(|slot| {
                        slot.variable
                            || slot.value.contains_live_callable_environment()
                            || slot
                                .value
                                .origins()
                                .any(|root| root.mode != Access::Immutable)
                    })
        }) {
            return true;
        }
        let live_handlers: Vec<_> = self
            .program
            .callables
            .get(&id)
            .into_iter()
            .flat_map(|callable| &callable.effects)
            .flat_map(|effect| self.effect_operations(effect))
            .filter(|operation| {
                ctx.handlers.get(operation).is_some_and(|handler| {
                    handler.live_callable_state
                        || handler
                            .origins()
                            .any(|origin| origin.mode != Access::Immutable)
                })
            })
            .collect();
        if live_handlers.is_empty() {
            return false;
        }
        if let Some(function) = function
            && ctx.reachable
            && !ctx.shadow
        {
            self.function(function, ledger);
        }
        live_handlers
            .iter()
            .any(|operation| self.named_may_use_handler(id, operation))
    }

    fn named_may_use_handler(&self, id: DefinitionId, operation: &Operation) -> bool {
        let uses_handler = |obligation: &Obligation| match obligation {
            Obligation::Operation(used) => used == operation,
            Obligation::Effect(effect) => self.program.effect_covers(effect, &operation.effect),
            _ => false,
        };
        if let Some(imported) = self.program.imported_functions.get(&id)
            && let Some(signature) = self.program.callables.get(&id)
        {
            let owner = self.program.hir.definition(id).name.span;
            return self
                .imported_effect_obligations(owner, signature, &imported.summary, owner)
                .iter()
                .any(uses_handler);
        }
        let Some(checked) = self.functions.iter().find(|function| function.id == id) else {
            // A foreign or currently recursive body has only its declared bound.
            return true;
        };
        self.rules.iter().any(|rule| {
            rule.conclusion.owner == checked.owner && uses_handler(&rule.conclusion.obligation)
        })
    }

    fn check_live(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
        message: &'static str,
    ) {
        if !ctx.reachable {
            return;
        }
        let revocations = ledger.revocations(value);
        if revocations.contains(&None) {
            self.error(Code::E0549, span, message);
        } else {
            for trigger in revocations.into_iter().flatten() {
                let premise = match trigger {
                    Revocation::Formal((owner, formal)) => Fact {
                        owner,
                        obligation: Obligation::Handoff(formal),
                    },
                    Revocation::Callback { site, position } => {
                        self.higher_order.protect_input(site, position);
                        Fact {
                            owner: site,
                            obligation: Obligation::CallbackHandoff(position),
                        }
                    }
                };
                self.deferred_errors
                    .push((vec![premise], Diagnostic::error(Code::E0549, span, message)));
            }
        }
    }

    fn handoff(&mut self, ctx: &Context, ledger: &mut Ledger, value: &mut Datum, span: Span) {
        if ledger.holds.iter().any(|(_, held)| {
            let held = ledger.loop_snapshot(held);
            value
                .roots
                .iter()
                .any(|moving| held.origins().any(|active| moving.overlaps(active)))
        }) {
            self.error(
                Code::E0535,
                span,
                "new handoff overlaps an active handler hold",
            );
            return;
        }
        if ledger
            .loop_snapshot(value)
            .origins()
            .any(|origin| origin.confined.is_some())
        {
            self.error(Code::E0604, span, "resource or draft cannot be handed off");
            return;
        }
        if !value.requires_new
            && (!value.writers()
                || value
                    .roots
                    .iter()
                    .any(|origin| origin.mode == Access::Shared))
        {
            self.error(
                Code::E0548,
                span,
                "new requires a new-qualified source or a pinned exclusive writer",
            );
            return;
        }
        if ledger.slots.values().any(|slot| {
            slot.mode == Mode::Shared
                && value.roots.iter().any(|root| {
                    ledger
                        .loop_snapshot(&slot.value)
                        .origins()
                        .any(|retained| root.overlaps(retained))
                })
        }) {
            self.error(
                Code::E0548,
                span,
                "new handoff has an independently retained shared writer",
            );
            return;
        }
        let dependencies: BTreeSet<_> = value
            .roots
            .iter()
            .flat_map(Origin::dependency_spans)
            .collect();
        if value
            .roots
            .iter()
            .flat_map(|origin| &origin.dependencies)
            .any(|dependency| {
                !dependency.prior_iteration
                    && ledger
                        .slots
                        .get(&dependency.span)
                        .is_some_and(|slot| slot.variable)
            })
        {
            self.error(Code::E0548, span, "reassignable slots cannot be handed off");
            return;
        }
        if ctx.reachable {
            for root in &value.roots {
                for &dependency in &root.dependencies {
                    ledger.revoke(dependency, Some(root), None);
                }
            }
        }
        self.require_schema(ctx, value, SchemaRequirement::Exclusive);
        for root in &value.roots {
            if ctx.via.contains(&root.region.source) {
                self.seed(ctx, Obligation::Handoff(root.region.source));
            }
        }
        for &id in &dependencies {
            if !ctx.via.contains(&id) {
                self.seed(ctx, Obligation::Write(id));
            }
        }
        value.detach_handed_off_paths();
    }

    fn place(&mut self, ctx: &mut Context, ledger: &mut Ledger, id: ExprId, prior: Datum) -> Datum {
        let ast = self.ast(ctx.file);
        match &ast.expr(id).value {
            Expr::Member { base, member, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate = self.coordinate(ctx, ledger, member);
                let (_, variable) = self.member_schema(ast.expr(*base).span, &coordinate);
                if variable || value.origins().any(|origin| origin.draft) {
                    value.slot_projection(coordinate)
                } else {
                    Datum::default()
                }
            }
            Expr::Index { base, index, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate =
                    self.collection_coordinate(ctx, self.ty(ast.expr(*base).span), *index);
                value.slot_projection(coordinate)
            }
            _ => prior,
        }
    }

    fn write(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        target: ExprId,
        prior: &Datum,
        value: Datum,
        span: Span,
    ) {
        let node = self.ast(ctx.file).expr(target);
        if let Expr::Path(path) = &node.value {
            if let Some(id) = self.declaration(path.span)
                && let Some((decl, mode, variable)) = ledger
                    .slots
                    .get(&id)
                    .map(|slot| (slot.decl, slot.mode, slot.variable))
            {
                if !variable {
                    self.error(
                        if mode == Mode::Plain {
                            Code::E0501
                        } else {
                            Code::E0502
                        },
                        node.span,
                        "binding cannot be reassigned",
                    );
                    return;
                }
                if self.references_scoped_resource(&value) {
                    self.error(
                        Code::E0604,
                        span,
                        "scoped resource cannot be assigned to a slot",
                    );
                }
                self.seed(ctx, Obligation::Replace(decl));
                for origin in value.origins().filter(|origin| origin.draft) {
                    if origin
                        .confined
                        .is_some_and(|scope| decl.start < scope.start)
                    {
                        self.error(
                            Code::E0607,
                            span,
                            "draft cannot be assigned to an outer slot",
                        );
                    }
                }
                let mut value = value;
                if mode == Mode::Shared {
                    self.require_shared_replacement(&value, span, false);
                    self.shared_local_input(ctx, decl, &value, span);
                } else if mode == Mode::Mut {
                    self.check_exclusive_reception(&value, span);
                } else if mode == Mode::Ref {
                    if value.roots.iter().any(|root| root.mode != Access::Ref) {
                        self.error(
                            Code::E0357,
                            span,
                            "ref slot replacement requires a ref expression",
                        );
                    } else {
                        self.check_ref_binding(span, &value, true);
                        if let Some(scope) = self.binding_scopes.get(&decl).copied() {
                            self.check_ref_scope(span, &value, scope);
                        }
                    }
                }
                let captured = ctx.caller_slots.contains(&id);
                if captured {
                    self.check_publication_source(ctx, ledger, &value, span);
                }
                if mode == Mode::Plain {
                    self.freeze_value(ctx, ledger, &mut value, span);
                } else {
                    value.receive_binding(Access::from_mode(mode));
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(decl.into());
                });
                if captured {
                    value.publications.insert(ctx.owner, true);
                }
                ledger.replace_slot(id, value, true);
                return;
            }
            self.error(
                Code::E0501,
                node.span,
                "assignment requires a replaceable local slot",
            );
            return;
        }
        let (Expr::Member { base, .. } | Expr::Index { base, .. }) = node.value else {
            self.error(Code::E0503, node.span, "invalid assignment target");
            return;
        };
        self.mutate(ctx, ledger, prior, span);
        self.check_draft_insertion(ctx, ledger, prior, &value, span);
        if let Some(coordinate) = prior
            .roots
            .first()
            .and_then(|origin| origin.region.selection.last())
        {
            let access = self
                .member_schema(self.ast(ctx.file).expr(base).span, coordinate)
                .0;
            if ctx.reachable
                && !value.roots.is_empty()
                && results::carries_result(self.program, self.ty(node.span))
            {
                ledger.lose_collection_elements_at(prior);
            }
            self.store_member((ctx, ledger), prior, value, access, span);
        }
    }

    fn store_member(
        &mut self,
        (ctx, ledger): (&Context, &mut Ledger),
        place: &Datum,
        value: Datum,
        access: Access,
        span: Span,
    ) {
        if ledger
            .loop_snapshot(&value)
            .origins()
            .any(|origin| origin.confined.is_some())
        {
            self.error(
                Code::E0604,
                span,
                "confined value cannot be stored in an outer object",
            );
        }
        if place.origins().any(|origin| {
            let source = origin.region.source;
            ctx.caller_sources.contains(&source)
                || ctx.formals.contains(&Some(source))
                    && (!ctx.new_formals.contains(&source) || !origin.new)
        }) {
            self.check_publication_source(ctx, ledger, &value, span);
        }
        if !ctx.reachable || value.roots.is_empty() {
            return;
        }
        if access == Access::Ref {
            self.check_stored_views(&ledger.loop_snapshot(&value), true, span);
        }
        if access == Access::Shared {
            self.require_shared_replacement(&value, span, true);
        }
        let mut value = self.receive_member(ctx, ledger, value, access, span);
        value
            .publications
            .insert(ctx.owner, place.roots.iter().any(|root| !root.new));
        ledger.replace_member(place, value, true);
    }

    fn check_draft_insertion(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        target: &Datum,
        value: &Datum,
        span: Span,
    ) {
        if target.roots.iter().any(|root| root.draft) {
            let snapshot = ledger.loop_snapshot(value);
            let message =
                "draft insertion requires an immutable snapshot or an isolated local value";
            if snapshot.origins().any(|origin| {
                origin.new
                    && origin.mode != Access::Immutable
                    && ctx.caller_sources.contains(&origin.region.source)
            }) {
                self.error(Code::E0535, span, message);
            } else {
                self.require_snapshot((ctx, ledger), &snapshot, Code::E0535, span, message);
            }
        }
    }

    fn mutate(&mut self, ctx: &Context, ledger: &Ledger, value: &Datum, span: Span) {
        if !value.writers() {
            self.error(Code::E0520, span, "write requires writable authority");
        }
        if ledger.slots.values().any(|slot| {
            slot.mode == Mode::Ref
                && slot.value.origins().any(|held| {
                    held.region.selection.iter().any(|coordinate| {
                        matches!(coordinate, Coordinate::Index(_) | Coordinate::Dynamic)
                    }) && value.origins().any(|written| held.overlaps(written))
                })
        }) {
            self.error(
                Code::E0537,
                span,
                "collection mutation overlaps a scoped element view",
            );
        }
        if ledger.iteration.iter().any(|iterable| {
            value
                .origins()
                .any(|value| iterable.origins().any(|iterator| value.overlaps(iterator)))
        }) {
            self.error(Code::E0526, span, "collection is already being iterated");
        }
        for conflict in ledger.hold_conflicts(value, Mode::Mut) {
            self.check_conflict(
                ctx,
                conflict,
                None,
                span,
                "write overlaps an active lexical handler hold",
            );
        }
        self.require_schema(ctx, value, SchemaRequirement::Writable);
        self.record_write(ctx, value);
    }

    fn record_write(&mut self, ctx: &Context, value: &Datum) {
        for origin in &value.roots {
            if !origin.new {
                self.seed(ctx, Obligation::WriteExisting(origin.region.source));
            }
            for id in origin
                .dependency_spans()
                .chain(std::iter::once(origin.region.source))
            {
                self.seed(ctx, Obligation::Write(id));
            }
        }
    }

    fn schema_requirements(&self, value: &Datum, mode: SchemaRequirement) -> BTreeSet<Obligation> {
        value
            .roots
            .iter()
            .flat_map(|origin| {
                origin
                    .reception
                    .iter()
                    .enumerate()
                    .filter_map(move |(index, step)| {
                        let Reception::Axis(path) = step else {
                            return None;
                        };
                        let axis = self.schema_axis(path)?.clone();
                        let mode = if index + 1 == origin.reception.len() {
                            mode
                        } else {
                            SchemaRequirement::Writable
                        };
                        Some(Obligation::Schema(axis, mode))
                    })
            })
            .collect()
    }

    fn require_schema(&mut self, ctx: &Context, value: &Datum, mode: SchemaRequirement) {
        for obligation in self.schema_requirements(value, mode) {
            self.seed(ctx, obligation);
        }
    }

    fn match_value(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        mode: Mode,
        value: &Datum,
        arms: &[MatchArm],
        span: Span,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let before = ledger.clone();
        let mut missed = Some(BTreeSet::new());
        let mut alternatives = Vec::new();
        let mut output = None;
        for (index, arm) in arms.iter().enumerate() {
            let Some(prefix) = missed else { break };
            let tests = self
                .pattern_tests(ctx, &before, arm.pattern, value)
                .after(&prefix);
            missed = tests.missed;
            let Some(inspected) = tests.matched else {
                continue;
            };
            let mut inside = before.clone();
            inside.mark_inspected(inspected);
            inside.take_choice(span, index);
            let mut local_ctx = ctx.clone();
            local_ctx.scope = ast.pattern(arm.pattern).span.join(ast.expr(arm.body).span);
            let storage = Storage {
                mode,
                ..Storage::default()
            };
            self.bind(
                &local_ctx,
                &mut inside,
                arm.pattern,
                &storage,
                value.clone(),
                BindingSite::ScopedPattern,
            );
            if let Some(guard) = arm.guard {
                self.expr(&mut local_ctx, &mut inside, guard);
                let truth = self.literal_bool(&local_ctx, guard);
                if truth != Some(true) && !inside.no_continuation {
                    missed = results::alternatives(missed, Some(inside.inspected.clone()));
                }
                if truth == Some(false) {
                    continue;
                }
            }
            let body = self.expr(&mut local_ctx, &mut inside, arm.body);
            let prior = ctx.return_values.len();
            ctx.return_values
                .extend(local_ctx.return_values.into_iter().skip(prior));
            if self.ty(ast.expr(arm.body).span) != &Ty::Never && !inside.no_continuation {
                output = Some(
                    output.map_or_else(|| body.clone(), |value: Datum| value.joined(body.clone())),
                );
                alternatives.push(inside);
            }
        }
        ledger.merge(&before, &alternatives);
        output.unwrap_or_default()
    }

    fn bind_on_match(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        pattern: PatternId,
        storage: &Storage,
        value: &Datum,
        site: BindingSite,
    ) -> bool {
        let paths = self.pattern_paths(ctx, ledger, pattern, value, true);
        let alternatives = paths
            .into_iter()
            .map(|(mut path, selected)| {
                self.bind(ctx, &mut path, pattern, storage, selected, site);
                path
            })
            .collect();
        ledger.continue_at_pattern(alternatives)
    }

    fn condition(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        condition: &Condition,
        matched: bool,
    ) -> bool {
        match condition {
            Condition::Expr(value) => {
                self.expr(ctx, ledger, *value);
            }
            Condition::Binding {
                mode,
                pattern,
                value,
            } => {
                let value = self.expr(ctx, ledger, *value);
                if matched {
                    return self.bind_on_match(
                        ctx,
                        ledger,
                        *pattern,
                        &Storage {
                            mode: *mode,
                            ..Storage::default()
                        },
                        &value,
                        BindingSite::ScopedPattern,
                    );
                }
                let alternatives = self
                    .pattern_paths(ctx, ledger, *pattern, &value, false)
                    .into_iter()
                    .map(|(ledger, _)| ledger)
                    .collect();
                return ledger.continue_at_pattern(alternatives);
            }
        }
        true
    }

    fn check_loop(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        syntax: LoopSyntax,
        prepare: impl Fn(
            &mut Self,
            &mut Context,
            &mut Ledger,
            Option<usize>,
        ) -> (Option<Ledger>, Option<results::CollectionTraversal>),
    ) {
        let LoopSyntax {
            owner,
            repeated,
            body,
            extent,
            exact_elements,
        } = syntax;
        let entry = ledger.clone();
        let body_span = self.ast(ctx.file).expr(body).span;
        let falls_through = self.ty(body_span) != &Ty::Never;
        let scope = ctx.scope;
        let program = self.program;
        let local_data = |span: Span| {
            span.file == scope.file
                && span.start >= scope.start
                && span.end <= scope.end
                && program.types.get(&span).is_some_and(|ty| {
                    !matches!(
                        ty,
                        Ty::Callable(_) | Ty::Unknown | Ty::Param(_) | Ty::Infer(_)
                    )
                })
        };
        // The ledger expands paths structurally. Bound loops that keep creating
        // deeper access paths or callback compositions instead of diverging here.
        let max_passes = 64 + entry.slots.len();
        let exact = match extent {
            LoopExtent::Exact(length) if length > 0 && (exact_elements || length <= max_passes) => {
                Some(length)
            }
            _ => None,
        };
        let mut head = entry.clone();
        if exact.is_none() && extent != LoopExtent::Exact(0) {
            head.take_choice(owner, 0);
        }
        let mut exact_exits = Vec::new();
        let mut size_limit = None;
        for iteration in 1..=exact.unwrap_or(max_passes) {
            let mut inside = head.clone();
            let mut local = ctx.clone();
            local.scope = body_span;
            let index = (exact.is_some() && exact_elements).then_some(iteration - 1);
            let (mut exit, traversal) = prepare(self, &mut local, &mut inside, index);
            local.loop_owner = Some(owner);
            if local.reachable {
                self.expr(&mut local, &mut inside, body);
            }
            let LoopTransfers {
                mut breaks,
                mut continues,
            } = self.loop_transfers.remove(&owner).unwrap_or_default();
            if local.reachable && falls_through {
                continues.push(inside);
            }
            if let Some(traversal) = traversal {
                traversal.finish(&mut exit, &mut breaks, &mut continues);
            }
            if let Some(length) = exact {
                ctx.return_values = std::mem::take(&mut local.return_values);
                exact_exits.append(&mut breaks);
                if iteration == length || continues.is_empty() {
                    exact_exits.extend(continues);
                    ledger.merge(&entry, &exact_exits);
                    return;
                }
            } else {
                breaks.extend(exit);
            }
            if !continues.is_empty() {
                let final_iteration = exact.map(|_| continues.clone());
                for backedge in &mut continues {
                    backedge.loop_backedge(owner, repeated, &entry, local_data, exact.is_none());
                    backedge.take_choice(owner, 1);
                }
                if let Some(final_iteration) = final_iteration {
                    let mut next = head.clone();
                    next.merge(&entry, &continues);
                    if next == head && !exact_elements {
                        // The remaining iterations have the same incoming
                        // ledger and produce the same transfers.
                        exact_exits.extend(final_iteration);
                        ledger.merge(&entry, &exact_exits);
                        return;
                    }
                    head = next;
                    continue;
                }
                continues.push(head.clone());
                let mut next = head.clone();
                next.merge(&entry, &continues);
                if next != head {
                    let size = next.size();
                    let limit = *size_limit
                        .get_or_insert_with(|| (entry.size() + size).saturating_mul(8).max(4096));
                    if size > limit {
                        break;
                    }
                    head = next;
                    continue;
                }
            }
            ctx.return_values = local.return_values;
            ledger.merge(&entry, &breaks);
            return;
        }
        self.diagnostics.push(Diagnostic::unsupported_at(
            owner,
            "could not stabilize loop provenance",
        ));
    }

    fn iterable_extent(&self, ctx: &Context, id: ExprId) -> LoopExtent {
        let ast = self.ast(ctx.file);
        match &ast.expr(id).value {
            Expr::Array(items) => LoopExtent::Exact(items.len()),
            Expr::Literal(value) => match ty::literal(value) {
                Ok(Value::Bytes(bytes)) => LoopExtent::Exact(bytes.len()),
                Ok(Value::Str(text)) => LoopExtent::Exact(text.chars().count()),
                _ => LoopExtent::Repeat,
            },
            Expr::Range {
                start: Some(start),
                end: Some(end),
                inclusive,
            } => {
                let int = |id| match &ast.expr(id).value {
                    Expr::Literal(value) => match ty::literal(value) {
                        Ok(Value::Int(number)) => Some(number),
                        _ => None,
                    },
                    _ => None,
                };
                let (Some(start), Some(end)) = (int(*start), int(*end)) else {
                    return LoopExtent::Repeat;
                };
                if start > end {
                    LoopExtent::Exact(0)
                } else {
                    let distance = end - start + u8::from(*inclusive);
                    usize::try_from(distance).map_or(LoopExtent::Repeat, LoopExtent::Exact)
                }
            }
            _ => LoopExtent::Repeat,
        }
    }

    fn literal_bool(&self, ctx: &Context, id: ExprId) -> Option<bool> {
        match &self.ast(ctx.file).expr(id).value {
            Expr::Literal(value) if value.kind == LiteralKind::Bool => Some(value.text == "true"),
            Expr::Unary { op, value } if op.value == "!" => {
                self.literal_bool(ctx, *value).map(|value| !value)
            }
            _ => None,
        }
    }

    fn result_constructor(&self, ctx: &Context, id: ExprId) -> bool {
        let ast = self.ast(ctx.file);
        let Expr::Call { callee, .. } = ast.expr(id).value else {
            return false;
        };
        matches!(&ast.expr(callee).value, Expr::Path(path) if path.segments.last().is_some_and(|s| matches!(s.name.value.as_str(), "Ok" | "Err")))
    }

    fn coordinate(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        member: &Member,
    ) -> Coordinate {
        match member {
            Member::Name(name) => Coordinate::Field(name.value.clone()),
            Member::Index(index) => Coordinate::Index(index.value.clone()),
            Member::Computed(id) => {
                self.expr(ctx, ledger, *id);
                if let Some(Value::Str(key)) = self
                    .program
                    .static_values
                    .get(&self.ast(ctx.file).expr(*id).span)
                {
                    Coordinate::Field(key.clone())
                } else {
                    self.index_coordinate(ctx, *id)
                }
            }
        }
    }

    fn index_coordinate(&self, ctx: &Context, id: ExprId) -> Coordinate {
        match &self.ast(ctx.file).expr(id).value {
            Expr::Literal(value) if value.kind == LiteralKind::Int => {
                if let Ok(Value::Int(index)) = ty::literal(value) {
                    Coordinate::Index(index.to_string())
                } else {
                    Coordinate::Dynamic
                }
            }
            _ => Coordinate::Dynamic,
        }
    }

    fn collection_coordinate(&self, ctx: &Context, ty: &Ty, id: ExprId) -> Coordinate {
        let ty = if let Ty::Draft(inner) = ty { inner } else { ty };
        if matches!(ty, Ty::Map(..)) {
            self.constant_map_key(ctx, id)
                .unwrap_or(Coordinate::Dynamic)
        } else {
            self.index_coordinate(ctx, id)
        }
    }

    fn project_index(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        value: &Datum,
        (ty, index, span): (&Ty, ExprId, Span),
    ) -> Datum {
        if let Expr::Range {
            start,
            end,
            inclusive,
        } = self.ast(ctx.file).expr(index).value
        {
            let Some(element) = self.schema_member(ty, &Coordinate::Dynamic) else {
                return Datum::default();
            };
            let bound = |id| match self.index_coordinate(ctx, id) {
                Coordinate::Index(index) => index.parse::<usize>().ok(),
                _ => None,
            };
            let start = start.map_or(Some(0), bound);
            let end = end.map_or_else(
                || self.slice_source_length(ledger, value),
                |end| bound(end).and_then(|bound| bound.checked_add(usize::from(inclusive))),
            );
            return self.array_slice(ctx, ledger, value, element, (start, end), span);
        }
        let coordinate = self.collection_coordinate(ctx, ty, index);
        let mode = self.schema_mode(ty, &coordinate).0;
        self.project_observed(ctx, ledger, value, (coordinate, mode, span))
    }

    fn project_observed(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        base: &Datum,
        (coordinate, mode, span): (Coordinate, Mode, Span),
    ) -> Datum {
        let mut selected = ledger.project_schema(base, coordinate.clone(), mode);
        if ctx.reachable
            && ctx.runtime
            && !ctx.shadow
            && ledger.storage_flow.is_some()
            && !self.ty(span).is_value()
            && !selected.roots.is_empty()
        {
            let index =
                self.storage_read_index(storage::ReadSite::Source(span, coordinate.clone()));
            ledger.record_storage_read(index, base, coordinate, mode, &mut selected);
        }
        selected
    }

    fn storage_read_index(&mut self, site: storage::ReadSite) -> usize {
        let next = self.storage_read_sites.len();
        *self.storage_read_sites.entry(site).or_insert(next)
    }

    fn slice_source_length(&self, ledger: &Ledger, array: &Datum) -> Option<usize> {
        // A deferred callback can change the length before the copy runs.
        ledger
            .storage_flow
            .is_none()
            .then(|| ledger.exact_array_length(array).or(array.array_len))
            .flatten()
    }

    fn array_slice(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        array: &Datum,
        element: &ty::Member,
        (start, end): (Option<usize>, Option<usize>),
        span: Span,
    ) -> Datum {
        let mut slice = Datum::source(span, Access::Mut, true);
        let length = start
            .zip(end)
            .and_then(|(start, end)| end.checked_sub(start));
        if let Some(length) = length {
            ledger.record_array_length(span, length);
        }
        if element.ty.is_value() || length == Some(0) {
            return slice;
        }
        let mut project = |ledger: &mut Ledger, coordinate| {
            let mut member =
                self.project_observed(ctx, ledger, array, (coordinate, element.mode.mode, span));
            // The result has a fresh container and still points to the
            // source's elements.
            member.requires_new = false;
            member.transform(&mut |origin| origin.new = false);
            member
        };
        if let (Some(start), Some(1)) = (start, length) {
            slice.members.insert(
                Coordinate::Index("0".into()),
                project(ledger, Coordinate::Index(start.to_string())),
            );
            return slice;
        }
        if let Some(start) = start {
            let source = ledger.snapshot(array);
            for coordinate in source.members.keys() {
                if let Coordinate::Index(index) = coordinate
                    && let Ok(index) = index.parse::<usize>()
                    && index >= start
                    && end.is_none_or(|end| index < end)
                {
                    let member = project(ledger, coordinate.clone());
                    slice
                        .members
                        .insert(Coordinate::Index((index - start).to_string()), member);
                }
            }
        }
        if length != Some(slice.members.len()) {
            let range = start.map_or(Coordinate::Dynamic, Coordinate::ArrayTail);
            slice
                .members
                .insert(Coordinate::Dynamic, project(ledger, range));
        }
        slice
    }

    fn constant_map_key(&self, ctx: &Context, id: ExprId) -> Option<Coordinate> {
        let node = self.ast(ctx.file).expr(id);
        let value = if let Expr::Literal(literal) = &node.value {
            ty::literal(literal).ok()?
        } else {
            self.program.static_values.get(&node.span)?.clone()
        };
        matches!(
            value,
            Value::Unit | Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Bytes(_)
        )
        .then(|| Coordinate::Index(ty::render(&value)))
    }

    fn member_schema(&self, base: Span, coordinate: &Coordinate) -> (Access, bool) {
        self.schema(self.ty(base), coordinate)
    }

    fn schema(&self, ty: &'a Ty, coordinate: &Coordinate) -> (Access, bool) {
        let (mode, variable) = self.schema_mode(ty, coordinate);
        (Access::from_mode(mode), variable)
    }

    fn schema_mode(&self, ty: &'a Ty, coordinate: &Coordinate) -> (Mode, bool) {
        self.schema_member(ty, coordinate)
            .map_or((Mode::Plain, false), |member| {
                (member.mode.mode, member.mode.variable)
            })
    }

    fn schema_member(&self, mut ty: &'a Ty, coordinate: &Coordinate) -> Option<&'a ty::Member> {
        if let Ty::Draft(inner) = ty {
            ty = inner;
        }
        if let Ty::Adt(adt) = ty {
            let def = self.program.hir.definition(adt.definition);
            if let Some(id) = def.stmt
                && let StmtKind::Type(decl) = &self.ast(def.name.span.file).stmt(id).value.kind
                && let TypeDefinition::Data(rep) = decl.definition
            {
                ty = self.ty(self.ast(def.name.span.file).ty(rep).span);
            }
        }
        if let Ty::Draft(inner) = ty {
            ty = inner;
        }
        match (ty, coordinate) {
            (Ty::Record(fields, _), Coordinate::Field(name)) => fields.get(name),
            (Ty::Tuple(fields), Coordinate::Index(index)) => index
                .parse::<usize>()
                .ok()
                .and_then(|index| fields.get(index)),
            (Ty::Map(..), Coordinate::MapKey) => None,
            (Ty::Array(member) | Ty::Map(_, member), _) => Some(member.as_ref()),
            _ => None,
        }
    }

    fn schema_axis(&self, region: &Region) -> Option<&Region> {
        self.member_schemas
            .get(&region.source)?
            .iter()
            .find(|axis| axis.matches_axis(region))
    }

    fn register_member_axes(&mut self, axes: &[(usize, Region)]) {
        for (_, axis) in axes {
            let regions = self.member_schemas.entry(axis.source).or_default();
            if !regions.contains(axis) {
                regions.push(axis.clone());
            }
        }
    }

    fn navigate(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        base: ExprId,
        steps: &[ExprId],
        span: Span,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let mut value = self.expr(ctx, ledger, base);
        let entry = ledger.clone();
        let mut present_ctx = ctx.clone();
        let mut missing = Vec::new();
        let mut ty = self.ty(ast.expr(base).span);
        let payload = Coordinate::Index("0".into());
        for &step in steps {
            let step = ast.expr(step);
            let (safe, index) = match &step.value {
                Expr::Member { safe, .. } => (*safe, None),
                Expr::Index { safe, index, .. } => (*safe, Some(*index)),
                _ => ril_base::ice!("unexpected navigation step"),
            };
            if safe && let Ty::Option(inner) = ty {
                let mut absent = ledger.clone();
                absent.take_choice(step.span, 1);
                missing.push(absent);
                ledger.take_choice(step.span, 0);
                value = ledger.project(&value, payload.clone(), Access::Immutable);
                ty = inner;
            }
            value = if let Some(index) = index {
                self.expr(&mut present_ctx, ledger, index);
                if safe {
                    missing.push(ledger.clone());
                }
                self.project_index(&present_ctx, ledger, &value, (ty, index, step.span))
            } else if let Expr::Member { member, .. } = &step.value {
                let coordinate = self.coordinate(&mut present_ctx, ledger, member);
                let mode = self.schema_mode(ty, &coordinate).0;
                self.project_observed(&present_ctx, ledger, &value, (coordinate, mode, step.span))
            } else {
                ril_base::ice!("unexpected navigation coordinate");
            };
            ty = self
                .program
                .navigation_values
                .get(&step.span)
                .unwrap_or(&Ty::Unknown);
        }
        ctx.return_values = present_ctx.return_values;
        missing.push(ledger.clone());
        ledger.merge(&entry, &missing);
        ctx.reachable &= !ledger.no_continuation;
        if matches!(ty, Ty::Option(_)) {
            value
        } else {
            let mut option = Datum::source(span, Access::Mut, true);
            option.members.insert(payload, value);
            option
        }
    }
}

fn member_axes(callable: &Callable, formals: &[Option<Span>]) -> Vec<(usize, Region)> {
    let mut axes = Vec::new();
    for (index, (parameter, decl)) in callable.parameters.iter().zip(formals).enumerate() {
        if let Some(source) = decl {
            collect_axes(&parameter.ty, &mut Vec::new(), &mut |selection| {
                let mut region = Region::root(*source);
                region.selection.extend_from_slice(selection);
                axes.push((index, region));
            });
        }
    }
    axes
}

fn extend_rows(rows: &mut Vec<Vec<Input>>, domain: &[Input]) {
    *rows = std::mem::take(rows)
        .into_iter()
        .flat_map(|row| {
            domain.iter().map(move |mode| {
                let mut result = row.clone();
                result.push(*mode);
                result
            })
        })
        .collect();
}

fn collect_axes(ty: &Ty, path: &mut Vec<Coordinate>, output: &mut impl FnMut(&[Coordinate])) {
    let mut visit = |coord, member: &ty::Member| {
        path.push(coord);
        if member.mode.mode == Mode::Via {
            output(path);
        }
        collect_axes(&member.ty, path, output);
        path.pop();
    };
    match ty {
        Ty::Array(item) | Ty::Map(_, item) => visit(Coordinate::Dynamic, item),
        Ty::Tuple(items) => {
            for (position, item) in items.iter().enumerate() {
                visit(Coordinate::Index(position.to_string()), item);
            }
        }
        Ty::Record(fields, _) => {
            for (name, item) in fields {
                visit(Coordinate::Field(name.clone()), item);
            }
        }
        _ => {}
    }
}

fn is_assignment(token: &str) -> bool {
    matches!(
        token,
        "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
    )
}
