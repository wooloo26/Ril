use std::collections::{BTreeMap, BTreeSet};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_frontend::{
    hir::{DefinitionId, DefinitionKind, Resolution},
    parser::FileKind,
    syntax::{
        Ast, Condition, Expr, ExprId, Function, LiteralKind, Member, Mode, Path, Pattern,
        PatternId, Signature, StateKind, StmtId, StmtKind, Storage, Transfer, TypeDefinition,
    },
};

use super::{
    Access, Analysis, CleanupAction, Input, Instance, Invocation, InvocationMode, ReturnSource,
    StorageUpdate, Summary,
    flow::{
        Coordinate, Datum, Ledger, Reception, Region, Replacement, Revocation, Slot, conflicts,
    },
    horn::{self, Rule},
};
use crate::ty::{self, AdtKind, Callable, Ty, TypedProgram, Value, reception};

mod calls;
mod higher_order;
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
    formals: Vec<Option<Span>>,
    caller_slots: BTreeSet<Span>,
    caller_sources: BTreeSet<Span>,
    owned_formals: BTreeSet<Span>,
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
            formals: Vec::new(),
            caller_slots: BTreeSet::new(),
            caller_sources: BTreeSet::new(),
            owned_formals: BTreeSet::new(),
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
        self.caller_sources.extend(
            outer
                .slots
                .values()
                .flat_map(|slot| slot.value.origins().map(|origin| origin.region.source)),
        );
    }
}

struct Requirement {
    fact: Fact,
    span: Span,
    message: &'static str,
}

struct CaptureConflict {
    write: Fact,
    reading: Option<Code>,
    writing: Option<Code>,
    span: Span,
}

struct DefinitionCheck {
    owner: Span,
    id: DefinitionId,
    formals: Vec<Option<Span>>,
    declared: Callable,
    return_sources: Vec<ReturnSource>,
    returns: Vec<Datum>,
    updates: BTreeMap<Region, Replacement>,
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
    models_publication: bool,
}

#[derive(Default)]
struct LoopTransfers {
    breaks: Vec<Ledger>,
    continues: Vec<Ledger>,
}

struct Analyzer<'a> {
    program: &'a TypedProgram,
    diagnostics: Vec<Diagnostic>,
    rules: Vec<Rule<Fact>>,
    requirements: Vec<Requirement>,
    deferred_errors: Vec<(Vec<Fact>, Diagnostic)>,
    capture_conflicts: Vec<CaptureConflict>,
    mode_uses: Vec<ModeUse>,
    member_schemas: BTreeMap<Span, Vec<Region>>,
    closure_modes: BTreeMap<Span, ClosureModes>,
    higher_order: higher_order::Calls,
    invocation_summaries: BTreeMap<Span, BTreeSet<Invocation>>,
    callback_results: Vec<calls::CallbackResult>,
    loop_transfers: BTreeMap<Span, LoopTransfers>,
    storage_exits: BTreeMap<Span, Vec<BTreeMap<Region, Replacement>>>,
    recursive_storage: BTreeMap<Span, storage::CallStorage>,
    recursive_calls: BTreeSet<Span>,
    resolving_callback_results: BTreeSet<usize>,
    functions: Vec<DefinitionCheck>,
    done: BTreeSet<DefinitionId>,
    cleanups: BTreeMap<Span, CleanupAction>,
}

fn collect(
    program: &TypedProgram,
    recursive_storage: BTreeMap<Span, storage::CallStorage>,
) -> Analyzer<'_> {
    let mut analyzer = Analyzer {
        program,
        diagnostics: Vec::new(),
        rules: Vec::new(),
        requirements: Vec::new(),
        deferred_errors: Vec::new(),
        capture_conflicts: Vec::new(),
        mode_uses: Vec::new(),
        member_schemas: BTreeMap::new(),
        closure_modes: BTreeMap::new(),
        higher_order: higher_order::Calls::default(),
        invocation_summaries: BTreeMap::new(),
        callback_results: Vec::new(),
        loop_transfers: BTreeMap::new(),
        storage_exits: BTreeMap::new(),
        recursive_storage,
        recursive_calls: BTreeSet::new(),
        resolving_callback_results: BTreeSet::new(),
        functions: Vec::new(),
        done: BTreeSet::new(),
        cleanups: BTreeMap::new(),
    };
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
    let facts = horn::solve(&analyzer.rules);
    for conflict in std::mem::take(&mut analyzer.capture_conflicts) {
        let code = if facts.contains(&conflict.write) {
            conflict.writing
        } else {
            conflict.reading
        };
        if let Some(code) = code {
            analyzer.error(
                code,
                conflict.span,
                "argument authority overlaps a callable capture",
            );
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
    for requirement in std::mem::take(&mut analyzer.requirements) {
        if !facts.contains(&requirement.fact) {
            analyzer.error(Code::E0527, requirement.span, requirement.message);
        }
    }
    let mut consuming_inputs = BTreeMap::new();
    let mut sharing_inputs = BTreeMap::new();
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
        let instances = analyzer.via_table(&function, &summary, &consumed, &facts);
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
                analyzer.error(Code::E0548, span, "via application requires new ownership");
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
                if handler
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
                            || origin.dependencies.contains(&source))
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
        let mut ledger = outer.clone();
        ledger.obligations.clear();
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
                ctx.owned_formals.insert(span);
            }
            let mut value = if param.ty.is_value() {
                Datum::default()
            } else {
                Datum::source(span, Access::from_mode(param.mode), param.mode == Mode::New)
            };
            value.transform(&mut |origin| {
                origin.dependencies.insert(span);
                origin.inherits_mode = param.mode == Mode::Via;
                origin.call_borrow = param.mode == Mode::Mut;
            });
            if param.ty.is_result() {
                value.results.insert(span);
                ledger.obligations.insert(span);
            }
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
        let captures = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(_, path)| self.declaration(path.span))
            .collect();
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
        let updates = Ledger::join_updates(exits.iter().collect());
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
            constructs: fun.returned_new,
            invocations: self
                .invocation_summaries
                .remove(&fun.owner)
                .into_iter()
                .flatten()
                .collect(),
            callback_returns: fun
                .returns
                .iter()
                .flat_map(|value| self.callback_return_contracts(&fun.formals, value))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            storage_updates: self.storage_contracts(fun),
            ..Summary::default()
        };
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
                    }
                }
                Obligation::ReadUp(span) => {
                    up.insert(*span);
                }
                Obligation::Effect(effect) => summary.effects.push(effect.clone()),
                Obligation::Operation(operation) => summary.effects.push(operation.effect.clone()),
                Obligation::Capture => summary.captures = true,
                _ => {}
            }
        }
        summary.writes.sort_unstable();
        summary.writes.dedup();
        summary.retained.sort_unstable();
        summary.effects.sort();
        summary.effects.dedup();
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

    fn storage_contracts(&self, fun: &DefinitionCheck) -> Vec<StorageUpdate> {
        let formal_index = |source| {
            fun.formals
                .iter()
                .position(|formal| *formal == Some(source))
        };
        let mut updates: Vec<_> = fun
            .updates
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
                    callback_returns: self.callback_return_contracts(&fun.formals, &update.value),
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
        consumed: &BTreeSet<usize>,
        facts: &BTreeSet<Fact>,
    ) -> Vec<Instance> {
        if fun.via.is_empty() && fun.member_axes.is_empty() {
            return Vec::new();
        }
        let mut rows: Vec<Vec<Input>> = vec![Vec::new()];
        let mut formals = BTreeMap::new();
        let mut axes = Vec::new();
        for (index, formal) in fun.formals.iter().enumerate() {
            let Some(source) = formal.filter(|span| fun.via.contains(span)) else {
                continue;
            };
            formals.insert(index, formals.len());
            axes.push(Region {
                source,
                selection: Vec::new(),
            });
            let needs_sharing = summary.retained.contains(&index)
                || facts.contains(&Fact {
                    owner: fun.owner,
                    obligation: Obligation::NeedsSharing(source),
                });
            let domain: &[Input] = if consumed.contains(&index) {
                if needs_sharing {
                    self.error(
                        Code::E0548,
                        fun.owner,
                        "via source cannot be both transferred and retained as shared",
                    );
                    return Vec::new();
                }
                &[Input::New]
            } else if needs_sharing {
                &[Input::Shared]
            } else if summary.writes.contains(&index) {
                &[Input::Mut, Input::Shared, Input::New]
            } else {
                &[
                    Input::Plain,
                    Input::Ref,
                    Input::Mut,
                    Input::Shared,
                    Input::New,
                ]
            };
            extend_rows(&mut rows, domain);
        }
        for (_, axis) in &fun.member_axes {
            axes.push(axis.clone());
            let requirements: Vec<_> = facts
                .iter()
                .filter_map(|fact| match &fact.obligation {
                    Obligation::Schema(path, required)
                        if fact.owner == fun.owner && axis == path =>
                    {
                        Some(*required)
                    }
                    _ => None,
                })
                .collect();
            let domain: Vec<_> = [Input::Plain, Input::Ref, Input::Mut, Input::Shared]
                .into_iter()
                .filter(|mode| requirements.iter().all(|r| r.accepts(mode.access())))
                .collect();
            if domain.is_empty() {
                self.error(
                    Code::E0520,
                    fun.owner,
                    "member via template has incompatible access requirements",
                );
                return Vec::new();
            }
            extend_rows(&mut rows, &domain);
        }
        rows.into_iter()
            .map(|modes| {
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
            })
            .collect()
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
                if let Some(fallback) = fallback {
                    ledger.inspect(&value);
                    self.expr(&mut ctx.clone(), &mut ledger.clone(), *fallback);
                }
                self.bind(ctx, ledger, *pattern, storage, value, *resource);
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
            StmtKind::Effect { .. } | StmtKind::Import(_) => {}
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
                let result = self.expr(&mut shadow, &mut slots, *expr);
                let mut except = result.results();
                except.extend(&ledger.obligations);
                self.check_results(&slots, &except);
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

    fn receive_member(&mut self, mut value: Datum, mode: Access, span: Span) -> Datum {
        if value.roots.is_empty() {
            return value;
        }
        if mode == Access::Immutable && !value.can_freeze() {
            self.error(
                Code::E0535,
                span,
                "live authority cannot enter an immutable member",
            );
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

    fn freeze_value(&mut self, ledger: &Ledger, value: &mut Datum, span: Span) {
        *value = ledger.snapshot(value);
        if !value.can_freeze() {
            self.error(
                Code::E0535,
                span,
                "live authority cannot be frozen as a plain snapshot",
            );
        }
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

    fn returned(&mut self, ctx: &mut Context, ledger: &mut Ledger, value: Datum, span: Span) {
        let value = ledger.snapshot(&value);
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
        if value.returns_borrowed_writer(ctx.expected) {
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
            Mode::Plain if value.origins().any(|root| root.mode != Access::Immutable) => {
                self.error(
                    Code::E0528,
                    span,
                    "plain return cannot expose live authority",
                );
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
            .push(ledger.call_updates(ctx.owner, &ctx.formals, &ctx.caller_slots));
    }

    fn publish_at_exit(&mut self, ctx: &Context, ledger: &Ledger, normal: bool) {
        if !ctx.runtime || ctx.shadow || !ctx.reachable {
            return;
        }
        for &slot in ctx.caller_slots.iter().chain(ctx.formals.iter().flatten()) {
            let Some(slot) = ledger.slots.get(&slot) else {
                continue;
            };
            let caller_root = !ctx.owned_formals.contains(&slot.decl);
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

    fn check_publication_source(&mut self, ctx: &Context, value: &Datum, span: Span) {
        if value
            .origins()
            .any(|origin| origin.call_borrow && origin.mode.writes())
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

    fn check_results(&mut self, ledger: &Ledger, except: &BTreeSet<Span>) {
        for span in ledger.obligations.difference(&ledger.inspected) {
            if !except.contains(span) {
                self.error(
                    Code::E0720,
                    *span,
                    "fallible result has not been inspected on normal exit",
                );
            }
        }
    }

    fn discard(&mut self, ledger: &Ledger, value: &Datum) {
        for span in value.results().difference(&ledger.inspected) {
            self.error(Code::E0720, *span, "discarded fallible result");
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
                self.error(Code::E0548, binding, "cleanup requires an owned sender");
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
                "cleanup must consume, mutate, or observe Self and return ()",
            );
        }
        if signature.effects.iter().any(|effect| effect == "fiber") {
            self.error(Code::E0616, binding, "@fiber is prohibited on cleanup");
        }
        for effect in &signature.effects {
            self.effect(ctx, ledger, effect, binding);
        }
        if parameter.mode == Mode::New && !value.requires_new {
            self.error(
                Code::E0548,
                binding,
                "cleanup requires an owned new resource",
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
        resource: bool,
    ) {
        let node = self.ast(ctx.file).pattern(id);
        match &node.value {
            Pattern::Binding(own, name) => {
                self.check_resource_binding(name.span, &value, resource);
                let binding = self
                    .definition(name.span)
                    .unwrap_or_else(|| ril_base::ice!("unresolved binding pattern"));
                let declaration = self.program.hir.definition(binding).name.span;
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
                let stateful_closure = value.creates_environment()
                    && value.origins().any(|origin| origin.mode.writes());
                match mode {
                    Mode::Mut if !value.requires_new && !value.writers() => self.error(
                        Code::E0520,
                        name.span,
                        "binding cannot manufacture write authority",
                    ),
                    Mode::Shared
                        if (!value.writers() || value.requires_new) && !stateful_closure =>
                    {
                        self.error(
                            Code::E0527,
                            name.span,
                            "shared binding requires a shared writable source",
                        );
                    }
                    Mode::Ref if value.roots.is_empty() && !resource => self.error(
                        Code::E0531,
                        name.span,
                        "ref binding has no live object source",
                    ),
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
                    self.freeze_value(ledger, &mut value, name.span);
                } else if mode != Mode::Via {
                    value.receive_binding(access);
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(declaration);
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
                    let child = ledger.project_schema(&value, coordinate, mode);
                    self.bind(ctx, ledger, item, storage, child, resource);
                }
            }
            Pattern::Slice { text, elements } => {
                let ast = self.ast(ctx.file);
                let (before, rest, after) = ast.slice_parts(elements);
                let mode = self.schema_mode(self.ty(node.span), &Coordinate::Dynamic).0;
                for (index, &item) in before.iter().enumerate() {
                    let child =
                        ledger.project_schema(&value, Coordinate::Index(index.to_string()), mode);
                    self.bind(ctx, ledger, item, storage, child, resource);
                }
                for &item in after {
                    let child = ledger.project_schema(&value, Coordinate::Dynamic, mode);
                    self.bind(ctx, ledger, item, storage, child, resource);
                }
                if let Some(rest) = rest
                    && let Pattern::Rest(Some(name)) = &ast.pattern(rest).value
                {
                    let decl = self.declaration(name.span).unwrap_or(name.span);
                    let mut slice = if *text {
                        Datum::default()
                    } else {
                        Datum::source(ast.pattern(rest).span, Access::Mut, true)
                    };
                    if let Ty::Array(element) = self.ty(node.span)
                        && !element.ty.is_value()
                    {
                        let mut child = ledger.project_schema(&value, Coordinate::Dynamic, mode);
                        child.requires_new = false;
                        child.transform(&mut |origin| origin.new = false);
                        slice.members.insert(Coordinate::Dynamic, child);
                    }
                    self.check_resource_binding(name.span, &slice, resource);
                    slice.transform(&mut |origin| {
                        origin.dependencies.insert(decl);
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
                ledger.inspect(&value);
                for (i, &item) in payload.iter().flatten().enumerate() {
                    self.bind(
                        ctx,
                        ledger,
                        item,
                        storage,
                        value.project(Coordinate::Index(i.to_string()), Access::Immutable),
                        resource,
                    );
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    let coordinate = Coordinate::Field(field.name.value.clone());
                    let mode = self.schema_mode(self.ty(node.span), &coordinate).0;
                    let member_mode = Access::from_mode(mode);
                    let child = ledger.project_schema(&value, coordinate, mode);
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
                        self.bind(ctx, ledger, pattern, &received, child, resource);
                    } else {
                        let mut child = child;
                        let decl = self.declaration(field.name.span).unwrap_or(field.name.span);
                        self.check_resource_binding(field.name.span, &child, resource);
                        child.transform(&mut |origin| {
                            origin.dependencies.insert(decl);
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
                    self.bind(ctx, &mut branch, item, storage, value, resource);
                    alternatives.push(branch);
                }
                if let Some(first) = alternatives.first() {
                    let mut prior = ledger.clone();
                    for (&decl, slot) in &first.slots {
                        if alternatives
                            .iter()
                            .all(|branch| branch.slots.contains_key(&decl))
                        {
                            prior.slots.entry(decl).or_insert_with(|| slot.clone());
                        }
                    }
                    ledger.merge(&prior, &alternatives);
                }
            }
            Pattern::Subset {
                binding: Some(id), ..
            } => self.bind(ctx, ledger, *id, storage, value, resource),
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
                            root.new = false;
                        }
                        value.requires_new = false;
                    }
                    "^mut" => {
                        if !value.writers() {
                            self.error(Code::E0520, span, "sharing requires writable authority");
                        }
                        self.require_schema(ctx, &value, SchemaRequirement::Writable);
                        for root in &mut value.roots {
                            root.fix_mode(Access::Shared);
                            root.explicit_share = true;
                            root.new &= value.requires_new;
                        }
                        value.requires_new = false;
                    }
                    "?" => {
                        ledger.inspect(&value);
                        self.storage_exit(ctx, ledger);
                        value = value.project(Coordinate::Index("0".into()), Access::Immutable);
                        value.results.clear();
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
                    ledger.inspect(&lhs);
                    lhs.project(Coordinate::Index("0".into()), Access::Immutable)
                        .joined(rhs)
                } else {
                    if matches!(op.value.as_str(), "==" | "!=")
                        && (self.result_constructor(ctx, *right)
                            || self.result_constructor(ctx, *left))
                    {
                        ledger.inspect(&lhs);
                        ledger.inspect(&rhs);
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
                for (i, &item) in items.iter().enumerate() {
                    let coordinate = Coordinate::Index(i.to_string());
                    let value = self.expr(ctx, ledger, item);
                    let access = self.member_schema(span, &coordinate).0;
                    let value = self.receive_member(value, access, ast.expr(item).span);
                    sequence.members.insert(coordinate, value);
                }
                sequence
            }
            Expr::Map(entries) => {
                let mut map = Datum::source(span, Access::Mut, true);
                for (i, &(key, value)) in entries.iter().enumerate() {
                    self.expr(ctx, ledger, key);
                    let coordinate = Coordinate::Index(i.to_string());
                    let access = self.member_schema(span, &coordinate).0;
                    let datum = self.expr(ctx, ledger, value);
                    map.members.insert(
                        coordinate,
                        self.receive_member(datum, access, ast.expr(value).span),
                    );
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
                ledger.project_schema(&value, coordinate, mode)
            }
            Expr::Index { base, index, .. } => {
                let value = self.expr(ctx, ledger, *base);
                self.expr(ctx, ledger, *index);
                let coordinate = self.index_coordinate(ctx, *index);
                let (mode, _) = self.schema_mode(self.ty(ast.expr(*base).span), &coordinate);
                ledger.project_schema(&value, coordinate, mode)
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                let mut local_ctx = ctx.clone();
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
                yes_ctx.reachable &= literal != Some(false);
                self.condition(&mut yes_ctx, &mut then_ledger, condition);
                let yes_value = self.expr(&mut yes_ctx, &mut then_ledger, *yes);
                let mut else_ledger = before.clone();
                else_ledger.take_choice(span, 1);
                let mut no_ctx = ctx.clone();
                no_ctx.reachable &= literal != Some(true);
                self.condition_unbound(&mut no_ctx, &mut else_ledger, condition);
                let no_value = no
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
                let can_yes_continue = can_yes && !then_ledger.no_continuation;
                let can_no_continue = can_no && !else_ledger.no_continuation;
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
                let before = ledger.clone();
                let mut inside = before.clone();
                let mut local = ctx.clone();
                let literal = match condition {
                    Condition::Expr(test) => self.literal_bool(ctx, *test),
                    Condition::Binding { .. } => None,
                };
                self.condition(&mut local, &mut inside, condition);
                let mut exits = Vec::new();
                if literal != Some(true) && local.reachable {
                    exits.push(inside.clone());
                }
                local.loop_owner = Some(span);
                local.reachable &= literal != Some(false);
                self.expr(&mut local, &mut inside, *body);
                if local.reachable && self.ty(ast.expr(*body).span) != &Ty::Never {
                    self.loop_transfers
                        .entry(span)
                        .or_default()
                        .continues
                        .push(inside);
                }
                ctx.return_values = local.return_values;
                self.merge_loop_exits(span, ledger, &before, exits);
                Datum::default()
            }
            Expr::For {
                iterable,
                pattern,
                body,
                mode,
            } => {
                let value = self.expr(ctx, ledger, *iterable);
                let before = ledger.clone();
                let mut inside = before.clone();
                let mut local = ctx.clone();
                local.loop_owner = Some(span);
                inside.iteration.push(value.clone());
                let storage = Storage {
                    mode: *mode,
                    ..Storage::default()
                };
                let coordinate = Coordinate::Dynamic;
                let schema = self
                    .schema_mode(self.ty(ast.expr(*iterable).span), &coordinate)
                    .0;
                let child = inside.project_schema(&value, coordinate, schema);
                self.bind(&local, &mut inside, *pattern, &storage, child, false);
                self.expr(&mut local, &mut inside, *body);
                if local.reachable && self.ty(ast.expr(*body).span) != &Ty::Never {
                    self.loop_transfers
                        .entry(span)
                        .or_default()
                        .continues
                        .push(inside);
                }
                ctx.return_values = local.return_values;
                self.merge_loop_exits(span, ledger, &before, vec![before.clone()]);
                Datum::default()
            }
            Expr::Match { mode, value, arms } => {
                let value = self.expr(ctx, ledger, *value);
                ledger.inspect(&value);
                let before = ledger.clone();
                let mut alternatives = Vec::new();
                let mut output = None;
                for (index, arm) in arms.iter().enumerate() {
                    let mut inside = before.clone();
                    inside.take_choice(span, index);
                    let mut local_ctx = ctx.clone();
                    let storage = Storage {
                        mode: *mode,
                        ..Storage::default()
                    };
                    self.bind(
                        &local_ctx,
                        &mut inside,
                        arm.pattern,
                        &storage,
                        value.clone(),
                        false,
                    );
                    if let Some(guard) = arm.guard {
                        self.expr(&mut local_ctx, &mut inside, guard);
                    }
                    let body = self.expr(&mut local_ctx, &mut inside, arm.body);
                    let prior = ctx.return_values.len();
                    ctx.return_values
                        .extend(local_ctx.return_values.into_iter().skip(prior));
                    if self.ty(ast.expr(arm.body).span) != &Ty::Never && !inside.no_continuation {
                        output = Some(output.map_or_else(
                            || body.clone(),
                            |value: Datum| value.joined(body.clone()),
                        ));
                        alternatives.push(inside);
                    }
                }
                ledger.merge(&before, &alternatives);
                output.unwrap_or_default()
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
                    ledger.inspect(&result);
                    self.storage_exit(ctx, ledger);
                    let mut payload =
                        result.project(Coordinate::Index("0".into()), Access::Immutable);
                    payload.results.clear();
                    payload
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
            && value.results().is_empty()
            && !matches!(node.value, Expr::Path(_))
        {
            value.results.insert(span);
            ledger.obligations.insert(span);
        }
        if self.ty(span).is_value() {
            value.roots.clear();
            value.members.clear();
            value.requires_new = false;
        }
        if matches!(
            node.value,
            Expr::Path(_)
                | Expr::Member { .. }
                | Expr::Index { .. }
                | Expr::Call { .. }
                | Expr::Pipeline { .. }
        ) {
            for root in &mut value.roots {
                root.explicit_share = false;
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
        let decl = self.program.hir.definition(id).name.span;
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
            slot.value.clone()
        } else if self
            .definition(span)
            .is_some_and(|id| self.program.hir.unit_constructor(id))
        {
            Datum::source(span, Access::Mut, true)
        } else if !self.ty(span).is_value()
            && matches!(
                self.program.hir.definition(id).kind,
                DefinitionKind::Constant | DefinitionKind::Function
            )
        {
            Datum::source(decl, Access::Immutable, false)
        } else {
            Datum::default()
        }
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
        if value.origins().any(|origin| origin.confined.is_some()) {
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
                "new requires qualified ownership or a pinned exclusive writer",
            );
            return;
        }
        if ledger.slots.values().any(|slot| {
            slot.mode == Mode::Shared
                && value
                    .roots
                    .iter()
                    .any(|root| slot.value.origins().any(|retained| root.overlaps(retained)))
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
            .flat_map(|origin| origin.dependencies.iter().copied())
            .collect();
        if dependencies
            .iter()
            .any(|id| ledger.slots.get(id).is_some_and(|slot| slot.variable))
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
                let coordinate = self.index_coordinate(ctx, *index);
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
                }
                let captured = ctx.caller_slots.contains(&id);
                if captured {
                    self.check_publication_source(ctx, &value, span);
                }
                if mode == Mode::Plain {
                    self.freeze_value(ledger, &mut value, span);
                } else {
                    value.receive_binding(Access::from_mode(mode));
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(decl);
                });
                if captured {
                    value.publications.insert(ctx.owner, true);
                    ledger.replace_slot(id, value, true);
                } else {
                    ledger.slots.entry(id).and_modify(|slot| slot.value = value);
                }
                return;
            }
            self.error(
                Code::E0501,
                node.span,
                "assignment requires a replaceable local slot",
            );
            return;
        }
        if !matches!(node.value, Expr::Member { .. } | Expr::Index { .. }) {
            self.error(Code::E0503, node.span, "invalid assignment target");
            return;
        }
        self.mutate(ctx, ledger, prior, span);
        if value.origins().any(|origin| origin.confined.is_some()) {
            self.error(
                Code::E0604,
                span,
                "confined value cannot be stored in an outer object",
            );
        }
        if prior.origins().any(|origin| {
            let source = origin.region.source;
            ctx.caller_sources.contains(&source)
                || ctx.formals.contains(&Some(source))
                    && (!ctx.owned_formals.contains(&source) || !origin.new)
        }) {
            self.check_publication_source(ctx, &value, span);
        }
        if ctx.reachable && !value.roots.is_empty() {
            let access = match &node.value {
                Expr::Member { base, .. } | Expr::Index { base, .. } => prior
                    .roots
                    .first()
                    .and_then(|origin| origin.region.selection.last())
                    .map(|coordinate| {
                        self.member_schema(self.ast(ctx.file).expr(*base).span, coordinate)
                            .0
                    }),
                _ => None,
            };
            if let Some(access) = access {
                if access == Access::Shared {
                    self.require_shared_replacement(&value, span, true);
                }
                let mut value = self.receive_member(value, access, span);
                value
                    .publications
                    .insert(ctx.owner, prior.roots.iter().any(|root| !root.new));
                ledger.replace_member(prior, value, true);
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
        if let Some(writable) = ledger.hold_conflict(value, Mode::Mut) {
            self.error(
                if writable { Code::E0523 } else { Code::E0524 },
                span,
                "write overlaps an active lexical handler hold",
            );
        }
        self.require_schema(ctx, value, SchemaRequirement::Writable);
        for origin in &value.roots {
            if !origin.new {
                self.seed(ctx, Obligation::WriteExisting(origin.region.source));
            }
            for id in origin
                .dependencies
                .iter()
                .copied()
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

    fn condition(&mut self, ctx: &mut Context, ledger: &mut Ledger, condition: &Condition) {
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
                ledger.inspect(&value);
                self.bind(
                    ctx,
                    ledger,
                    *pattern,
                    &Storage {
                        mode: *mode,
                        ..Storage::default()
                    },
                    value,
                    false,
                );
            }
        }
    }

    fn merge_loop_exits(
        &mut self,
        owner: Span,
        ledger: &mut Ledger,
        before: &Ledger,
        mut exits: Vec<Ledger>,
    ) {
        let transfers = self.loop_transfers.remove(&owner).unwrap_or_default();
        exits.extend(transfers.breaks);
        if !exits.is_empty() {
            // Another iteration can contribute effects only when the loop has an exit.
            exits.extend(transfers.continues);
        }
        ledger.merge(before, &exits);
    }

    fn condition_unbound(&mut self, ctx: &mut Context, ledger: &mut Ledger, condition: &Condition) {
        match condition {
            Condition::Expr(value) => {
                self.expr(ctx, ledger, *value);
            }
            Condition::Binding { value, .. } => {
                let value = self.expr(ctx, ledger, *value);
                ledger.inspect(&value);
            }
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
                value = value.project(payload.clone(), Access::Immutable);
                ty = inner;
            }
            let coordinate = if let Some(index) = index {
                self.expr(&mut present_ctx, ledger, index);
                self.index_coordinate(&present_ctx, index)
            } else if let Expr::Member { member, .. } = &step.value {
                self.coordinate(&mut present_ctx, ledger, member)
            } else {
                ril_base::ice!("unexpected navigation coordinate");
            };
            if safe && index.is_some() {
                missing.push(ledger.clone());
            }
            let mode = self.schema_mode(ty, &coordinate).0;
            value = ledger.project_schema(&value, coordinate, mode);
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
    for (index, (param, decl)) in callable.parameters.iter().zip(formals).enumerate() {
        if let Some(source) = decl {
            let mut region = Region {
                source: *source,
                selection: Vec::new(),
            };
            collect_axes(index, &param.ty, &mut region, &mut axes);
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

fn collect_axes(index: usize, ty: &Ty, region: &mut Region, output: &mut Vec<(usize, Region)>) {
    let mut visit = |coord, member: &ty::Member| {
        region.selection.push(coord);
        if member.mode.mode == Mode::Via {
            output.push((index, region.clone()));
        }
        collect_axes(index, &member.ty, region, output);
        region.selection.pop();
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
