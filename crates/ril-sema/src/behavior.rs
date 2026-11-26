//! Interprocedural failure (`may_panic`, `may_abort`), termination (`may_diverge`),
//! purity/totality (`pure`/`total`), shortest BFS provenance witnesses, and IDE/inspect
//! site facts (closures, `with` handlers, effect call dispatch, `defer` double-panic warnings).

use std::collections::{BTreeMap, BTreeSet};

use ril_hir::{DefinitionId, DefinitionKind, Intrinsic, Program, Resolution};
use ril_source::span::{FileId, Span};
use ril_syntax::{
    parser::FileKind,
    syntax::{
        Ast, Condition, Expr, ExprId, Handler, LiteralKind, Mode, Pattern, StmtId, StmtKind,
        StringPart,
    },
};
use serde::{Deserialize, Serialize};

use crate::{
    access::{Analysis, Summary, horn},
    ty::{Callable, Ty, TypedProgram},
};

/// Compact cross-package behavior summary persisted in `.rili` outside `abi_hash`.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct BehaviorSummary {
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub may_panic: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub may_abort: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub may_diverge: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub defer_invoked: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub defer_effects: Vec<String>,
}

impl BehaviorSummary {
    pub fn is_empty(&self) -> bool {
        !self.may_panic
            && !self.may_abort
            && !self.may_diverge
            && self.defer_invoked.is_empty()
            && self.defer_effects.is_empty()
    }
}

/// Static cause classification for shortest provenance witness steps.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum WitnessCause {
    Panic,
    Assert,
    IndexOob,
    DivZero,
    ShiftBounds,
    IoTrap,
    DeferDoublePanic,
    StackOverflow,
    FfiAbort,
    CtlStackAlloc,
    LoopAlloc,
    BigShift,
    Loop,
    Recursion,
    IndirectCall,
    Ffi,
    External,
    Truncated,
}

impl WitnessCause {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Panic => "panic",
            Self::Assert => "assert",
            Self::IndexOob => "index_oob",
            Self::DivZero => "div_zero",
            Self::ShiftBounds => "shift_bounds",
            Self::IoTrap => "io_trap",
            Self::DeferDoublePanic => "defer_double_panic",
            Self::StackOverflow => "stack_overflow",
            Self::FfiAbort => "ffi_abort",
            Self::CtlStackAlloc => "ctl_stack_alloc",
            Self::LoopAlloc => "loop_alloc",
            Self::BigShift => "big_shift",
            Self::Loop => "loop",
            Self::Recursion => "recursion",
            Self::IndirectCall => "indirect_call",
            Self::Ffi => "ffi",
            Self::External => "external",
            Self::Truncated => "truncated",
        }
    }
}

/// Single step in a shortest BFS provenance witness chain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WitnessStep {
    pub at: Option<Span>,
    pub call: Option<String>,
    pub cause: Option<WitnessCause>,
    pub detail: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BehaviorWitnesses {
    pub may_panic: Vec<WitnessStep>,
    pub may_abort: Vec<WitnessStep>,
    pub may_diverge: Vec<WitnessStep>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeferDoublePanicWarning {
    pub defer_span: Span,
    pub enclosing_fn: Option<DefinitionId>,
    pub defer_panic: Vec<WitnessStep>,
    pub scope_panic_span: Option<Span>,
    pub scope_panic_detail: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureSiteFact {
    pub span: Span,
    pub enclosing: Option<DefinitionId>,
    pub captures: Vec<String>,
    pub effect_ops: Vec<String>,
    pub behavior: BehaviorSummary,
    pub witnesses: BehaviorWitnesses,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WithSiteFact {
    pub span: Span,
    pub enclosing: Option<DefinitionId>,
    pub op: String,
    pub scope: Span,
    pub handler_span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectCallSiteFact {
    pub span: Span,
    pub enclosing: Option<DefinitionId>,
    pub op: String,
    pub bound_by: Option<Span>,
}

#[derive(Clone, Debug, Default)]
pub struct BehaviorAnalysis {
    pub summaries: BTreeMap<DefinitionId, BehaviorSummary>,
    pub witnesses: BTreeMap<DefinitionId, BehaviorWitnesses>,
    pub defer_warnings: Vec<DeferDoublePanicWarning>,
    pub closures: Vec<ClosureSiteFact>,
    pub with_sites: Vec<WithSiteFact>,
    pub effect_calls: Vec<EffectCallSiteFact>,
}

/// Observational purity predicate matching `doc/SPEC.md#failure-model-and-purity`.
pub fn is_pure(callable: &Callable, summary: &Summary) -> bool {
    let has_writable_param = callable.parameters.iter().any(|p| {
        matches!(p.mode, Mode::Mut | Mode::Shared) || p.ty.contains_writable_member_schema()
    });
    let has_live_up = callable
        .state
        .iter()
        .any(|clause| clause == "up" || clause.starts_with("up("));
    !has_writable_param
        && !callable.open_effects
        && !callable.open_state
        && callable.effects.is_empty()
        && summary.effects.is_empty()
        && summary.writes.is_empty()
        && summary.retained.is_empty()
        && !summary.captures
        && !has_live_up
}

/// Totality predicate: observationally pure + no panic + no process abort + terminating.
pub fn is_total(callable: &Callable, summary: &Summary, behavior: &BehaviorSummary) -> bool {
    is_pure(callable, summary)
        && !behavior.may_panic
        && !behavior.may_abort
        && !behavior.may_diverge
        && !summary.nonreturning
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Owner {
    Fn(DefinitionId),
    Closure(Span),
    Defer(Span),
    PostDefer(Span),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum BKind {
    Panic,
    Abort,
    Diverge,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct BFact {
    owner: Owner,
    kind: BKind,
}

#[derive(Clone, Debug)]
struct RuleOrigin {
    at: Option<Span>,
    call: Option<String>,
    cause: Option<WitnessCause>,
    detail: Option<String>,
    /// For binary premises (`[defer_panic, post_defer_panic] -> abort`), follow premise 0.
    follow_premise: Option<usize>,
}

struct WalkCtx {
    owner: Owner,
    enclosing_fn: Option<DefinitionId>,
    file: FileId,
    in_loop: bool,
    in_defer: bool,
    formal_indices: BTreeMap<DefinitionId, usize>,
    local_closures: BTreeMap<DefinitionId, Span>,
    non_zero_locals: BTreeSet<DefinitionId>,
    active_post_defers: Vec<Owner>,
    handlers: Vec<(String, Span, Option<Owner>)>,
    /// Closures found in user files for site reporting.
    user_file: bool,
}

struct ClosureMeta {
    span: Span,
    enclosing: Option<DefinitionId>,
    captures: Vec<String>,
    effect_ops: Vec<String>,
}

struct Collector<'a> {
    program: &'a TypedProgram,
    analysis: &'a Analysis,
    rules: Vec<horn::Rule<BFact>>,
    origins: Vec<RuleOrigin>,
    call_edges: BTreeMap<DefinitionId, BTreeSet<(DefinitionId, Span)>>,
    defer_invoked: BTreeMap<DefinitionId, BTreeSet<usize>>,
    defer_effects: BTreeMap<DefinitionId, BTreeSet<String>>,
    defer_records: Vec<(Span, Option<DefinitionId>, Owner, Owner, bool)>,
    closures_meta: Vec<ClosureMeta>,
    with_sites: Vec<WithSiteFact>,
    effect_calls: Vec<EffectCallSiteFact>,
}

pub fn analyze(program: &TypedProgram, analysis: &Analysis) -> BehaviorAnalysis {
    let mut collector = Collector {
        program,
        analysis,
        rules: Vec::new(),
        origins: Vec::new(),
        call_edges: BTreeMap::new(),
        defer_invoked: BTreeMap::new(),
        defer_effects: BTreeMap::new(),
        defer_records: Vec::new(),
        closures_meta: Vec::new(),
        with_sites: Vec::new(),
        effect_calls: Vec::new(),
    };

    // 1. Seed imported functions from `.rili` `Interface.behavior`.
    for (&def_id, imported) in &program.imported_behaviors {
        let name = program.hir.export_name(def_id);
        let owner = Owner::Fn(def_id);
        if imported.may_panic {
            collector.seed(
                owner,
                BKind::Panic,
                RuleOrigin {
                    at: None,
                    call: Some(name.clone()),
                    cause: Some(WitnessCause::External),
                    detail: None,
                    follow_premise: None,
                },
            );
        }
        if imported.may_abort {
            collector.seed(
                owner,
                BKind::Abort,
                RuleOrigin {
                    at: None,
                    call: Some(name.clone()),
                    cause: Some(WitnessCause::External),
                    detail: None,
                    follow_premise: None,
                },
            );
        }
        if imported.may_diverge {
            collector.seed(
                owner,
                BKind::Diverge,
                RuleOrigin {
                    at: None,
                    call: Some(name),
                    cause: Some(WitnessCause::External),
                    detail: None,
                    follow_premise: None,
                },
            );
        }
    }

    // 2. Walk every file & function body (including stdlib so stdlib combinators have exact facts).
    let mut all_fns = Vec::new();
    for file in program.hir.files() {
        let user_file = !program.hir.is_stdlib_file(file.id);
        collector.walk_items(file.id, &file.ast.items, user_file, &mut all_fns);
    }

    // 3. Tarjan SCC on direct call graph -> seed Recursion (MayDiverge) + StackOverflow (MayAbort).
    let recursive = find_recursive_functions(&collector.call_edges);
    for (fn_id, call_span) in recursive {
        let name = display_def_name(&program.hir, fn_id);
        collector.seed(
            Owner::Fn(fn_id),
            BKind::Diverge,
            RuleOrigin {
                at: Some(call_span),
                call: Some(name.clone()),
                cause: Some(WitnessCause::Recursion),
                detail: None,
                follow_premise: None,
            },
        );
        collector.seed(
            Owner::Fn(fn_id),
            BKind::Abort,
            RuleOrigin {
                at: Some(call_span),
                call: Some(name),
                cause: Some(WitnessCause::StackOverflow),
                detail: Some("recursive call cycle".into()),
                follow_premise: None,
            },
        );
    }

    // 4. Solve Horn system via BFS to obtain mathematically shortest, cycle-free witness tree.
    let (facts, derived_by) = horn::solve_with_witnesses(&collector.rules);

    let mut out = BehaviorAnalysis {
        with_sites: collector.with_sites,
        effect_calls: collector.effect_calls,
        ..BehaviorAnalysis::default()
    };

    // Include imported functions in `summaries`.
    for (&def_id, imported) in &program.imported_behaviors {
        out.summaries.insert(def_id, imported.clone());
    }

    // Extract summaries & shortest witnesses for every local/stdlib function.
    for fn_id in all_fns {
        let owner = Owner::Fn(fn_id);
        let summary = BehaviorSummary {
            may_panic: facts.contains(&BFact {
                owner,
                kind: BKind::Panic,
            }),
            may_abort: facts.contains(&BFact {
                owner,
                kind: BKind::Abort,
            }),
            may_diverge: facts.contains(&BFact {
                owner,
                kind: BKind::Diverge,
            }),
            defer_invoked: collector
                .defer_invoked
                .get(&fn_id)
                .map(|s| s.iter().copied().collect())
                .unwrap_or_default(),
            defer_effects: collector
                .defer_effects
                .get(&fn_id)
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default(),
        };
        let witnesses = BehaviorWitnesses {
            may_panic: if summary.may_panic {
                extract_witness(
                    program,
                    BFact {
                        owner,
                        kind: BKind::Panic,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                )
            } else {
                Vec::new()
            },
            may_abort: if summary.may_abort {
                extract_witness(
                    program,
                    BFact {
                        owner,
                        kind: BKind::Abort,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                )
            } else {
                Vec::new()
            },
            may_diverge: if summary.may_diverge {
                extract_witness(
                    program,
                    BFact {
                        owner,
                        kind: BKind::Diverge,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                )
            } else {
                Vec::new()
            },
        };
        out.summaries.insert(fn_id, summary);
        out.witnesses.insert(fn_id, witnesses);
    }

    // Extract closure site facts (user files only).
    for ClosureMeta {
        span,
        enclosing,
        captures,
        effect_ops,
    } in collector.closures_meta
    {
        let owner = Owner::Closure(span);
        let behavior = BehaviorSummary {
            may_panic: facts.contains(&BFact {
                owner,
                kind: BKind::Panic,
            }),
            may_abort: facts.contains(&BFact {
                owner,
                kind: BKind::Abort,
            }),
            may_diverge: facts.contains(&BFact {
                owner,
                kind: BKind::Diverge,
            }),
            defer_invoked: Vec::new(),
            defer_effects: Vec::new(),
        };
        let witnesses = BehaviorWitnesses {
            may_panic: if behavior.may_panic {
                extract_witness(
                    program,
                    BFact {
                        owner,
                        kind: BKind::Panic,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                )
            } else {
                Vec::new()
            },
            may_abort: if behavior.may_abort {
                extract_witness(
                    program,
                    BFact {
                        owner,
                        kind: BKind::Abort,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                )
            } else {
                Vec::new()
            },
            may_diverge: if behavior.may_diverge {
                extract_witness(
                    program,
                    BFact {
                        owner,
                        kind: BKind::Diverge,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                )
            } else {
                Vec::new()
            },
        };
        out.closures.push(ClosureSiteFact {
            span,
            enclosing,
            captures,
            effect_ops,
            behavior,
            witnesses,
        });
    }

    // Extract `W0601` DOUBLE_PANIC warnings for user-file `defer` statements.
    for (defer_span, enclosing_fn, defer_owner, post_owner, nested_in_defer) in
        collector.defer_records
    {
        if program.hir.is_stdlib_file(defer_span.file) {
            continue;
        }
        let defer_panics = facts.contains(&BFact {
            owner: defer_owner,
            kind: BKind::Panic,
        });
        let scope_panics = nested_in_defer
            || facts.contains(&BFact {
                owner: post_owner,
                kind: BKind::Panic,
            });
        if defer_panics && scope_panics {
            let defer_panic = extract_witness(
                program,
                BFact {
                    owner: defer_owner,
                    kind: BKind::Panic,
                },
                &collector.rules,
                &collector.origins,
                &derived_by,
            );
            let (scope_panic_span, scope_panic_detail) = if nested_in_defer {
                (None, Some("nested inside outer defer cleanup".into()))
            } else {
                let post_steps = extract_witness(
                    program,
                    BFact {
                        owner: post_owner,
                        kind: BKind::Panic,
                    },
                    &collector.rules,
                    &collector.origins,
                    &derived_by,
                );
                let first = post_steps.first();
                let span = first.and_then(|s| s.at);
                let detail = first.map(|s| {
                    if let Some(call) = &s.call {
                        format!("enclosing scope may panic here via `{call}`")
                    } else if let Some(cause) = s.cause {
                        format!("enclosing scope may panic here ({})", cause.as_str())
                    } else {
                        "enclosing scope may panic here".into()
                    }
                });
                (span, detail)
            };
            out.defer_warnings.push(DeferDoublePanicWarning {
                defer_span,
                enclosing_fn,
                defer_panic,
                scope_panic_span,
                scope_panic_detail,
            });
        }
    }

    out
}

impl<'a> Collector<'a> {
    fn ast(&self, file: FileId) -> &'a Ast {
        &self.program.hir.file(file).ast
    }

    fn resolve_def(&self, span: Span) -> Option<DefinitionId> {
        self.program
            .hir
            .resolve(span)
            .and_then(Resolution::definition)
    }

    fn push_rule(&mut self, rule: horn::Rule<BFact>, origin: RuleOrigin) {
        self.rules.push(rule);
        self.origins.push(origin);
    }

    fn seed(&mut self, owner: Owner, kind: BKind, origin: RuleOrigin) {
        self.push_rule(
            horn::Rule {
                premises: Vec::new(),
                conclusion: BFact { owner, kind },
            },
            origin,
        );
    }

    fn seed_in_ctx(&mut self, ctx: &WalkCtx, kind: BKind, origin: RuleOrigin) {
        self.seed(ctx.owner, kind, origin.clone());
        if kind == BKind::Panic {
            for &post in &ctx.active_post_defers {
                self.seed(post, BKind::Panic, origin.clone());
            }
        }
    }

    fn link(&mut self, from: Owner, to: Owner, kind: BKind, origin: RuleOrigin) {
        if from == to {
            return;
        }
        self.push_rule(
            horn::Rule {
                premises: vec![BFact { owner: from, kind }],
                conclusion: BFact { owner: to, kind },
            },
            origin,
        );
    }

    fn link_in_ctx(&mut self, from: Owner, ctx: &WalkCtx, kind: BKind, origin: RuleOrigin) {
        self.link(from, ctx.owner, kind, origin.clone());
        if kind == BKind::Panic {
            for &post in &ctx.active_post_defers {
                self.link(from, post, BKind::Panic, origin.clone());
            }
        }
    }

    fn link_all_in_ctx(&mut self, from: Owner, ctx: &WalkCtx, origin: RuleOrigin) {
        self.link_in_ctx(from, ctx, BKind::Panic, origin.clone());
        self.link_in_ctx(from, ctx, BKind::Abort, origin.clone());
        self.link_in_ctx(from, ctx, BKind::Diverge, origin);
    }

    fn walk_items(
        &mut self,
        file: FileId,
        items: &[StmtId],
        user_file: bool,
        all_fns: &mut Vec<DefinitionId>,
    ) {
        for &stmt_id in items {
            let stmt = self.ast(file).stmt(stmt_id);
            match &stmt.value.kind {
                StmtKind::Function(function) => {
                    if let Some(def_id) = self.resolve_def(function.name.span) {
                        all_fns.push(def_id);
                        self.walk_function(file, def_id, function, user_file, all_fns);
                    }
                }
                StmtKind::Sub { items, .. } => {
                    self.walk_items(file, items, user_file, all_fns);
                }
                _ => {}
            }
        }
    }

    fn walk_function(
        &mut self,
        file: FileId,
        def_id: DefinitionId,
        function: &ril_syntax::syntax::Function,
        user_file: bool,
        all_fns: &mut Vec<DefinitionId>,
    ) {
        let owner = Owner::Fn(def_id);
        let is_foreign = self.program.hir.file(file).kind == FileKind::Foreign;

        // Walk `where` helpers attached to the function first so helper functions are registered.
        self.walk_items(file, &function.helpers, user_file, all_fns);

        if is_foreign {
            let name = display_def_name(&self.program.hir, def_id);
            let span = function.name.span;
            self.seed(
                owner,
                BKind::Panic,
                RuleOrigin {
                    at: Some(span),
                    call: Some(name.clone()),
                    cause: Some(WitnessCause::Ffi),
                    detail: None,
                    follow_premise: None,
                },
            );
            self.seed(
                owner,
                BKind::Abort,
                RuleOrigin {
                    at: Some(span),
                    call: Some(name.clone()),
                    cause: Some(WitnessCause::FfiAbort),
                    detail: None,
                    follow_premise: None,
                },
            );
            self.seed(
                owner,
                BKind::Diverge,
                RuleOrigin {
                    at: Some(span),
                    call: Some(name),
                    cause: Some(WitnessCause::Ffi),
                    detail: None,
                    follow_premise: None,
                },
            );
            return;
        }

        // Bodyless stdlib primitives: seed exact runtime failure/termination traits.
        if function.body.is_none() {
            if let Some(intrinsic) = self.program.hir.intrinsic(def_id) {
                let name = display_def_name(&self.program.hir, def_id);
                match intrinsic {
                    Intrinsic::Panic => {
                        self.seed(
                            owner,
                            BKind::Panic,
                            RuleOrigin {
                                at: None,
                                call: Some(name),
                                cause: Some(WitnessCause::Panic),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                    }
                    Intrinsic::ArrayInsert => {
                        self.seed(
                            owner,
                            BKind::Panic,
                            RuleOrigin {
                                at: None,
                                call: Some(name),
                                cause: Some(WitnessCause::IndexOob),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                    }
                    Intrinsic::Print => {
                        self.seed(
                            owner,
                            BKind::Panic,
                            RuleOrigin {
                                at: None,
                                call: Some(name.clone()),
                                cause: Some(WitnessCause::IoTrap),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                        self.seed(
                            owner,
                            BKind::Diverge,
                            RuleOrigin {
                                at: None,
                                call: Some(name),
                                cause: Some(WitnessCause::Ffi),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                    }
                    Intrinsic::FileRead | Intrinsic::FileWrite => {
                        self.seed(
                            owner,
                            BKind::Diverge,
                            RuleOrigin {
                                at: None,
                                call: Some(name),
                                cause: Some(WitnessCause::Ffi),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                    }
                    _ => {}
                }
            }
            return;
        }

        let mut formal_indices = BTreeMap::new();
        for (idx, param) in function.signature.params.iter().enumerate() {
            if let Some(name) = &param.name
                && let Some(param_id) = self.resolve_def(name.span)
            {
                formal_indices.insert(param_id, idx);
            }
        }

        let mut ctx = WalkCtx {
            owner,
            enclosing_fn: Some(def_id),
            file,
            in_loop: false,
            in_defer: false,
            formal_indices,
            local_closures: BTreeMap::new(),
            non_zero_locals: BTreeSet::new(),
            active_post_defers: Vec::new(),
            handlers: Vec::new(),
            user_file,
        };

        for &guard in &function.signature.guards {
            self.walk_expr(&mut ctx, guard, all_fns);
        }
        if let Some(body) = function.body {
            self.walk_expr(&mut ctx, body, all_fns);
        }
    }

    fn walk_block(
        &mut self,
        ctx: &mut WalkCtx,
        statements: &[StmtId],
        helpers: &[StmtId],
        block_span: Span,
        all_fns: &mut Vec<DefinitionId>,
    ) {
        self.walk_items(ctx.file, helpers, ctx.user_file, all_fns);
        let saved_post_defers = ctx.active_post_defers.len();
        let saved_handlers = ctx.handlers.len();
        let saved_closures = ctx.local_closures.clone();
        let saved_non_zero = ctx.non_zero_locals.clone();

        for &stmt_id in statements {
            let stmt = self.ast(ctx.file).stmt(stmt_id);
            let stmt_span = stmt.span;
            match &stmt.value.kind {
                StmtKind::Function(function) => {
                    if let Some(def_id) = self.resolve_def(function.name.span) {
                        all_fns.push(def_id);
                        self.walk_function(ctx.file, def_id, function, ctx.user_file, all_fns);
                    }
                }
                StmtKind::Sub { items, .. } => {
                    self.walk_items(ctx.file, items, ctx.user_file, all_fns);
                }
                StmtKind::Binding {
                    pattern,
                    value,
                    fallback,
                    ..
                } => {
                    if let Some(expr) = value {
                        self.walk_expr(ctx, *expr, all_fns);
                        if let Pattern::Binding(_, name) =
                            &self.ast(ctx.file).pattern(*pattern).value
                            && let Some(binding_id) = self.resolve_def(name.span)
                            && let Expr::Closure { .. } = &self.ast(ctx.file).expr(*expr).value
                        {
                            ctx.local_closures
                                .insert(binding_id, self.ast(ctx.file).expr(*expr).span);
                        }
                    }
                    if let Some(fb) = fallback {
                        self.walk_expr(ctx, *fb, all_fns);
                    }
                }
                StmtKind::Defer(body) => {
                    let defer_owner = Owner::Defer(stmt_span);
                    let post_owner = Owner::PostDefer(stmt_span);

                    // Walk defer body under its own child owner with `in_defer = true`.
                    let mut defer_ctx = WalkCtx {
                        owner: defer_owner,
                        enclosing_fn: ctx.enclosing_fn,
                        file: ctx.file,
                        in_loop: ctx.in_loop,
                        in_defer: true,
                        formal_indices: ctx.formal_indices.clone(),
                        local_closures: ctx.local_closures.clone(),
                        non_zero_locals: ctx.non_zero_locals.clone(),
                        active_post_defers: Vec::new(),
                        handlers: ctx.handlers.clone(),
                        user_file: ctx.user_file,
                    };
                    self.walk_expr(&mut defer_ctx, *body, all_fns);

                    // Normal exit or unwind panic in defer propagates to enclosing owner.
                    let defer_origin = RuleOrigin {
                        at: Some(stmt_span),
                        call: None,
                        cause: None,
                        detail: Some("defer cleanup".into()),
                        follow_premise: Some(0),
                    };
                    self.link_in_ctx(defer_owner, ctx, BKind::Panic, defer_origin.clone());
                    self.link_in_ctx(defer_owner, ctx, BKind::Abort, defer_origin.clone());
                    self.link_in_ctx(defer_owner, ctx, BKind::Diverge, defer_origin);

                    // DOUBLE_PANIC abort rule:
                    // If already inside an outer defer, any panic in nested defer can abort;
                    // otherwise if BOTH defer body and post-defer scope can panic -> MayAbort!
                    let abort_origin = RuleOrigin {
                        at: Some(stmt_span),
                        call: None,
                        cause: Some(WitnessCause::DeferDoublePanic),
                        detail: Some("panic in defer during unwind".into()),
                        follow_premise: Some(0),
                    };
                    if ctx.in_defer {
                        self.link_in_ctx(defer_owner, ctx, BKind::Abort, abort_origin);
                    } else {
                        self.push_rule(
                            horn::Rule {
                                premises: vec![
                                    BFact {
                                        owner: defer_owner,
                                        kind: BKind::Panic,
                                    },
                                    BFact {
                                        owner: post_owner,
                                        kind: BKind::Panic,
                                    },
                                ],
                                conclusion: BFact {
                                    owner: ctx.owner,
                                    kind: BKind::Abort,
                                },
                            },
                            abort_origin,
                        );
                    }

                    self.defer_records.push((
                        stmt_span,
                        ctx.enclosing_fn,
                        defer_owner,
                        post_owner,
                        ctx.in_defer,
                    ));
                    ctx.active_post_defers.push(post_owner);
                }
                StmtKind::With(handler) => {
                    let scope = Span::new(ctx.file, stmt_span.start, block_span.end);
                    self.register_handler(ctx, handler, stmt_span, scope, all_fns);
                }
                StmtKind::Expr(expr) => {
                    self.walk_expr(ctx, *expr, all_fns);
                }
                StmtKind::Type(_)
                | StmtKind::Effect { .. }
                | StmtKind::Import(_)
                | StmtKind::Error => {}
            }
        }

        ctx.active_post_defers.truncate(saved_post_defers);
        ctx.handlers.truncate(saved_handlers);
        ctx.local_closures = saved_closures;
        ctx.non_zero_locals = saved_non_zero;
    }

    fn register_handler(
        &mut self,
        ctx: &mut WalkCtx,
        handler: &Handler,
        with_span: Span,
        scope: Span,
        all_fns: &mut Vec<DefinitionId>,
    ) {
        if handler.is_ctl {
            self.seed_in_ctx(
                ctx,
                BKind::Abort,
                RuleOrigin {
                    at: Some(with_span),
                    call: None,
                    cause: Some(WitnessCause::CtlStackAlloc),
                    detail: Some("with ctl stack allocation".into()),
                    follow_premise: None,
                },
            );
        }
        self.walk_expr(ctx, handler.value, all_fns);
        let handler_owner = self.callable_owner(ctx, handler.value);
        let op_name = format_handler_op(handler);
        if ctx.user_file {
            let handler_span = self.ast(ctx.file).expr(handler.value).span;
            self.with_sites.push(WithSiteFact {
                span: with_span,
                enclosing: ctx.enclosing_fn,
                op: op_name.clone(),
                scope,
                handler_span,
            });
        }
        ctx.handlers.push((op_name, with_span, handler_owner));
    }

    fn callable_owner(&self, ctx: &WalkCtx, expr_id: ExprId) -> Option<Owner> {
        let node = self.ast(ctx.file).expr(expr_id);
        match &node.value {
            Expr::Closure { .. } => Some(Owner::Closure(node.span)),
            Expr::Path(path) => {
                let def_id = self.resolve_def(path.span)?;
                if let Some(&closure_span) = ctx.local_closures.get(&def_id) {
                    Some(Owner::Closure(closure_span))
                } else if self.program.hir.definition(def_id).kind == DefinitionKind::Function {
                    Some(Owner::Fn(def_id))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn walk_expr(&mut self, ctx: &mut WalkCtx, expr_id: ExprId, all_fns: &mut Vec<DefinitionId>) {
        let node = self.ast(ctx.file).expr(expr_id);
        let span = node.span;
        match &node.value {
            Expr::Path(_)
            | Expr::Unit
            | Expr::Literal(_)
            | Expr::Quote(_)
            | Expr::Meta(_)
            | Expr::Accessor(_)
            | Expr::Hole => {}
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation(inner) = part {
                        self.walk_expr(ctx, *inner, all_fns);
                    }
                }
                if ctx.in_loop {
                    self.seed_in_ctx(
                        ctx,
                        BKind::Abort,
                        RuleOrigin {
                            at: Some(span),
                            call: None,
                            cause: Some(WitnessCause::LoopAlloc),
                            detail: Some("string allocation in loop".into()),
                            follow_premise: None,
                        },
                    );
                }
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                self.walk_block(ctx, statements, helpers, span, all_fns);
            }
            Expr::With {
                handlers,
                statements,
                helpers,
            } => {
                let saved = ctx.handlers.len();
                for handler in handlers {
                    self.register_handler(ctx, handler, span, span, all_fns);
                }
                self.walk_block(ctx, statements, helpers, span, all_fns);
                ctx.handlers.truncate(saved);
            }
            Expr::Unary { value, .. } => {
                self.walk_expr(ctx, *value, all_fns);
            }
            Expr::Binary { op, left, right } => {
                let op_str = op.value.as_str();
                // Assignment to `map[k] = v` inserts safely without panicking; array `xs[i] = v` panics OOB.
                if op_str == "=" {
                    if let Expr::Index {
                        base,
                        index,
                        safe: false,
                    } = &self.ast(ctx.file).expr(*left).value
                    {
                        self.walk_expr(ctx, *base, all_fns);
                        self.walk_expr(ctx, *index, all_fns);
                        let base_ty = self.program.types.get(&self.ast(ctx.file).expr(*base).span);
                        if !matches!(base_ty, Some(Ty::Map(..))) {
                            self.seed_in_ctx(
                                ctx,
                                BKind::Panic,
                                RuleOrigin {
                                    at: Some(self.ast(ctx.file).expr(*left).span),
                                    call: None,
                                    cause: Some(WitnessCause::IndexOob),
                                    detail: None,
                                    follow_premise: None,
                                },
                            );
                        } else if ctx.in_loop {
                            self.seed_in_ctx(
                                ctx,
                                BKind::Abort,
                                RuleOrigin {
                                    at: Some(span),
                                    call: None,
                                    cause: Some(WitnessCause::LoopAlloc),
                                    detail: Some("map insertion in loop".into()),
                                    follow_premise: None,
                                },
                            );
                        }
                    } else {
                        self.walk_expr(ctx, *left, all_fns);
                    }
                    self.walk_expr(ctx, *right, all_fns);
                    return;
                }
                self.walk_expr(ctx, *left, all_fns);
                self.walk_expr(ctx, *right, all_fns);
                let left_ty = self.program.types.get(&self.ast(ctx.file).expr(*left).span);
                match op_str {
                    "/" | "%" | "/=" | "%=" if matches!(left_ty, Some(Ty::Int) | None) => {
                        if !self.is_nonzero_expr(ctx, *right) {
                            self.seed_in_ctx(
                                ctx,
                                BKind::Panic,
                                RuleOrigin {
                                    at: Some(span),
                                    call: None,
                                    cause: Some(WitnessCause::DivZero),
                                    detail: None,
                                    follow_premise: None,
                                },
                            );
                        }
                    }
                    "<<" | ">>" | "<<=" | ">>="
                        if !self.is_small_nonneg_int_literal(ctx, *right) =>
                    {
                        self.seed_in_ctx(
                            ctx,
                            BKind::Panic,
                            RuleOrigin {
                                at: Some(span),
                                call: None,
                                cause: Some(WitnessCause::ShiftBounds),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                        if matches!(op_str, "<<" | "<<=") {
                            self.seed_in_ctx(
                                ctx,
                                BKind::Abort,
                                RuleOrigin {
                                    at: Some(span),
                                    call: None,
                                    cause: Some(WitnessCause::BigShift),
                                    detail: Some("unbounded left shift allocation".into()),
                                    follow_premise: None,
                                },
                            );
                        }
                    }
                    _ => {}
                }
            }
            Expr::Cast { value, .. } => {
                self.walk_expr(ctx, *value, all_fns);
            }
            Expr::Pipeline { value, target, .. } => {
                self.walk_expr(ctx, *value, all_fns);
                let target_node = self.ast(ctx.file).expr(*target);
                match &target_node.value {
                    Expr::Call { callee, args } => {
                        let mut full_args = Vec::with_capacity(args.len() + 1);
                        full_args.push(*value);
                        for arg in args {
                            full_args.push(arg.value);
                        }
                        self.walk_call_like(ctx, span, *callee, &full_args, all_fns);
                    }
                    _ => {
                        self.walk_call_like(ctx, span, *target, &[*value], all_fns);
                    }
                }
            }
            Expr::Member { base, member, .. } => {
                self.walk_expr(ctx, *base, all_fns);
                if let ril_syntax::syntax::Member::Computed(idx) = member {
                    self.walk_expr(ctx, *idx, all_fns);
                }
            }
            Expr::Index { base, index, safe } => {
                self.walk_expr(ctx, *base, all_fns);
                self.walk_expr(ctx, *index, all_fns);
                if !*safe {
                    self.seed_in_ctx(
                        ctx,
                        BKind::Panic,
                        RuleOrigin {
                            at: Some(span),
                            call: None,
                            cause: Some(WitnessCause::IndexOob),
                            detail: None,
                            follow_premise: None,
                        },
                    );
                }
            }
            Expr::Range { start, end, .. } => {
                if let Some(s) = start {
                    self.walk_expr(ctx, *s, all_fns);
                }
                if let Some(e) = end {
                    self.walk_expr(ctx, *e, all_fns);
                }
            }
            Expr::Call { callee, args } => {
                let arg_ids: Vec<ExprId> = args.iter().map(|a| a.value).collect();
                self.walk_call_like(ctx, span, *callee, &arg_ids, all_fns);
            }
            Expr::Wrap { args, .. } => {
                for arg in args {
                    self.walk_expr(ctx, arg.value, all_fns);
                }
            }
            Expr::Record { fields, .. } => {
                for field in fields {
                    if let Some(v) = field.value {
                        self.walk_expr(ctx, v, all_fns);
                    }
                }
                if ctx.in_loop {
                    self.seed_in_ctx(
                        ctx,
                        BKind::Abort,
                        RuleOrigin {
                            at: Some(span),
                            call: None,
                            cause: Some(WitnessCause::LoopAlloc),
                            detail: Some("record allocation in loop".into()),
                            follow_premise: None,
                        },
                    );
                }
            }
            Expr::Array(items) | Expr::Tuple(items) => {
                for &item in items {
                    self.walk_expr(ctx, item, all_fns);
                }
                if ctx.in_loop && !items.is_empty() {
                    self.seed_in_ctx(
                        ctx,
                        BKind::Abort,
                        RuleOrigin {
                            at: Some(span),
                            call: None,
                            cause: Some(WitnessCause::LoopAlloc),
                            detail: Some("collection allocation in loop".into()),
                            follow_premise: None,
                        },
                    );
                }
            }
            Expr::Map(entries) => {
                for &(k, v) in entries {
                    self.walk_expr(ctx, k, all_fns);
                    self.walk_expr(ctx, v, all_fns);
                }
                if ctx.in_loop && !entries.is_empty() {
                    self.seed_in_ctx(
                        ctx,
                        BKind::Abort,
                        RuleOrigin {
                            at: Some(span),
                            call: None,
                            cause: Some(WitnessCause::LoopAlloc),
                            detail: Some("map allocation in loop".into()),
                            follow_premise: None,
                        },
                    );
                }
            }
            Expr::If {
                is_meta,
                condition,
                yes,
                no,
            } => {
                if *is_meta && let Some(&branch) = self.program.meta_if_decisions.get(&span) {
                    if branch {
                        self.walk_expr(ctx, *yes, all_fns);
                    } else if let Some(no_expr) = no {
                        self.walk_expr(ctx, *no_expr, all_fns);
                    }
                    return;
                }
                self.walk_condition(ctx, condition, all_fns);
                let (yes_nz, no_nz) = self.zero_guard_locals(ctx, condition);
                let saved = ctx.non_zero_locals.clone();
                if let Some(id) = yes_nz {
                    ctx.non_zero_locals.insert(id);
                }
                self.walk_expr(ctx, *yes, all_fns);
                ctx.non_zero_locals = saved.clone();
                if let Some(no_expr) = no {
                    if let Some(id) = no_nz {
                        ctx.non_zero_locals.insert(id);
                    }
                    self.walk_expr(ctx, *no_expr, all_fns);
                }
                ctx.non_zero_locals = saved;
            }
            Expr::While { condition, body } => {
                self.seed_in_ctx(
                    ctx,
                    BKind::Diverge,
                    RuleOrigin {
                        at: Some(span),
                        call: None,
                        cause: Some(WitnessCause::Loop),
                        detail: None,
                        follow_premise: None,
                    },
                );
                self.walk_condition(ctx, condition, all_fns);
                let prev_loop = ctx.in_loop;
                ctx.in_loop = true;
                self.walk_expr(ctx, *body, all_fns);
                ctx.in_loop = prev_loop;
            }
            Expr::For { iterable, body, .. } => {
                self.walk_expr(ctx, *iterable, all_fns);
                let prev_loop = ctx.in_loop;
                ctx.in_loop = true;
                self.walk_expr(ctx, *body, all_fns);
                ctx.in_loop = prev_loop;
            }
            Expr::Match {
                is_meta,
                value,
                arms,
                ..
            } => {
                if *is_meta
                    && let Some(&chosen) = self.program.meta_match_decisions.get(&span)
                    && let Some(arm) = arms.get(chosen)
                {
                    self.walk_expr(ctx, arm.body, all_fns);
                    return;
                }
                self.walk_expr(ctx, *value, all_fns);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.walk_expr(ctx, guard, all_fns);
                    }
                    self.walk_expr(ctx, arm.body, all_fns);
                }
            }
            Expr::Closure { params, body, .. } => {
                let closure_owner = Owner::Closure(span);
                let mut formal_indices = BTreeMap::new();
                for (idx, param) in params.iter().enumerate() {
                    if let Some(name) = &param.name
                        && let Some(id) = self.resolve_def(name.span)
                    {
                        formal_indices.insert(id, idx);
                    }
                }
                let mut closure_ctx = WalkCtx {
                    owner: closure_owner,
                    enclosing_fn: ctx.enclosing_fn,
                    file: ctx.file,
                    in_loop: false,
                    in_defer: false,
                    formal_indices,
                    local_closures: BTreeMap::new(),
                    non_zero_locals: BTreeSet::new(),
                    active_post_defers: Vec::new(),
                    handlers: Vec::new(), // Route 1: closures never capture outer `with` handlers!
                    user_file: ctx.user_file,
                };
                self.walk_expr(&mut closure_ctx, *body, all_fns);

                if ctx.user_file {
                    let captures = self.collect_closure_captures(span);
                    let effect_ops = self.collect_closure_effect_ops(span);
                    if ctx.in_loop && !captures.is_empty() {
                        self.seed_in_ctx(
                            ctx,
                            BKind::Abort,
                            RuleOrigin {
                                at: Some(span),
                                call: None,
                                cause: Some(WitnessCause::LoopAlloc),
                                detail: Some("closure environment allocation in loop".into()),
                                follow_premise: None,
                            },
                        );
                    }
                    self.closures_meta.push(ClosureMeta {
                        span,
                        enclosing: ctx.enclosing_fn,
                        captures,
                        effect_ops,
                    });
                }
            }
            Expr::Transfer { value, .. } => {
                if let Some(v) = value {
                    self.walk_expr(ctx, *v, all_fns);
                }
            }
        }
    }

    fn walk_condition(
        &mut self,
        ctx: &mut WalkCtx,
        condition: &Condition,
        all_fns: &mut Vec<DefinitionId>,
    ) {
        match condition {
            Condition::Expr(e) => self.walk_expr(ctx, *e, all_fns),
            Condition::Binding { value, .. } => self.walk_expr(ctx, *value, all_fns),
        }
    }

    fn walk_call_like(
        &mut self,
        ctx: &mut WalkCtx,
        call_span: Span,
        callee_expr: ExprId,
        args: &[ExprId],
        all_fns: &mut Vec<DefinitionId>,
    ) {
        let callee_node = self.ast(ctx.file).expr(callee_expr);
        for &arg in args {
            self.walk_expr(ctx, arg, all_fns);
        }
        // Only walk callee expression if it is complex (not a plain resolved path).
        if !matches!(callee_node.value, Expr::Path(_)) {
            self.walk_expr(ctx, callee_expr, all_fns);
        }

        // Case 1: Resolved definition (function, primitive, or effect op).
        if let Expr::Path(path) = &callee_node.value
            && let Some(def_id) = self.resolve_def(path.span)
        {
            // 1a. Effect operation call (`Eff::op(...)`).
            if let Some(eff_id) = self.program.hir.operation_effect(def_id) {
                let eff_name = &self.program.hir.definition(eff_id).name.value;
                let op_short = &self.program.hir.definition(def_id).name.value;
                let is_ctl = self.program.hir.is_ctl_operation(def_id);
                let op_label = if is_ctl {
                    format!("ctl {eff_name}::{op_short}")
                } else {
                    format!("{eff_name}::{op_short}")
                };
                let lookup_key = format!("{eff_name}::{op_short}");
                let bound = ctx
                    .handlers
                    .iter()
                    .rev()
                    .find(|(k, _, _)| k.strip_prefix("ctl ").unwrap_or(k) == lookup_key)
                    .cloned();
                if ctx.user_file {
                    self.effect_calls.push(EffectCallSiteFact {
                        span: call_span,
                        enclosing: ctx.enclosing_fn,
                        op: op_label.clone(),
                        bound_by: bound.as_ref().map(|(_, s, _)| *s),
                    });
                }
                if let Some((_, _, Some(handler_owner))) = bound {
                    self.link_all_in_ctx(
                        handler_owner,
                        ctx,
                        RuleOrigin {
                            at: Some(call_span),
                            call: Some(op_label),
                            cause: None,
                            detail: None,
                            follow_premise: Some(0),
                        },
                    );
                } else if ctx.in_defer
                    && let Some(fn_id) = ctx.enclosing_fn
                {
                    self.defer_effects
                        .entry(fn_id)
                        .or_default()
                        .insert(eff_name.to_owned());
                }
                return;
            }

            // 1b. Special compiler intrinsics.
            if let Some(intrinsic) = self.program.hir.intrinsic(def_id) {
                match intrinsic {
                    Intrinsic::RecoverPanic => {
                        if let Some(&arg0) = args.first()
                            && let Some(cb_owner) = self.callable_owner(ctx, arg0)
                        {
                            let origin = RuleOrigin {
                                at: Some(call_span),
                                call: Some("recover_panic".into()),
                                cause: None,
                                detail: None,
                                follow_premise: Some(0),
                            };
                            self.link_in_ctx(cb_owner, ctx, BKind::Abort, origin.clone());
                            self.link_in_ctx(cb_owner, ctx, BKind::Diverge, origin.clone());
                            // Inside `defer`, `enter_cleanup` suspends the outer panic so
                            // `recover_panic` CANNOT stop DOUBLE_PANIC!
                            if ctx.in_defer {
                                self.link_in_ctx(cb_owner, ctx, BKind::Panic, origin);
                            }
                        }
                        return;
                    }
                    Intrinsic::Derive => {
                        if let Some(&arg1) = args.get(1)
                            && let Some(cb_owner) = self.callable_owner(ctx, arg1)
                        {
                            self.link_all_in_ctx(
                                cb_owner,
                                ctx,
                                RuleOrigin {
                                    at: Some(call_span),
                                    call: Some("derive".into()),
                                    cause: None,
                                    detail: None,
                                    follow_premise: Some(0),
                                },
                            );
                        }
                        if ctx.in_loop {
                            self.seed_in_ctx(
                                ctx,
                                BKind::Abort,
                                RuleOrigin {
                                    at: Some(call_span),
                                    call: Some("derive".into()),
                                    cause: Some(WitnessCause::LoopAlloc),
                                    detail: None,
                                    follow_premise: None,
                                },
                            );
                        }
                        return;
                    }
                    Intrinsic::UnwindCtl => {
                        return;
                    }
                    Intrinsic::Clone
                    | Intrinsic::ArrayPush
                    | Intrinsic::ArrayInsert
                    | Intrinsic::MapInsert
                    | Intrinsic::StringFromScalars
                    | Intrinsic::BytesFromArray
                        if ctx.in_loop =>
                    {
                        let name = display_def_name(&self.program.hir, def_id);
                        self.seed_in_ctx(
                            ctx,
                            BKind::Abort,
                            RuleOrigin {
                                at: Some(call_span),
                                call: Some(name),
                                cause: Some(WitnessCause::LoopAlloc),
                                detail: None,
                                follow_premise: None,
                            },
                        );
                    }
                    _ => {}
                }
            }

            // 1c. `assert(true, ...)` constant exemption.
            let def = self.program.hir.definition(def_id);
            if def.name.value == "assert"
                && self.program.hir.is_stdlib_file(def.name.span.file)
                && let Some(&cond_expr) = args.first()
                && matches!(
                    &self.ast(ctx.file).expr(cond_expr).value,
                    Expr::Literal(lit) if lit.kind == LiteralKind::Bool && lit.text == "true"
                )
            {
                return;
            }

            // 1d. Formal parameter callback call (`f(...)`).
            if let Some(&formal_idx) = ctx.formal_indices.get(&def_id) {
                if ctx.in_defer
                    && let Some(fn_id) = ctx.enclosing_fn
                {
                    self.defer_invoked
                        .entry(fn_id)
                        .or_default()
                        .insert(formal_idx);
                }
                return;
            }

            // 1e. Known local closure binding call (`let f = \...; f()`).
            if let Some(&closure_span) = ctx.local_closures.get(&def_id) {
                let name = def.name.value.clone();
                self.link_all_in_ctx(
                    Owner::Closure(closure_span),
                    ctx,
                    RuleOrigin {
                        at: Some(call_span),
                        call: Some(name),
                        cause: None,
                        detail: None,
                        follow_premise: Some(0),
                    },
                );
                return;
            }

            // 1f. Named function call (local, stdlib, foreign, or imported).
            if matches!(
                def.kind,
                DefinitionKind::Function | DefinitionKind::Primitive(_)
            ) {
                if let Some(caller_fn) = ctx.enclosing_fn
                    && !self.program.imported_behaviors.contains_key(&def_id)
                {
                    self.call_edges
                        .entry(caller_fn)
                        .or_default()
                        .insert((def_id, call_span));
                }
                let callee_name = display_def_name(&self.program.hir, def_id);
                let is_assert = def.name.value == "assert"
                    && self.program.hir.is_stdlib_file(def.name.span.file);
                let origin = RuleOrigin {
                    at: Some(call_span),
                    call: Some(callee_name),
                    cause: is_assert.then_some(WitnessCause::Assert),
                    detail: None,
                    follow_premise: Some(0),
                };
                self.link_all_in_ctx(Owner::Fn(def_id), ctx, origin);

                // Higher-order parametricity: link callback arguments invoked by callee.
                if let Some(summary) = self.analysis.summaries.get(&def_id) {
                    for &cb_idx in &summary.invoked {
                        if let Some(&arg_expr) = args.get(cb_idx) {
                            self.link_callback_arg(ctx, call_span, arg_expr, false);
                        }
                    }
                }
                if let Some(imported) = self.program.imported_behaviors.get(&def_id) {
                    for &cb_idx in &imported.defer_invoked {
                        if let Some(&arg_expr) = args.get(cb_idx) {
                            self.link_callback_arg(ctx, call_span, arg_expr, true);
                        }
                    }
                }
                return;
            }

            // 1g. Variant / nominal constructor call (never panics or diverges).
            if matches!(
                def.kind,
                DefinitionKind::Variant(_) | DefinitionKind::Type | DefinitionKind::Sum(_)
            ) {
                if ctx.in_loop && !args.is_empty() {
                    self.seed_in_ctx(
                        ctx,
                        BKind::Abort,
                        RuleOrigin {
                            at: Some(call_span),
                            call: Some(def.name.value.clone()),
                            cause: Some(WitnessCause::LoopAlloc),
                            detail: None,
                            follow_premise: None,
                        },
                    );
                }
                return;
            }
        }

        // Case 2: Indirect call to a direct closure literal (`(\x -> ...)(1)`).
        if let Expr::Closure { .. } = &callee_node.value {
            self.link_all_in_ctx(
                Owner::Closure(callee_node.span),
                ctx,
                RuleOrigin {
                    at: Some(call_span),
                    call: None,
                    cause: None,
                    detail: None,
                    follow_premise: Some(0),
                },
            );
            return;
        }

        // Case 3: Opaque dynamic callable (e.g. pulled from an array/record).
        let detail = self
            .program
            .hir
            .file(ctx.file)
            .source_text()
            .get(callee_node.span.start..callee_node.span.end)
            .map(str::trim)
            .filter(|s| s.len() <= 32)
            .map(ToOwned::to_owned);
        self.seed_in_ctx(
            ctx,
            BKind::Panic,
            RuleOrigin {
                at: Some(call_span),
                call: None,
                cause: Some(WitnessCause::IndirectCall),
                detail: detail.clone(),
                follow_premise: None,
            },
        );
        self.seed_in_ctx(
            ctx,
            BKind::Abort,
            RuleOrigin {
                at: Some(call_span),
                call: None,
                cause: Some(WitnessCause::StackOverflow),
                detail: detail.clone(),
                follow_premise: None,
            },
        );
        self.seed_in_ctx(
            ctx,
            BKind::Diverge,
            RuleOrigin {
                at: Some(call_span),
                call: None,
                cause: Some(WitnessCause::IndirectCall),
                detail,
                follow_premise: None,
            },
        );
    }

    fn link_callback_arg(
        &mut self,
        ctx: &WalkCtx,
        call_span: Span,
        arg_expr: ExprId,
        in_callee_defer: bool,
    ) {
        if let Some(cb_owner) = self.callable_owner(ctx, arg_expr) {
            let origin = RuleOrigin {
                at: Some(call_span),
                call: None,
                cause: None,
                detail: Some("callback argument".into()),
                follow_premise: Some(0),
            };
            self.link_all_in_ctx(cb_owner, ctx, origin);
            if in_callee_defer {
                self.link_in_ctx(
                    cb_owner,
                    ctx,
                    BKind::Abort,
                    RuleOrigin {
                        at: Some(call_span),
                        call: None,
                        cause: Some(WitnessCause::DeferDoublePanic),
                        detail: Some("callback invoked in callee defer".into()),
                        follow_premise: Some(0),
                    },
                );
            }
            return;
        }
        // Check if passing a formal parameter of the caller (parametric, do not taint caller).
        if let Expr::Path(path) = &self.ast(ctx.file).expr(arg_expr).value
            && let Some(def_id) = self.resolve_def(path.span)
            && ctx.formal_indices.contains_key(&def_id)
        {
            return;
        }
        // Otherwise opaque dynamic callable passed into HOF.
        self.seed_in_ctx(
            ctx,
            BKind::Panic,
            RuleOrigin {
                at: Some(call_span),
                call: None,
                cause: Some(WitnessCause::IndirectCall),
                detail: Some("dynamic callback".into()),
                follow_premise: None,
            },
        );
        self.seed_in_ctx(
            ctx,
            BKind::Diverge,
            RuleOrigin {
                at: Some(call_span),
                call: None,
                cause: Some(WitnessCause::IndirectCall),
                detail: Some("dynamic callback".into()),
                follow_premise: None,
            },
        );
    }

    fn is_nonzero_expr(&self, ctx: &WalkCtx, expr_id: ExprId) -> bool {
        let node = self.ast(ctx.file).expr(expr_id);
        match &node.value {
            Expr::Literal(lit) if lit.kind == LiteralKind::Int => {
                parse_int_literal(&lit.text).is_some_and(|n| n != 0)
            }
            Expr::Unary { op, value } if op.value == "-" => self.is_nonzero_expr(ctx, *value),
            Expr::Path(path) => self
                .resolve_def(path.span)
                .is_some_and(|id| ctx.non_zero_locals.contains(&id)),
            _ => false,
        }
    }

    fn is_small_nonneg_int_literal(&self, ctx: &WalkCtx, expr_id: ExprId) -> bool {
        let node = self.ast(ctx.file).expr(expr_id);
        matches!(
            &node.value,
            Expr::Literal(lit)
                if lit.kind == LiteralKind::Int
                    && parse_int_literal(&lit.text).is_some_and(|n| (0..=64).contains(&n))
        )
    }

    /// Recognizes simple `x == 0` / `x != 0` guards so `checked_div`/`checked_rem` are total.
    fn zero_guard_locals(
        &self,
        ctx: &WalkCtx,
        condition: &Condition,
    ) -> (Option<DefinitionId>, Option<DefinitionId>) {
        let Condition::Expr(expr_id) = condition else {
            return (None, None);
        };
        let Expr::Binary { op, left, right } = &self.ast(ctx.file).expr(*expr_id).value else {
            return (None, None);
        };
        let is_zero = |id: ExprId| {
            matches!(
                &self.ast(ctx.file).expr(id).value,
                Expr::Literal(lit)
                    if lit.kind == LiteralKind::Int && parse_int_literal(&lit.text) == Some(0)
            )
        };
        let local_id = |id: ExprId| match &self.ast(ctx.file).expr(id).value {
            Expr::Path(path) => self.resolve_def(path.span),
            _ => None,
        };
        let target = if is_zero(*right) {
            local_id(*left)
        } else if is_zero(*left) {
            local_id(*right)
        } else {
            None
        };
        match op.value.as_str() {
            "==" => (None, target),
            "!=" => (target, None),
            _ => (None, None),
        }
    }

    fn collect_closure_captures(&self, closure_span: Span) -> Vec<String> {
        let mut out = Vec::new();
        let mut seen = BTreeSet::new();
        if let Some(entries) = self.analysis.closure_captures.get(&closure_span) {
            for &(decl_span, mode) in entries {
                if !seen.insert(decl_span) {
                    continue;
                }
                let name = self
                    .program
                    .hir
                    .definitions()
                    .find(|(_, d)| d.name.span == decl_span)
                    .map(|(_, d)| d.name.value.clone());
                if let Some(name) = name {
                    let prefix = match mode {
                        Mode::Mut => "mut ",
                        Mode::Shared => "^mut ",
                        Mode::Ref => "ref ",
                        Mode::New => "new ",
                        _ => "",
                    };
                    out.push(format!("{prefix}{name}"));
                }
            }
        }
        out
    }

    fn collect_closure_effect_ops(&self, closure_span: Span) -> Vec<String> {
        let mut ops = BTreeSet::new();
        if let Some(Ty::Callable(c)) = self.program.types.get(&closure_span) {
            for eff in &c.effects {
                if eff == "io" {
                    ops.insert("@io".into());
                } else {
                    ops.insert(format!("@{eff}"));
                }
            }
            if c.open_effects {
                ops.insert("@".into());
            }
        }
        ops.into_iter().collect()
    }
}

fn format_handler_op(handler: &Handler) -> String {
    let path = handler
        .operation
        .segments
        .iter()
        .map(|s| s.name.value.as_str())
        .collect::<Vec<_>>()
        .join("::");
    if handler.is_ctl {
        format!("ctl {path}")
    } else {
        path
    }
}

fn parse_int_literal(raw: &str) -> Option<i128> {
    let cleaned = raw.replace('_', "");
    if let Some(hex) = cleaned
        .strip_prefix("0x")
        .or_else(|| cleaned.strip_prefix("0X"))
    {
        i128::from_str_radix(hex, 16).ok()
    } else if let Some(bin) = cleaned
        .strip_prefix("0b")
        .or_else(|| cleaned.strip_prefix("0B"))
    {
        i128::from_str_radix(bin, 2).ok()
    } else if let Some(oct) = cleaned
        .strip_prefix("0o")
        .or_else(|| cleaned.strip_prefix("0O"))
    {
        i128::from_str_radix(oct, 8).ok()
    } else {
        cleaned.parse::<i128>().ok()
    }
}

fn display_def_name(hir: &Program, id: DefinitionId) -> String {
    let def = hir.definition(id);
    if hir.is_stdlib_file(def.name.span.file) {
        let export = hir.export_name(id);
        if let Some(rest) = export.strip_prefix("ril/") {
            return format!("ril/{rest}");
        }
        export
    } else {
        def.name.value.clone()
    }
}

/// Tarjan SCC over direct call edges; returns every function in a recursive cycle
/// along with a representative cyclic call span.
fn find_recursive_functions(
    edges: &BTreeMap<DefinitionId, BTreeSet<(DefinitionId, Span)>>,
) -> Vec<(DefinitionId, Span)> {
    struct Tarjan<'a> {
        edges: &'a BTreeMap<DefinitionId, BTreeSet<(DefinitionId, Span)>>,
        index: usize,
        indices: BTreeMap<DefinitionId, usize>,
        lowlink: BTreeMap<DefinitionId, usize>,
        stack: Vec<DefinitionId>,
        on_stack: BTreeSet<DefinitionId>,
        sccs: Vec<Vec<DefinitionId>>,
    }

    impl Tarjan<'_> {
        fn visit(&mut self, v: DefinitionId) {
            let idx = self.index;
            self.index += 1;
            self.indices.insert(v, idx);
            self.lowlink.insert(v, idx);
            self.stack.push(v);
            self.on_stack.insert(v);

            if let Some(neighbors) = self.edges.get(&v) {
                let targets: Vec<DefinitionId> = neighbors.iter().map(|(w, _)| *w).collect();
                for w in targets {
                    if !self.indices.contains_key(&w) {
                        self.visit(w);
                        if let Some(&lw) = self.lowlink.get(&w)
                            && let Some(lv) = self.lowlink.get_mut(&v)
                        {
                            *lv = (*lv).min(lw);
                        }
                    } else if self.on_stack.contains(&w)
                        && let Some(&iw) = self.indices.get(&w)
                        && let Some(lv) = self.lowlink.get_mut(&v)
                    {
                        *lv = (*lv).min(iw);
                    }
                }
            }

            if self.lowlink.get(&v) == self.indices.get(&v) {
                let mut comp = Vec::new();
                while let Some(w) = self.stack.pop() {
                    self.on_stack.remove(&w);
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                self.sccs.push(comp);
            }
        }
    }

    let mut nodes: BTreeSet<DefinitionId> = edges.keys().copied().collect();
    for targets in edges.values() {
        for &(t, _) in targets {
            nodes.insert(t);
        }
    }
    let mut tarjan = Tarjan {
        edges,
        index: 0,
        indices: BTreeMap::new(),
        lowlink: BTreeMap::new(),
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        sccs: Vec::new(),
    };
    for node in nodes {
        if !tarjan.indices.contains_key(&node) {
            tarjan.visit(node);
        }
    }

    let mut recursive = Vec::new();
    for comp in tarjan.sccs {
        let member_set: BTreeSet<DefinitionId> = comp.iter().copied().collect();
        if comp.len() > 1 {
            for fn_id in comp {
                if let Some((_, span)) = edges
                    .get(&fn_id)
                    .and_then(|ns| ns.iter().find(|(t, _)| member_set.contains(t)))
                {
                    recursive.push((fn_id, *span));
                }
            }
        } else if let Some(&fn_id) = comp.first()
            && let Some((_, span)) = edges
                .get(&fn_id)
                .and_then(|ns| ns.iter().find(|(t, _)| *t == fn_id))
        {
            recursive.push((fn_id, *span));
        }
    }
    recursive.sort_by_key(|(id, _)| *id);
    recursive
}

const MAX_WITNESS_HOPS: usize = 8;

/// Reconstructs a shortest, cycle-free witness chain from the BFS derivation tree,
/// collapsing consecutive stdlib hops so user code + leaf root cause stay crystal clear.
fn extract_witness(
    program: &TypedProgram,
    start: BFact,
    rules: &[horn::Rule<BFact>],
    origins: &[RuleOrigin],
    derived_by: &BTreeMap<BFact, usize>,
) -> Vec<WitnessStep> {
    let mut steps = Vec::new();
    let mut visited = BTreeSet::new();
    let mut cur = start;
    let mut skipped_stdlib = 0usize;

    while visited.insert(cur) {
        let Some(&rule_idx) = derived_by.get(&cur) else {
            break;
        };
        let Some(rule) = rules.get(rule_idx) else {
            break;
        };
        let Some(origin) = origins.get(rule_idx) else {
            break;
        };
        let is_leaf = origin.follow_premise.is_none() || rule.premises.is_empty();
        let is_stdlib_hop = !is_leaf
            && origin
                .at
                .is_some_and(|s| program.hir.is_stdlib_file(s.file));

        if is_stdlib_hop {
            skipped_stdlib += 1;
        } else {
            let mut detail = origin.detail.clone();
            if skipped_stdlib > 0 {
                let note = format!("via {skipped_stdlib} stdlib hop(s)");
                detail = Some(match detail {
                    Some(existing) => format!("{existing} ({note})"),
                    None => note,
                });
                skipped_stdlib = 0;
            }
            steps.push(WitnessStep {
                at: origin.at,
                call: origin.call.clone(),
                cause: origin.cause,
                detail,
            });
            if steps.len() >= MAX_WITNESS_HOPS && !is_leaf {
                steps.push(WitnessStep {
                    at: None,
                    call: None,
                    cause: Some(WitnessCause::Truncated),
                    detail: Some("witness depth limit reached".into()),
                });
                break;
            }
        }

        if let Some(p_idx) = origin.follow_premise
            && let Some(&next) = rule.premises.get(p_idx)
        {
            cur = next;
        } else {
            break;
        }
    }
    steps
}
