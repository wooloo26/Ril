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
    Access, Analysis, CleanupAction, Input, Instance, Summary,
    flow::{Coordinate, Datum, Ledger, Slot, conflicts},
    horn::{self, Rule},
};
use crate::ty::{self, AdtKind, Callable, Ty, TypedProgram, Value};

mod calls;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Obligation {
    Write(Span),
    Replace(Span),
    Retain(Span),
    Share(Span),
    ReadUp(Span),
    Capture,
    StatefulHandler,
    Effect(String),
    Operation(DefinitionId),
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
    via: BTreeSet<Span>,
    handlers: BTreeMap<DefinitionId, Datum>,
    local_effects: BTreeSet<String>,
    expected: Mode,
    returns: Vec<Span>,
    declared_contained: Vec<(Access, Span)>,
    return_values: Vec<Datum>,
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
            via: BTreeSet::new(),
            handlers: BTreeMap::new(),
            local_effects: BTreeSet::new(),
            expected: Mode::Plain,
            returns: Vec::new(),
            declared_contained: Vec::new(),
            return_values: Vec::new(),
            reachable: true,
            shadow: false,
            in_function: false,
            runtime: true,
        }
    }
}

struct Requirement {
    fact: Fact,
    span: Span,
    message: &'static str,
}

struct DefinitionCheck {
    owner: Span,
    id: DefinitionId,
    formals: Vec<Option<Span>>,
    declared: Callable,
    actual_roots: Vec<usize>,
    actual_contained: Vec<(Access, usize)>,
    via: BTreeSet<Span>,
    returned_new: bool,
    capture_names: BTreeSet<Span>,
}

struct ModeUse {
    callee: DefinitionId,
    choices: Vec<(usize, Input, Span)>,
}

struct Analyzer<'a> {
    program: &'a TypedProgram,
    diagnostics: Vec<Diagnostic>,
    rules: Vec<Rule<Fact>>,
    requirements: Vec<Requirement>,
    deferred_effect_errors: Vec<(Fact, Diagnostic)>,
    mode_uses: Vec<ModeUse>,
    functions: Vec<DefinitionCheck>,
    done: BTreeSet<DefinitionId>,
    cleanups: BTreeMap<Span, CleanupAction>,
}

pub(super) fn check(program: &TypedProgram) -> Result<Analysis, Vec<Diagnostic>> {
    let mut analyzer = Analyzer {
        program,
        diagnostics: Vec::new(),
        rules: Vec::new(),
        requirements: Vec::new(),
        deferred_effect_errors: Vec::new(),
        mode_uses: Vec::new(),
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
    let facts = horn::solve(&analyzer.rules);
    for (fact, diagnostic) in std::mem::take(&mut analyzer.deferred_effect_errors) {
        if facts.contains(&fact)
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
    for function in std::mem::take(&mut analyzer.functions) {
        let summary = analyzer.finish_function(&facts, &function);
        let instances = analyzer.via_table(&function, &summary);
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
            if summary.retained.contains(&index) && mode != Input::Shared {
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
    if analyzer.diagnostics.is_empty() {
        Ok(analysis)
    } else {
        Err(analyzer.diagnostics)
    }
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

    fn effect(&mut self, ctx: &Context, effect: &str, span: Span) {
        self.use_effect(ctx, Obligation::Effect(effect.into()), span, None);
    }

    fn use_effect(
        &mut self,
        ctx: &Context,
        obligation: Obligation,
        span: Span,
        if_exercised: Option<Fact>,
    ) {
        if ctx.shadow || !ctx.reachable {
            return;
        }
        let hir = &self.program.hir;
        let (label, operations) = match &obligation {
            Obligation::Operation(operation) => {
                let effect = hir.operation_effect(*operation).unwrap_or_else(|| {
                    ril_base::ice!("operation summary refers to a non-effect function")
                });
                (hir.effect_label(effect), vec![*operation])
            }
            Obligation::Effect(effect) => {
                let operations = hir
                    .effect_by_label(effect)
                    .map_or_else(Vec::new, |id| hir.effect_operations(id).collect());
                (effect.clone(), operations)
            }
            _ => ril_base::ice!("expected effect obligation"),
        };
        if !operations.is_empty() && operations.iter().all(|id| ctx.handlers.contains_key(id)) {
            for handler in operations.iter().filter_map(|id| ctx.handlers.get(id)) {
                self.link_invocation_if(ctx, handler, if_exercised.as_ref());
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
        let error = if ctx.local_effects.contains(&label) {
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
                self.deferred_effect_errors
                    .push((fact, Diagnostic::error(code, span, message)));
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
        ledger.revoked.clear();
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
            let mut value = if param.ty.is_value() {
                Datum::default()
            } else {
                Datum::source(span, Access::from_mode(param.mode), param.mode == Mode::New)
            };
            value.transform(&mut |origin| {
                origin.dependencies.insert(span);
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
        if ctx.expected == Mode::Infer
            && ctx.via.is_empty()
            && !callable
                .parameters
                .iter()
                .any(|parameter| has_via(&parameter.ty))
        {
            self.error(
                Code::E0412,
                ctx.owner,
                "infer requires via in this callable's parameter list",
            );
        }
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
        let mut actual_roots = BTreeSet::new();
        let mut actual_contained = BTreeSet::new();
        for value in &ctx.return_values {
            for origin in &value.roots {
                if matches!(ctx.expected, Mode::Ref | Mode::Shared | Mode::Infer)
                    && let Some(index) = ctx
                        .formals
                        .iter()
                        .position(|param| *param == Some(origin.region.source))
                {
                    actual_roots.insert(index);
                    if ctx.expected == Mode::Shared {
                        self.seed(&ctx, Obligation::Retain(origin.region.source));
                    }
                }
            }
            for origin in value.members.values().flat_map(Datum::origins) {
                if !origin.new
                    && let Some(index) = ctx
                        .formals
                        .iter()
                        .position(|param| *param == Some(origin.region.source))
                {
                    actual_contained.insert((origin.mode, index));
                }
            }
        }
        self.functions.push(DefinitionCheck {
            owner: ctx.owner,
            id,
            formals: ctx.formals,
            declared: (**callable).clone(),
            via: ctx.via,
            actual_roots: actual_roots.into_iter().collect(),
            actual_contained: actual_contained.into_iter().collect(),
            returned_new: !ctx.return_values.is_empty()
                && ctx.return_values.iter().all(|value| value.requires_new),
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
            roots: fun.actual_roots.clone(),
            contained: fun.actual_contained.clone(),
            constructs: fun.returned_new,
            ..Summary::default()
        };
        let mut up = BTreeSet::new();
        for fact in facts.iter().filter(|fact| fact.owner == fun.owner) {
            match &fact.obligation {
                Obligation::Write(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.writes.push(param);
                    }
                }
                Obligation::Share(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.retained.push(param);
                    }
                }
                Obligation::ReadUp(span) => {
                    up.insert(*span);
                }
                Obligation::Effect(effect) => summary.effects.push(effect.clone()),
                Obligation::Operation(operation) => {
                    if let Some(effect) = self.program.hir.operation_effect(*operation) {
                        summary.effects.push(self.program.hir.effect_label(effect));
                    }
                }
                Obligation::Capture => summary.captures = true,
                _ => {}
            }
        }
        summary.writes.sort_unstable();
        summary.retained.sort_unstable();
        summary.effects.sort();
        summary.effects.dedup();
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
                .any(|declared| self.program.hir.effect_covers(declared, effect))
            {
                self.error(Code::E0612, name, format!("unhandled @{effect}"));
            }
        }
        for effect in &sig.effects {
            if !summary
                .effects
                .iter()
                .any(|actual| self.program.hir.effect_covers(effect, actual))
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

    fn via_table(&self, fun: &DefinitionCheck, summary: &Summary) -> Vec<Instance> {
        if fun.via.is_empty() {
            return Vec::new();
        }
        let mut rows: Vec<Vec<Input>> = vec![Vec::new()];
        for (index, formal) in fun.formals.iter().enumerate() {
            if formal.is_none_or(|span| !fun.via.contains(&span)) {
                continue;
            }
            let domain: &[Input] = if summary.retained.contains(&index) {
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
            rows = rows
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
        rows.into_iter()
            .map(|modes| Instance {
                modes,
                summary: summary.clone(),
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
                if !ctx.reachable {
                    return Datum::default();
                }
                if *resource {
                    self.cleanup(ctx, &mut value, span, node.span, storage.mode);
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

    fn returned(&mut self, ctx: &mut Context, ledger: &mut Ledger, value: Datum, span: Span) {
        ledger.inspect(&value);
        if value.origins().any(|origin| origin.confined.is_some()) {
            self.error(Code::E0604, span, "confined authority cannot be returned");
        }
        if !ctx.runtime || ctx.shadow {
            return;
        }
        if value.creates_environment() {
            self.seed(ctx, Obligation::Capture);
        }
        match ctx.expected {
            Mode::Plain if value.requires_new => self.error(
                Code::E0544,
                ctx.owner,
                "fresh shared return must declare -> new",
            ),
            Mode::Plain
                if value
                    .roots
                    .iter()
                    .any(|root| root.mode != Access::Immutable) =>
            {
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
        ctx.return_values.push(value);
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

    fn cleanup(
        &mut self,
        ctx: &Context,
        value: &mut Datum,
        value_span: Span,
        binding: Span,
        mode: Mode,
    ) {
        if matches!(self.ty(value_span), Ty::Sender(_)) {
            if !value.requires_new {
                self.error(Code::E0548, binding, "cleanup requires an owned sender");
            }
            value.transform(&mut |origin| {
                origin.confined = Some(binding);
                origin.mode = if mode == Mode::Mut {
                    Access::Mut
                } else {
                    Access::Ref
                };
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
                .any(|clause| matches!(clause.as_str(), "^mut" | "capture"))
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
            self.effect(ctx, effect, binding);
        }
        if parameter.mode == Mode::New && !value.requires_new {
            self.error(
                Code::E0548,
                binding,
                "cleanup requires an owned new resource",
            );
        }
        value.transform(&mut |origin| {
            origin.confined = Some(binding);
            origin.mode = if mode == Mode::Mut {
                Access::Mut
            } else {
                Access::Ref
            };
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
                        Obligation::Replace(name.span),
                        "var requires reachable slot replacement",
                    );
                }
                if matches!(mode, Mode::Mut | Mode::Shared) {
                    self.requirement(
                        ctx,
                        name.span,
                        Obligation::Write(name.span),
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
                    Mode::Plain
                        if !resource
                            && !value.requires_new
                            && value
                                .origins()
                                .any(|origin| origin.mode != Access::Immutable) =>
                    {
                        self.error(
                            Code::E0535,
                            name.span,
                            "live authority cannot be frozen as a plain snapshot",
                        );
                    }
                    Mode::Via if ctx.via.is_empty() => {
                        self.error(Code::E0412, name.span, "let via requires a mode template");
                    }
                    Mode::Via
                        if !value.origins().any(|origin| {
                            origin
                                .dependencies
                                .iter()
                                .any(|source| ctx.via.contains(source))
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
                if let Some(ty) = self.program.bindings.get(
                    &self
                        .definition(name.span)
                        .unwrap_or_else(|| ril_base::ice!("unresolved binding pattern")),
                ) {
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
                if mode != Mode::Via {
                    for root in &mut value.roots {
                        root.mode = access;
                    }
                    if mode == Mode::Plain && !resource {
                        value.transform(&mut |origin| {
                            origin.mode = Access::Immutable;
                        });
                    }
                    value.requires_new = false;
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(name.span);
                });
                ledger.stamp(&mut value);
                ledger.slots.insert(
                    name.span,
                    Slot {
                        decl: name.span,
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
            Pattern::Tuple(items)
            | Pattern::Slice {
                elements: items, ..
            } => {
                for (i, &item) in items.iter().enumerate() {
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
                    let child = value.project(
                        Coordinate::Field(field.name.value.clone()),
                        Access::Immutable,
                    );
                    if let Some(pattern) = field.pattern {
                        self.bind(ctx, ledger, pattern, &field.storage, child, resource);
                    } else {
                        let mut child = child;
                        child.transform(&mut |origin| {
                            origin.dependencies.insert(field.name.span);
                        });
                        ledger.slots.insert(
                            field.name.span,
                            Slot {
                                decl: field.name.span,
                                variable: field.storage.variable,
                                mode: field.storage.mode,
                                value: child,
                            },
                        );
                    }
                }
            }
            Pattern::Or(items) => {
                if let Some(&first) = items.first() {
                    self.bind(ctx, ledger, first, storage, value, resource);
                }
            }
            Pattern::Subset {
                binding: Some(id), ..
            } => self.bind(ctx, ledger, *id, storage, value, resource),
            _ => {}
        }
    }

    fn expr(&mut self, ctx: &mut Context, ledger: &mut Ledger, id: ExprId) -> Datum {
        let ast = self.ast(ctx.file);
        let node = ast.expr(id);
        let span = node.span;
        if let Some((base, steps)) = ast.navigation_chain(id) {
            return self.navigate(ctx, ledger, base, &steps, span);
        }
        let mut value = match &node.value {
            Expr::Path(path) => self.read(ctx, ledger, path),
            Expr::Unary { op, value } => {
                let mut value = self.expr(ctx, ledger, *value);
                match op.value.as_str() {
                    "new" => self.handoff(ctx, ledger, &mut value, span),
                    "ref" => {
                        for root in &mut value.roots {
                            root.mode = Access::Ref;
                        }
                        value.requires_new = false;
                    }
                    "^mut" => {
                        if !value.writers() {
                            self.error(Code::E0520, span, "sharing requires writable authority");
                        }
                        for root in &mut value.roots {
                            root.mode = Access::Shared;
                        }
                        value.requires_new = false;
                    }
                    "?" => {
                        ledger.inspect(&value);
                        value = value.project(Coordinate::Index("0".into()), Access::Immutable);
                        value.results.clear();
                    }
                    _ => value = Datum::default(),
                }
                value
            }
            Expr::Binary { op, left, right } => {
                let lhs = self.expr(ctx, ledger, *left);
                let literal = self.literal_bool(ctx, *left);
                let skip = matches!(
                    (op.value.as_str(), literal),
                    ("&&", Some(false)) | ("||", Some(true))
                );
                let fallible = op.value == "??" && self.ty(ast.expr(*left).span).is_result();
                let rhs = if skip {
                    let mut dead = ctx.clone();
                    dead.reachable = false;
                    self.expr(&mut dead, &mut ledger.clone(), *right)
                } else if fallible {
                    self.fallback_handler(ctx, ledger, *right, span)
                } else {
                    self.expr(ctx, ledger, *right)
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
                    let value = if let Some(expr) = field.value {
                        self.expr(ctx, ledger, expr)
                    } else {
                        self.read_span(ctx, ledger, field.name.span)
                    };
                    record
                        .members
                        .insert(Coordinate::Field(field.name.value.clone()), value);
                }
                record
            }
            Expr::Tuple(items) | Expr::Array(items) => {
                let mut sequence = Datum::source(span, Access::Mut, true);
                for (i, &item) in items.iter().enumerate() {
                    sequence.members.insert(
                        Coordinate::Index(i.to_string()),
                        self.expr(ctx, ledger, item),
                    );
                }
                sequence
            }
            Expr::Map(entries) => {
                let mut map = Datum::source(span, Access::Mut, true);
                for (i, &(key, value)) in entries.iter().enumerate() {
                    self.expr(ctx, ledger, key);
                    map.members.insert(
                        Coordinate::Index(i.to_string()),
                        self.expr(ctx, ledger, value),
                    );
                }
                map
            }
            Expr::Member { base, member, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate = self.coordinate(ctx, ledger, member);
                let (mode, variable) = self.member_schema(ast.expr(*base).span, &coordinate);
                let mode = if variable && self.ty(span).is_value() {
                    Access::Mut
                } else {
                    mode
                };
                value.project(coordinate, mode)
            }
            Expr::Index { base, index, .. } => {
                let value = self.expr(ctx, ledger, *base);
                self.expr(ctx, ledger, *index);
                let coordinate = self.index_coordinate(ctx, *index);
                let (mode, _) = self.member_schema(ast.expr(*base).span, &coordinate);
                value.project(coordinate, mode)
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
                if can_yes {
                    alternatives.push(then_ledger);
                }
                if can_no {
                    alternatives.push(else_ledger);
                }
                ledger.merge(&before, &alternatives);
                match (can_yes, can_no) {
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
                if matches!(condition, Condition::Expr(test) if self.literal_bool(ctx, *test) == Some(false))
                {
                    local.reachable = false;
                }
                self.condition(&mut local, &mut inside, condition);
                self.expr(&mut local, &mut inside, *body);
                if local.reachable {
                    ledger.merge(&before, &[before.clone(), inside]);
                }
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
                inside.iteration.push(value.clone());
                let storage = Storage {
                    mode: *mode,
                    ..Storage::default()
                };
                self.bind(
                    ctx,
                    &mut inside,
                    *pattern,
                    &storage,
                    value.project(Coordinate::Dynamic, Access::from_mode(*mode)),
                    false,
                );
                self.expr(ctx, &mut inside, *body);
                ledger.merge(&before, &[before.clone(), inside]);
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
                    if self.ty(ast.expr(arm.body).span) != &Ty::Never {
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
                if *kind == Transfer::Return && ctx.reachable {
                    self.returned(ctx, ledger, value, span);
                    self.check_results(ledger, &BTreeSet::new());
                }
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
        ledger.stamp(&mut value);
        value
    }

    fn read(&mut self, ctx: &Context, ledger: &Ledger, path: &Path) -> Datum {
        self.read_span(ctx, ledger, path.span)
    }

    fn read_span(&mut self, ctx: &Context, ledger: &Ledger, span: Span) -> Datum {
        let Some(decl) = self.declaration(span) else {
            return Datum::default();
        };
        if let Some(slot) = ledger.slots.get(&decl) {
            if ctx.reachable && (ledger.revoked.contains(&decl) || ledger.dead(&slot.value)) {
                self.error(Code::E0549, span, "source path was ended by new handoff");
            }
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
        } else if !self.ty(span).is_value()
            && self.definition(span).is_some_and(|def| {
                self.program.hir.definition(def).kind == DefinitionKind::Constant
            })
        {
            Datum::source(decl, Access::Immutable, false)
        } else {
            Datum::default()
        }
    }

    fn handoff(&mut self, ctx: &Context, ledger: &mut Ledger, value: &mut Datum, span: Span) {
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
            ledger.revoked.extend(&dependencies);
        }
        for id in dependencies {
            self.seed(ctx, Obligation::Write(id));
        }
        for root in &mut value.roots {
            root.new = true;
            root.dependencies.clear();
        }
        value.requires_new = true;
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
                && let Some(slot) = ledger.slots.get_mut(&id)
            {
                if !slot.variable {
                    self.error(
                        if slot.mode == Mode::Plain {
                            Code::E0501
                        } else {
                            Code::E0502
                        },
                        node.span,
                        "binding cannot be reassigned",
                    );
                    return;
                }
                self.seed(ctx, Obligation::Replace(slot.decl));
                for origin in value.origins().filter(|origin| origin.draft) {
                    if origin
                        .confined
                        .is_some_and(|scope| slot.decl.start < scope.start)
                    {
                        self.error(
                            Code::E0607,
                            span,
                            "draft cannot be assigned to an outer slot",
                        );
                    }
                }
                let mut value = value;
                value.transform(&mut |origin| {
                    origin.dependencies.insert(slot.decl);
                    origin.mode = Access::from_mode(slot.mode);
                });
                slot.value = value;
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
        if prior
            .origins()
            .any(|origin| ctx.formals.contains(&Some(origin.region.source)))
        {
            if value.creates_environment() {
                self.seed(ctx, Obligation::Capture);
            }
            for source in value
                .origins()
                .filter(|origin| origin.mode == Access::Shared)
            {
                self.seed(ctx, Obligation::Retain(source.region.source));
                self.seed(ctx, Obligation::Share(source.region.source));
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
        if ledger
            .holds
            .iter()
            .any(|held| conflicts(value, Mode::Mut, held, Mode::Ref).is_some())
        {
            self.error(
                Code::E0524,
                span,
                "write overlaps the active lexical handler view",
            );
        }
        for origin in &value.roots {
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

    fn schema(&self, mut ty: &'a Ty, coordinate: &Coordinate) -> (Access, bool) {
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
        let member = match (ty, coordinate) {
            (Ty::Record(fields, _), Coordinate::Field(name)) => fields.get(name),
            (Ty::Tuple(fields), Coordinate::Index(index)) => index
                .parse::<usize>()
                .ok()
                .and_then(|index| fields.get(index)),
            (Ty::Array(member) | Ty::Map(_, member), _) => Some(member.as_ref()),
            _ => None,
        };
        member.map_or((Access::Immutable, false), |member| {
            (Access::from_mode(member.mode.mode), member.mode.variable)
        })
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
                self.expr(ctx, ledger, index);
                self.index_coordinate(ctx, index)
            } else if let Expr::Member { member, .. } = &step.value {
                self.coordinate(ctx, ledger, member)
            } else {
                ril_base::ice!("unexpected navigation coordinate");
            };
            if safe && index.is_some() {
                missing.push(ledger.clone());
            }
            value = value.project(coordinate.clone(), self.schema(ty, &coordinate).0);
            ty = self
                .program
                .navigation_values
                .get(&step.span)
                .unwrap_or(&Ty::Unknown);
        }
        missing.push(ledger.clone());
        ledger.merge(&entry, &missing);
        if matches!(ty, Ty::Option(_)) {
            value
        } else {
            let mut option = Datum::source(span, Access::Mut, true);
            option.members.insert(payload, value);
            option
        }
    }
}

fn has_via(ty: &Ty) -> bool {
    match ty {
        Ty::Array(item) | Ty::Map(_, item) => item.mode.mode == Mode::Via || has_via(&item.ty),
        Ty::Tuple(items) => items
            .iter()
            .any(|item| item.mode.mode == Mode::Via || has_via(&item.ty)),
        Ty::Record(fields, _) => fields
            .values()
            .any(|item| item.mode.mode == Mode::Via || has_via(&item.ty)),
        _ => false,
    }
}

fn is_assignment(token: &str) -> bool {
    matches!(
        token,
        "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
    )
}
