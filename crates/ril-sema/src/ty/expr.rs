mod builtins;
mod calls;
mod composites;
mod sums;

use std::{collections::HashSet, sync::Arc};

use num_traits::{Signed, Zero};
use ril_hir::{DefinitionId, DefinitionKind, Resolution};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Argument, Condition, Expr, ExprId, Mode, StmtKind, Transfer};

use super::{
    AdtKind, Callable, LiteralError, Member, Parameter, Ty, Value,
    check::{Checker, Env, Phase, substitute, unknown_callable},
    literal,
};

impl Checker<'_> {
    pub(super) fn expect(&mut self, env: &mut Env, expr: ExprId, expected: &Ty) -> Ty {
        let found = self.expr(env, expr, Some(expected));
        self.require(env, self.ast(env.file).expr(expr).span, &found, expected);
        found
    }

    pub(super) fn expr(&mut self, env: &mut Env, id: ExprId, expected: Option<&Ty>) -> Ty {
        let node = self.ast(env.file).expr(id);
        let known = expected.map(|ty| self.normalize(ty));
        let expected = known.as_ref();
        let span = node.span;
        if let Some((base, steps)) = self.ast(env.file).navigation_chain(id) {
            let ty = self.navigation(env, base, &steps);
            self.types.insert(span, ty.clone());
            return ty;
        }
        let ty = match &node.value {
            Expr::Path(path) => self.path_expr(env, path, expected, false),
            Expr::Unit => Ty::Unit,
            Expr::Literal(value) => self.literal_type(value, span),
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let syntax::StringPart::Interpolation(value) = part {
                        let ty = self.expr(env, *value, None);
                        if !matches!(
                            ty,
                            Ty::Str | Ty::Bool | Ty::Int | Ty::F64 | Ty::Unknown | Ty::Never
                        ) {
                            self.error(
                                Code::E0301,
                                self.ast(env.file).expr(*value).span,
                                "interpolation requires str, bool, int, or f64",
                            );
                        }
                    }
                }
                Ty::Str
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                for &helper in helpers {
                    if !matches!(
                        &self.ast(env.file).stmt(helper).value.kind,
                        StmtKind::Function(_)
                    ) {
                        self.statement(env, helper, false);
                    }
                }
                let has_ctl_stmt = statements.iter().any(|&item| {
                    matches!(
                        &self.ast(env.file).stmt(item).value.kind,
                        StmtKind::With(h) if h.is_ctl
                    )
                });
                let ctl_answer = if has_ctl_stmt {
                    Some(expected.cloned().unwrap_or_else(|| self.fresh()))
                } else {
                    None
                };
                let mut ctl_arm_results = Vec::new();
                let mut result = Ty::Unit;
                for (index, &item) in statements.iter().enumerate() {
                    let last = index + 1 == statements.len();
                    let right = if let StmtKind::With(handler) =
                        &self.ast(env.file).stmt(item).value.kind
                        && handler.is_ctl
                    {
                        if let Some(arm_res) =
                            self.check_handler_arm(env, handler, ctl_answer.as_ref())
                        {
                            ctl_arm_results.push(arm_res);
                        }
                        Ty::Unit
                    } else if last
                        && let StmtKind::Expr(expr) = self.ast(env.file).stmt(item).value.kind
                    {
                        self.expr(env, expr, ctl_answer.as_ref().or(expected))
                    } else {
                        self.statement(env, item, last)
                    };
                    if result != Ty::Never {
                        result = right;
                    }
                }
                for arm_res in ctl_arm_results {
                    result = self.join(env, span, result, arm_res);
                }
                for &helper in helpers {
                    if let StmtKind::Function(fun) = &self.ast(env.file).stmt(helper).value.kind {
                        self.function(env, fun);
                    }
                }
                if self.exposes_type(&result, |id| {
                    let def = self.hir.definition(id);
                    def.name.span.file == env.file
                        && def.stmt.is_some_and(|stmt| helpers.contains(&stmt))
                }) {
                    self.error(Code::E0315, span, "block result exposes a local type");
                    Ty::Unknown
                } else {
                    result
                }
            }
            Expr::With {
                handlers,
                statements,
                helpers,
            } => {
                let has_ctl = handlers.iter().any(|h| h.is_ctl);
                let answer_ty = if has_ctl {
                    Some(expected.cloned().unwrap_or_else(|| self.fresh()))
                } else {
                    None
                };
                let mut arm_results = Vec::new();
                for handler in handlers {
                    if let Some(arm_res) = self.check_handler_arm(env, handler, answer_ty.as_ref())
                    {
                        arm_results.push(arm_res);
                    }
                }
                for &helper in helpers {
                    if !matches!(
                        &self.ast(env.file).stmt(helper).value.kind,
                        StmtKind::Function(_)
                    ) {
                        self.statement(env, helper, false);
                    }
                }
                let mut result = Ty::Unit;
                for (index, &item) in statements.iter().enumerate() {
                    let last = index + 1 == statements.len();
                    let right = if last
                        && let StmtKind::Expr(expr) = self.ast(env.file).stmt(item).value.kind
                    {
                        self.expr(env, expr, answer_ty.as_ref().or(expected))
                    } else {
                        self.statement(env, item, last)
                    };
                    if result != Ty::Never {
                        result = right;
                    }
                }
                for arm_res in arm_results {
                    result = self.join(env, span, result, arm_res);
                }
                for &helper in helpers {
                    if let StmtKind::Function(fun) = &self.ast(env.file).stmt(helper).value.kind {
                        self.function(env, fun);
                    }
                }
                if self.exposes_type(&result, |id| {
                    let def = self.hir.definition(id);
                    def.name.span.file == env.file
                        && def.stmt.is_some_and(|stmt| helpers.contains(&stmt))
                }) {
                    self.error(Code::E0315, span, "with block result exposes a local type");
                    Ty::Unknown
                } else {
                    result
                }
            }
            Expr::Unary { op, value } => self.unary(env, op, *value),
            Expr::Binary { op, left, right } => self.binary(env, op, *left, *right, expected),
            Expr::Cast { value, target } => {
                let actual = self.expr(env, *value, None);
                let target = self.type_expr(env, *target);
                if !self.sum_subset(env, &actual, &target) {
                    self.require(env, span, &actual, &target);
                }
                target
            }
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let argument = Argument {
                    name: None,
                    mode: *mode,
                    value: *value,
                };
                let target_node = self.ast(env.file).expr(*target);
                let result = if let Expr::Call { callee, args } = &target_node.value {
                    let arguments = std::iter::once(argument)
                        .chain(args.iter().cloned())
                        .collect::<Vec<_>>();
                    self.call(env, *callee, &arguments, expected, span)
                } else if matches!(target_node.value, Expr::Wrap { .. }) {
                    self.expr(env, *value, None);
                    self.error(
                        Code::E0338,
                        target_node.span,
                        "nominal wrapper cannot be a direct pipeline target; use a closure",
                    );
                    Ty::Unknown
                } else {
                    self.call(env, *target, &[argument], expected, span)
                };
                if *propagate {
                    self.propagate(env, result, span)
                } else {
                    result
                }
            }
            Expr::Member { base, member, .. } => {
                let receiver = self.expr(env, *base, None);
                if receiver.is_option(self.hir)
                    && let Some((code, cause_span)) = self
                        .narrow_errors
                        .get(&self.ast(env.file).expr(*base).span)
                        .copied()
                {
                    self.error_diag(
                        ril_source::diag::Diagnostic::error(
                            code,
                            span,
                            "projection depends on an invalidated narrowing",
                        )
                        .with_label(cause_span, "narrowing invalidated here"),
                    );
                    return Ty::Unknown;
                }
                self.project(env, member, &receiver, span, false)
            }
            Expr::Index { base, index, .. } => {
                let base = self.expr(env, *base, None);
                self.index(env, base, *index, false, span)
            }
            Expr::Range { start, end, .. } => {
                for &value in start.iter().chain(end) {
                    self.expect(env, value, &Ty::Int);
                }
                Ty::Range
            }
            Expr::Call { callee, args } => self.call(env, *callee, args, expected, span),
            Expr::Wrap { path, args } => self.wrap(env, path, args, expected, span),
            Expr::Record { name, fields } => {
                self.record(env, name.as_ref(), fields, expected, span)
            }
            Expr::Array(items) => {
                let mut member = if let Some(Ty::Array(member)) = expected {
                    self.literal_element(env, items.first().copied(), member)
                } else {
                    self.inferred_element(env, items.first().copied())
                };
                if items.is_empty() && expected.is_none() {
                    self.error(
                        Code::E0344,
                        span,
                        "empty array requires an expected element type",
                    );
                }
                for &item in items {
                    self.receive_literal_element(env, item, &mut member);
                }
                Ty::Array(Box::new(member))
            }
            Expr::Tuple(items) => {
                let mut members = Vec::new();
                for (position, &item) in items.iter().enumerate() {
                    let member = match expected {
                        Some(Ty::Tuple(known)) => known.get(position),
                        _ => None,
                    };
                    let ty = self.expr(env, item, member.map(|m| &m.ty));
                    members.push(Member {
                        mode: member.map_or(super::MemberMode::PLAIN, |m| {
                            self.literal_element(env, Some(item), m).mode
                        }),
                        ty,
                    });
                }
                Ty::Tuple(members)
            }
            Expr::Map(items) => {
                let (key, mut member) = match expected {
                    Some(Ty::Map(key, value)) => (
                        (**key).clone(),
                        self.literal_element(env, items.first().map(|(_, value)| *value), value),
                    ),
                    _ => (
                        self.fresh(),
                        self.inferred_element(env, items.first().map(|(_, value)| *value)),
                    ),
                };
                if items.is_empty() && expected.is_none() {
                    self.error(
                        Code::E0344,
                        span,
                        "empty map requires expected key and value types",
                    );
                }
                for &(k, v) in items {
                    self.expect(env, k, &key);
                    self.receive_literal_element(env, v, &mut member);
                }
                if !self.eligible_key(env, &self.normalize(&key), &mut HashSet::new()) {
                    self.error(Code::E0328, span, "invalid map key type");
                }
                Ty::Map(Box::new(key), Box::new(member))
            }
            Expr::Quote(ty) => Ty::TypeValue(Some(Box::new(self.type_expr(env, *ty)))),
            Expr::Meta(inner) => {
                if env.phase != Phase::Runtime {
                    self.error(
                        Code::E0810,
                        span,
                        "'meta' expression is only allowed in runtime code; compile-time code is already evaluated statically",
                    );
                }
                let mut local = env.clone();
                local.phase = Phase::MetaValue;
                local.expected_return = None;
                local.inferred_return = None;
                local.return_scope = None;
                local.effects_seen.clear();
                if env.phase == Phase::Runtime {
                    local.static_boundary = Some(span);
                }
                let stripped_expected = expected.map(Self::strip_live_modes);
                let ty = self.expr(&mut local, *inner, stripped_expected.as_ref());
                let norm = self.normalize(&ty);
                if !env.shadow && !local.effects_seen.is_empty() {
                    self.error(
                        Code::E0810,
                        span,
                        "compile-time meta expression cannot perform runtime effects",
                    );
                }
                let valid_output = if norm.contains_type_value() {
                    self.error(
                        Code::E0816,
                        span,
                        "type values cannot escape a compile-time meta expression into runtime code",
                    );
                    false
                } else if !self.meta_exportable(&local, &norm, &mut HashSet::new()) {
                    self.error(
                        Code::E0816,
                        span,
                        "meta expression result cannot cross into runtime code",
                    );
                    false
                } else {
                    true
                };
                if !env.shadow && env.phase == Phase::Runtime && valid_output {
                    self.stage_static_expr(&local, *inner, span);
                }
                norm
            }
            Expr::If {
                is_meta,
                condition,
                yes,
                no,
            } => {
                if *is_meta {
                    if env.phase != Phase::Runtime {
                        self.error(
                            Code::E0810,
                            span,
                            "'meta if' is only allowed in runtime functions; compile-time code uses plain 'if'",
                        );
                    }
                    let mut cond_env = env.clone();
                    cond_env.phase = Phase::MetaValue;
                    let cond_span = match condition {
                        Condition::Expr(test) => self.ast(env.file).expr(*test).span,
                        Condition::Binding { value, .. } => self.ast(env.file).expr(*value).span,
                    };
                    if env.phase == Phase::Runtime {
                        cond_env.static_boundary = Some(cond_span);
                    }
                    self.condition(&mut cond_env, condition);
                    let mut yes_env = env.clone();
                    yes_env.refinements = cond_env.refinements.clone();
                    let mut no_env = env.clone();
                    if let Condition::Expr(test) = condition {
                        no_env.refinements = yes_env.refinements.clone();
                        let mut concrete = cond_env.clone();
                        concrete.require_concrete_types = true;
                        match self.evaluate_static(&concrete, *test) {
                            Ok(Value::Bool(taken)) => {
                                self.meta_if_decisions.insert(span, taken);
                                return if taken {
                                    self.assumption(&mut yes_env, condition, true);
                                    let ty = self.expr(&mut yes_env, *yes, expected);
                                    env.refinements = yes_env.refinements;
                                    env.effects_seen.extend(yes_env.effects_seen);
                                    ty
                                } else {
                                    self.assumption(&mut no_env, condition, false);
                                    let ty = no
                                        .map(|no| self.expr(&mut no_env, no, expected))
                                        .unwrap_or(Ty::Unit);
                                    env.refinements = no_env.refinements;
                                    env.effects_seen.extend(no_env.effects_seen);
                                    ty
                                };
                            }
                            Ok(_) => {}
                            Err(super::eval::Signal::Dependent(_)) => {
                                if let Some(cond_span) =
                                    self.stage_condition(&cond_env, *test, true)
                                {
                                    use super::staging::StaticGate::Condition;
                                    yes_env.staging_gates.push(Condition {
                                        span: cond_span,
                                        expected: true,
                                    });
                                    no_env.staging_gates.push(Condition {
                                        span: cond_span,
                                        expected: false,
                                    });
                                }
                            }
                            Err(failure) => {
                                let diag = failure.diagnostic(self.ast(env.file).expr(*test).span);
                                self.diagnostics.push(diag);
                            }
                        }
                    } else if let Condition::Binding { pattern, value, .. } = condition {
                        let mut concrete = cond_env.clone();
                        concrete.require_concrete_types = true;
                        match self.evaluate_static(&concrete, *value) {
                            Ok(val) => {
                                if !matches!(val, Value::Type(_)) {
                                    let val_span = self.ast(env.file).expr(*value).span;
                                    self.static_values.insert(val_span, val.clone());
                                }
                                let mut bindings = Default::default();
                                match self.value_pattern(
                                    &mut yes_env,
                                    *pattern,
                                    &val,
                                    &mut bindings,
                                ) {
                                    Ok(taken) => {
                                        self.meta_if_decisions.insert(span, taken);
                                        return if taken {
                                            let ty = self.expr(&mut yes_env, *yes, expected);
                                            env.refinements = yes_env.refinements;
                                            env.effects_seen.extend(yes_env.effects_seen);
                                            ty
                                        } else {
                                            let ty = no
                                                .map(|no| self.expr(&mut no_env, no, expected))
                                                .unwrap_or(Ty::Unit);
                                            env.refinements = no_env.refinements;
                                            env.effects_seen.extend(no_env.effects_seen);
                                            ty
                                        };
                                    }
                                    Err(super::eval::Signal::Dependent(_)) => {}
                                    Err(failure) => {
                                        let diag = failure
                                            .diagnostic(self.ast(env.file).pattern(*pattern).span);
                                        self.diagnostics.push(diag);
                                    }
                                }
                            }
                            Err(super::eval::Signal::Dependent(_)) => {}
                            Err(failure) => {
                                let diag = failure.diagnostic(self.ast(env.file).expr(*value).span);
                                self.diagnostics.push(diag);
                            }
                        }
                    }
                    self.assumption(&mut yes_env, condition, true);
                    self.assumption(&mut no_env, condition, false);
                    let yes = self.expr(&mut yes_env, *yes, expected);
                    let no = no
                        .map(|no| self.expr(&mut no_env, no, expected))
                        .unwrap_or(Ty::Unit);
                    env.refinements = self.merge_refinements(&yes_env, &no_env, &yes, &no);
                    env.effects_seen.extend(yes_env.effects_seen);
                    env.effects_seen.extend(no_env.effects_seen);
                    self.join(env, span, yes, no)
                } else {
                    let mut yes_env = env.clone();
                    self.condition(&mut yes_env, condition);
                    let mut no_env = env.clone();
                    if let Condition::Expr(_) = condition {
                        no_env.refinements = yes_env.refinements.clone();
                    }
                    self.assumption(&mut yes_env, condition, true);
                    self.assumption(&mut no_env, condition, false);
                    let yes = self.expr(&mut yes_env, *yes, expected);
                    let no = no
                        .map(|no| self.expr(&mut no_env, no, expected))
                        .unwrap_or(Ty::Unit);
                    env.refinements = self.merge_refinements(&yes_env, &no_env, &yes, &no);
                    env.effects_seen.extend(yes_env.effects_seen);
                    env.effects_seen.extend(no_env.effects_seen);
                    self.join(env, span, yes, no)
                }
            }
            Expr::While { condition, body } => {
                let mut body_env = env.clone();
                self.condition(&mut body_env, condition);
                if let Condition::Expr(test) = condition
                    && let Some(span) = self.stage_condition(env, *test, false)
                {
                    body_env
                        .staging_gates
                        .push(super::staging::StaticGate::Condition {
                            span,
                            expected: true,
                        });
                }
                self.assumption(&mut body_env, condition, true);
                let body_result = self.expr(&mut body_env, *body, Some(&Ty::Unit));
                let body_span = self.ast(env.file).expr(*body).span;
                self.require(&body_env, body_span, &body_result, &Ty::Unit);
                env.refinements = self.merge_refinements(env, &body_env, &Ty::Unit, &body_result);
                env.effects_seen.extend(body_env.effects_seen);
                if matches!(condition, Condition::Expr(test) if matches!(&self.ast(env.file).expr(*test).value,
                    Expr::Literal(value) if matches!(literal(value), Ok(Value::Bool(true)))))
                    && !self.has_break(env, *body)
                {
                    Ty::Never
                } else {
                    Ty::Unit
                }
            }
            Expr::For {
                iterable,
                pattern,
                body,
                ..
            } => {
                let ty = self.expr(env, *iterable, None);
                let norm = match self.normalize(&ty) {
                    Ty::Draft(inner) => *inner,
                    other => other,
                };
                let item = if let Some(elem) = norm.as_set(self.hir) {
                    elem.clone()
                } else {
                    match norm {
                        Ty::Range => Ty::Int,
                        Ty::Array(item) => item.ty,
                        Ty::Map(key, value) => Ty::Tuple(vec![Member::plain(*key), *value]),
                        Ty::Unknown => Ty::Unknown,
                        _ => {
                            self.error(
                                Code::E0355,
                                self.ast(env.file).expr(*iterable).span,
                                "value is not iterable",
                            );
                            Ty::Unknown
                        }
                    }
                };
                if !matches!(item, Ty::Unknown | Ty::Never) {
                    let shape = self.pattern_shape(env, *pattern, &item);
                    if self.useful(env, &[shape], super::coverage::Shape::Any, &item) {
                        self.error(
                            Code::E0345,
                            self.ast(env.file).pattern(*pattern).span,
                            "for-loop pattern must be irrefutable",
                        );
                    }
                }
                self.pattern(env, *pattern, &item);
                let body_ty = self.expr(env, *body, Some(&Ty::Unit));
                let body_span = self.ast(env.file).expr(*body).span;
                self.require(env, body_span, &body_ty, &Ty::Unit);
                Ty::Unit
            }
            Expr::Match {
                is_meta,
                value,
                arms,
                ..
            } => {
                let input = if *is_meta {
                    let mut scrut_env = env.clone();
                    scrut_env.phase = Phase::MetaValue;
                    if env.phase == Phase::Runtime {
                        scrut_env.static_boundary = Some(self.ast(env.file).expr(*value).span);
                    }
                    self.expr(&mut scrut_env, *value, None)
                } else {
                    self.expr(env, *value, None)
                };
                self.check_match(env, *is_meta, arms, (*value, &input), expected, span)
            }
            Expr::Closure {
                params,
                obligations,
                body,
            } => {
                if env.phase == Phase::Runtime
                    && !env.shadow
                    && params.iter().any(|param| param.is_meta)
                {
                    self.error(
                        Code::E0810,
                        span,
                        "callables with meta parameters require a direct call",
                    );
                }
                self.closure(env, (span, params), obligations, *body, expected)
            }
            Expr::Accessor(segments) => {
                let label = match expected {
                    Some(Ty::Callable(call)) => call.parameters.first().map(|p| p.ty.clone()),
                    _ => None,
                }
                .unwrap_or(Ty::Unknown);
                let mut base = self.normalize(&label);
                let mut optional = false;
                for (safe, coordinate) in segments {
                    optional |= *safe;
                    base = if optional && let Some(inner) = base.as_option(self.hir).cloned() {
                        let next = self.project(env, coordinate, &inner, span, false);
                        if *safe && next.is_option(self.hir) {
                            next
                        } else {
                            self.make_option(next)
                        }
                    } else {
                        self.project(env, coordinate, &base, span, false)
                    };
                }
                Ty::Callable(Arc::new(Callable {
                    parameters: vec![Parameter {
                        label: None,
                        mode: Mode::Plain,
                        ty: label,
                        optional: false,
                        is_meta: false,
                    }],
                    result: base,
                    ..unknown_callable()
                }))
            }
            Expr::Transfer { kind, value } => {
                if *kind == Transfer::Return {
                    self.check_return(env, *value, span);
                }
                Ty::Never
            }
            Expr::Hole => {
                self.error(Code::E0360, span, "unfinished expression hole");
                Ty::Never
            }
        };
        let ty = self.apply_refinement(env, id, ty);
        self.types.insert(span, ty.clone());
        ty
    }

    fn strip_live_modes(ty: &Ty) -> Ty {
        match ty {
            Ty::Array(member) => {
                Ty::Array(Box::new(Member::plain(Self::strip_live_modes(&member.ty))))
            }
            Ty::Map(key, member) => Ty::Map(
                Box::new(Self::strip_live_modes(key)),
                Box::new(Member::plain(Self::strip_live_modes(&member.ty))),
            ),
            Ty::Record(fields, open) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, member)| {
                        (
                            name.clone(),
                            Member::plain(Self::strip_live_modes(&member.ty)),
                        )
                    })
                    .collect(),
                *open,
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|member| Member::plain(Self::strip_live_modes(&member.ty)))
                    .collect(),
            ),
            other => other.clone(),
        }
    }

    pub(super) fn literal_type(&mut self, syntax: &syntax::Literal, span: Span) -> Ty {
        match literal(syntax) {
            Ok(Value::Int(_)) => Ty::Int,
            Ok(Value::F64(_)) => Ty::F64,
            Ok(Value::Str(_)) => Ty::Str,
            Ok(Value::Bytes(_)) => Ty::Bytes,
            Ok(Value::Bool(_)) => Ty::Bool,
            Err(LiteralError::Overflow) => {
                self.error(
                    Code::E0326,
                    span,
                    "floating literal is outside the finite f64 range",
                );
                Ty::Unknown
            }
            _ => Ty::Unknown,
        }
    }

    fn path_expr(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        expected: Option<&Ty>,
        called: bool,
    ) -> Ty {
        if let Some(id) = self.resolve(path.span) {
            let def = self.hir.definition(id);
            if matches!(def.kind, DefinitionKind::Variant(_)) {
                return self.variant(env, id, expected, path.span);
            }
            let ty = self.def_type(env, id, path.span, called);
            substitute(&ty, &env.generics)
        } else {
            if matches!(self.hir.resolve(path.span), Some(Resolution::Module(_))) {
                self.error(Code::E0319, path.span, "module cannot be used as a value");
            }
            Ty::Unknown
        }
    }

    fn unary(&mut self, env: &mut Env, op: &syntax::Name, value: ExprId) -> Ty {
        let ty = self.expr(env, value, None);
        match op.value.as_str() {
            "!" => {
                if !self.fits(env, &ty, &Ty::Bool) {
                    self.error(Code::E0350, op.span, "logical negation requires bool");
                }
                Ty::Bool
            }
            "-" => {
                self.require_domain(env, &ty, &[Ty::Int, Ty::F64], op.span);
                ty
            }
            "~" => {
                self.require_domain(env, &ty, &[Ty::Int], op.span);
                ty
            }
            "?" => self.propagate(env, ty, op.span),
            "ref" | "^mut" if self.is_value_ty(env, &ty) => {
                self.error(
                    Code::E0402,
                    op.span,
                    "value types do not have live access modes",
                );
                ty
            }
            _ => ty,
        }
    }

    fn binary(
        &mut self,
        env: &mut Env,
        op: &syntax::Name,
        left: ExprId,
        right: ExprId,
        expected: Option<&Ty>,
    ) -> Ty {
        let name = op.value.as_str();
        let assignment = matches!(
            name,
            "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | "&=" | "|=" | "^="
        );
        let ast = self.ast(env.file);
        let previous = env.unrefined;
        let previous_map_store = env.map_store;
        if assignment {
            env.unrefined = Some(ast.expr(left).span);
        }
        if name == "=" {
            env.map_store = Some(ast.expr(left).span);
        }
        let a = self.expr(
            env,
            left,
            if name == "??" {
                None
            } else {
                expected.filter(|_| matches!(name, "+" | "-" | "*" | "/" | "%"))
            },
        );
        env.unrefined = previous;
        env.map_store = previous_map_store;
        let a = self.normalize(&a);
        let fallback;
        let right_expected = if name == "??" {
            if let Some(item) = a.as_option(self.hir) {
                Some(item)
            } else if let Some((ok, error)) = a.as_result(self.hir) {
                fallback = Ty::Callable(Arc::new(Callable {
                    parameters: vec![Parameter {
                        label: None,
                        mode: Mode::Plain,
                        ty: error.clone(),
                        optional: false,
                        is_meta: false,
                    }],
                    result: ok.clone(),
                    open_effects: true,
                    open_state: true,
                    ..unknown_callable()
                }));
                Some(&fallback)
            } else {
                None
            }
        } else if matches!(name, "<<" | ">>") {
            None
        } else {
            Some(&a)
        };
        let gate_depth = env.staging_gates.len();
        let saved_refinements = if matches!(name, "&&" | "||") {
            let saved = env.refinements.clone();
            self.relate(env, left, name == "&&");
            if let Some(span) = self.stage_condition(env, left, false) {
                env.staging_gates
                    .push(super::staging::StaticGate::Condition {
                        span,
                        expected: name == "&&",
                    });
            }
            Some(saved)
        } else {
            None
        };
        let b = self.expr(env, right, right_expected);
        env.staging_gates.truncate(gate_depth);
        if let Some(saved) = saved_refinements {
            env.refinements = saved;
        }
        let b = self.normalize(&b);
        if !assignment
            && matches!(
                name,
                "+" | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "<<"
                    | ">>"
                    | "&"
                    | "|"
                    | "^"
                    | "<"
                    | ">"
                    | "<="
                    | ">="
            )
        {
            for expression in [left, right] {
                let span = ast.expr(expression).span;
                if let Some((code, cause_span)) = self.narrow_errors.get(&span).copied() {
                    self.error_diag(
                        ril_source::diag::Diagnostic::error(
                            code,
                            span,
                            "operation depends on an invalidated narrowing",
                        )
                        .with_label(cause_span, "narrowing invalidated here"),
                    );
                    return Ty::Unknown;
                }
            }
        }
        if matches!(
            name,
            "+" | "-" | "*" | "/" | "%" | "==" | "!=" | "<" | ">" | "<=" | ">="
        ) && matches!(a, Ty::Infer(_))
            && !matches!(b, Ty::Infer(_) | Ty::Unknown)
        {
            self.fits(env, &a, &b);
        }
        let a = self.normalize(&a);
        if name == "??" {
            if let Some(ty) = a.as_option(self.hir) {
                let ty = ty.clone();
                self.require(env, op.span, &b, &ty);
                return ty;
            }
            if let Some((ok, err)) = a.as_result(self.hir) {
                let (ok, err) = (ok.clone(), err.clone());
                if let Ty::Callable(call) = b
                    && call.parameters.len() == 1
                {
                    if let Some(param) = call.parameters.first() {
                        self.require(env, op.span, &err, &param.ty);
                    }
                    self.require(env, op.span, &call.result, &ok);
                    return ok;
                }
                self.error(
                    Code::E0711,
                    op.span,
                    "result fallback requires a one-argument callable",
                );
                return Ty::Unknown;
            }
            if matches!(a, Ty::Unknown | Ty::Never) {
                return Ty::Unknown;
            }
            self.error(
                Code::E0714,
                op.span,
                "fallback requires an option or result",
            );
            return Ty::Unknown;
        }
        if matches!(name, "&&" | "||") {
            let valid = self.fits(env, &a, &Ty::Bool) && self.fits(env, &b, &Ty::Bool);
            if !valid {
                self.error(
                    Code::E0350,
                    op.span,
                    "logical operators require bool operands",
                );
            }
            return Ty::Bool;
        }
        let comparison = matches!(name, "==" | "!=" | "<" | ">" | "<=" | ">=");
        if matches!(name, "==" | "!=") && [left, right].iter().any(|&expr| self.is_none(env, expr))
        {
            for (id, ty) in [(left, &a), (right, &b)] {
                if self.is_none(env, id) {
                    continue;
                }
                let span = ast.expr(id).span;
                if (self.narrowings.contains_key(&span)
                    && !ty.is_option(self.hir)
                    && !matches!(ty, Ty::Unknown))
                    || self.is_known_none(env, id)
                {
                    self.error(
                        Code::E0311,
                        span,
                        "None test contradicts the current narrowing",
                    );
                    return Ty::Bool;
                }
            }
        }
        let base = if assignment {
            name.strip_suffix('=').unwrap_or_default()
        } else {
            name
        };
        let equality = matches!(name, "==" | "!=");
        if !equality || !matches!((&a, &b), (Ty::TypeValue(_), Ty::TypeValue(_))) {
            self.require(env, op.span, &b, &a);
        }
        match base {
            "" => {}
            "+" | "-" | "*" | "/" | "%" => {
                self.require_domain(env, &a, &[Ty::Int, Ty::F64], op.span);
            }
            "&" | "|" | "^" | "<<" | ">>" => self.require_domain(env, &a, &[Ty::Int], op.span),
            "<" | ">" | "<=" | ">=" => {
                self.require_domain(env, &a, &[Ty::Int, Ty::F64, Ty::Str, Ty::Bytes], op.span);
            }
            "==" | "!="
                if !(self.is_none(env, left) || self.is_none(env, right))
                    && !self.equatable(env, &a, &mut HashSet::new()) =>
            {
                self.error(Code::E0327, op.span, "type does not support equality");
            }
            _ => {}
        }
        if matches!(base, "/" | "%" | "<<" | ">>")
            && let Some(integer) = self.literal_integer(env, right)
            && (matches!(base, "/" | "%") && integer.is_zero()
                || matches!(base, "<<" | ">>") && integer.is_negative())
        {
            self.error(
                Code::E0361,
                self.ast(env.file).expr(right).span,
                "invalid literal divisor or shift count",
            );
        }
        if assignment {
            self.writes_place(env, left, ast.expr(left).span);
            Ty::Unit
        } else if comparison {
            Ty::Bool
        } else {
            a
        }
    }

    pub(super) fn is_none(&self, env: &Env, id: ExprId) -> bool {
        matches!(&self.ast(env.file).expr(id).value, Expr::Path(path) if path.segments.last().is_some_and(|part| part.name.value == "None"))
    }

    fn equatable(&mut self, env: &Env, ty: &Ty, seen: &mut HashSet<DefinitionId>) -> bool {
        match ty {
            Ty::Callable(_) | Ty::Draft(_) => false,
            Ty::Array(item) => self.equatable(env, &item.ty, seen),
            Ty::Tuple(items) => items.iter().all(|item| self.equatable(env, &item.ty, seen)),
            Ty::Record(fields, _) => fields
                .values()
                .all(|field| self.equatable(env, &field.ty, seen)),
            Ty::Map(key, value) => {
                self.equatable(env, key, seen) && self.equatable(env, &value.ty, seen)
            }
            Ty::Adt(adt) if seen.insert(adt.definition) => {
                let result = if adt.is_linear {
                    false
                } else if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
                    self.sum_variants(adt)
                        .values()
                        .flatten()
                        .all(|payload| self.equatable(env, payload, seen))
                } else {
                    self.representation(env, adt)
                        .is_none_or(|ty| self.equatable(env, &ty, seen))
                };
                seen.remove(&adt.definition);
                result
            }
            _ => true,
        }
    }

    fn literal_integer(&self, env: &Env, id: ExprId) -> Option<num_bigint::BigInt> {
        let ast = self.ast(env.file);
        match &ast.expr(id).value {
            Expr::Literal(number) => match literal(number).ok()? {
                Value::Int(number) => Some(number),
                _ => None,
            },
            Expr::Unary { op, value } if op.value == "-" => {
                self.literal_integer(env, *value).map(|i| -i)
            }
            _ => None,
        }
    }

    fn require_domain(&mut self, env: &Env, actual: &Ty, valid: &[Ty], span: Span) {
        let mut current = actual.clone();
        while let Ty::Adt(adt) = &current {
            if adt.kind == AdtKind::Opaque
                && adt.defining_scope == env.scope
                && let Some(rep) = self.representation(env, adt)
            {
                current = rep;
                continue;
            }
            break;
        }
        let valid_type = match &current {
            Ty::Param(id) => env
                .domains
                .get(id)
                .is_some_and(|domain| domain.iter().all(|item| valid.contains(item))),
            Ty::Unknown | Ty::Never => true,
            Ty::Infer(_) => false,
            _ => valid.contains(&current),
        };
        if !valid_type {
            self.error(
                Code::E0327,
                span,
                format!("operator does not accept {}", actual.display(self.hir)),
            );
        }
    }

    fn condition(&mut self, env: &mut Env, condition: &Condition) {
        match condition {
            Condition::Binding { pattern, value, .. } => {
                let ty = self.expr(env, *value, None);
                self.pattern(env, *pattern, &ty);
            }
            Condition::Expr(value) => {
                let ty = self.expr(env, *value, Some(&Ty::Bool));
                if !self.fits(env, &ty, &Ty::Bool) {
                    self.error(
                        Code::E0350,
                        self.ast(env.file).expr(*value).span,
                        "condition must be bool",
                    );
                }
            }
        }
    }

    fn has_break(&self, env: &Env, id: ExprId) -> bool {
        let ast = self.ast(env.file);
        match &ast.expr(id).value {
            Expr::Transfer {
                kind: Transfer::Break,
                ..
            } => true,
            Expr::Block { statements, .. } => {
                statements
                    .iter()
                    .any(|&stmt| match &ast.stmt(stmt).value.kind {
                        StmtKind::Expr(id) => self.has_break(env, *id),
                        StmtKind::Binding {
                            value, fallback, ..
                        } => {
                            value.is_some_and(|v| self.has_break(env, v))
                                || fallback.is_some_and(|f| self.has_break(env, f))
                        }
                        _ => false,
                    })
            }
            Expr::If { yes, no, .. } => {
                self.has_break(env, *yes) || no.is_some_and(|no| self.has_break(env, no))
            }
            Expr::Match { arms, .. } => arms.iter().any(|arm| self.has_break(env, arm.body)),
            Expr::Binary { left, right, .. } => {
                self.has_break(env, *left) || self.has_break(env, *right)
            }
            Expr::Unary { value, .. } => self.has_break(env, *value),
            _ => false,
        }
    }
}
