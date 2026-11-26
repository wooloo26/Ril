use std::collections::{BTreeMap, VecDeque};

use ril_hir::DefinitionId;
use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_syntax::syntax::{Argument, Expr, ExprId, MatchArm, PatternId};

use super::{
    GenericValue, Ty, TypedProgram, Value,
    check::{Checker, Env, Phase},
    eval::Signal,
};

#[derive(Clone)]
pub(super) enum StaticInput {
    Ready(Value),
    Supplied(ExprId),
    Default(ExprId),
}

pub(super) struct Application<'a> {
    pub span: Span,
    pub supplied: &'a [bool],
    pub inputs: &'a BTreeMap<usize, StaticInput>,
}

#[derive(Clone, Copy)]
pub(super) enum StaticGate {
    Condition { span: Span, expected: bool },
    Match { span: Span, expected: usize },
}

pub(super) struct StaticCondition {
    caller: Env,
    expression: ExprId,
    is_meta: bool,
}

pub(super) struct StaticMatch {
    caller: Env,
    expression: ExprId,
    arms: Vec<(PatternId, Option<ExprId>)>,
}

pub(super) struct StaticBinding {
    pub name: Option<DefinitionId>,
    pub guards: Vec<ExprId>,
    pub input: StaticInput,
}

pub(super) struct MetaCall {
    pub target: Span,
    pub caller: Env,
    pub callee: Env,
    pub bindings: Vec<StaticBinding>,
    pub needs_specialization: bool,
}

pub(super) struct StaticFold {
    pub caller: Env,
    pub target: DefinitionId,
    pub args: Vec<Argument>,
}

#[derive(Clone, Default, PartialEq, Eq)]
struct StaticContext {
    values: BTreeMap<DefinitionId, Value>,
    types: BTreeMap<DefinitionId, Ty>,
}

#[derive(Clone, Copy)]
enum Site<'a> {
    Bind(&'a MetaCall),
    Fold(&'a StaticFold),
    MetaCondition(&'a StaticCondition),
    MetaMatch(&'a StaticMatch),
}

impl Site<'_> {
    fn caller(&self) -> &Env {
        match self {
            Self::Bind(plan) => &plan.caller,
            Self::Fold(plan) => &plan.caller,
            Self::MetaCondition(plan) => &plan.caller,
            Self::MetaMatch(plan) => &plan.caller,
        }
    }
}

impl TypedProgram {
    /// Materialize a call's erased parameters in the caller's native specialization.
    pub fn static_arguments(
        &self,
        span: Span,
        statics: &BTreeMap<DefinitionId, Value>,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Result<BTreeMap<DefinitionId, Value>, Diagnostic> {
        let Some(plan) = self.meta_calls.get(&span) else {
            return Ok(BTreeMap::new());
        };
        if plan.needs_specialization {
            return self
                .static_checker()
                .materialize_meta_call(span, plan, statics, types);
        }
        Ok(plan
            .bindings
            .iter()
            .filter_map(|binding| match (binding.name, &binding.input) {
                (Some(id), StaticInput::Ready(value)) => Some((id, value.clone())),
                _ => None,
            })
            .collect())
    }

    pub fn static_value(
        &self,
        span: Span,
        statics: &BTreeMap<DefinitionId, Value>,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Result<Option<Value>, Diagnostic> {
        if let Some(value) = self.static_values.get(&span) {
            return Ok(Some(value.clone()));
        }
        if let Some(plan) = self.static_folds.get(&span) {
            let caller = realize(&plan.caller, statics, types);
            let mut checker = self.static_checker();
            let result = checker.evaluate_static_call(&caller, plan.target, &plan.args, span);
            if let Some(diagnostic) = checker.diagnostics.into_iter().next() {
                return Err(diagnostic);
            }
            return result.map(Some).map_err(|failure| failure.diagnostic(span));
        }
        Ok(self.static_condition(span, statics, types).map(Value::Bool))
    }

    pub fn static_condition(
        &self,
        span: Span,
        statics: &BTreeMap<DefinitionId, Value>,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Option<bool> {
        let condition = self.static_conditions.get(&span)?;
        let caller = realize(&condition.caller, statics, types);
        match self
            .static_checker()
            .evaluate_static(&caller, condition.expression)
        {
            Ok(Value::Bool(value)) => Some(value),
            _ => None,
        }
    }

    /// Select an arm when the subject and the guards needed for selection are static,
    /// returning the arm index alongside any type-pattern bindings (`<let X>`).
    pub fn static_selected_arm_with_bindings(
        &self,
        span: Span,
        statics: &BTreeMap<DefinitionId, Value>,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Option<(usize, BTreeMap<DefinitionId, Ty>)> {
        let plan = self.static_matches.get(&span)?;
        let env = realize(&plan.caller, statics, types);
        let mut checker = self.static_checker();
        let value = checker.evaluate_static(&env, plan.expression).ok()?;
        for (index, &(pattern, guard)) in plan.arms.iter().enumerate() {
            let mut local = env.clone();
            let mut bindings = Default::default();
            if !checker
                .value_pattern(&mut local, pattern, &value, &mut bindings)
                .ok()?
            {
                continue;
            }
            if let Some(guard) = guard {
                match checker
                    .evaluate_with_bindings(&local, guard, &mut bindings)
                    .ok()?
                {
                    Value::Bool(true) => {}
                    Value::Bool(false) => continue,
                    _ => return None,
                }
            }
            let bound_types = local
                .generics
                .into_iter()
                .filter_map(|(id, gv)| match gv {
                    GenericValue::Type(ty) => Some((id, ty)),
                    _ => None,
                })
                .collect();
            return Some((index, bound_types));
        }
        None
    }

    /// Select an arm when the subject and the guards needed for selection are static.
    pub fn static_selected_arm(
        &self,
        span: Span,
        statics: &BTreeMap<DefinitionId, Value>,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Option<usize> {
        self.static_selected_arm_with_bindings(span, statics, types)
            .map(|(index, _)| index)
    }

    fn gate_excludes(&self, gate: StaticGate, context: &StaticContext) -> bool {
        match gate {
            StaticGate::Condition { span, expected } => self
                .static_condition(span, &context.values, &context.types)
                .is_some_and(|actual| actual != expected),
            StaticGate::Match { span, expected } => self
                .static_selected_arm(span, &context.values, &context.types)
                .is_some_and(|actual| actual != expected),
        }
    }

    pub(super) fn validate_specializations(&self) -> Result<(), Vec<Diagnostic>> {
        let mut sites = BTreeMap::<_, Vec<_>>::new();
        let calls = self
            .meta_calls
            .iter()
            .map(|(&span, plan)| (span, Site::Bind(plan)));
        let folds = self
            .static_folds
            .iter()
            .map(|(&span, plan)| (span, Site::Fold(plan)));
        let conds = self
            .static_conditions
            .iter()
            .filter(|(_, plan)| plan.is_meta)
            .map(|(&span, plan)| (span, Site::MetaCondition(plan)));
        let matches = self
            .static_matches
            .iter()
            .map(|(&span, plan)| (span, Site::MetaMatch(plan)));
        for (span, site) in calls.chain(folds).chain(conds).chain(matches) {
            sites
                .entry(site.caller().staging_owner)
                .or_default()
                .push((span, site));
        }
        for group in sites.values_mut() {
            group.sort_unstable_by_key(|(span, _)| *span);
        }
        let mut visited = BTreeMap::<_, Vec<StaticContext>>::new();
        let mut pending = VecDeque::from([(None, StaticContext::default(), 0)]);
        let mut diagnostics = Vec::new();
        while let Some((owner, context, depth)) = pending.pop_front() {
            for &(span, site) in sites.get(&owner).into_iter().flatten() {
                if site
                    .caller()
                    .staging_gates
                    .iter()
                    .any(|&gate| self.gate_excludes(gate, &context))
                {
                    continue;
                }
                let result = match site {
                    Site::Fold(_) => self
                        .static_value(span, &context.values, &context.types)
                        .map(|_| ()),
                    Site::MetaCondition(plan) => {
                        let caller = realize(&plan.caller, &context.values, &context.types);
                        match self
                            .static_checker()
                            .evaluate_static(&caller, plan.expression)
                        {
                            Ok(_) | Err(Signal::Dependent(_)) => Ok(()),
                            Err(failure) => Err(failure.diagnostic(span)),
                        }
                    }
                    Site::MetaMatch(plan) => {
                        let caller = realize(&plan.caller, &context.values, &context.types);
                        let mut checker = self.static_checker();
                        match checker.evaluate_static(&caller, plan.expression) {
                            Ok(val) => {
                                let mut outcome = Ok(());
                                for &(pattern, guard) in &plan.arms {
                                    let mut local = caller.clone();
                                    let mut bindings = Default::default();
                                    match checker.value_pattern(
                                        &mut local,
                                        pattern,
                                        &val,
                                        &mut bindings,
                                    ) {
                                        Ok(true) => {}
                                        Ok(false) => continue,
                                        Err(Signal::Dependent(_)) => break,
                                        Err(failure) => {
                                            outcome = Err(failure.diagnostic(span));
                                            break;
                                        }
                                    }
                                    if let Some(guard) = guard {
                                        match checker.evaluate_with_bindings(
                                            &local,
                                            guard,
                                            &mut bindings,
                                        ) {
                                            Ok(Value::Bool(true)) => break,
                                            Ok(Value::Bool(false)) => continue,
                                            Ok(_) | Err(Signal::Dependent(_)) => break,
                                            Err(failure) => {
                                                outcome = Err(failure.diagnostic(span));
                                                break;
                                            }
                                        }
                                    }
                                    break;
                                }
                                outcome
                            }
                            Err(Signal::Dependent(_)) => Ok(()),
                            Err(failure) => Err(failure.diagnostic(span)),
                        }
                    }
                    Site::Bind(plan) => self
                        .static_arguments(span, &context.values, &context.types)
                        .and_then(|values| {
                            let next_owner = Some(plan.target);
                            if sites.contains_key(&next_owner) {
                                let mut next = context.clone();
                                next.values.extend(values);
                                if let Some(types) = self.type_arguments.get(&span) {
                                    next.types.extend(
                                        types
                                            .iter()
                                            .map(|(&id, ty)| (id, ty.specialize(&context.types))),
                                    );
                                }
                                let instances = visited.entry(next_owner).or_default();
                                if !instances.contains(&next) {
                                    if depth >= self.static_budget {
                                        return Err(Diagnostic::error(
                                            Code::E0811,
                                            span,
                                            "static specialization exceeded the evaluation budget",
                                        ));
                                    }
                                    instances.push(next.clone());
                                    pending.push_back((next_owner, next, depth + 1));
                                }
                            }
                            Ok(())
                        }),
                };
                if let Err(diagnostic) = result
                    && !diagnostics.iter().any(|existing: &Diagnostic| {
                        existing.code == diagnostic.code && existing.primary == diagnostic.primary
                    })
                {
                    diagnostics.push(diagnostic);
                }
            }
        }
        if diagnostics.is_empty() {
            Ok(())
        } else {
            Err(diagnostics)
        }
    }

    fn static_checker(&self) -> Checker<'_> {
        Checker::for_static_evaluation(self)
    }
}

impl Checker<'_> {
    pub(super) fn stage_condition(
        &mut self,
        caller: &Env,
        expression: ExprId,
        is_meta: bool,
    ) -> Option<Span> {
        if caller.shadow || caller.phase != Phase::Runtime {
            return None;
        }
        let span = self.ast(caller.file).expr(expression).span;
        self.static_conditions.insert(
            span,
            StaticCondition {
                caller: caller.clone(),
                expression,
                is_meta,
            },
        );
        Some(span)
    }

    pub(super) fn stage_match(
        &mut self,
        env: &Env,
        span: Span,
        expression: ExprId,
        arms: &[MatchArm],
    ) -> bool {
        if env.shadow || env.phase != Phase::Runtime {
            return false;
        }
        self.static_matches.insert(
            span,
            StaticMatch {
                caller: env.clone(),
                expression,
                arms: arms.iter().map(|arm| (arm.pattern, arm.guard)).collect(),
            },
        );
        true
    }

    pub(super) fn materialize_meta_call(
        &mut self,
        span: Span,
        plan: &MetaCall,
        statics: &BTreeMap<DefinitionId, Value>,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Result<BTreeMap<DefinitionId, Value>, Diagnostic> {
        let caller = realize(&plan.caller, statics, types);
        let mut callee = realize(&plan.callee, statics, types);
        let mut supplied: Vec<_> = plan
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(index, binding)| {
                if let StaticInput::Supplied(expression) = binding.input {
                    Some((index, expression))
                } else {
                    None
                }
            })
            .collect();
        supplied
            .sort_unstable_by_key(|&(_, expression)| self.ast(caller.file).expr(expression).span);
        let mut arguments = BTreeMap::new();
        for (index, expression) in supplied {
            let value = self
                .evaluate_static(&caller, expression)
                .map_err(|failure| failure.diagnostic(span))?;
            arguments.insert(index, value);
        }
        let mut values = BTreeMap::new();
        let mut guards = Vec::new();
        for (index, binding) in plan.bindings.iter().enumerate() {
            let input = match &binding.input {
                StaticInput::Ready(value) => value.clone(),
                StaticInput::Supplied(_) => arguments
                    .remove(&index)
                    .unwrap_or_else(|| ril_source::ice!("evaluated static call input is missing")),
                StaticInput::Default(expr) => self
                    .evaluate_static(&callee, *expr)
                    .map_err(|failure| failure.diagnostic(span))?,
            };
            if let Some(id) = binding.name {
                callee
                    .generics
                    .insert(id, GenericValue::Data(input.clone()));
                values.insert(id, input.clone());
            }
            if !binding.guards.is_empty() {
                guards.push((&binding.guards, input));
            }
        }
        for (checks, input) in guards {
            self.check_meta_input(&mut callee, checks, &input, span);
        }
        if let Some(diagnostic) = self.diagnostics.first() {
            return Err(diagnostic.clone());
        }
        Ok(values)
    }

    pub(super) fn check_meta_input(
        &mut self,
        env: &mut Env,
        guards: &[ExprId],
        input: &Value,
        span: Span,
    ) {
        let input = GenericValue::Data(input.clone());
        for &guard in guards {
            if let Expr::Path(path) = &self.ast(env.file).expr(guard).value {
                self.apply_static_check(env, path, &input, span);
            }
        }
    }
}

/// Apply lexical caller arguments to the recorded type environment. The callee's
/// generic substitutions can refer to type parameters of the enclosing specialization.
fn realize(
    template: &Env,
    statics: &BTreeMap<DefinitionId, Value>,
    types: &BTreeMap<DefinitionId, Ty>,
) -> Env {
    let mut env = template.clone();
    env.require_concrete_types = true;
    env.generics = types
        .iter()
        .map(|(&id, ty)| (id, GenericValue::Type(ty.clone())))
        .chain(
            statics
                .iter()
                .map(|(&id, value)| (id, GenericValue::Data(value.clone()))),
        )
        .chain(template.generics.iter().map(|(&id, argument)| {
            let argument = match argument {
                GenericValue::Type(ty) => GenericValue::Type(ty.specialize(types)),
                value => value.clone(),
            };
            (id, argument)
        }))
        .collect();
    env
}

impl Signal {
    pub(super) fn diagnostic(self, root: Span) -> Diagnostic {
        match self {
            Signal::Error(code, span, message) => Diagnostic::error(code, span, message),
            Signal::Dependent(span) => Diagnostic::error(
                Code::E0814,
                span,
                "compile-time parameter has no concrete argument in this specialization",
            ),
            _ => Diagnostic::error(
                Code::E0814,
                root,
                "control transfer has no static evaluation target",
            ),
        }
    }
}
