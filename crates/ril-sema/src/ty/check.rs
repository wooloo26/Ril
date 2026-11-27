mod decls;

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use ril_hir::{DefinitionId, DefinitionKind, Program, Resolution, ScopeId};
use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_syntax::syntax::{self, Ast, Mode, Name, Storage};

use super::narrowing::Refinements;
use super::{
    AdtKind, Callable, GenericValue, Member, MemberMode, Parameter, Ty, TypedProgram, Value,
};

pub(super) const DEFAULT_BUDGET: u64 = 10_000;

pub(super) fn check(hir: Program, budget: Option<u64>) -> Result<TypedProgram, Vec<Diagnostic>> {
    let (program, diagnostics) = check_impl(hir, budget, false);
    if diagnostics.is_empty() {
        Ok(program)
    } else {
        Err(diagnostics)
    }
}

pub(super) fn check_partial(hir: Program, budget: Option<u64>) -> (TypedProgram, Vec<Diagnostic>) {
    check_impl(hir, budget, true)
}

fn check_impl(hir: Program, budget: Option<u64>, partial: bool) -> (TypedProgram, Vec<Diagnostic>) {
    let mut ck = Checker::new(&hir, budget);
    for (id, def) in hir.definitions() {
        if def.kind == DefinitionKind::Function && def.stmt.is_some() {
            ck.declare_function(id);
        }
    }
    for file in hir.files() {
        let scope = hir.module_scope(file.id);
        let mut env = Env::new(file.id, scope);
        for &item in &file.ast.items {
            ck.statement(&mut env, item, false);
        }
    }
    for (env, ty, span) in std::mem::take(&mut ck.pending_clone_checks) {
        ck.check_clone(&env, &ty, span, false);
    }
    let mut diagnostics = std::mem::take(&mut ck.diagnostics);
    if !partial && !diagnostics.is_empty() {
        return (
            TypedProgram {
                hir,
                types: HashMap::new(),
                type_arguments: HashMap::new(),
                bindings: HashMap::new(),
                callables: BTreeMap::new(),
                imported_functions: BTreeMap::new(),
                imported_behaviors: BTreeMap::new(),
                imported_must_consume: HashSet::new(),
                narrow_drops: Vec::new(),
                static_values: HashMap::new(),
                meta_calls: HashMap::new(),
                static_folds: HashMap::new(),
                static_conditions: HashMap::new(),
                static_matches: HashMap::new(),
                meta_if_decisions: HashMap::new(),
                meta_match_decisions: HashMap::new(),
                static_generic_arguments: HashMap::new(),
                static_budget: 0,
                meta_parameters: HashSet::new(),
                inspection_scopes: HashMap::new(),
                narrowings: HashMap::new(),
                navigation_values: HashMap::new(),
                propagation_inputs: HashMap::new(),
                nominal_layouts: HashMap::new(),
                record_adts: HashSet::new(),
                effect_instances: BTreeMap::new(),
                operation_effects: HashMap::new(),
                operation_instances: HashMap::new(),
                effect_applications: HashMap::new(),
                subset_tags: HashMap::new(),
                tuple_payloads: HashMap::new(),
                receptions: HashMap::new(),
                boxed_var_captures: std::collections::BTreeSet::new(),
            },
            diagnostics,
        );
    }
    let types = std::mem::take(&mut ck.types)
        .into_iter()
        .map(|(span, ty)| (span, ck.normalize(&ty)))
        .collect();
    let bindings = std::mem::take(&mut ck.bindings)
        .into_iter()
        .map(|(id, ty)| (id, ck.normalize(&ty)))
        .collect();
    let navigation_values = std::mem::take(&mut ck.navigation_values)
        .into_iter()
        .map(|(span, ty)| (span, ck.normalize(&ty)))
        .collect();
    let propagation_inputs = std::mem::take(&mut ck.propagation_inputs)
        .into_iter()
        .map(|(span, ty)| (span, ck.normalize(&ty)))
        .collect();
    let nominal_layouts = std::mem::take(&mut ck.nominal_layouts)
        .into_iter()
        .map(|(id, ty)| (id, ck.normalize(&ty)))
        .collect();
    let static_generic_arguments = std::mem::take(&mut ck.generic_arguments)
        .into_iter()
        .map(|(span, arguments)| {
            let arguments: HashMap<_, _> = arguments
                .into_iter()
                .map(|(id, arg)| {
                    (
                        id,
                        match arg {
                            GenericValue::Type(ty) => GenericValue::Type(ck.normalize(&ty)),
                            value => value,
                        },
                    )
                })
                .collect();
            (span, arguments)
        })
        .collect::<HashMap<_, _>>();
    let type_arguments = static_generic_arguments
        .iter()
        .map(|(&span, args)| {
            let args = args
                .iter()
                .filter_map(|(&id, value)| match value {
                    GenericValue::Type(ty) => Some((id, ty.clone())),
                    _ => None,
                })
                .collect();
            (span, args)
        })
        .collect();
    let Checker {
        callables,
        static_values,
        meta_calls,
        static_folds,
        static_conditions,
        static_matches,
        meta_if_decisions,
        meta_match_decisions,
        budget: static_budget,
        meta_parameters,
        inspection_scopes,
        narrowings,
        effect_instances,
        operation_effects,
        operation_instances,
        effect_applications,
        subset_tags,
        tuple_payloads,
        receptions,
        record_adts,
        narrow_drops,
        ..
    } = ck;
    let mut program = TypedProgram {
        hir,
        types,
        type_arguments,
        bindings,
        callables,
        imported_functions: BTreeMap::new(),
        imported_behaviors: BTreeMap::new(),
        imported_must_consume: HashSet::new(),
        narrow_drops,
        static_values,
        meta_calls,
        static_folds,
        static_conditions,
        static_matches,
        meta_if_decisions,
        meta_match_decisions,
        static_generic_arguments,
        static_budget,
        meta_parameters,
        inspection_scopes,
        narrowings,
        navigation_values,
        propagation_inputs,
        nominal_layouts,
        record_adts,
        effect_instances,
        operation_effects,
        operation_instances,
        effect_applications,
        subset_tags,
        tuple_payloads,
        receptions,
        boxed_var_captures: std::collections::BTreeSet::new(),
    };
    if let Err(spec_diags) = program.validate_specializations() {
        diagnostics.extend(spec_diags);
    }
    if !partial && !diagnostics.is_empty() {
        return (program, diagnostics);
    }
    program.boxed_var_captures = super::captures::collect_boxed_var_captures(&program.hir);
    (program, diagnostics)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Phase {
    Runtime,
    MetaValue,
    TypeEval,
}

#[derive(Clone)]
pub(super) struct Env {
    pub(super) file: FileId,
    pub(super) scope: ScopeId,
    pub(super) caller_scope: Option<ScopeId>,
    pub(super) error_span: Option<Span>,
    pub(super) phase: Phase,
    pub(super) generics: HashMap<DefinitionId, GenericValue>,
    pub(super) domains: HashMap<DefinitionId, Vec<Ty>>,
    pub(super) meta_keys: HashMap<DefinitionId, Ty>,
    pub(super) expected_return: Option<Ty>,
    pub(super) inferred_return: Option<usize>,
    pub(super) return_scope: Option<Span>,
    pub(super) shadow: bool,
    pub(super) effects_seen: HashSet<String>,
    pub(super) refinements: Refinements,
    pub(super) unrefined: Option<Span>,
    pub(super) nominal_fields: Option<Span>,
    pub(super) map_store: Option<Span>,
    pub(super) checking_type_template: bool,
    pub(super) allow_open_record: bool,
    pub(super) mode_scope: Option<bool>,
    pub(super) staging_owner: Option<Span>,
    pub(super) staging_gates: Vec<super::staging::StaticGate>,
    pub(super) require_concrete_types: bool,
    pub(super) static_boundary: Option<Span>,
}

impl Env {
    pub(super) fn new(file: FileId, scope: ScopeId) -> Self {
        Self {
            file,
            scope,
            caller_scope: None,
            error_span: None,
            phase: Phase::Runtime,
            generics: HashMap::new(),
            domains: HashMap::new(),
            meta_keys: HashMap::new(),
            expected_return: None,
            inferred_return: None,
            return_scope: None,
            shadow: false,
            effects_seen: HashSet::new(),
            refinements: Refinements::default(),
            unrefined: None,
            nominal_fields: None,
            map_store: None,
            checking_type_template: false,
            allow_open_record: false,
            mode_scope: Some(false),
            staging_owner: None,
            staging_gates: Vec::new(),
            require_concrete_types: false,
            static_boundary: None,
        }
    }

    pub(super) fn effective_scope(&self) -> ScopeId {
        self.caller_scope.unwrap_or(self.scope)
    }
}

pub(super) struct Checker<'a> {
    pub(super) hir: &'a Program,
    pub(super) diagnostics: Vec<Diagnostic>,
    pub(super) types: HashMap<Span, Ty>,
    pub(super) generic_arguments: HashMap<Span, HashMap<DefinitionId, GenericValue>>,
    pub(super) bindings: HashMap<DefinitionId, Ty>,
    pub(super) callables: BTreeMap<DefinitionId, Arc<Callable>>,
    pub(super) static_values: HashMap<Span, Value>,
    pub(super) meta_calls: HashMap<Span, super::staging::MetaCall>,
    pub(super) static_folds: HashMap<Span, super::staging::StaticFold>,
    pub(super) static_conditions: HashMap<Span, super::staging::StaticCondition>,
    pub(super) static_matches: HashMap<Span, super::staging::StaticMatch>,
    pub(super) meta_if_decisions: HashMap<Span, bool>,
    pub(super) meta_match_decisions: HashMap<Span, usize>,
    pub(super) meta_parameters: HashSet<DefinitionId>,
    pub(super) inspection_scopes: HashMap<Span, ScopeId>,
    next_infer: u32,
    substitutions: HashMap<u32, Ty>,
    pub(super) resolving: HashSet<DefinitionId>,
    checked: HashSet<DefinitionId>,
    schemes: HashSet<DefinitionId>,
    pub(super) live: HashSet<DefinitionId>,
    pub(super) implicit_exits: Vec<ImplicitExits>,
    pub(super) narrowings: HashMap<Span, usize>,
    pub(super) navigation_values: HashMap<Span, Ty>,
    pub(super) propagation_inputs: HashMap<Span, Ty>,
    pub(super) nominal_layouts: HashMap<DefinitionId, Ty>,
    pub(super) record_adts: HashSet<DefinitionId>,
    pub(super) effect_instances: BTreeMap<String, super::effects::Instance>,
    pub(super) operation_effects: HashMap<Span, String>,
    pub(super) operation_instances: HashMap<Span, super::effects::Instance>,
    pub(super) effect_applications: HashMap<Span, Vec<String>>,
    pub(super) subset_tags: HashMap<Span, Vec<String>>,
    pub(super) tuple_payloads: HashMap<Span, usize>,
    pub(super) receptions: HashMap<Span, Vec<super::reception::Adjustment>>,
    pub(super) narrow_errors: HashMap<Span, (Code, Span)>,
    pub(super) narrow_drops: Vec<super::NarrowDrop>,
    pub(super) pending_clone_checks: Vec<(Env, Ty, Span)>,
    constants: HashSet<DefinitionId>,
    active_metadata: HashSet<Span>,
    pub(super) stack: Vec<DefinitionId>,
    pub(super) budget: u64,
}

#[derive(Default)]
pub(super) struct ImplicitExits {
    pub(super) returns: Vec<(Span, Ty)>,
    pub(super) errors: Vec<Ty>,
    pub(super) none: bool,
}

impl<'a> Checker<'a> {
    pub(super) fn new(hir: &'a Program, budget: Option<u64>) -> Self {
        Self {
            hir,
            diagnostics: Vec::new(),
            types: HashMap::new(),
            generic_arguments: HashMap::new(),
            bindings: HashMap::new(),
            callables: BTreeMap::new(),
            static_values: HashMap::new(),
            meta_calls: HashMap::new(),
            static_folds: HashMap::new(),
            static_conditions: HashMap::new(),
            static_matches: HashMap::new(),
            meta_if_decisions: HashMap::new(),
            meta_match_decisions: HashMap::new(),
            meta_parameters: HashSet::new(),
            next_infer: 0,
            substitutions: HashMap::new(),
            resolving: HashSet::new(),
            checked: HashSet::new(),
            schemes: HashSet::new(),
            live: HashSet::new(),
            implicit_exits: Vec::new(),
            inspection_scopes: HashMap::new(),
            narrowings: HashMap::new(),
            propagation_inputs: HashMap::new(),
            nominal_layouts: HashMap::new(),
            record_adts: HashSet::new(),
            effect_instances: BTreeMap::new(),
            operation_effects: HashMap::new(),
            operation_instances: HashMap::new(),
            effect_applications: HashMap::new(),
            navigation_values: HashMap::new(),
            subset_tags: HashMap::new(),
            tuple_payloads: HashMap::new(),
            receptions: HashMap::new(),
            narrow_errors: HashMap::new(),
            narrow_drops: Vec::new(),
            pending_clone_checks: Vec::new(),
            constants: HashSet::new(),
            active_metadata: HashSet::new(),
            stack: Vec::new(),
            budget: budget.unwrap_or(DEFAULT_BUDGET),
        }
    }

    pub(super) fn for_static_evaluation(program: &'a TypedProgram) -> Self {
        let mut checker = Self::new(&program.hir, Some(program.static_budget));
        checker.types.clone_from(&program.types);
        checker.bindings.clone_from(&program.bindings);
        checker.callables.clone_from(&program.callables);
        checker.checked.extend(program.callables.keys().copied());
        checker.static_values.clone_from(&program.static_values);
        checker.meta_parameters.clone_from(&program.meta_parameters);
        checker
            .generic_arguments
            .clone_from(&program.static_generic_arguments);
        checker.narrowings.clone_from(&program.narrowings);
        checker
            .navigation_values
            .clone_from(&program.navigation_values);
        checker.tuple_payloads.clone_from(&program.tuple_payloads);
        checker
    }

    pub(super) fn ast(&self, file: FileId) -> &'a Ast {
        &self.hir.file(file).ast
    }

    pub(super) fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        self.error_diag(Diagnostic::error(code, span, message));
    }

    pub(super) fn error_diag(&mut self, diagnostic: Diagnostic) {
        if !self.diagnostics.iter().any(|existing| {
            existing.code == diagnostic.code && existing.primary == diagnostic.primary
        }) {
            self.diagnostics.push(diagnostic);
        }
    }

    pub(super) fn resolve(&self, span: Span) -> Option<DefinitionId> {
        self.hir.resolve(span).and_then(Resolution::definition)
    }

    pub(super) fn exposes_type(
        &self,
        ty: &Ty,
        mut confined: impl FnMut(DefinitionId) -> bool,
    ) -> bool {
        let mut escaped = false;
        transform(&self.normalize(ty), &mut |part| {
            if let Ty::Adt(adt) = part {
                escaped |= confined(adt.definition);
            }
            None
        });
        escaped
    }

    pub(super) fn closure_exits(&mut self, index: usize) -> &mut ImplicitExits {
        self.implicit_exits
            .get_mut(index)
            .unwrap_or_else(|| ril_source::ice!("missing inference state for the current closure"))
    }

    pub(super) fn fresh(&mut self) -> Ty {
        let id = self.next_infer;
        self.next_infer += 1;
        Ty::Infer(id)
    }

    pub(super) fn normalize(&self, ty: &Ty) -> Ty {
        if let Ty::Infer(var) = ty
            && let Some(replace) = self.substitutions.get(var)
        {
            return self.normalize(replace);
        }
        transform(ty, &mut |ty| {
            if matches!(ty, Ty::Infer(var) if self.substitutions.contains_key(var)) {
                Some(self.normalize(ty))
            } else {
                None
            }
        })
    }

    pub(super) fn member_mode(&self, env: &Env, storage: &Storage) -> MemberMode {
        if let Some(path) = &storage.mode_path
            && let Some(id) = self.resolve(path.span)
            && let Some(GenericValue::Mode(mode) | GenericValue::Data(Value::Mode(mode))) =
                env.generics.get(&id)
        {
            return *mode;
        }
        MemberMode {
            variable: storage.variable,
            mode: storage.mode,
        }
    }

    fn bind_variable(&mut self, id: u32, ty: &Ty) -> bool {
        let mut occurs = false;
        transform(ty, &mut |found| {
            occurs |= *found == Ty::Infer(id);
            None
        });
        if !occurs {
            self.substitutions.insert(id, ty.clone());
        }
        !occurs
    }

    pub(super) fn fits(&mut self, env: &Env, actual: &Ty, expected: &Ty) -> bool {
        let actual = self.normalize(actual);
        let expected = self.normalize(expected);
        if actual == expected
            || matches!(actual, Ty::Unknown | Ty::Never)
            || matches!(expected, Ty::Unknown)
        {
            return true;
        }
        match (&actual, &expected) {
            (Ty::Infer(var), _) => self.bind_variable(*var, &expected),
            (_, Ty::Infer(var)) => self.bind_variable(*var, &actual),
            (Ty::Param(id), _) => env
                .generics
                .get(id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty),
                    _ => None,
                })
                .is_some_and(|found| found != &actual && self.fits(env, found, &expected)),
            (_, Ty::Param(id)) => env
                .generics
                .get(id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty),
                    _ => None,
                })
                .is_some_and(|found| found != &expected && self.fits(env, &actual, found)),
            (Ty::Draft(a), Ty::Draft(b)) => self.equiv(env, a, b),
            (Ty::TypeValue(Some(a)), Ty::TypeValue(Some(b))) => {
                self.equiv(env, a, b) && self.normalize(a) == self.normalize(b)
            }
            (Ty::TypeValue(Some(_)), Ty::TypeValue(None)) => true,
            (Ty::Array(a), Ty::Array(b)) => self.member_fits(env, a, b, true),
            (Ty::Map(ak, a), Ty::Map(bk, b)) => {
                self.equiv(env, ak, bk) && self.member_fits(env, a, b, true)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|(a, b)| self.member_fits(env, a, b, false))
            }
            (Ty::Record(a, a_open), Ty::Record(b, b_open)) => {
                (*b_open || !a_open && a.len() == b.len())
                    && b.iter().all(|(name, b)| {
                        a.get(name)
                            .is_some_and(|a| self.member_fits(env, a, b, false))
                    })
            }
            (Ty::Callable(a), Ty::Callable(b)) => self.callable_fits(env, a, b),
            (Ty::Adt(a), Ty::Adt(b)) if a.definition == b.definition => {
                let covariant = matches!(
                    self.hir.std_type(a.definition),
                    Some(ril_hir::StdType::Option | ril_hir::StdType::Result)
                );
                a.arguments.len() == b.arguments.len()
                    && a.arguments
                        .iter()
                        .zip(&b.arguments)
                        .all(|(actual, expected)| match (actual, expected) {
                            (GenericValue::Type(actual), GenericValue::Type(expected)) => {
                                if covariant {
                                    self.fits(env, actual, expected)
                                } else {
                                    self.equiv(env, actual, expected)
                                }
                            }
                            _ => actual == expected,
                        })
            }
            (Ty::Adt(adt), _) if adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope => {
                self.representation(env, adt)
                    .is_some_and(|ty| self.fits(env, &ty, &expected))
            }
            (_, Ty::Adt(adt)) if adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope => {
                self.representation(env, adt)
                    .is_some_and(|ty| self.fits(env, &actual, &ty))
            }
            _ => false,
        }
    }

    pub(super) fn equiv(&mut self, env: &Env, a: &Ty, b: &Ty) -> bool {
        let a = self.normalize(a);
        let b = self.normalize(b);
        if a == b || matches!(a, Ty::Unknown) || matches!(b, Ty::Unknown) {
            return true;
        }
        match (&a, &b) {
            (Ty::Infer(var), _) => self.bind_variable(*var, &b),
            (_, Ty::Infer(var)) => self.bind_variable(*var, &a),
            (Ty::Param(id), _) => env
                .generics
                .get(id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty),
                    _ => None,
                })
                .is_some_and(|found| found != &a && self.equiv(env, found, &b)),
            (_, Ty::Param(id)) => env
                .generics
                .get(id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty),
                    _ => None,
                })
                .is_some_and(|found| found != &b && self.equiv(env, &a, found)),
            (Ty::Draft(x), Ty::Draft(y)) => self.equiv(env, x, y),
            (Ty::TypeValue(Some(x)), Ty::TypeValue(Some(y))) => self.equiv(env, x, y),
            (Ty::Array(x), Ty::Array(y)) => self.member_equiv(env, x, y),
            (Ty::Map(xk, x), Ty::Map(yk, y)) => {
                self.equiv(env, xk, yk) && self.member_equiv(env, x, y)
            }
            (Ty::Tuple(x), Ty::Tuple(y)) => {
                x.len() == y.len() && x.iter().zip(y).all(|(x, y)| self.member_equiv(env, x, y))
            }
            (Ty::Record(x, x_open), Ty::Record(y, y_open)) => {
                x_open == y_open
                    && x.len() == y.len()
                    && x.iter()
                        .all(|(k, xv)| y.get(k).is_some_and(|yv| self.member_equiv(env, xv, yv)))
            }
            (Ty::Callable(x), Ty::Callable(y)) => self.callable_equiv(env, x, y),
            (Ty::Adt(x), Ty::Adt(y)) if x.definition == y.definition => {
                x.arguments.len() == y.arguments.len()
                    && x.arguments
                        .iter()
                        .zip(&y.arguments)
                        .all(|(xa, ya)| match (xa, ya) {
                            (GenericValue::Type(xt), GenericValue::Type(yt)) => {
                                self.equiv(env, xt, yt)
                            }
                            _ => xa == ya,
                        })
            }
            (Ty::Adt(adt), _) if adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope => {
                self.representation(env, adt)
                    .is_some_and(|ty| self.equiv(env, &ty, &b))
            }
            (_, Ty::Adt(adt)) if adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope => {
                self.representation(env, adt)
                    .is_some_and(|ty| self.equiv(env, &a, &ty))
            }
            _ => false,
        }
    }

    fn member_equiv(&mut self, env: &Env, a: &Member, b: &Member) -> bool {
        a.mode.variable == b.mode.variable
            && (a.mode.mode == b.mode.mode || a.mode.mode == Mode::Via || b.mode.mode == Mode::Via)
            && self.equiv(env, &a.ty, &b.ty)
    }

    fn callable_equiv(&mut self, env: &Env, a: &Callable, b: &Callable) -> bool {
        a.is_ctl == b.is_ctl
            && a.parameters.len() == b.parameters.len()
            && a.open_effects == b.open_effects
            && a.effects == b.effects
            && a.open_state == b.open_state
            && a.state == b.state
            && (a.result_mode == b.result_mode
                || a.result_mode == Mode::Infer
                || b.result_mode == Mode::Infer)
            && a.parameters.iter().zip(&b.parameters).all(|(p, q)| {
                self.parameter_callable_mode(env, p) == self.parameter_callable_mode(env, q)
                    && match (&p.label, &q.label) {
                        (Some(x), Some(y)) => x == y,
                        _ => true,
                    }
                    && self.equiv(env, &p.ty, &q.ty)
            })
            && self.equiv(env, &a.result, &b.result)
    }

    fn member_fits(&mut self, env: &Env, a: &Member, b: &Member, container: bool) -> bool {
        a.mode.variable == b.mode.variable
            && (a.mode.mode == b.mode.mode || b.mode.mode == Mode::Via)
            && if container || a.mode.variable || matches!(a.mode.mode, Mode::Mut | Mode::Shared) {
                self.equiv(env, &a.ty, &b.ty)
            } else {
                self.fits(env, &a.ty, &b.ty)
            }
    }

    fn state_clause_fits(expected: &[String], clause: &str) -> bool {
        if expected.iter().any(|e| e == clause) {
            return true;
        }
        if clause == "up" || clause == "up(ref)" || clause.starts_with("up(") {
            if expected.iter().any(|e| e == "up") {
                return true;
            }
            if clause != "up" && expected.iter().any(|e| e == "up(ref)") {
                let inner = clause
                    .strip_prefix("up(")
                    .and_then(|s| s.strip_suffix(')'))
                    .unwrap_or("");
                return inner.split(',').all(|binding| {
                    let b = binding.trim();
                    !b.starts_with("mut ") && !b.starts_with("^mut ")
                });
            }
        }
        false
    }

    fn callable_fits(&mut self, env: &Env, actual: &Callable, expected: &Callable) -> bool {
        actual.is_ctl == expected.is_ctl
            && actual.parameters.len() == expected.parameters.len()
            && (expected.open_effects
                || !actual.open_effects
                    && actual.effects.iter().all(|effect| {
                        expected
                            .effects
                            .iter()
                            .any(|cover| self.effect_covers(cover, effect))
                    }))
            && (expected.open_state
                || !actual.open_state
                    && actual
                        .state
                        .iter()
                        .all(|clause| Self::state_clause_fits(&expected.state, clause)))
            && (actual.result_mode == expected.result_mode
                || expected.result_mode == Mode::Infer
                || actual.result_mode == Mode::New && expected.result_mode == Mode::Plain)
            && actual
                .parameters
                .iter()
                .zip(&expected.parameters)
                .all(|(a, b)| {
                    self.parameter_callable_mode(env, a) == self.parameter_callable_mode(env, b)
                        && b.label
                            .as_ref()
                            .is_none_or(|name| a.label.as_ref() == Some(name))
                        && self.fits(env, &b.ty, &a.ty)
                })
            && self.fits(env, &actual.result, &expected.result)
    }

    pub(super) fn require(&mut self, env: &Env, span: Span, actual: &Ty, expected: &Ty) -> bool {
        if self.fits(env, actual, expected) {
            return true;
        }
        if let Some((code, cause_span)) = self.narrow_errors.get(&span).copied() {
            self.error_diag(
                Diagnostic::error(code, span, "previous narrowing no longer holds")
                    .with_label(cause_span, "narrowing invalidated here"),
            );
            return false;
        }
        let actual = self.normalize(actual);
        let expected = self.normalize(expected);
        if let (Ty::Callable(actual), Ty::Callable(expected)) = (&actual, &expected) {
            let code = if actual.parameters.len() != expected.parameters.len() {
                Code::E0314
            } else if actual
                .parameters
                .iter()
                .zip(&expected.parameters)
                .any(|(a, b)| {
                    self.parameter_callable_mode(env, a) != self.parameter_callable_mode(env, b)
                })
            {
                Code::E0407
            } else {
                Code::E0534
            };
            self.error(
                code,
                span,
                "callable is incompatible with the target signature",
            );
            return false;
        }
        let code = if matches!((&actual, &expected), (Ty::Adt(a), Ty::Adt(b)) if a.definition != b.definition
            && a.kind == AdtKind::Nominal && b.kind == AdtKind::Nominal)
        {
            Code::E0305
        } else {
            Code::E0301
        };
        self.error(
            code,
            span,
            format!(
                "expected {}, found {}",
                expected.display(self.hir),
                actual.display(self.hir)
            ),
        );
        false
    }

    pub(super) fn join(&mut self, env: &Env, span: Span, one: Ty, two: Ty) -> Ty {
        if matches!(one, Ty::Never) {
            two
        } else if matches!(two, Ty::Never) || self.fits(env, &two, &one) {
            self.normalize(&one)
        } else if self.fits(env, &one, &two) {
            self.normalize(&two)
        } else if env.phase == Phase::TypeEval
            && matches!((&one, &two), (Ty::TypeValue(_), Ty::TypeValue(_)))
        {
            Ty::TypeValue(None)
        } else {
            self.error(
                Code::E0351,
                span,
                format!(
                    "branch types {} and {} cannot join",
                    one.display(self.hir),
                    two.display(self.hir)
                ),
            );
            Ty::Unknown
        }
    }

    pub(super) fn define_name(&mut self, name: &Name, ty: Ty) {
        if let Some(id) = self.resolve(name.span) {
            self.bindings.insert(id, ty);
        }
    }
}

pub(super) fn substitute(ty: &Ty, generics: &HashMap<DefinitionId, GenericValue>) -> Ty {
    transform(ty, &mut |ty| {
        if let Ty::Param(id) = ty
            && let Some(GenericValue::Type(ty)) = generics.get(id)
        {
            Some(ty.clone())
        } else {
            None
        }
    })
}

pub(super) fn transform(ty: &Ty, f: &mut impl FnMut(&Ty) -> Option<Ty>) -> Ty {
    if let Some(replaced) = f(ty) {
        return replaced;
    }
    let wrap = |t, f: &mut _| Box::new(transform(t, f));
    let member = |m: &Member, f: &mut _| Member {
        mode: m.mode,
        ty: transform(&m.ty, f),
    };
    match ty {
        Ty::Adt(adt) => Ty::Adt(Arc::new(super::Adt {
            arguments: adt
                .arguments
                .iter()
                .map(|arg| match arg {
                    GenericValue::Type(ty) => GenericValue::Type(transform(ty, f)),
                    arg => arg.clone(),
                })
                .collect(),
            ..(**adt).clone()
        })),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|item| member(item, f)).collect()),
        Ty::Record(items, open) => Ty::Record(
            items
                .iter()
                .map(|(name, item)| (name.clone(), member(item, f)))
                .collect(),
            *open,
        ),
        Ty::Array(item) => Ty::Array(Box::new(member(item, f))),
        Ty::Map(key, item) => Ty::Map(wrap(key, f), Box::new(member(item, f))),
        Ty::Draft(ty) => Ty::Draft(wrap(ty, f)),
        Ty::Projection(ty, key) => Ty::Projection(wrap(ty, f), *key),
        Ty::TypeValue(Some(ty)) => Ty::TypeValue(Some(wrap(ty, f))),
        Ty::Callable(call) => Ty::Callable(Arc::new(Callable {
            result: transform(&call.result, f),
            parameters: call
                .parameters
                .iter()
                .map(|p| Parameter {
                    ty: transform(&p.ty, f),
                    ..p.clone()
                })
                .collect(),
            ..(**call).clone()
        })),
        _ => ty.clone(),
    }
}

pub(super) fn unknown_callable() -> Callable {
    Callable {
        is_ctl: false,
        parameters: Vec::new(),
        result: Ty::Unknown,
        result_mode: Mode::Plain,
        effects: Vec::new(),
        open_effects: false,
        state: Vec::new(),
        open_state: false,
    }
}

pub(super) fn path_name(path: &syntax::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.name.value.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
