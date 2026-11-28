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
                imported_must_consume_params: HashMap::new(),
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
                proved_ops: HashSet::new(),
                navigation_values: HashMap::new(),
                propagation_inputs: HashMap::new(),
                nominal_layouts: HashMap::new(),
                record_adts: HashSet::new(),
                effect_instances: BTreeMap::new(),
                operation_effects: HashMap::new(),
                operation_instances: HashMap::new(),
                effect_applications: HashMap::new(),
                effect_var_applications: HashMap::new(),
                subset_tags: HashMap::new(),
                tuple_payloads: HashMap::new(),
                receptions: HashMap::new(),
                exported_param_proofs: BTreeMap::new(),
                exported_return_proofs: BTreeMap::new(),
                exported_type_invariants: BTreeMap::new(),
                boxed_var_captures: std::collections::BTreeSet::new(),
            },
            diagnostics,
        );
    }
    let types = std::mem::take(&mut ck.types)
        .into_iter()
        .map(|(span, ty)| (span, ck.finalize(&ty)))
        .collect();
    let bindings = std::mem::take(&mut ck.bindings)
        .into_iter()
        .map(|(id, ty)| (id, ck.finalize(&ty)))
        .collect();
    let navigation_values = std::mem::take(&mut ck.navigation_values)
        .into_iter()
        .map(|(span, ty)| (span, ck.finalize(&ty)))
        .collect();
    let propagation_inputs = std::mem::take(&mut ck.propagation_inputs)
        .into_iter()
        .map(|(span, ty)| (span, ck.finalize(&ty)))
        .collect();
    let nominal_layouts = std::mem::take(&mut ck.nominal_layouts)
        .into_iter()
        .map(|(id, ty)| (id, ck.finalize(&ty)))
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
                            GenericValue::Type(ty) => GenericValue::Type(ck.finalize(&ty)),
                            GenericValue::Effects(row) => {
                                GenericValue::Effects(ck.normalize_effect_row(&row))
                            }
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
        proved_ops,
        effect_instances,
        operation_effects,
        operation_instances,
        effect_applications,
        effect_var_applications,
        subset_tags,
        tuple_payloads,
        receptions,
        record_adts,
        narrow_drops,
        exported_param_proofs,
        exported_return_proofs,
        exported_type_invariants,
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
        imported_must_consume_params: HashMap::new(),
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
        proved_ops,
        navigation_values,
        propagation_inputs,
        nominal_layouts,
        record_adts,
        effect_instances,
        operation_effects,
        operation_instances,
        effect_applications,
        effect_var_applications,
        subset_tags,
        tuple_payloads,
        receptions,
        exported_param_proofs,
        exported_return_proofs,
        exported_type_invariants,
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
pub(super) struct PendingClosureParamProof {
    pub(super) cb_param_idx: usize,
    pub(super) tf_id: DefinitionId,
    pub(super) extra: Vec<Option<syntax::ExprId>>,
    pub(super) def_file: FileId,
    pub(super) formal_to_caller: HashMap<DefinitionId, syntax::ExprId>,
}

#[derive(Clone)]
pub(super) struct PendingHandlerProofs {
    pub(super) op_id: DefinitionId,
    pub(super) op_file: FileId,
    pub(super) is_ctl: bool,
}

#[derive(Clone)]
pub(super) struct CtlResumeProof {
    pub(super) op_id: DefinitionId,
    pub(super) op_file: FileId,
    pub(super) formal_to_local: HashMap<DefinitionId, DefinitionId>,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum ReturnProofRef {
    Expr(syntax::ExprId),
    Type(syntax::TypeId),
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
    pub(super) return_proofs: Vec<ReturnProofRef>,
    pub(super) pending_closure_param_proofs: Vec<PendingClosureParamProof>,
    pub(super) pending_handler_proofs: Option<PendingHandlerProofs>,
    pub(super) active_handler_return_proofs: Option<CtlResumeProof>,
    pub(super) ctl_resume_proofs: HashMap<DefinitionId, CtlResumeProof>,
    pub(super) callback_param_sigs: HashMap<DefinitionId, (FileId, syntax::Signature)>,
    pub(super) checking_fn_tail: bool,
    pub(super) active_defers: Vec<syntax::ExprId>,
    pub(super) shadow: bool,
    pub(super) effects_seen: HashSet<String>,
    pub(super) effect_vars_seen: HashSet<DefinitionId>,
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
            return_proofs: Vec::new(),
            pending_closure_param_proofs: Vec::new(),
            pending_handler_proofs: None,
            active_handler_return_proofs: None,
            ctl_resume_proofs: HashMap::new(),
            callback_param_sigs: HashMap::new(),
            checking_fn_tail: false,
            active_defers: Vec::new(),
            shadow: false,
            effects_seen: HashSet::new(),
            effect_vars_seen: HashSet::new(),
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
    pub(super) effect_infers: Vec<super::EffectRow>,
    pub(super) resolving: HashSet<DefinitionId>,
    pub(super) must_consume_active: HashSet<DefinitionId>,
    checked: HashSet<DefinitionId>,
    schemes: HashSet<DefinitionId>,
    pub(super) live: HashSet<DefinitionId>,
    pub(super) confined_locals: HashSet<DefinitionId>,
    pub(super) captured_locals: HashSet<DefinitionId>,
    pub(super) implicit_exits: Vec<ImplicitExits>,
    pub(super) narrowings: HashMap<Span, usize>,
    pub(super) proved_ops: HashSet<Span>,
    pub(super) lowered_proof_preds:
        HashMap<DefinitionId, Result<super::proofs::LoweredTypeFn, super::proofs::LowerError>>,
    pub(super) exported_param_proofs: BTreeMap<DefinitionId, Vec<super::proofs::ExportProof>>,
    pub(super) exported_return_proofs: BTreeMap<DefinitionId, Vec<super::proofs::ExportProof>>,
    pub(super) exported_type_invariants: BTreeMap<DefinitionId, Vec<super::proofs::ExportProof>>,
    pub(super) navigation_values: HashMap<Span, Ty>,
    pub(super) propagation_inputs: HashMap<Span, Ty>,
    pub(super) nominal_layouts: HashMap<DefinitionId, Ty>,
    pub(super) record_adts: HashSet<DefinitionId>,
    pub(super) effect_instances: BTreeMap<String, super::effects::Instance>,
    pub(super) operation_effects: HashMap<Span, String>,
    pub(super) operation_instances: HashMap<Span, super::effects::Instance>,
    pub(super) effect_applications: HashMap<Span, Vec<String>>,
    pub(super) effect_var_applications: HashMap<Span, Vec<DefinitionId>>,
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
            effect_infers: Vec::new(),
            resolving: HashSet::new(),
            must_consume_active: HashSet::new(),
            checked: HashSet::new(),
            schemes: HashSet::new(),
            live: HashSet::new(),
            confined_locals: HashSet::new(),
            captured_locals: HashSet::new(),
            implicit_exits: Vec::new(),
            inspection_scopes: HashMap::new(),
            narrowings: HashMap::new(),
            proved_ops: HashSet::new(),
            lowered_proof_preds: HashMap::new(),
            exported_param_proofs: BTreeMap::new(),
            exported_return_proofs: BTreeMap::new(),
            exported_type_invariants: BTreeMap::new(),
            propagation_inputs: HashMap::new(),
            nominal_layouts: HashMap::new(),
            record_adts: HashSet::new(),
            effect_instances: BTreeMap::new(),
            operation_effects: HashMap::new(),
            operation_instances: HashMap::new(),
            effect_applications: HashMap::new(),
            effect_var_applications: HashMap::new(),
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

    pub(super) fn fresh_effect(&mut self) -> usize {
        let id = self.effect_infers.len();
        self.effect_infers.push(super::EffectRow::default());
        id
    }

    pub(super) fn normalize_effect_row(&self, row: &super::EffectRow) -> super::EffectRow {
        let mut out = super::EffectRow {
            concrete: row.concrete.clone(),
            vars: row.vars.clone(),
            infers: Vec::new(),
            open: row.open,
            direct_open: row.direct_open,
        };
        let mut stack = row.infers.clone();
        let mut seen = HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            if let Some(bound) = self.effect_infers.get(id) {
                for eff in &bound.concrete {
                    if !out.concrete.contains(eff) {
                        out.concrete.push(eff.clone());
                    }
                }
                for &v in &bound.vars {
                    if !out.vars.contains(&v) {
                        out.vars.push(v);
                    }
                }
                for &nested in &bound.infers {
                    stack.push(nested);
                }
                out.open |= bound.open;
                out.direct_open |= bound.direct_open;
            }
        }
        out.concrete.sort();
        out.vars.sort();
        out
    }

    pub(super) fn effect_label_has_ctl(&self, effect: &str) -> bool {
        if effect == "io" {
            return false;
        }
        let def = self
            .effect_instances
            .get(effect)
            .map(|inst| inst.definition)
            .or_else(|| self.hir.effect_by_label(effect));
        def.is_some_and(|id| {
            self.hir
                .effect_operations(id)
                .any(|op| self.hir.is_ctl_operation(op))
        })
    }

    pub(super) fn normalize(&self, ty: &Ty) -> Ty {
        if let Ty::Infer(var) = ty
            && let Some(replace) = self.substitutions.get(var)
        {
            return self.normalize(replace);
        }
        transform(ty, &mut |ty| match ty {
            Ty::Infer(var) if self.substitutions.contains_key(var) => Some(self.normalize(ty)),
            _ => None,
        })
    }

    pub(super) fn finalize(&self, ty: &Ty) -> Ty {
        if let Ty::Infer(var) = ty
            && let Some(replace) = self.substitutions.get(var)
        {
            return self.finalize(replace);
        }
        transform(ty, &mut |ty| match ty {
            Ty::Infer(var) if self.substitutions.contains_key(var) => Some(self.finalize(ty)),
            Ty::Callable(call) if !call.effect_infers.is_empty() => {
                let row = self.normalize_effect_row(&super::EffectRow {
                    concrete: call.effects.clone(),
                    vars: call.effect_vars.clone(),
                    infers: call.effect_infers.clone(),
                    open: call.open_effects,
                    direct_open: call.direct_open_effects,
                });
                Some(Ty::Callable(Arc::new(Callable {
                    parameters: call
                        .parameters
                        .iter()
                        .map(|p| Parameter {
                            ty: self.finalize(&p.ty),
                            ..p.clone()
                        })
                        .collect(),
                    result: self.finalize(&call.result),
                    effects: row.concrete,
                    effect_vars: row.vars,
                    effect_infers: Vec::new(),
                    open_effects: row.open,
                    direct_open_effects: row.direct_open,
                    ..(**call).clone()
                })))
            }
            Ty::Adt(adt)
                if adt
                    .arguments
                    .iter()
                    .any(|a| matches!(a, GenericValue::Effects(r) if !r.infers.is_empty())) =>
            {
                Some(Ty::Adt(Arc::new(super::Adt {
                    arguments: adt
                        .arguments
                        .iter()
                        .map(|arg| match arg {
                            GenericValue::Type(t) => GenericValue::Type(self.finalize(t)),
                            GenericValue::Effects(r) => {
                                GenericValue::Effects(self.normalize_effect_row(r))
                            }
                            other => other.clone(),
                        })
                        .collect(),
                    ..(**adt).clone()
                })))
            }
            _ => None,
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

    pub(super) fn has_type_invariants(&self, def_id: DefinitionId) -> bool {
        let def = self.hir.definition(def_id);
        let Some(stmt) = def.stmt else {
            return false;
        };
        matches!(
            &self.ast(def.name.span.file).stmt(stmt).value.kind,
            syntax::StmtKind::Type(decl) if !decl.guards.is_empty()
        )
    }

    pub(super) fn contains_live_member_schema_deep(
        &mut self,
        env: &Env,
        ty: &Ty,
        seen: &mut HashSet<DefinitionId>,
    ) -> bool {
        match self.normalize(ty) {
            Ty::Draft(_) => true,
            Ty::Array(m) | Ty::Map(_, m) => {
                m.mode.variable
                    || m.mode.mode != Mode::Plain
                    || self.contains_live_member_schema_deep(env, &m.ty, seen)
            }
            Ty::Tuple(ms) => ms.iter().any(|m| {
                m.mode.variable
                    || m.mode.mode != Mode::Plain
                    || self.contains_live_member_schema_deep(env, &m.ty, seen)
            }),
            Ty::Record(fields, _) => fields.values().any(|m| {
                m.mode.variable
                    || m.mode.mode != Mode::Plain
                    || self.contains_live_member_schema_deep(env, &m.ty, seen)
            }),
            Ty::Adt(adt) => {
                if !seen.insert(adt.definition) {
                    return false;
                }
                let res = adt.arguments.iter().any(|arg| match arg {
                    GenericValue::Type(t) => self.contains_live_member_schema_deep(env, t, seen),
                    _ => false,
                }) || match adt.kind {
                    AdtKind::Nominal | AdtKind::Opaque => self
                        .representation(env, &adt)
                        .is_some_and(|rep| self.contains_live_member_schema_deep(env, &rep, seen)),
                    AdtKind::Sum | AdtKind::OpaqueSum => {
                        self.sum_variants(&adt).values().flatten().any(|payload| {
                            self.contains_live_member_schema_deep(env, payload, seen)
                        })
                    }
                };
                seen.remove(&adt.definition);
                res
            }
            _ => false,
        }
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
                            (GenericValue::Effects(actual), GenericValue::Effects(expected)) => {
                                if !expected.infers.is_empty() {
                                    for &eid in &expected.infers {
                                        if let Some(slot) = self.effect_infers.get_mut(eid) {
                                            slot.merge(actual);
                                        }
                                    }
                                    true
                                } else {
                                    actual == expected
                                }
                            }
                            _ => actual == expected,
                        })
            }
            (Ty::Adt(adt), _)
                if adt.kind == AdtKind::Opaque
                    && adt.defining_scope == env.scope
                    && !self.has_type_invariants(adt.definition) =>
            {
                self.representation(env, adt)
                    .is_some_and(|ty| self.fits(env, &ty, &expected))
            }
            (_, Ty::Adt(adt))
                if adt.kind == AdtKind::Opaque
                    && adt.defining_scope == env.scope
                    && !self.has_type_invariants(adt.definition) =>
            {
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
            (Ty::Adt(adt), _)
                if adt.kind == AdtKind::Opaque
                    && adt.defining_scope == env.scope
                    && !self.has_type_invariants(adt.definition) =>
            {
                self.representation(env, adt)
                    .is_some_and(|ty| self.equiv(env, &ty, &b))
            }
            (_, Ty::Adt(adt))
                if adt.kind == AdtKind::Opaque
                    && adt.defining_scope == env.scope
                    && !self.has_type_invariants(adt.definition) =>
            {
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
        let effects_eq = if !b.effect_infers.is_empty() && a.effect_infers.is_empty() {
            for &eid in &b.effect_infers {
                if let Some(slot) = self.effect_infers.get_mut(eid) {
                    slot.merge(&super::EffectRow {
                        concrete: a.effects.clone(),
                        vars: a.effect_vars.clone(),
                        infers: Vec::new(),
                        open: a.open_effects,
                        direct_open: a.direct_open_effects,
                    });
                }
            }
            true
        } else if !a.effect_infers.is_empty() && b.effect_infers.is_empty() {
            for &eid in &a.effect_infers {
                if let Some(slot) = self.effect_infers.get_mut(eid) {
                    slot.merge(&super::EffectRow {
                        concrete: b.effects.clone(),
                        vars: b.effect_vars.clone(),
                        infers: Vec::new(),
                        open: b.open_effects,
                        direct_open: b.direct_open_effects,
                    });
                }
            }
            true
        } else {
            a.open_effects == b.open_effects
                && a.direct_open_effects == b.direct_open_effects
                && a.effects == b.effects
                && a.effect_vars == b.effect_vars
        };
        a.is_ctl == b.is_ctl
            && a.parameters.len() == b.parameters.len()
            && effects_eq
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
        if actual.is_ctl != expected.is_ctl || actual.parameters.len() != expected.parameters.len()
        {
            return false;
        }
        let effects_ok = if !expected.effect_infers.is_empty() {
            // Union any effects of `actual` not already covered by `expected`'s explicit effects/vars
            // into each effect inference variable on `expected`.
            let extra_concrete: Vec<String> = actual
                .effects
                .iter()
                .filter(|eff| {
                    !expected
                        .effects
                        .iter()
                        .any(|cover| self.effect_covers(cover, eff))
                })
                .cloned()
                .collect();
            let extra_vars: Vec<DefinitionId> = actual
                .effect_vars
                .iter()
                .filter(|v| !expected.effect_vars.contains(v))
                .copied()
                .collect();
            let extra_infers: Vec<usize> = actual
                .effect_infers
                .iter()
                .filter(|i| !expected.effect_infers.contains(i))
                .copied()
                .collect();
            for &eid in &expected.effect_infers {
                if let Some(slot) = self.effect_infers.get_mut(eid) {
                    slot.merge(&super::EffectRow {
                        concrete: extra_concrete.clone(),
                        vars: extra_vars.clone(),
                        infers: extra_infers.clone(),
                        open: actual.open_effects,
                        direct_open: actual.direct_open_effects,
                    });
                }
            }
            true
        } else if expected.open_effects {
            true
        } else if expected.direct_open_effects {
            !actual.open_effects
                && actual.effects.iter().all(|eff| {
                    expected
                        .effects
                        .iter()
                        .any(|cover| self.effect_covers(cover, eff))
                        || !self.effect_label_has_ctl(eff)
                })
                && actual.effect_vars.iter().all(|v| {
                    expected.effect_vars.contains(v) || self.hir.is_direct_effect_param(*v)
                })
        } else {
            !actual.open_effects
                && !actual.direct_open_effects
                && actual.effects.iter().all(|effect| {
                    expected
                        .effects
                        .iter()
                        .any(|cover| self.effect_covers(cover, effect))
                })
                && actual
                    .effect_vars
                    .iter()
                    .all(|v| expected.effect_vars.contains(v))
        };
        effects_ok
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
            let direct_ctl_mismatch = expected.direct_open_effects
                && !expected.open_effects
                && (actual.open_effects
                    || actual.effects.iter().any(|eff| {
                        !expected
                            .effects
                            .iter()
                            .any(|cover| self.effect_covers(cover, eff))
                            && self.effect_label_has_ctl(eff)
                    })
                    || actual.effect_vars.iter().any(|v| {
                        !expected.effect_vars.contains(v) && !self.hir.is_direct_effect_param(*v)
                    }));
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
            } else if direct_ctl_mismatch {
                Code::E0616
            } else {
                Code::E0534
            };
            let msg = if code == Code::E0616 {
                "callable using ctl effect cannot be passed to a '@fn' target"
            } else {
                "callable is incompatible with the target signature"
            };
            self.error(code, span, msg);
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

pub(super) fn substitute_effect_row(
    row: &super::EffectRow,
    generics: &HashMap<DefinitionId, GenericValue>,
) -> super::EffectRow {
    let mut out = super::EffectRow {
        concrete: row.concrete.clone(),
        vars: Vec::new(),
        infers: row.infers.clone(),
        open: row.open,
        direct_open: row.direct_open,
    };
    for &var in &row.vars {
        if let Some(GenericValue::Effects(bound)) = generics.get(&var) {
            out.merge(bound);
        } else if !out.vars.contains(&var) {
            out.vars.push(var);
        }
    }
    out.concrete.sort();
    out.vars.sort();
    out.infers.sort();
    out
}

pub(super) fn substitute(ty: &Ty, generics: &HashMap<DefinitionId, GenericValue>) -> Ty {
    transform(ty, &mut |ty| match ty {
        Ty::Param(id) => {
            if let Some(GenericValue::Type(ty)) = generics.get(id) {
                Some(ty.clone())
            } else {
                None
            }
        }
        Ty::Callable(call) if !call.effect_vars.is_empty() => {
            let row = substitute_effect_row(
                &super::EffectRow {
                    concrete: call.effects.clone(),
                    vars: call.effect_vars.clone(),
                    infers: call.effect_infers.clone(),
                    open: call.open_effects,
                    direct_open: call.direct_open_effects,
                },
                generics,
            );
            Some(Ty::Callable(Arc::new(Callable {
                result: substitute(&call.result, generics),
                parameters: call
                    .parameters
                    .iter()
                    .map(|p| Parameter {
                        ty: substitute(&p.ty, generics),
                        ..p.clone()
                    })
                    .collect(),
                effects: row.concrete,
                effect_vars: row.vars,
                effect_infers: row.infers,
                open_effects: row.open,
                direct_open_effects: row.direct_open,
                ..(**call).clone()
            })))
        }
        Ty::Adt(adt)
            if adt
                .arguments
                .iter()
                .any(|a| matches!(a, GenericValue::Effects(r) if !r.vars.is_empty())) =>
        {
            Some(Ty::Adt(Arc::new(super::Adt {
                arguments: adt
                    .arguments
                    .iter()
                    .map(|arg| match arg {
                        GenericValue::Type(t) => GenericValue::Type(substitute(t, generics)),
                        GenericValue::Effects(r) => {
                            GenericValue::Effects(substitute_effect_row(r, generics))
                        }
                        other => other.clone(),
                    })
                    .collect(),
                ..(**adt).clone()
            })))
        }
        _ => None,
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
        effect_vars: Vec::new(),
        effect_infers: Vec::new(),
        open_effects: false,
        direct_open_effects: false,
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
