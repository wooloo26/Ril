use std::collections::{BTreeMap, BTreeSet, HashMap};

use ril_hir::{DefinitionId, DefinitionKind, Resolution};
use ril_source::span::{FileId, Span};
use ril_syntax::syntax::{
    Ast, Condition, Expr, ExprId, Mode, Pattern, PatternId, StmtId, StmtKind, Storage, StringPart,
};

use super::{
    Body, CallTarget, LocalDecl, ThirExpr, ThirExprId, ThirExprKind, ThirPat, ThirPatId, ThirStmt,
    ThirStmtId, ThirStmtKind,
};
use crate::ty::{Ty, TypedProgram};

pub(super) struct BodyBuilder<'a> {
    typed: &'a TypedProgram,
    ast: &'a Ast,
    owner: Option<DefinitionId>,
    file: FileId,
    all_var_defs: &'a BTreeSet<DefinitionId>,
    fn_up_captures: &'a HashMap<DefinitionId, Vec<DefinitionId>>,
    boxed_var_captures: &'a mut BTreeSet<DefinitionId>,
    closure_references: &'a mut BTreeMap<Span, BTreeSet<DefinitionId>>,
    pub(super) exprs: Vec<ThirExpr>,
    pub(super) stmts: Vec<ThirStmt>,
    pub(super) pats: Vec<ThirPat>,
    locals: Vec<LocalDecl>,
    expr_by_span: HashMap<Span, ThirExprId>,
}

impl<'a> BodyBuilder<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        typed: &'a TypedProgram,
        ast: &'a Ast,
        owner: Option<DefinitionId>,
        file: FileId,
        all_var_defs: &'a BTreeSet<DefinitionId>,
        fn_up_captures: &'a HashMap<DefinitionId, Vec<DefinitionId>>,
        boxed_var_captures: &'a mut BTreeSet<DefinitionId>,
        closure_references: &'a mut BTreeMap<Span, BTreeSet<DefinitionId>>,
    ) -> Self {
        Self {
            typed,
            ast,
            owner,
            file,
            all_var_defs,
            fn_up_captures,
            boxed_var_captures,
            closure_references,
            exprs: Vec::new(),
            stmts: Vec::new(),
            pats: Vec::new(),
            locals: Vec::new(),
            expr_by_span: HashMap::new(),
        }
    }

    pub(super) fn record_local(&mut self, definition: DefinitionId, span: Span, storage: Storage) {
        let ty = self
            .typed
            .bindings
            .get(&definition)
            .cloned()
            .unwrap_or(Ty::Unknown);
        self.locals.push(LocalDecl {
            definition,
            span,
            ty,
            storage,
            boxed: false,
        });
    }

    fn push_expr(&mut self, span: Span, kind: ThirExprKind) -> ThirExprId {
        let id = ThirExprId(u32::try_from(self.exprs.len()).unwrap_or(u32::MAX));
        let ty = self.typed.types.get(&span).cloned().unwrap_or(Ty::Unknown);
        let narrowing_depth = self.typed.narrowings.get(&span).copied().unwrap_or(0);
        let has_static_value = self.typed.static_values.contains_key(&span);
        let inspection_scope = self.typed.inspection_scope(span);
        let navigation_ty = self.typed.navigation_values.get(&span).cloned();
        let propagation_ty = self.typed.propagation_inputs.get(&span).cloned();
        self.exprs.push(ThirExpr {
            span,
            ty,
            narrowing_depth,
            has_static_value,
            inspection_scope,
            navigation_ty,
            propagation_ty,
            kind,
        });
        self.expr_by_span.insert(span, id);
        id
    }

    fn push_stmt(&mut self, span: Span, kind: ThirStmtKind) -> ThirStmtId {
        let id = ThirStmtId(u32::try_from(self.stmts.len()).unwrap_or(u32::MAX));
        self.stmts.push(ThirStmt { span, kind });
        id
    }

    fn push_pat(
        &mut self,
        span: Span,
        binding: Option<(DefinitionId, Storage)>,
        children: Vec<ThirPatId>,
    ) -> ThirPatId {
        let id = ThirPatId(u32::try_from(self.pats.len()).unwrap_or(u32::MAX));
        let ty = self.typed.types.get(&span).cloned().unwrap_or(Ty::Unknown);
        self.pats.push(ThirPat {
            span,
            ty,
            binding,
            children,
        });
        id
    }

    fn note_ref(
        &mut self,
        def: DefinitionId,
        closure_refs: &mut Option<&mut BTreeSet<DefinitionId>>,
    ) {
        let Some(set) = closure_refs.as_deref_mut() else {
            return;
        };
        let mut worklist = vec![def];
        let mut seen_fns = BTreeSet::new();
        while let Some(id) = worklist.pop() {
            set.insert(id);
            if self.all_var_defs.contains(&id) {
                // Only box if `id` is defined outside the active closure (checked at closure finish).
            }
            if seen_fns.insert(id)
                && let Some(ups) = self.fn_up_captures.get(&id)
            {
                worklist.extend(ups.iter().copied());
            }
        }
    }

    fn lower_pat(
        &mut self,
        id: PatternId,
        inherited_var: bool,
        bound_in_closure: &mut Option<&mut BTreeSet<DefinitionId>>,
    ) -> ThirPatId {
        let node = self.ast.pattern(id);
        let span = node.span;
        match &node.value {
            Pattern::Binding(storage, name) => {
                let mut eff = storage.clone();
                eff.variable |= inherited_var;
                let binding = match self.typed.hir.resolve(name.span) {
                    Some(Resolution::Definition(def)) => {
                        self.record_local(def, name.span, eff.clone());
                        if let Some(bound) = bound_in_closure.as_deref_mut() {
                            bound.insert(def);
                        }
                        Some((def, eff))
                    }
                    _ => None,
                };
                self.push_pat(span, binding, Vec::new())
            }
            Pattern::Or(items) | Pattern::Tuple(items) => {
                let children = items
                    .iter()
                    .map(|&p| self.lower_pat(p, false, bound_in_closure))
                    .collect();
                self.push_pat(span, None, children)
            }
            Pattern::Slice { elements, .. } => {
                let children = elements
                    .iter()
                    .map(|&p| self.lower_pat(p, false, bound_in_closure))
                    .collect();
                self.push_pat(span, None, children)
            }
            Pattern::Rest(Some(name)) => {
                let binding = match self.typed.hir.resolve(name.span) {
                    Some(Resolution::Definition(def)) => {
                        let st = Storage {
                            variable: false,
                            mode: Mode::Plain,
                            mode_path: None,
                            bind_mode: false,
                        };
                        self.record_local(def, name.span, st.clone());
                        if let Some(bound) = bound_in_closure.as_deref_mut() {
                            bound.insert(def);
                        }
                        Some((def, st))
                    }
                    _ => None,
                };
                self.push_pat(span, binding, Vec::new())
            }
            Pattern::Constructor(_, Some(args)) => {
                let children = args
                    .iter()
                    .map(|&p| self.lower_pat(p, false, bound_in_closure))
                    .collect();
                self.push_pat(span, None, children)
            }
            Pattern::Record { fields, .. } => {
                let mut children = Vec::new();
                for field in fields {
                    if let Some(p) = field.pattern {
                        children.push(self.lower_pat(p, false, bound_in_closure));
                    } else if let Some(Resolution::Definition(def)) =
                        self.typed.hir.resolve(field.name.span)
                    {
                        self.record_local(def, field.name.span, field.storage.clone());
                        if let Some(bound) = bound_in_closure.as_deref_mut() {
                            bound.insert(def);
                        }
                        children.push(self.push_pat(
                            field.name.span,
                            Some((def, field.storage.clone())),
                            Vec::new(),
                        ));
                    }
                }
                self.push_pat(span, None, children)
            }
            Pattern::Subset {
                binding: Some(inner),
                ..
            } => {
                let child = self.lower_pat(*inner, false, bound_in_closure);
                self.push_pat(span, None, vec![child])
            }
            Pattern::Wildcard
            | Pattern::Unit
            | Pattern::Literal(_)
            | Pattern::Rest(None)
            | Pattern::Constructor(_, None)
            | Pattern::Range { .. }
            | Pattern::Subset { binding: None, .. }
            | Pattern::Type(_)
            | Pattern::TypeBinding(_) => self.push_pat(span, None, Vec::new()),
        }
    }

    pub(super) fn lower_stmt(
        &mut self,
        id: StmtId,
        mut closure_refs: Option<&mut BTreeSet<DefinitionId>>,
        mut closure_bound: Option<&mut BTreeSet<DefinitionId>>,
    ) -> ThirStmtId {
        let node = self.ast.stmt(id);
        let span = node.span;
        let kind = match &node.value.kind {
            StmtKind::Binding {
                pattern,
                storage,
                value,
                fallback,
                resource: true,
                ..
            } => {
                let val = value
                    .map(|e| self.lower_expr(e, closure_refs.as_deref_mut()))
                    .unwrap_or_else(|| self.push_expr(span, ThirExprKind::Unit));
                let fb = fallback.map(|e| self.lower_expr(e, closure_refs.as_deref_mut()));
                let pat = self.lower_pat(*pattern, false, &mut closure_bound);
                ThirStmtKind::Resource {
                    pat,
                    mode: storage.mode,
                    value: val,
                    fallback: fb,
                }
            }
            StmtKind::Binding {
                pattern,
                storage,
                value,
                fallback,
                resource: false,
                ..
            } => {
                let val = value.map(|e| self.lower_expr(e, closure_refs.as_deref_mut()));
                let fb = fallback.map(|e| self.lower_expr(e, closure_refs.as_deref_mut()));
                let pat = self.lower_pat(*pattern, storage.variable, &mut closure_bound);
                ThirStmtKind::Binding {
                    pat,
                    storage: storage.clone(),
                    value: val,
                    fallback: fb,
                }
            }
            StmtKind::With(handlers) => {
                let exprs = handlers
                    .iter()
                    .map(|h| self.lower_expr(h.value, closure_refs.as_deref_mut()))
                    .collect();
                ThirStmtKind::With { handlers: exprs }
            }
            StmtKind::Expr(expr) => {
                let e = self.lower_expr(*expr, closure_refs);
                ThirStmtKind::Expr(e)
            }
            StmtKind::Function(fun) => {
                if let Some(Resolution::Definition(def)) = self.typed.hir.resolve(fun.name.span) {
                    ThirStmtKind::NestedDecl(def)
                } else {
                    ThirStmtKind::Other
                }
            }
            _ => ThirStmtKind::Other,
        };
        self.push_stmt(span, kind)
    }

    pub(super) fn lower_expr(
        &mut self,
        id: ExprId,
        mut closure_refs: Option<&mut BTreeSet<DefinitionId>>,
    ) -> ThirExprId {
        let node = self.ast.expr(id);
        let span = node.span;
        let kind = match &node.value {
            Expr::Unit => ThirExprKind::Unit,
            Expr::Literal(_) => ThirExprKind::Literal,
            Expr::Hole => ThirExprKind::Hole,
            Expr::Quote(_) => ThirExprKind::Quote,
            Expr::Accessor(_) => ThirExprKind::Accessor,
            Expr::Path(path) => match self.typed.hir.resolve(path.span) {
                Some(Resolution::Definition(def)) => {
                    self.note_ref(def, &mut closure_refs);
                    if self.typed.hir.definition(def).kind == DefinitionKind::Local {
                        ThirExprKind::Local(def)
                    } else {
                        ThirExprKind::Global(def)
                    }
                }
                _ => ThirExprKind::Unit,
            },
            Expr::Interpolated(parts) => {
                let exprs = parts
                    .iter()
                    .filter_map(|part| match part {
                        StringPart::Interpolation(e) => {
                            Some(self.lower_expr(*e, closure_refs.as_deref_mut()))
                        }
                        StringPart::Text(_) => None,
                    })
                    .collect();
                ThirExprKind::Interpolated(exprs)
            }
            Expr::Block {
                statements,
                helpers,
            } => {
                let mut stmts = Vec::with_capacity(statements.len());
                for &s in statements {
                    stmts.push(self.lower_stmt(s, closure_refs.as_deref_mut(), None));
                }
                let mut helper_stmts = Vec::with_capacity(helpers.len());
                for &h in helpers {
                    helper_stmts.push(self.lower_stmt(h, closure_refs.as_deref_mut(), None));
                }
                ThirExprKind::Block {
                    stmts,
                    helpers: helper_stmts,
                }
            }
            Expr::Unary { op, value } => {
                let val = self.lower_expr(*value, closure_refs.as_deref_mut());
                ThirExprKind::Unary {
                    op: op.value.clone(),
                    value: val,
                }
            }
            Expr::Binary { op, left, right } => {
                let l = self.lower_expr(*left, closure_refs.as_deref_mut());
                let r = self.lower_expr(*right, closure_refs.as_deref_mut());
                ThirExprKind::Binary {
                    op: op.value.clone(),
                    left: l,
                    right: r,
                }
            }
            Expr::Cast { value, .. } => {
                let v = self.lower_expr(*value, closure_refs.as_deref_mut());
                ThirExprKind::Cast { value: v }
            }
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let v = self.lower_expr(*value, closure_refs.as_deref_mut());
                let t = self.lower_expr(*target, closure_refs.as_deref_mut());
                ThirExprKind::Pipeline {
                    value: v,
                    mode: *mode,
                    target: t,
                    propagate: *propagate,
                }
            }
            Expr::Member { base, safe, .. } => {
                let b = self.lower_expr(*base, closure_refs.as_deref_mut());
                ThirExprKind::Member {
                    base: b,
                    safe: *safe,
                }
            }
            Expr::Index { base, index, safe } => {
                let b = self.lower_expr(*base, closure_refs.as_deref_mut());
                let idx = self.lower_expr(*index, closure_refs.as_deref_mut());
                ThirExprKind::Index {
                    base: b,
                    index: idx,
                    safe: *safe,
                }
            }
            Expr::Range {
                start,
                end,
                inclusive,
            } => {
                let s = start.map(|e| self.lower_expr(e, closure_refs.as_deref_mut()));
                let e = end.map(|e| self.lower_expr(e, closure_refs.as_deref_mut()));
                ThirExprKind::Range {
                    start: s,
                    end: e,
                    inclusive: *inclusive,
                }
            }
            Expr::Call { callee, args } => {
                let target = match &self.ast.expr(*callee).value {
                    Expr::Path(path) => match self.typed.hir.resolve(path.span) {
                        Some(Resolution::Definition(def)) => {
                            match self.typed.hir.definition(def).kind {
                                DefinitionKind::Primitive(_) => CallTarget::Primitive(def),
                                DefinitionKind::Variant(_) | DefinitionKind::Type => {
                                    CallTarget::Constructor(def)
                                }
                                DefinitionKind::Function
                                    if self.typed.hir.operation_effect(def).is_some() =>
                                {
                                    CallTarget::EffectOperation(def)
                                }
                                DefinitionKind::Function => CallTarget::Direct(def),
                                _ => CallTarget::Indirect,
                            }
                        }
                        _ => CallTarget::Indirect,
                    },
                    _ => CallTarget::Indirect,
                };
                let callee_id = self.lower_expr(*callee, closure_refs.as_deref_mut());
                let lowered_args = args
                    .iter()
                    .map(|arg| {
                        (
                            arg.mode,
                            self.lower_expr(arg.value, closure_refs.as_deref_mut()),
                        )
                    })
                    .collect();
                ThirExprKind::Call {
                    callee: callee_id,
                    target,
                    args: lowered_args,
                }
            }
            Expr::Record { fields, .. } => {
                let mut lowered = Vec::with_capacity(fields.len());
                for field in fields {
                    let val = if let Some(expr) = field.value {
                        self.lower_expr(expr, closure_refs.as_deref_mut())
                    } else if let Some(Resolution::Definition(def)) =
                        self.typed.hir.resolve(field.name.span)
                    {
                        self.note_ref(def, &mut closure_refs);
                        self.push_expr(field.name.span, ThirExprKind::Local(def))
                    } else {
                        self.push_expr(field.name.span, ThirExprKind::Unit)
                    };
                    lowered.push((field.name.value.clone(), val));
                }
                ThirExprKind::Record { fields: lowered }
            }
            Expr::Array(items) => {
                let elems = items
                    .iter()
                    .map(|&e| self.lower_expr(e, closure_refs.as_deref_mut()))
                    .collect();
                ThirExprKind::Array(elems)
            }
            Expr::Tuple(items) => {
                let elems = items
                    .iter()
                    .map(|&e| self.lower_expr(e, closure_refs.as_deref_mut()))
                    .collect();
                ThirExprKind::Tuple(elems)
            }
            Expr::Map(entries) => {
                let pairs = entries
                    .iter()
                    .map(|&(k, v)| {
                        (
                            self.lower_expr(k, closure_refs.as_deref_mut()),
                            self.lower_expr(v, closure_refs.as_deref_mut()),
                        )
                    })
                    .collect();
                ThirExprKind::Map(pairs)
            }
            Expr::If { condition, yes, no } => {
                let cond = self.lower_condition(condition, closure_refs.as_deref_mut());
                let y = self.lower_expr(*yes, closure_refs.as_deref_mut());
                let n = no.map(|e| self.lower_expr(e, closure_refs.as_deref_mut()));
                ThirExprKind::If {
                    cond,
                    yes: y,
                    no: n,
                }
            }
            Expr::While { condition, body } => {
                let cond = self.lower_condition(condition, closure_refs.as_deref_mut());
                let b = self.lower_expr(*body, closure_refs.as_deref_mut());
                ThirExprKind::While { cond, body: b }
            }
            Expr::For {
                mode,
                iterable,
                pattern,
                body,
            } => {
                let iter = self.lower_expr(*iterable, closure_refs.as_deref_mut());
                let pat = self.lower_pat(*pattern, false, &mut None);
                let b = self.lower_expr(*body, closure_refs.as_deref_mut());
                ThirExprKind::For {
                    mode: *mode,
                    iterable: iter,
                    pat,
                    body: b,
                }
            }
            Expr::Match { mode, value, arms } => {
                let scrut = self.lower_expr(*value, closure_refs.as_deref_mut());
                let lowered_arms = arms
                    .iter()
                    .map(|arm| {
                        let pat = self.lower_pat(arm.pattern, false, &mut None);
                        let guard = arm
                            .guard
                            .map(|g| self.lower_expr(g, closure_refs.as_deref_mut()));
                        let body = self.lower_expr(arm.body, closure_refs.as_deref_mut());
                        (pat, guard, body)
                    })
                    .collect();
                ThirExprKind::Match {
                    mode: *mode,
                    scrutinee: scrut,
                    arms: lowered_arms,
                }
            }
            Expr::Closure { params, body, .. } => {
                let mut inner_refs = BTreeSet::new();
                let mut inner_params = BTreeSet::new();
                for param in params {
                    if let Some(name) = &param.name
                        && let Some(Resolution::Definition(pid)) = self.typed.hir.resolve(name.span)
                    {
                        inner_params.insert(pid);
                        self.record_local(
                            pid,
                            name.span,
                            Storage {
                                variable: false,
                                mode: param.mode,
                                mode_path: None,
                                bind_mode: false,
                            },
                        );
                    }
                }
                let body_id = self.lower_expr(*body, Some(&mut inner_refs));
                // Remove definitions declared inside this closure span; remaining refs are outer captures.
                inner_refs.retain(|def| {
                    if inner_params.contains(def) {
                        return false;
                    }
                    let def_span = self.typed.hir.definition(*def).name.span;
                    !(def_span.file == span.file
                        && def_span.start >= span.start
                        && def_span.end <= span.end)
                });
                for &captured in &inner_refs {
                    if self.all_var_defs.contains(&captured) {
                        self.boxed_var_captures.insert(captured);
                    }
                    if let Some(outer) = closure_refs.as_deref_mut() {
                        outer.insert(captured);
                    }
                }
                let captures: Vec<_> = inner_refs.iter().copied().collect();
                self.closure_references.insert(span, inner_refs);
                ThirExprKind::Closure {
                    captures,
                    body: body_id,
                }
            }
            Expr::Transfer { value, .. } => {
                let v = value.map(|e| self.lower_expr(e, closure_refs));
                ThirExprKind::Transfer(v)
            }
        };
        self.push_expr(span, kind)
    }

    fn lower_condition(
        &mut self,
        condition: &Condition,
        closure_refs: Option<&mut BTreeSet<DefinitionId>>,
    ) -> Option<ThirExprId> {
        match condition {
            Condition::Expr(expr) => Some(self.lower_expr(*expr, closure_refs)),
            Condition::Binding { pattern, value, .. } => {
                let v = self.lower_expr(*value, closure_refs);
                let _ = self.lower_pat(*pattern, false, &mut None);
                Some(v)
            }
        }
    }

    pub(super) fn finish(self, root_expr: Option<ThirExprId>) -> Body {
        Body {
            owner: self
                .owner
                .unwrap_or_else(|| ril_source::ice!("THIR body missing owner")),
            file: self.file,
            exprs: self.exprs,
            stmts: self.stmts,
            pats: self.pats,
            locals: self.locals,
            expr_by_span: self.expr_by_span,
            root_expr,
        }
    }
}
