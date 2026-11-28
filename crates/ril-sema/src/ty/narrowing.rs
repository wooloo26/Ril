use std::collections::{HashMap, HashSet};

use num_traits::ToPrimitive;
use ril_hir::{DefinitionId, Intrinsic};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{
    Condition, Expr, ExprId, Member, Mode, Parameter as SyntaxParam, Pattern, PatternId, StmtId,
    StmtKind,
};

use super::{
    NarrowDrop, NarrowDropCause, Ty, Value,
    check::{Checker, Env},
    dbm::{Atom, Dbm, KeyConst, Place, ProofPred},
    proofs::{CallReturnProof, LinExpr, ReturnAtom},
};

const MAX_WIDEN_ITERS: usize = 4;
const MAX_LOOP_DEPTH: usize = 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Fact {
    pub(super) depth: usize,
    pub(super) is_none: bool,
    pub(super) invalidated: Option<(Code, Span)>,
}

#[derive(Clone, Default)]
pub(super) struct Refinements {
    pub(super) options: HashMap<Place, Fact>,
    pub(super) dbm: Dbm,
    pub(super) call_proofs: HashMap<ExprId, Vec<CallReturnProof>>,
}

impl Checker<'_> {
    pub(super) fn place(&self, env: &Env, expr: ExprId) -> Option<Place> {
        let ast = self.ast(env.file);
        let node = ast.expr(expr);
        match &node.value {
            Expr::Path(path) => Some(Place {
                root: self.resolve(path.span)?,
                path: Vec::new(),
            }),
            Expr::Member {
                base,
                member,
                safe: false,
            } => {
                let mut place = self.place(env, *base)?;
                let suffix = match member {
                    Member::Name(name) | Member::Index(name) => name.value.clone(),
                    Member::Computed(expr) => {
                        match self.static_values.get(&ast.expr(*expr).span)? {
                            Value::Int(v) => v.to_string(),
                            Value::Str(v) => v.clone(),
                            _ => return None,
                        }
                    }
                };
                place.path.push(suffix);
                Some(place)
            }
            Expr::Index {
                base,
                index,
                safe: false,
            } => {
                let mut place = self.place(env, *base)?;
                let Expr::Literal(value) = &ast.expr(*index).value else {
                    return None;
                };
                let key = match super::literal(value).ok()? {
                    Value::Int(v) => v.to_string(),
                    Value::Str(v) => v,
                    _ => return None,
                };
                place.path.push(key);
                Some(place)
            }
            Expr::Call { callee, args } => {
                let Expr::Path(path) = &ast.expr(*callee).value else {
                    return None;
                };
                let id = self.resolve(path.span)?;
                if self.hir.intrinsic(id) == Some(Intrinsic::Inner)
                    && let [arg] = args.as_slice()
                {
                    let mut place = self.resolve_place(env, arg.value)?;
                    place.path.push("#inner".to_owned());
                    return Some(place);
                }
                None
            }
            _ => None,
        }
    }

    pub(super) fn resolve_place(&self, env: &Env, expr: ExprId) -> Option<Place> {
        match &self.ast(env.file).expr(expr).value {
            Expr::Unary { op, value } if matches!(op.value.as_str(), "ref" | "^mut") => {
                self.resolve_place(env, *value)
            }
            _ => self.place(env, expr),
        }
    }

    pub(super) fn resolve_local(&self, env: &Env, expr: ExprId) -> Option<DefinitionId> {
        match &self.ast(env.file).expr(expr).value {
            Expr::Path(path) => self.resolve(path.span),
            Expr::Unary { op, value } if matches!(op.value.as_str(), "ref" | "^mut") => {
                self.resolve_local(env, *value)
            }
            _ => None,
        }
    }

    pub(super) fn apply_refinement(&mut self, env: &Env, expr: ExprId, mut ty: Ty) -> Ty {
        let span = self.ast(env.file).expr(expr).span;
        self.narrow_errors.remove(&span);
        self.narrowings.remove(&span);
        if env.unrefined == Some(span) {
            return ty;
        }
        if let Some(place) = self.place(env, expr)
            && let Some(fact) = env.refinements.options.get(&place)
        {
            if let Some((code, cause_span)) = fact.invalidated {
                self.narrow_errors.insert(span, (code, cause_span));
            } else if fact.depth > 0 {
                for _ in 0..fact.depth {
                    if let Some(inner) = ty.as_option(self.hir) {
                        ty = inner.clone();
                    } else {
                        return ty;
                    }
                }
                self.narrowings.insert(span, fact.depth);
            }
        }
        ty
    }

    pub(super) fn is_known_none(&self, env: &Env, expr: ExprId) -> bool {
        self.place(env, expr).is_some_and(|place| {
            env.refinements
                .options
                .get(&place)
                .is_some_and(|fact| fact.invalidated.is_none() && fact.is_none)
        })
    }

    pub(super) fn assumption(&mut self, env: &mut Env, condition: &Condition, truth: bool) {
        match condition {
            Condition::Expr(expr) => self.relate(env, *expr, truth),
            Condition::Binding { pattern, value, .. } => {
                if truth {
                    self.seed_pattern_proofs(env, *pattern, *value);
                } else {
                    self.negate_pattern_proofs(env, *pattern, *value);
                }
            }
        }
    }

    pub(super) fn relate(&mut self, env: &mut Env, test: ExprId, truth: bool) {
        self.relate_option(env, test, truth);
        self.relate_proofs(env, test, truth);
    }

    fn relate_option(&mut self, env: &mut Env, test: ExprId, truth: bool) {
        let ast = self.ast(env.file);
        let node = ast.expr(test);
        match &node.value {
            Expr::Unary { op, value } if op.value == "!" => {
                self.relate_option(env, *value, !truth);
            }
            Expr::Binary { op, left, right }
                if op.value == "&&" && truth || op.value == "||" && !truth =>
            {
                self.relate_option(env, *left, truth);
                self.relate_option(env, *right, truth);
            }
            Expr::Binary { op, left, right } if matches!(op.value.as_str(), "==" | "!=") => {
                let compared = if self.is_none(env, *left) {
                    *right
                } else if self.is_none(env, *right) {
                    *left
                } else {
                    return;
                };
                let span = ast.expr(compared).span;
                if self
                    .types
                    .get(&span)
                    .is_some_and(|ty| ty.is_option(self.hir))
                    && let Some(place) = self.place(env, compared)
                {
                    let non_none =
                        matches!((op.value.as_str(), truth), ("==", false) | ("!=", true));
                    if non_none {
                        if env
                            .refinements
                            .options
                            .get(&place)
                            .is_some_and(|f| f.invalidated.is_none() && f.is_none)
                        {
                            env.refinements.dbm.unsat = true;
                        }
                        let depth = env
                            .refinements
                            .options
                            .get(&place)
                            .filter(|f| f.invalidated.is_none())
                            .map_or(1, |f| f.depth + 1);
                        env.refinements.options.insert(
                            place,
                            Fact {
                                depth,
                                is_none: false,
                                invalidated: None,
                            },
                        );
                    } else {
                        if env
                            .refinements
                            .options
                            .get(&place)
                            .is_some_and(|f| f.invalidated.is_none() && f.depth > 0)
                        {
                            env.refinements.dbm.unsat = true;
                        }
                        let depth = env
                            .refinements
                            .options
                            .get(&place)
                            .filter(|f| f.invalidated.is_none())
                            .map_or(0, |f| f.depth);
                        env.refinements.options.insert(
                            place,
                            Fact {
                                depth,
                                is_none: true,
                                invalidated: None,
                            },
                        );
                    }
                }
            }
            _ => {}
        }
    }

    // -------------------------------------------------------------------------
    // DBM-Powered Symbolic Proof Engine
    // -------------------------------------------------------------------------

    pub(super) fn static_constant_value(&self, id: DefinitionId) -> Option<&Value> {
        let def = self.hir.definition(id);
        let stmt = def.stmt?;
        let ast = self.ast(def.name.span.file);
        if let StmtKind::Binding {
            value: Some(expr), ..
        } = &ast.stmt(stmt).value.kind
        {
            let span = ast.expr(*expr).span;
            return self.static_values.get(&span);
        }
        None
    }

    pub(super) fn const_int(&self, env: &Env, expr: ExprId) -> Option<i128> {
        self.const_int_in_dbm(env, &env.refinements.dbm, expr)
    }

    pub(super) fn const_int_in_dbm(&self, env: &Env, dbm: &Dbm, expr: ExprId) -> Option<i128> {
        let ast = self.ast(env.file);
        if let Some(n) = self.literal_integer(env, expr) {
            return n.to_i128();
        }
        let span = ast.expr(expr).span;
        if let Some(Value::Int(n)) = self.static_values.get(&span) {
            return n.to_i128();
        }
        if let Some(place) = self.resolve_place(env, expr) {
            if let Some(c) = dbm.exact(&Atom::Val(place.clone())) {
                return Some(c);
            }
            if place.path.is_empty()
                && let Some(Value::Int(n)) = self.static_constant_value(place.root)
            {
                return n.to_i128();
            }
        }
        None
    }

    pub(super) fn is_int_expr(&self, env: &Env, expr: ExprId) -> bool {
        let ast = self.ast(env.file);
        let span = ast.expr(expr).span;
        if let Some(ty) = self.types.get(&span) {
            return matches!(self.normalize(ty), Ty::Int);
        }
        // During pre-typecheck loop abstract interpretation, structurally verify integer type
        // (never treat `f64`, `str`, or unresolved expressions as `int`).
        match &ast.expr(expr).value {
            Expr::Literal(lit) => matches!(super::literal(lit), Ok(Value::Int(_))),
            Expr::Path(path) => self
                .resolve(path.span)
                .and_then(|id| self.bindings.get(&id))
                .is_some_and(|ty| matches!(self.normalize(ty), Ty::Int)),
            Expr::Call { callee, .. } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                {
                    if self.hir.intrinsic(id) == Some(Intrinsic::Len) {
                        return true;
                    }
                    return self
                        .callables
                        .get(&id)
                        .is_some_and(|sig| matches!(self.normalize(&sig.result), Ty::Int));
                }
                false
            }
            Expr::Unary { op, value } if op.value == "-" => self.is_int_expr(env, *value),
            Expr::Binary { op, left, right }
                if matches!(op.value.as_str(), "+" | "-" | "*" | "/" | "%") =>
            {
                self.is_int_expr(env, *left) && self.is_int_expr(env, *right)
            }
            _ => false,
        }
    }

    pub(super) fn key_expr_to_atom(&self, env: &Env, dbm: &mut Dbm, expr: ExprId) -> Option<Atom> {
        let ast = self.ast(env.file);
        if let Some(p) = self.resolve_place(env, expr) {
            return Some(Atom::Val(p));
        }
        let span = ast.expr(expr).span;
        if let Some(val) = self.static_values.get(&span) {
            match val {
                Value::Int(n) => return n.to_i128().map(|c| Atom::KeyConst(KeyConst::Int(c))),
                Value::Str(s) => return Some(Atom::KeyConst(KeyConst::Str(s.clone()))),
                Value::Bool(b) => return Some(Atom::KeyConst(KeyConst::Bool(*b))),
                Value::Bytes(b) => return Some(Atom::KeyConst(KeyConst::Bytes(b.clone()))),
                Value::Unit => return Some(Atom::KeyConst(KeyConst::Unit)),
                _ => {}
            }
        }
        match &ast.expr(expr).value {
            Expr::Unit => return Some(Atom::KeyConst(KeyConst::Unit)),
            Expr::Literal(lit) => match super::literal(lit).ok()? {
                Value::Int(n) => return n.to_i128().map(|c| Atom::KeyConst(KeyConst::Int(c))),
                Value::Str(s) => return Some(Atom::KeyConst(KeyConst::Str(s))),
                Value::Bool(b) => return Some(Atom::KeyConst(KeyConst::Bool(b))),
                Value::Bytes(b) => return Some(Atom::KeyConst(KeyConst::Bytes(b))),
                _ => return None,
            },
            Expr::Unary { op, value } if op.value == "-" => {
                if let Some(Atom::KeyConst(KeyConst::Int(c))) =
                    self.key_expr_to_atom(env, dbm, *value)
                {
                    return c.checked_neg().map(|nc| Atom::KeyConst(KeyConst::Int(nc)));
                }
            }
            _ => {}
        }
        if self.is_int_expr(env, expr) {
            if let Some(c) = self.const_int_in_dbm(env, dbm, expr) {
                return Some(Atom::KeyConst(KeyConst::Int(c)));
            }
            return Some(self.expr_to_atom(env, dbm, expr));
        }
        None
    }

    pub(super) fn ty_contains_f64(&self, env: &Env, ty: &Ty) -> bool {
        let mut seen = HashSet::new();
        self.ty_contains_f64_rec(env, ty, &mut seen)
    }

    fn ty_contains_f64_rec(&self, env: &Env, ty: &Ty, seen: &mut HashSet<DefinitionId>) -> bool {
        match self.normalize(ty) {
            Ty::F64 => true,
            Ty::Param(id) => env
                .domains
                .get(&id)
                .is_none_or(|dom| dom.iter().any(|t| self.ty_contains_f64_rec(env, t, seen))),
            Ty::Tuple(items) => items
                .iter()
                .any(|m| self.ty_contains_f64_rec(env, &m.ty, seen)),
            Ty::Record(fields, _) => fields
                .values()
                .any(|m| self.ty_contains_f64_rec(env, &m.ty, seen)),
            Ty::Array(item) => self.ty_contains_f64_rec(env, &item.ty, seen),
            Ty::Map(k, v) => {
                self.ty_contains_f64_rec(env, &k, seen)
                    || self.ty_contains_f64_rec(env, &v.ty, seen)
            }
            Ty::Draft(inner) => self.ty_contains_f64_rec(env, &inner, seen),
            Ty::Adt(adt) if seen.insert(adt.definition) => {
                let res = adt.arguments.iter().any(|arg| match arg {
                    super::GenericValue::Type(t) => self.ty_contains_f64_rec(env, t, seen),
                    _ => false,
                }) || self
                    .nominal_layouts
                    .get(&adt.definition)
                    .is_some_and(|rep| self.ty_contains_f64_rec(env, rep, seen));
                seen.remove(&adt.definition);
                res
            }
            _ => false,
        }
    }

    fn container_key_contains_f64(&self, env: &Env, container_expr: ExprId) -> bool {
        let span = self.ast(env.file).expr(container_expr).span;
        let ty = self.types.get(&span).cloned().or_else(|| {
            self.resolve_local(env, container_expr)
                .and_then(|id| self.bindings.get(&id).cloned())
        });
        let Some(ty) = ty else {
            return true;
        };
        let mut norm = self.normalize(&ty);
        if let Ty::Draft(inner) = norm {
            norm = self.normalize(&inner);
        }
        if let Some(elem) = norm.as_set(self.hir) {
            return self.ty_contains_f64(env, elem);
        }
        match norm {
            Ty::Map(k, _) => self.ty_contains_f64(env, &k),
            _ => true,
        }
    }

    fn is_map_indexed_write(&self, env: &Env, expr: ExprId) -> Option<(ExprId, ExprId)> {
        let ast = self.ast(env.file);
        let Expr::Index {
            base,
            index,
            safe: false,
        } = &ast.expr(expr).value
        else {
            return None;
        };
        let base_span = ast.expr(*base).span;
        let base_ty = self.types.get(&base_span).cloned().or_else(|| {
            self.resolve_local(env, *base)
                .and_then(|id| self.bindings.get(&id).cloned())
        })?;
        let mut norm = self.normalize(&base_ty);
        if let Ty::Draft(inner) = norm {
            norm = self.normalize(&inner);
        }
        matches!(norm, Ty::Map(..)).then_some((*base, *index))
    }

    fn is_map_safe_index(&self, env: &Env, expr: ExprId) -> Option<(ExprId, ExprId)> {
        let ast = self.ast(env.file);
        let Expr::Index {
            base,
            index,
            safe: true,
        } = &ast.expr(expr).value
        else {
            return None;
        };
        let base_span = ast.expr(*base).span;
        let base_ty = self.types.get(&base_span).cloned().or_else(|| {
            self.resolve_local(env, *base)
                .and_then(|id| self.bindings.get(&id).cloned())
        })?;
        let mut norm = self.normalize(&base_ty);
        if let Ty::Draft(inner) = norm {
            norm = self.normalize(&inner);
        }
        matches!(norm, Ty::Map(..)).then_some((*base, *index))
    }

    pub(super) fn is_set_stdlib_callee(&self, id: DefinitionId, name: &str) -> bool {
        let def = self.hir.definition(id);
        self.hir.is_stdlib_file(def.name.span.file)
            && self.hir.primitive_module(id) == Some("Set")
            && def.name.value == name
    }

    pub(super) fn is_map_clear_callee(&self, id: DefinitionId) -> bool {
        let def = self.hir.definition(id);
        self.hir.is_stdlib_file(def.name.span.file)
            && self.hir.primitive_module(id) == Some("Map")
            && def.name.value == "clear"
    }

    fn lower_expr_to_lin(&self, env: &Env, dbm: &Dbm, expr: ExprId) -> Option<LinExpr<Atom>> {
        if !self.is_int_expr(env, expr) {
            return None;
        }
        if let Some(c) = self.const_int_in_dbm(env, dbm, expr) {
            return Some(LinExpr::Const(c));
        }
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && self.hir.intrinsic(id) == Some(Intrinsic::Len)
                    && let [arg] = args.as_slice()
                {
                    if let Some(p) = self.resolve_place(env, arg.value) {
                        return Some(LinExpr::Pos {
                            atom: Atom::Len(p),
                            offset: 0,
                        });
                    }
                    if let Some(n) = self.literal_collection_len(env, arg.value) {
                        return Some(LinExpr::Const(n as i128));
                    }
                }
                if let Some(p) = self.resolve_place(env, expr) {
                    return Some(LinExpr::Pos {
                        atom: Atom::Val(p),
                        offset: 0,
                    });
                }
                None
            }
            Expr::Path(_) | Expr::Member { safe: false, .. } => {
                let p = self.resolve_place(env, expr)?;
                Some(LinExpr::Pos {
                    atom: Atom::Val(p),
                    offset: 0,
                })
            }
            Expr::Unary { op, value } if op.value == "-" => {
                self.lower_expr_to_lin(env, dbm, *value)?.neg()
            }
            Expr::Binary { op, left, right } if matches!(op.value.as_str(), "+" | "-") => {
                let l = self.lower_expr_to_lin(env, dbm, *left)?;
                let r = self.lower_expr_to_lin(env, dbm, *right)?;
                if op.value == "+" {
                    if let Some(sum) = l.clone().add(r.clone()) {
                        return Some(sum);
                    }
                    if let (
                        LinExpr::Pos {
                            atom: a,
                            offset: oa,
                        },
                        LinExpr::Pos {
                            atom: b,
                            offset: ob,
                        },
                    ) = (l, r)
                        && let Some((hi, bonus)) = dbm.find_diff_eq_sum(&a, &b)
                        && let Some(offset) = oa.checked_add(ob).and_then(|s| s.checked_add(bonus))
                    {
                        return Some(LinExpr::Pos { atom: hi, offset });
                    }
                    None
                } else {
                    l.sub(r)
                }
            }
            _ => None,
        }
    }

    pub(super) fn relate_proofs(&self, env: &mut Env, test: ExprId, truth: bool) {
        let mut dbm = std::mem::take(&mut env.refinements.dbm);
        self.relate_proofs_in_dbm(env, &mut dbm, test, truth);
        env.refinements.dbm = dbm;
    }

    fn relate_proofs_in_dbm(&self, env: &Env, dbm: &mut Dbm, test: ExprId, truth: bool) {
        let ast = self.ast(env.file);
        match &ast.expr(test).value {
            Expr::Literal(lit) => {
                if let Ok(Value::Bool(b)) = super::literal(lit)
                    && b != truth
                {
                    dbm.unsat = true;
                }
            }
            Expr::Path(_) | Expr::Member { safe: false, .. } => {
                let span = ast.expr(test).span;
                let is_bool = self
                    .types
                    .get(&span)
                    .is_some_and(|t| matches!(self.normalize(t), Ty::Bool));
                if is_bool && let Some(p) = self.resolve_place(env, test) {
                    dbm.add_bool(p, truth);
                }
            }
            Expr::Unary { op, value } if op.value == "!" => {
                self.relate_proofs_in_dbm(env, dbm, *value, !truth);
            }
            Expr::Binary { op, left, right }
                if (op.value == "&&" && truth) || (op.value == "||" && !truth) =>
            {
                self.relate_proofs_in_dbm(env, dbm, *left, truth);
                // Soundness: if `right` mutates any variable/collection, drop invalidated `left` facts before `right`.
                let mut mutated_vars = HashSet::new();
                let mut resized_colls = HashSet::new();
                let mut has_open = false;
                self.collect_loop_mutations(
                    env,
                    *right,
                    &mut mutated_vars,
                    &mut resized_colls,
                    &mut has_open,
                );
                for var in mutated_vars {
                    dbm.forget_matching(|a| matches!(a, Atom::Val(p) if p.root == var));
                }
                for coll in resized_colls {
                    dbm.forget_matching(
                        |a| matches!(a, Atom::Len(p) | Atom::Val(p) if p.root == coll),
                    );
                }
                if has_open {
                    dbm.forget_matching(|a| match a {
                        Atom::Val(p) | Atom::Len(p) => {
                            self.live.contains(&p.root)
                                && !(p.path.is_empty() && self.confined_locals.contains(&p.root))
                        }
                        _ => false,
                    });
                }
                self.relate_proofs_in_dbm(env, dbm, *right, truth);
            }
            Expr::Binary { op, left, right }
                if (op.value == "||" && truth) || (op.value == "&&" && !truth) =>
            {
                let mut left_dbm = dbm.clone();
                let mut right_dbm = dbm.clone();
                self.relate_proofs_in_dbm(env, &mut left_dbm, *left, truth);
                self.relate_proofs_in_dbm(env, &mut right_dbm, *right, truth);
                *dbm = Dbm::join(&left_dbm, &right_dbm);
            }
            Expr::Call { callee, args } => {
                // Proof-carrying boolean return (`Reflects(P)` / `Implies(P)`).
                if let Some(proofs) = env.refinements.call_proofs.get(&test) {
                    for cp in proofs {
                        if cp.is_payload {
                            continue;
                        }
                        let should_apply = match cp.kind {
                            super::proofs::ProofKind::Reflects => true,
                            super::proofs::ProofKind::Implies => truth,
                            _ => false,
                        };
                        if should_apply
                            && let Some(pred) = cp.pred.map_atoms(&mut |ra| match ra {
                                ReturnAtom::Caller(a) => Some(a.clone()),
                                _ => None,
                            })
                        {
                            let effective = if truth { pred } else { pred.negate() };
                            dbm.assume(&effective);
                        }
                    }
                }
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && (matches!(
                        self.hir.intrinsic(id),
                        Some(Intrinsic::HasKey | Intrinsic::MapContains)
                    ) || self.is_set_stdlib_callee(id, "contains"))
                    && let [c_arg, k_arg] = args.as_slice()
                    && let Some(c_place) = self.resolve_place(env, c_arg.value)
                    && let Some(k_atom) = self.key_expr_to_atom(env, dbm, k_arg.value)
                {
                    if truth {
                        dbm.add_contains(Atom::Val(c_place), k_atom);
                    } else {
                        dbm.add_not_contains(Atom::Val(c_place), k_atom);
                    }
                }
            }
            Expr::Binary { op, left, right }
                if matches!(op.value.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") =>
            {
                // Handle `m?[k] != None` / `m?[k] == None` membership tests.
                if matches!(op.value.as_str(), "==" | "!=") {
                    let compared = if self.is_none(env, *left) {
                        Some(*right)
                    } else if self.is_none(env, *right) {
                        Some(*left)
                    } else {
                        None
                    };
                    if let Some(cmp_expr) = compared
                        && let Some((base, index)) = self.is_map_safe_index(env, cmp_expr)
                        && let Some(c_place) = self.resolve_place(env, base)
                        && let Some(k_atom) = self.key_expr_to_atom(env, dbm, index)
                    {
                        let non_none =
                            matches!((op.value.as_str(), truth), ("==", false) | ("!=", true));
                        if non_none {
                            dbm.add_contains(Atom::Val(c_place), k_atom);
                        } else {
                            dbm.add_not_contains(Atom::Val(c_place), k_atom);
                        }
                        return;
                    }
                    // Handle `cond == true` / `cond == false` / `cond != true` / `cond != false`.
                    let bool_lit = |e: ExprId| -> Option<bool> {
                        if let Expr::Literal(lit) = &ast.expr(e).value
                            && let Ok(Value::Bool(b)) = super::literal(lit)
                        {
                            Some(b)
                        } else {
                            None
                        }
                    };
                    if let Some(b) = bool_lit(*right) {
                        let eff = (op.value == "==") == truth;
                        self.relate_proofs_in_dbm(env, dbm, *left, if eff { b } else { !b });
                        return;
                    }
                    if let Some(b) = bool_lit(*left) {
                        let eff = (op.value == "==") == truth;
                        self.relate_proofs_in_dbm(env, dbm, *right, if eff { b } else { !b });
                        return;
                    }
                }
                if !self.is_int_expr(env, *left) || !self.is_int_expr(env, *right) {
                    return;
                }
                let effective = match (op.value.as_str(), truth) {
                    (s, true) => s,
                    ("==", false) => "!=",
                    ("!=", false) => "==",
                    ("<", false) => ">=",
                    ("<=", false) => ">",
                    (">", false) => "<=",
                    (">=", false) => "<",
                    _ => return,
                };
                if let (Some(l), Some(r)) = (
                    self.lower_expr_to_lin(env, dbm, *left),
                    self.lower_expr_to_lin(env, dbm, *right),
                ) && let Some(pred) = LinExpr::compare(effective, l, r)
                {
                    dbm.assume(&pred);
                }
                // Always also check non-difference `a + b <= c` comparisons so `sum_le` is recorded
                // even when one operand happens to equal `0` on the first loop iteration!
                self.relate_non_diff_comparison(env, dbm, effective, *left, *right);
            }
            _ => {}
        }
    }

    fn relate_non_diff_comparison(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        op: &str,
        left: ExprId,
        right: ExprId,
    ) {
        let ast = self.ast(env.file);
        // Handle `a + b <= rhs` / `a + b < rhs` when `b` has a known lower bound (e.g., `i + m <= n` in String::split!).
        if let Expr::Binary {
            op: bop,
            left: a,
            right: b,
        } = &ast.expr(left).value
            && bop.value == "+"
            && matches!(op, "<=" | "<" | "==")
            && let Some(rhs_lin) = self.lower_expr_to_lin(env, dbm, right)
        {
            let a_at = self
                .resolve_place(env, *a)
                .map(Atom::Val)
                .unwrap_or_else(|| self.expr_to_atom(env, dbm, *a));
            let b_at = self
                .resolve_place(env, *b)
                .map(Atom::Val)
                .unwrap_or_else(|| self.expr_to_atom(env, dbm, *b));
            let c_at = self
                .resolve_place(env, right)
                .map(Atom::Val)
                .unwrap_or_else(|| self.expr_to_atom(env, dbm, right));
            if !matches!(a_at, Atom::Temp(_) | Atom::Zero)
                && !matches!(b_at, Atom::Temp(_) | Atom::Zero)
                && !matches!(c_at, Atom::Temp(_) | Atom::Zero)
            {
                dbm.add_sum_le(a_at, b_at, c_at, if op == "<" { -1 } else { 0 });
            }
            for &(x, y) in &[(*a, *b), (*b, *a)] {
                if let Some(x_lin) = self.lower_expr_to_lin(env, dbm, x) {
                    let y_t = dbm.fresh_temp();
                    self.constrain_expr(env, dbm, &y_t, y);
                    let y_lb = dbm.lb(&y_t);
                    dbm.project_out(|at| *at == y_t);
                    if let Some(lb) = y_lb
                        && let Some(shifted) = x_lin.add(LinExpr::Const(lb))
                    {
                        let cmp_op = if op == "==" { "<=" } else { op };
                        if let Some(pred) = LinExpr::compare(cmp_op, shifted, rhs_lin.clone()) {
                            dbm.assume(&pred);
                        }
                    }
                }
            }
        }
        // Symmetric: `lhs >= a + b` / `lhs > a + b`.
        if matches!(op, ">=" | ">" | "==") {
            let flipped = match op {
                ">=" => "<=",
                ">" => "<",
                _ => "==",
            };
            if let Expr::Binary { op: bop, .. } = &ast.expr(right).value
                && bop.value == "+"
            {
                self.relate_non_diff_comparison(env, dbm, flipped, right, left);
            }
        }
    }

    // -------------------------------------------------------------------------
    // O(1) Expression Transfer Lemmas into DBM
    // -------------------------------------------------------------------------

    pub(super) fn constrain_expr(&self, env: &Env, dbm: &mut Dbm, target: &Atom, expr: ExprId) {
        if dbm.unsat {
            return;
        }
        // 1. Exact constant.
        if let Some(c) = self.const_int_in_dbm(env, dbm, expr) {
            dbm.add_eq(target.clone(), Atom::Zero, c);
            return;
        }
        // 2. Direct Place.
        if let Some(place) = self.resolve_place(env, expr) {
            dbm.add_eq(target.clone(), Atom::Val(place), 0);
            if let Expr::Index {
                base, safe: false, ..
            } = &self.ast(env.file).expr(expr).value
            {
                let base_ty = self
                    .types
                    .get(&self.ast(env.file).expr(*base).span)
                    .cloned()
                    .or_else(|| {
                        self.resolve_local(env, *base)
                            .and_then(|id| self.bindings.get(&id).cloned())
                    });
                if base_ty.is_some_and(|t| self.normalize(&t) == Ty::Bytes) {
                    dbm.add_le(Atom::Zero, target.clone(), 0);
                    dbm.add_le(target.clone(), Atom::Zero, 255);
                }
            }
            return;
        }
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Call { callee, args } => {
                // `len(x)`
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && self.hir.intrinsic(id) == Some(Intrinsic::Len)
                    && let [arg] = args.as_slice()
                {
                    self.constrain_len_expr(env, dbm, target, arg.value);
                    return;
                }
                // Inline call return proofs (e.g., `xs[lower_bound(xs, t)]`, `10 / abs_pos()`).
                if let Some(proofs) = env.refinements.call_proofs.get(&expr) {
                    for cp in proofs {
                        if cp.is_payload {
                            continue;
                        }
                        if let Some(pred) = cp.pred.map_atoms(&mut |ra| match ra {
                            ReturnAtom::SubjectVal(p) if p.is_empty() => Some(target.clone()),
                            ReturnAtom::Caller(a) => Some(a.clone()),
                            _ => None,
                        }) {
                            dbm.assume(&pred);
                        }
                    }
                }
            }
            Expr::Unary { op, value } if op.value == "-" => {
                let a = self.expr_to_atom(env, dbm, *value);
                if let Some(lo) = dbm.lb(&a)
                    && let Some(neg_lo) = lo.checked_neg()
                {
                    dbm.add_le(target.clone(), Atom::Zero, neg_lo);
                }
                if let Some(hi) = dbm.ub(&a)
                    && let Some(neg_hi) = hi.checked_neg()
                {
                    dbm.add_le(Atom::Zero, target.clone(), hi);
                    let _ = neg_hi;
                }
                if dbm.is_nonzero(&a) {
                    dbm.add_ne(target.clone(), Atom::Zero, 0);
                }
            }
            Expr::Binary { op, left, right } => match op.value.as_str() {
                "+" => {
                    // Check Convex Midpoint Lemma A: `lo + (hi - lo) / k` or `(hi - lo) / k + lo` (k >= 2).
                    if self.try_convex_midpoint_add(env, dbm, target, *left, *right)
                        || self.try_convex_midpoint_add(env, dbm, target, *right, *left)
                    {
                        return;
                    }
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if let Some(cb) = dbm.exact(&b) {
                        dbm.add_eq(target.clone(), a.clone(), cb);
                    } else if let Some(ca) = dbm.exact(&a) {
                        dbm.add_eq(target.clone(), b.clone(), ca);
                    } else {
                        if let Some(lb_b) = dbm.lb(&b)
                            && let Some(neg) = lb_b.checked_neg()
                        {
                            // target >= a + lb(b)  <=>  a - target <= -lb(b)
                            dbm.add_le(a.clone(), target.clone(), neg);
                        }
                        if let Some(ub_b) = dbm.ub(&b) {
                            // target <= a + ub(b)  <=>  target - a <= ub(b)
                            dbm.add_le(target.clone(), a.clone(), ub_b);
                        }
                        if let Some(lb_a) = dbm.lb(&a)
                            && let Some(neg) = lb_a.checked_neg()
                        {
                            dbm.add_le(b.clone(), target.clone(), neg);
                        }
                        if let Some(ub_a) = dbm.ub(&a) {
                            dbm.add_le(target.clone(), b.clone(), ub_a);
                        }
                        if let (Some(la), Some(lb)) = (dbm.lb(&a), dbm.lb(&b))
                            && let Some(sum) = la.checked_add(lb)
                            && let Some(neg) = sum.checked_neg()
                        {
                            dbm.add_le(Atom::Zero, target.clone(), neg);
                        }
                        if let (Some(ua), Some(ub)) = (dbm.ub(&a), dbm.ub(&b))
                            && let Some(sum) = ua.checked_add(ub)
                        {
                            dbm.add_le(target.clone(), Atom::Zero, sum);
                        }
                        for (rhs_atom, k) in dbm.sum_upper_bounds(&a, &b) {
                            dbm.add_le(target.clone(), rhs_atom, k);
                        }
                        if let Some((hi_atom, bonus)) = dbm.find_diff_eq_sum(&a, &b) {
                            dbm.add_eq(target.clone(), hi_atom, bonus);
                        }
                    }
                }
                "-" => {
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if let Some(cb) = dbm.exact(&b)
                        && let Some(neg_cb) = cb.checked_neg()
                    {
                        dbm.add_eq(target.clone(), a.clone(), neg_cb);
                    } else {
                        // Direct difference bounds from closed matrix: `a - b <= diff_ub(a, b)` & `b - a <= diff_ub(b, a)`!
                        if let Some(du) = dbm.diff_ub(&a, &b) {
                            dbm.add_le(target.clone(), Atom::Zero, du);
                        }
                        if let Some(dl) = dbm.diff_ub(&b, &a) {
                            // b - a <= dl => -(a - b) <= dl => 0 - target <= dl
                            dbm.add_le(Atom::Zero, target.clone(), dl);
                        }
                        if let Some(lb_b) = dbm.lb(&b)
                            && let Some(neg) = lb_b.checked_neg()
                        {
                            // target <= a - lb(b)  <=>  target - a <= -lb(b)
                            dbm.add_le(target.clone(), a.clone(), neg);
                        }
                        if let Some(ub_b) = dbm.ub(&b) {
                            // target >= a - ub(b)  <=>  a - target <= ub(b)
                            dbm.add_le(a.clone(), target.clone(), ub_b);
                        }
                        dbm.add_diff_eq(target.clone(), a, b, 0);
                    }
                }
                "*" => {
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if dbm.is_pos(&a) && dbm.is_pos(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), -1);
                        dbm.add_le(a.clone(), target.clone(), 0);
                        dbm.add_le(b.clone(), target.clone(), 0);
                    } else if dbm.is_nonneg(&a) && dbm.is_nonneg(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                    }
                    if dbm.is_nonzero(&a) && dbm.is_nonzero(&b) {
                        dbm.add_ne(target.clone(), Atom::Zero, 0);
                    }
                    if let (Some(la), Some(ua), Some(lb), Some(ub)) =
                        (dbm.lb(&a), dbm.ub(&a), dbm.lb(&b), dbm.ub(&b))
                        && let (Some(p1), Some(p2), Some(p3), Some(p4)) = (
                            la.checked_mul(lb),
                            la.checked_mul(ub),
                            ua.checked_mul(lb),
                            ua.checked_mul(ub),
                        )
                    {
                        let min_p = p1.min(p2).min(p3).min(p4);
                        let max_p = p1.max(p2).max(p3).max(p4);
                        if let Some(neg) = min_p.checked_neg() {
                            dbm.add_le(Atom::Zero, target.clone(), neg);
                        }
                        dbm.add_le(target.clone(), Atom::Zero, max_p);
                    }
                }
                "/" => {
                    // Check Convex Midpoint Lemma B: `(lo + hi) / 2` when `0 <= lo <= hi`.
                    if self.try_convex_midpoint_div(env, dbm, target, *left, *right) {
                        return;
                    }
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if dbm.is_nonneg(&a) && dbm.is_pos(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                        dbm.add_le(target.clone(), a.clone(), 0);
                        if dbm.is_pos(&a) && dbm.lb(&b).is_some_and(|k| k >= 2) {
                            // a >= 1, b >= 2 => a / b <= a - 1
                            dbm.add_le(target.clone(), a.clone(), -1);
                        }
                        if dbm.entails_le(&b, &a, 0) {
                            // a >= b > 0 => a / b >= 1
                            dbm.add_le(Atom::Zero, target.clone(), -1);
                        }
                    }
                }
                "%" => {
                    // Non-negative Modulo Lemma: `a >= 0 && b > 0 => 0 <= a % b < b && a % b <= a`.
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if dbm.is_nonneg(&a) && dbm.is_pos(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                        dbm.add_le(target.clone(), b, -1);
                        dbm.add_le(target.clone(), a, 0);
                    }
                }
                "&" => {
                    // Two's-complement BigInt bitwise AND: if either operand is >= 0,
                    // its infinite sign-bit prefix is 0, so `0 <= (a & b) <= nonneg_operand`.
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if dbm.is_nonneg(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                        dbm.add_le(target.clone(), b.clone(), 0);
                    }
                    if dbm.is_nonneg(&a) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                        dbm.add_le(target.clone(), a, 0);
                    }
                }
                "|" | "^" => {
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if dbm.is_nonneg(&a) && dbm.is_nonneg(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                    }
                }
                ">>" => {
                    // Arithmetic right shift on non-negative `a` with `b >= 0`: `0 <= (a >> b) <= a`.
                    let a = self
                        .resolve_place(env, *left)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *left));
                    let b = self
                        .resolve_place(env, *right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, *right));
                    if dbm.is_nonneg(&a) && dbm.is_nonneg(&b) {
                        dbm.add_le(Atom::Zero, target.clone(), 0);
                        dbm.add_le(target.clone(), a.clone(), 0);
                        if dbm.is_pos(&a) && dbm.is_pos(&b) {
                            dbm.add_le(target.clone(), a.clone(), -1);
                        }
                        if let (Some(ua), Some(lb)) = (dbm.ub(&a), dbm.lb(&b))
                            && ua >= 0
                            && lb >= 0
                        {
                            let shifted = if lb >= 127 { 0 } else { ua >> (lb as u32) };
                            dbm.add_le(target.clone(), Atom::Zero, shifted);
                        }
                    }
                }
                _ => {}
            },
            Expr::Index {
                base, safe: false, ..
            } => {
                if self
                    .types
                    .get(&ast.expr(*base).span)
                    .is_some_and(|t| self.normalize(t) == Ty::Bytes)
                {
                    dbm.add_le(Atom::Zero, target.clone(), 0);
                    dbm.add_le(target.clone(), Atom::Zero, 255);
                }
            }
            Expr::Block { statements, .. } => {
                if let Some(&last) = statements.last()
                    && let StmtKind::Expr(tail) = ast.stmt(last).value.kind
                {
                    self.constrain_expr(env, dbm, target, tail);
                }
            }
            _ => {}
        }
    }

    /// Convex Midpoint Lemma A: `lo + (hi - lo) / k` with constant `k >= 2`:
    /// `lo <= hi => lo <= target <= hi`, and `lo < hi => lo <= target <= hi - 1`.
    fn try_convex_midpoint_add(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        target: &Atom,
        lo_expr: ExprId,
        div_expr: ExprId,
    ) -> bool {
        let ast = self.ast(env.file);
        let Expr::Binary {
            op,
            left: diff_expr,
            right: denom_expr,
        } = &ast.expr(div_expr).value
        else {
            return false;
        };
        if op.value != "/" {
            return false;
        }
        let Some(k) = self.const_int_in_dbm(env, dbm, *denom_expr) else {
            return false;
        };
        if k < 2 {
            return false;
        }
        let Expr::Binary {
            op: sub_op,
            left: hi_expr,
            right: lo_expr2,
        } = &ast.expr(*diff_expr).value
        else {
            return false;
        };
        if sub_op.value != "-" {
            return false;
        }
        let lo = self.expr_to_atom(env, dbm, lo_expr);
        let lo2 = self.expr_to_atom(env, dbm, *lo_expr2);
        if !(lo == lo2 || (dbm.entails_le(&lo, &lo2, 0) && dbm.entails_le(&lo2, &lo, 0))) {
            return false;
        }
        let hi = self.expr_to_atom(env, dbm, *hi_expr);
        if !dbm.entails_le(&lo, &hi, 0) {
            return false;
        }
        // lo <= target
        dbm.add_le(lo.clone(), target.clone(), 0);
        if dbm.entails_le(&lo, &hi, -1) {
            // lo < hi => target <= hi - 1
            dbm.add_le(target.clone(), hi, -1);
        } else {
            // lo <= hi => target <= hi
            dbm.add_le(target.clone(), hi, 0);
        }
        true
    }

    /// Convex Midpoint Lemma B: `(lo + hi) / 2` when `0 <= lo <= hi` (or `0 <= hi <= lo`).
    fn try_convex_midpoint_div(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        target: &Atom,
        sum_expr: ExprId,
        denom_expr: ExprId,
    ) -> bool {
        if self.const_int_in_dbm(env, dbm, denom_expr) != Some(2) {
            return false;
        }
        let Expr::Binary { op, left, right } = &self.ast(env.file).expr(sum_expr).value else {
            return false;
        };
        if op.value != "+" {
            return false;
        }
        let a = self.expr_to_atom(env, dbm, *left);
        let b = self.expr_to_atom(env, dbm, *right);
        if !dbm.is_nonneg(&a) || !dbm.is_nonneg(&b) {
            return false;
        }
        let (lo, hi) = if dbm.entails_le(&a, &b, 0) {
            (a, b)
        } else if dbm.entails_le(&b, &a, 0) {
            (b, a)
        } else {
            return false;
        };
        dbm.add_le(lo.clone(), target.clone(), 0);
        if dbm.entails_le(&lo, &hi, -1) {
            dbm.add_le(target.clone(), hi, -1);
        } else {
            dbm.add_le(target.clone(), hi, 0);
        }
        true
    }

    pub(super) fn expr_to_atom(&self, env: &Env, dbm: &mut Dbm, expr: ExprId) -> Atom {
        if let Some(c) = self.const_int_in_dbm(env, dbm, expr) {
            if c == 0 {
                return Atom::Zero;
            }
            let t = dbm.fresh_temp();
            dbm.add_eq(t.clone(), Atom::Zero, c);
            return t;
        }
        if let Some(p) = self.resolve_place(env, expr) {
            let a = Atom::Val(p);
            dbm.ensure_atom(a.clone());
            return a;
        }
        if let Expr::Call { callee, args } = &self.ast(env.file).expr(expr).value
            && let Expr::Path(path) = &self.ast(env.file).expr(*callee).value
            && let Some(id) = self.resolve(path.span)
            && self.hir.intrinsic(id) == Some(Intrinsic::Len)
            && let [arg] = args.as_slice()
            && let Some(p) = self.resolve_place(env, arg.value)
        {
            let a = Atom::Len(p);
            dbm.ensure_atom(a.clone());
            return a;
        }
        let t = dbm.fresh_temp();
        self.constrain_expr(env, dbm, &t, expr);
        t
    }

    fn literal_collection_len(&self, env: &Env, expr: ExprId) -> Option<usize> {
        let ast = self.ast(env.file);
        let span = ast.expr(expr).span;
        if let Some(val) = self.static_values.get(&span) {
            match val {
                Value::Str(s) => return Some(s.chars().count()),
                Value::Bytes(b) => return Some(b.len()),
                Value::Array(items) => return Some(items.len()),
                Value::Map(entries) => return Some(entries.len()),
                _ => {}
            }
        }
        match &ast.expr(expr).value {
            Expr::Array(items) => Some(items.len()),
            Expr::Map(entries) if entries.is_empty() => Some(0),
            Expr::Literal(lit) => match super::literal(lit).ok()? {
                Value::Str(s) => Some(s.chars().count()),
                Value::Bytes(b) => Some(b.len()),
                _ => None,
            },
            Expr::Path(path) => {
                let id = self.resolve(path.span)?;
                match self.static_constant_value(id)? {
                    Value::Str(s) => Some(s.chars().count()),
                    Value::Bytes(b) => Some(b.len()),
                    Value::Array(items) => Some(items.len()),
                    Value::Map(entries) => Some(entries.len()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(super) fn constrain_len_expr(&self, env: &Env, dbm: &mut Dbm, target: &Atom, expr: ExprId) {
        if dbm.unsat {
            return;
        }
        dbm.add_le(Atom::Zero, target.clone(), 0);
        if let Some(n) = self.literal_collection_len(env, expr) {
            dbm.add_eq(target.clone(), Atom::Zero, n as i128);
            return;
        }
        if let Some(place) = self.resolve_place(env, expr) {
            dbm.add_eq(target.clone(), Atom::Len(place), 0);
            return;
        }
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Wrap { args, .. } => {
                if let [arg] = args.as_slice() {
                    self.constrain_len_expr(env, dbm, target, arg.value);
                }
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && matches!(
                        self.hir.intrinsic(id),
                        Some(Intrinsic::Clone | Intrinsic::Inner)
                    )
                    && let [arg] = args.as_slice()
                {
                    self.constrain_len_expr(env, dbm, target, arg.value);
                    return;
                }
                if let Some(proofs) = env.refinements.call_proofs.get(&expr) {
                    for cp in proofs {
                        if cp.is_payload {
                            continue;
                        }
                        if let Some(pred) = cp.pred.map_atoms(&mut |ra| match ra {
                            ReturnAtom::SubjectLen(p) if p.is_empty() => Some(target.clone()),
                            ReturnAtom::Caller(a) => Some(a.clone()),
                            _ => None,
                        }) {
                            dbm.assume(&pred);
                        }
                    }
                }
            }
            Expr::Index {
                base,
                index,
                safe: false,
            } => {
                if let Expr::Range {
                    start,
                    end,
                    inclusive,
                } = ast.expr(*index).value
                {
                    self.constrain_slice_len(env, dbm, target, *base, start, end, inclusive, false);
                }
            }
            Expr::Block { statements, .. } => {
                if let Some(&last) = statements.last()
                    && let StmtKind::Expr(tail) = ast.stmt(last).value.kind
                {
                    self.constrain_len_expr(env, dbm, target, tail);
                }
            }
            _ => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn constrain_slice_len(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        target: &Atom,
        base: ExprId,
        start: Option<ExprId>,
        end: Option<ExprId>,
        inclusive: bool,
        assume_valid: bool,
    ) {
        if dbm.unsat {
            return;
        }
        let base_len = if let Some(p) = self.resolve_place(env, base) {
            let a = Atom::Len(p);
            dbm.ensure_atom(a.clone());
            a
        } else if let Some(n) = self.literal_collection_len(env, base) {
            let t = dbm.fresh_temp();
            dbm.add_eq(t.clone(), Atom::Zero, n as i128);
            t
        } else {
            let t = dbm.fresh_temp();
            self.constrain_len_expr(env, dbm, &t, base);
            t
        };
        let lo_atom = match start {
            Some(lo) => self.expr_to_atom(env, dbm, lo),
            None => Atom::Zero,
        };
        let hi_atom = match end {
            Some(hi) => self.expr_to_atom(env, dbm, hi),
            None => base_len.clone(),
        };
        let bonus: i128 = i128::from(inclusive);
        // Soundness guard: only assert slice length equality when bounds are valid in `dbm`
        // (or already validated at runtime by `Some(sub)` unwrap of `xs?[a..b]`).
        // This prevents an ill-typed/out-of-bounds slice from poisoning `dbm.unsat`!
        let valid = if assume_valid {
            dbm.add_le(Atom::Zero, lo_atom.clone(), 0);
            dbm.add_le(lo_atom.clone(), hi_atom.clone(), 0);
            dbm.add_le(
                hi_atom.clone(),
                base_len.clone(),
                if inclusive { -1 } else { 0 },
            );
            !dbm.unsat
        } else {
            dbm.is_nonneg(&lo_atom)
                && dbm.entails_le(&lo_atom, &hi_atom, 0)
                && dbm.entails_le(&hi_atom, &base_len, if inclusive { -1 } else { 0 })
        };
        if !valid {
            return;
        }
        dbm.add_le(target.clone(), base_len.clone(), 0);
        if let (Some(c_lo), Some(c_hi)) = (dbm.exact(&lo_atom), dbm.exact(&hi_atom))
            && let Some(len) = c_hi.checked_sub(c_lo).and_then(|d| d.checked_add(bonus))
            && len >= 0
        {
            dbm.add_eq(target.clone(), Atom::Zero, len);
        } else if lo_atom == Atom::Zero && !inclusive {
            dbm.add_eq(target.clone(), hi_atom.clone(), 0);
        } else if let Some(c_lo) = dbm.exact(&lo_atom)
            && let Some(offset) = bonus.checked_sub(c_lo)
        {
            dbm.add_eq(target.clone(), hi_atom.clone(), offset);
        } else {
            dbm.add_diff_eq(target.clone(), hi_atom.clone(), lo_atom.clone(), bonus);
            if let Some(d_ub) = dbm.diff_ub(&hi_atom, &lo_atom)
                && let Some(u) = d_ub.checked_add(bonus)
            {
                dbm.add_le(target.clone(), Atom::Zero, u);
            }
            if let Some(d_lb) = dbm.diff_ub(&lo_atom, &hi_atom)
                && let Some(l) = d_lb.checked_sub(bonus)
            {
                dbm.add_le(Atom::Zero, target.clone(), l);
            }
        }
    }

    pub(super) fn is_proved_map_index(
        &self,
        env: &Env,
        base_expr: Option<ExprId>,
        key_expr: ExprId,
    ) -> bool {
        if env.refinements.dbm.unsat {
            return true;
        }
        let Some(base_expr) = base_expr else {
            return false;
        };
        let Some(base_place) = self.resolve_place(env, base_expr) else {
            return false;
        };
        let mut scratch = env.refinements.dbm.clone();
        let Some(key_atom) = self.key_expr_to_atom(env, &mut scratch, key_expr) else {
            return false;
        };
        scratch.entails_contains(&Atom::Val(base_place), &key_atom)
    }

    // -------------------------------------------------------------------------
    // Proof Queries (used by `/`, `%`, `<<`, `>>`, `xs[i]`, `s[lo..hi]`)
    // -------------------------------------------------------------------------

    pub(super) fn is_proved_nonzero(&self, env: &Env, expr: ExprId) -> bool {
        let mut scratch = env.refinements.dbm.clone();
        let t = self.expr_to_atom(env, &mut scratch, expr);
        scratch.is_nonzero(&t)
    }

    pub(super) fn is_proved_nonneg(&self, env: &Env, expr: ExprId) -> bool {
        let mut scratch = env.refinements.dbm.clone();
        let t = self.expr_to_atom(env, &mut scratch, expr);
        scratch.is_nonneg(&t)
    }

    pub(super) fn is_proved_index(
        &self,
        env: &Env,
        base_expr: Option<ExprId>,
        index: ExprId,
    ) -> bool {
        let Some(base_expr) = base_expr else {
            return false;
        };
        let mut scratch = env.refinements.dbm.clone();
        let idx = self.expr_to_atom(env, &mut scratch, index);
        if !scratch.is_nonneg(&idx) {
            return false;
        }
        let len_atom = if let Some(n) = self.literal_collection_len(env, base_expr) {
            let t = scratch.fresh_temp();
            scratch.add_eq(t.clone(), Atom::Zero, n as i128);
            t
        } else if let Some(p) = self.resolve_place(env, base_expr) {
            let a = Atom::Len(p);
            scratch.ensure_atom(a.clone());
            a
        } else {
            let t = scratch.fresh_temp();
            self.constrain_len_expr(env, &mut scratch, &t, base_expr);
            t
        };
        scratch.entails_le(&idx, &len_atom, -1)
    }

    pub(super) fn is_proved_slice(
        &self,
        env: &Env,
        base_expr: Option<ExprId>,
        range_expr: ExprId,
    ) -> bool {
        let Some(base_expr) = base_expr else {
            return false;
        };
        let Expr::Range {
            start,
            end,
            inclusive,
        } = self.ast(env.file).expr(range_expr).value
        else {
            return false;
        };
        let mut scratch = env.refinements.dbm.clone();
        let len_atom = if let Some(n) = self.literal_collection_len(env, base_expr) {
            let t = scratch.fresh_temp();
            scratch.add_eq(t.clone(), Atom::Zero, n as i128);
            t
        } else if let Some(p) = self.resolve_place(env, base_expr) {
            let a = Atom::Len(p);
            scratch.ensure_atom(a.clone());
            a
        } else {
            let t = scratch.fresh_temp();
            self.constrain_len_expr(env, &mut scratch, &t, base_expr);
            t
        };
        match (start, end, inclusive) {
            (None, None, false) => true,
            (None, Some(hi), false) => {
                let h = self.expr_to_atom(env, &mut scratch, hi);
                scratch.is_nonneg(&h) && scratch.entails_le(&h, &len_atom, 0)
            }
            (None, Some(hi), true) => {
                let h = self.expr_to_atom(env, &mut scratch, hi);
                scratch.is_nonneg(&h) && scratch.entails_le(&h, &len_atom, -1)
            }
            (Some(lo), None, false) => {
                let l = self.expr_to_atom(env, &mut scratch, lo);
                scratch.is_nonneg(&l) && scratch.entails_le(&l, &len_atom, 0)
            }
            (Some(lo), Some(hi), false) => {
                let l = self.expr_to_atom(env, &mut scratch, lo);
                let h = self.expr_to_atom(env, &mut scratch, hi);
                scratch.is_nonneg(&l)
                    && scratch.entails_le(&l, &h, 0)
                    && scratch.entails_le(&h, &len_atom, 0)
            }
            (Some(lo), Some(hi), true) => {
                let l = self.expr_to_atom(env, &mut scratch, lo);
                let h = self.expr_to_atom(env, &mut scratch, hi);
                scratch.is_nonneg(&l)
                    && scratch.entails_le(&l, &h, 0)
                    && scratch.entails_le(&h, &len_atom, -1)
            }
            _ => false,
        }
    }

    // -------------------------------------------------------------------------
    // Bindings, Patterns, `match` Arms & Runtime Guards
    // -------------------------------------------------------------------------

    pub(super) fn seed_binding_proofs(
        &self,
        env: &mut Env,
        pattern: PatternId,
        value: Option<ExprId>,
        _is_var: bool,
    ) {
        let Some(expr) = value else { return };
        self.seed_pattern_proofs(env, pattern, expr);
    }

    pub(super) fn seed_pattern_proofs(
        &self,
        env: &mut Env,
        pattern: PatternId,
        value_expr: ExprId,
    ) {
        let ast = self.ast(env.file);
        match &ast.pattern(pattern).value {
            Pattern::Binding(_, name) => {
                let Some(id) = self.resolve(name.span) else {
                    return;
                };
                let target = Place::local(id);
                self.invalidate_place_proofs(env, &target);
                self.seed_place_from_expr(env, &target, value_expr);
            }
            Pattern::Slice { elements, .. } => {
                let fixed = elements
                    .iter()
                    .filter(|item| !matches!(ast.pattern(**item).value, Pattern::Rest(_)))
                    .count();
                let has_rest = elements
                    .iter()
                    .any(|&item| matches!(ast.pattern(item).value, Pattern::Rest(_)));
                let src_len = if let Some(coll) = self.resolve_place(env, value_expr) {
                    let a = Atom::Len(coll);
                    env.refinements.dbm.ensure_atom(a.clone());
                    a
                } else {
                    let mut dbm = env.refinements.dbm.clone();
                    let t = dbm.fresh_temp();
                    self.constrain_len_expr(env, &mut dbm, &t, value_expr);
                    env.refinements.dbm = dbm;
                    t
                };
                if has_rest {
                    env.refinements
                        .dbm
                        .add_le(Atom::Zero, src_len.clone(), -(fixed as i128));
                } else {
                    env.refinements
                        .dbm
                        .add_eq(src_len.clone(), Atom::Zero, fixed as i128);
                }
                for &elem in elements {
                    if let Pattern::Rest(Some(rest_name)) = &ast.pattern(elem).value
                        && let Some(rest_id) = self.resolve(rest_name.span)
                    {
                        let rest_len = Atom::Len(Place::local(rest_id));
                        // Exact: `len(rest) == len(src) - fixed`!
                        env.refinements
                            .dbm
                            .add_eq(rest_len, src_len.clone(), -(fixed as i128));
                    }
                }
                env.refinements.dbm.forget_temps();
            }
            Pattern::Literal(lit) => {
                if let Some(p) = self.resolve_place(env, value_expr) {
                    match super::literal(lit) {
                        Ok(Value::Int(n)) => {
                            if let Some(c) = n.to_i128() {
                                env.refinements.dbm.add_eq(Atom::Val(p), Atom::Zero, c);
                            }
                        }
                        Ok(Value::Bool(b)) => {
                            env.refinements.dbm.add_bool(p, b);
                        }
                        _ => {}
                    }
                }
            }
            Pattern::Range {
                low,
                high,
                inclusive,
            } => {
                if let Some(p) = self.resolve_place(env, value_expr) {
                    let a = Atom::Val(p);
                    if let Ok(Value::Int(n)) = super::literal(low)
                        && let Some(c) = n.to_i128()
                        && let Some(neg) = c.checked_neg()
                    {
                        env.refinements.dbm.add_le(Atom::Zero, a.clone(), neg);
                    }
                    if let Ok(Value::Int(n)) = super::literal(high)
                        && let Some(c) = n.to_i128()
                    {
                        let bound = if *inclusive { c } else { c.saturating_sub(1) };
                        env.refinements.dbm.add_le(a, Atom::Zero, bound);
                    }
                }
            }
            Pattern::Constructor(path, items_opt) => {
                let tag_name = path.segments.last().map(|s| s.name.value.as_str());
                if tag_name == Some("None") {
                    if let Some((base, index)) = self.is_map_safe_index(env, value_expr)
                        && let Some(c_place) = self.resolve_place(env, base)
                    {
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, index) {
                            dbm.add_not_contains(Atom::Val(c_place), k_atom);
                        }
                        env.refinements.dbm = dbm;
                    } else if let Some(opt_place) = self.place(env, value_expr)
                        && env
                            .refinements
                            .options
                            .get(&opt_place)
                            .is_some_and(|f| f.invalidated.is_none() && f.depth > 0)
                    {
                        env.refinements.dbm.unsat = true;
                    }
                } else if tag_name == Some("Some") {
                    if let Some((base, index)) = self.is_map_safe_index(env, value_expr)
                        && let Some(c_place) = self.resolve_place(env, base)
                    {
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, index) {
                            dbm.add_contains(Atom::Val(c_place), k_atom);
                        }
                        env.refinements.dbm = dbm;
                    } else if let Some(opt_place) = self.place(env, value_expr)
                        && env
                            .refinements
                            .options
                            .get(&opt_place)
                            .is_some_and(|f| f.invalidated.is_none() && f.is_none)
                    {
                        env.refinements.dbm.unsat = true;
                    }
                }
                if let Some(items) = items_opt
                    && matches!(tag_name, Some("Some" | "Ok"))
                    && let [inner_pat] = items.as_slice()
                    && let Pattern::Binding(_, name) = &ast.pattern(*inner_pat).value
                    && let Some(id) = self.resolve(name.span)
                {
                    let target = Place::local(id);
                    self.apply_call_proof_to_place(env, &target, value_expr, true);
                    // Safe slice unwrap `Some(sub) = xs?[a..b]`: seed exact slice length!
                    if tag_name == Some("Some")
                        && let Expr::Index {
                            base,
                            index,
                            safe: true,
                        } = &ast.expr(value_expr).value
                        && let Expr::Range {
                            start,
                            end,
                            inclusive,
                        } = ast.expr(*index).value
                    {
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        self.constrain_slice_len(
                            env,
                            &mut dbm,
                            &Atom::Len(target.clone()),
                            *base,
                            start,
                            end,
                            inclusive,
                            true,
                        );
                        dbm.forget_temps();
                        env.refinements.dbm = dbm;
                    }
                    if let Expr::Call { callee, args } = &ast.expr(value_expr).value
                        && let Expr::Path(cp) = &ast.expr(*callee).value
                        && cp
                            .segments
                            .last()
                            .is_some_and(|s| matches!(s.name.value.as_str(), "Some" | "Ok"))
                        && let [arg] = args.as_slice()
                    {
                        self.seed_place_from_expr(env, &target, arg.value);
                    }
                }
            }
            Pattern::Wrap(path, items) => {
                let tag_name = path.segments.last().map(|s| s.name.value.as_str());
                if tag_name == Some("Some") {
                    if let Some((base, index)) = self.is_map_safe_index(env, value_expr)
                        && let Some(c_place) = self.resolve_place(env, base)
                    {
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, index) {
                            dbm.add_contains(Atom::Val(c_place), k_atom);
                        }
                        env.refinements.dbm = dbm;
                    } else if let Some(opt_place) = self.place(env, value_expr)
                        && env
                            .refinements
                            .options
                            .get(&opt_place)
                            .is_some_and(|f| f.invalidated.is_none() && f.is_none)
                    {
                        env.refinements.dbm.unsat = true;
                    }
                }
                if matches!(tag_name, Some("Some" | "Ok"))
                    && let [inner_pat] = items.as_slice()
                    && let Pattern::Binding(_, name) = &ast.pattern(*inner_pat).value
                    && let Some(id) = self.resolve(name.span)
                {
                    let target = Place::local(id);
                    self.apply_call_proof_to_place(env, &target, value_expr, true);
                    if tag_name == Some("Some")
                        && let Expr::Index {
                            base,
                            index,
                            safe: true,
                        } = &ast.expr(value_expr).value
                        && let Expr::Range {
                            start,
                            end,
                            inclusive,
                        } = ast.expr(*index).value
                    {
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        self.constrain_slice_len(
                            env,
                            &mut dbm,
                            &Atom::Len(target.clone()),
                            *base,
                            start,
                            end,
                            inclusive,
                            true,
                        );
                        dbm.forget_temps();
                        env.refinements.dbm = dbm;
                    }
                    // Also handle direct `Some(v)` / `Ok(v)` literal expressions.
                    if let Expr::Call { callee, args } = &ast.expr(value_expr).value
                        && let Expr::Path(cp) = &ast.expr(*callee).value
                        && cp
                            .segments
                            .last()
                            .is_some_and(|s| matches!(s.name.value.as_str(), "Some" | "Ok"))
                        && let [arg] = args.as_slice()
                    {
                        self.seed_place_from_expr(env, &target, arg.value);
                    }
                } else if let [inner_pat] = items.as_slice()
                    && let Some(mut p) = self.resolve_place(env, value_expr)
                {
                    p.path.push("#inner".to_owned());
                    if let Pattern::Binding(_, name) = &ast.pattern(*inner_pat).value
                        && let Some(id) = self.resolve(name.span)
                    {
                        let dst = Place::local(id);
                        env.refinements
                            .dbm
                            .copy_atom_eq(Atom::Val(dst.clone()), Atom::Val(p.clone()));
                        env.refinements
                            .dbm
                            .copy_atom_eq(Atom::Len(dst), Atom::Len(p));
                    }
                }
            }
            Pattern::Tuple(items) => {
                if let Expr::Tuple(vals) = &ast.expr(value_expr).value {
                    for (&pat_i, &val_i) in items.iter().zip(vals.iter()) {
                        self.seed_pattern_proofs(env, pat_i, val_i);
                    }
                } else if let Some(base) = self.resolve_place(env, value_expr) {
                    for (i, &pat_i) in items.iter().enumerate() {
                        if let Pattern::Binding(_, name) = &ast.pattern(pat_i).value
                            && let Some(id) = self.resolve(name.span)
                        {
                            let mut sub = base.clone();
                            sub.path.push(i.to_string());
                            let dst = Place::local(id);
                            env.refinements
                                .dbm
                                .copy_atom_eq(Atom::Val(dst.clone()), Atom::Val(sub.clone()));
                            env.refinements
                                .dbm
                                .copy_atom_eq(Atom::Len(dst), Atom::Len(sub));
                        }
                    }
                }
            }
            Pattern::Record { fields, .. } => {
                if let Some(base) = self.resolve_place(env, value_expr) {
                    for field in fields {
                        let sub_pat = field.pattern;
                        let target_id = if let Some(sp) = sub_pat {
                            match &ast.pattern(sp).value {
                                Pattern::Binding(_, name) => self.resolve(name.span),
                                _ => None,
                            }
                        } else {
                            self.resolve(field.name.span)
                        };
                        if let Some(id) = target_id {
                            let mut sub = base.clone();
                            sub.path.push(field.name.value.clone());
                            let dst = Place::local(id);
                            env.refinements
                                .dbm
                                .copy_atom_eq(Atom::Val(dst.clone()), Atom::Val(sub.clone()));
                            env.refinements
                                .dbm
                                .copy_atom_eq(Atom::Len(dst), Atom::Len(sub));
                        }
                    }
                }
            }
            Pattern::Or(alts) => {
                let mut acc: Option<Dbm> = None;
                for &alt in alts {
                    let mut branch = env.clone();
                    self.seed_pattern_proofs(&mut branch, alt, value_expr);
                    acc = Some(match acc {
                        None => branch.refinements.dbm,
                        Some(cur) => Dbm::join(&cur, &branch.refinements.dbm),
                    });
                }
                if let Some(joined) = acc {
                    env.refinements.dbm = joined;
                }
            }
            _ => {}
        }
    }

    /// Negate an unguarded pattern onto `env` for subsequent `match` arms (or `if let ... else`).
    pub(super) fn negate_pattern_proofs(
        &self,
        env: &mut Env,
        pattern: PatternId,
        value_expr: ExprId,
    ) {
        let ast = self.ast(env.file);
        match &ast.pattern(pattern).value {
            Pattern::Literal(lit) => {
                if let Some(p) = self.resolve_place(env, value_expr) {
                    match super::literal(lit) {
                        Ok(Value::Int(n)) => {
                            if let Some(c) = n.to_i128() {
                                env.refinements.dbm.add_ne(Atom::Val(p), Atom::Zero, c);
                            }
                        }
                        Ok(Value::Bool(b)) => {
                            env.refinements.dbm.add_bool(p, !b);
                        }
                        _ => {}
                    }
                }
            }
            Pattern::Constructor(path, items_opt) => {
                let tag_name = path.segments.last().map(|s| s.name.value.as_str());
                let inner_irrefutable = items_opt.as_ref().is_none_or(|items| {
                    items.iter().all(|&p| {
                        matches!(
                            ast.pattern(p).value,
                            Pattern::Wildcard | Pattern::Binding(_, _)
                        )
                    })
                });
                if inner_irrefutable {
                    if tag_name == Some("None") {
                        if let Some((base, index)) = self.is_map_safe_index(env, value_expr)
                            && let Some(c_place) = self.resolve_place(env, base)
                        {
                            let mut dbm = std::mem::take(&mut env.refinements.dbm);
                            if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, index) {
                                dbm.add_contains(Atom::Val(c_place), k_atom);
                            }
                            env.refinements.dbm = dbm;
                        } else if let Some(opt_place) = self.place(env, value_expr)
                            && env
                                .refinements
                                .options
                                .get(&opt_place)
                                .is_some_and(|f| f.invalidated.is_none() && f.is_none)
                        {
                            env.refinements.dbm.unsat = true;
                        }
                    } else if tag_name == Some("Some") {
                        if let Some((base, index)) = self.is_map_safe_index(env, value_expr)
                            && let Some(c_place) = self.resolve_place(env, base)
                        {
                            let mut dbm = std::mem::take(&mut env.refinements.dbm);
                            if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, index) {
                                dbm.add_not_contains(Atom::Val(c_place), k_atom);
                            }
                            env.refinements.dbm = dbm;
                        } else if let Some(opt_place) = self.place(env, value_expr)
                            && env
                                .refinements
                                .options
                                .get(&opt_place)
                                .is_some_and(|f| f.invalidated.is_none() && f.depth > 0)
                        {
                            env.refinements.dbm.unsat = true;
                        }
                    }
                }
            }
            Pattern::Wrap(path, items) => {
                let tag_name = path.segments.last().map(|s| s.name.value.as_str());
                let inner_irrefutable = items.iter().all(|&p| {
                    matches!(
                        ast.pattern(p).value,
                        Pattern::Wildcard | Pattern::Binding(_, _)
                    )
                });
                if inner_irrefutable && tag_name == Some("Some") {
                    if let Some((base, index)) = self.is_map_safe_index(env, value_expr)
                        && let Some(c_place) = self.resolve_place(env, base)
                    {
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, index) {
                            dbm.add_not_contains(Atom::Val(c_place), k_atom);
                        }
                        env.refinements.dbm = dbm;
                    } else if let Some(opt_place) = self.place(env, value_expr)
                        && env
                            .refinements
                            .options
                            .get(&opt_place)
                            .is_some_and(|f| f.invalidated.is_none() && f.depth > 0)
                    {
                        env.refinements.dbm.unsat = true;
                    }
                }
            }
            Pattern::Range {
                low,
                high,
                inclusive,
            } => {
                if let Some(p) = self.resolve_place(env, value_expr) {
                    let a = Atom::Val(p);
                    let mut alts = Vec::new();
                    if let Ok(Value::Int(n)) = super::literal(low)
                        && let Some(c) = n.to_i128()
                        && let Some(cm1) = c.checked_sub(1)
                    {
                        alts.push(ProofPred::diff_le(Some(a.clone()), None, cm1));
                    }
                    if let Ok(Value::Int(n)) = super::literal(high)
                        && let Some(c) = n.to_i128()
                    {
                        let neg_gt = if *inclusive {
                            c.checked_add(1).and_then(|v| v.checked_neg())
                        } else {
                            c.checked_neg()
                        };
                        if let Some(b) = neg_gt {
                            alts.push(ProofPred::diff_le(None, Some(a), b));
                        }
                    }
                    if !alts.is_empty() {
                        env.refinements.dbm.assume(&ProofPred::or(alts));
                    }
                }
            }
            Pattern::Slice { elements, .. } => {
                let fixed = elements
                    .iter()
                    .filter(|item| !matches!(ast.pattern(**item).value, Pattern::Rest(_)))
                    .count();
                let has_rest = elements
                    .iter()
                    .any(|&item| matches!(ast.pattern(item).value, Pattern::Rest(_)));
                let all_elem_irrefutable = elements.iter().all(|&item| {
                    matches!(
                        ast.pattern(item).value,
                        Pattern::Wildcard | Pattern::Binding(_, _) | Pattern::Rest(_)
                    )
                });
                if all_elem_irrefutable && let Some(coll) = self.resolve_place(env, value_expr) {
                    if !has_rest && fixed == 0 {
                        // Negating empty slice `[]` => `len(xs) != 0` => unit-propagates to `len(xs) >= 1`!
                        env.refinements.dbm.add_ne(Atom::Len(coll), Atom::Zero, 0);
                    } else if has_rest && fixed >= 1 {
                        // Negating `[a, ..rest]` => `len(xs) <= fixed - 1`!
                        env.refinements.dbm.add_le(
                            Atom::Len(coll),
                            Atom::Zero,
                            (fixed - 1) as i128,
                        );
                    }
                }
            }
            Pattern::Or(alts) => {
                for &alt in alts {
                    self.negate_pattern_proofs(env, alt, value_expr);
                }
            }
            _ => {}
        }
    }

    pub(super) fn seed_place_from_expr(&self, env: &mut Env, target: &Place, expr: ExprId) {
        // 1. Direct call postcondition proofs (`-> new []Cell |> Len(1)`, `-> new Shelf |> HasRows`, etc.).
        self.apply_call_proof_to_place(env, target, expr, false);

        // 2. If `expr` is `?` propagation on a fallible call (`let x = f()?`), seed payload proof!
        let ast = self.ast(env.file);
        if let Expr::Unary { op, value } = &ast.expr(expr).value
            && op.value == "?"
        {
            self.apply_call_proof_to_place(env, target, *value, true);
        }

        // 3. Composite structural seeding (tuples, records, wrap::(...), arrays, str, bytes).
        self.seed_composite_from_expr(env, target, expr);

        // 4. Scalar `int` value seeding (only when `expr` is integer-typed).
        if self.is_int_expr(env, expr) {
            let val_atom = Atom::Val(target.clone());
            let mut dbm = std::mem::take(&mut env.refinements.dbm);
            let t = dbm.fresh_temp();
            self.constrain_expr(env, &mut dbm, &t, expr);
            dbm.add_eq(val_atom, t.clone(), 0);
            dbm.project_out(|a| *a == t);
            env.refinements.dbm = dbm;
        }
    }

    fn seed_composite_from_expr(&self, env: &mut Env, prefix: &Place, expr: ExprId) {
        let ast = self.ast(env.file);
        // Seed length if `expr` has known collection/str/bytes length.
        let expr_span = ast.expr(expr).span;
        let maybe_len_target = match self.types.get(&expr_span) {
            Some(ty) => {
                matches!(
                    ty,
                    Ty::Array(_) | Ty::Str | Ty::Bytes | Ty::Map(..) | Ty::Unknown | Ty::Infer(_)
                ) || ty.as_set(self.hir).is_some()
            }
            None => matches!(
                &ast.expr(expr).value,
                Expr::Array(_) | Expr::Literal(_) | Expr::Index { .. } | Expr::Call { .. }
            ),
        };
        if maybe_len_target {
            let mut dbm = std::mem::take(&mut env.refinements.dbm);
            let direct_slice = matches!(&ast.expr(expr).value, Expr::Index { safe: false, .. });
            if direct_slice {
                // Constrain `Atom::Len(prefix)` directly so 3-variable `diff_eq` survives temp projection!
                let target_len = Atom::Len(prefix.clone());
                self.constrain_len_expr(env, &mut dbm, &target_len, expr);
                dbm.forget_temps();
            } else {
                let t = dbm.fresh_temp();
                self.constrain_len_expr(env, &mut dbm, &t, expr);
                // Only attach `Len(prefix)` if we learned something beyond `>= 0`.
                if dbm.lb(&t).is_some_and(|l| l > 0)
                    || dbm.ub(&t).is_some()
                    || self.resolve_place(env, expr).is_some()
                    || matches!(&ast.expr(expr).value, Expr::Array(_) | Expr::Literal(_))
                    || env.refinements.call_proofs.contains_key(&expr)
                {
                    dbm.add_eq(Atom::Len(prefix.clone()), t.clone(), 0);
                }
                dbm.project_out(|a| *a == t);
            }
            env.refinements.dbm = dbm;
        }
        // Copy membership facts across aliasing/cloning (`let m2 = m`, `let m2 = clone(m)`).
        if let Some(src_place) = self.resolve_place(env, expr) {
            env.refinements
                .dbm
                .copy_container_membership(&Atom::Val(prefix.clone()), &Atom::Val(src_place));
        } else if let Expr::Call { callee, args } = &ast.expr(expr).value
            && let Expr::Path(path) = &ast.expr(*callee).value
            && let Some(id) = self.resolve(path.span)
            && matches!(
                self.hir.intrinsic(id),
                Some(Intrinsic::Clone | Intrinsic::Inner)
            )
            && let [arg] = args.as_slice()
            && let Some(src_place) = self.resolve_place(env, arg.value)
        {
            env.refinements
                .dbm
                .copy_container_membership(&Atom::Val(prefix.clone()), &Atom::Val(src_place));
        }
        // Map literal membership & length seeding (`let m = ["a": 1, "b": 2]`).
        if let Expr::Map(entries) = &ast.expr(expr).value {
            let mut dbm = std::mem::take(&mut env.refinements.dbm);
            let len_atom = Atom::Len(prefix.clone());
            if entries.is_empty() {
                dbm.add_eq(len_atom.clone(), Atom::Zero, 0);
            } else {
                dbm.add_le(Atom::Zero, len_atom.clone(), -1);
                dbm.add_le(len_atom.clone(), Atom::Zero, entries.len() as i128);
            }
            let allow_seed = !self.container_key_contains_f64(env, expr);
            let mut distinct_consts = HashSet::new();
            let mut all_distinct_consts = true;
            for &(k_expr, _) in entries {
                if let Some(k_atom) = self.key_expr_to_atom(env, &mut dbm, k_expr) {
                    if let Atom::KeyConst(ref kc) = k_atom {
                        if !distinct_consts.insert(kc.clone()) {
                            all_distinct_consts = false;
                        }
                    } else {
                        all_distinct_consts = false;
                    }
                    if allow_seed {
                        dbm.add_contains(Atom::Val(prefix.clone()), k_atom);
                    }
                } else {
                    all_distinct_consts = false;
                }
            }
            if all_distinct_consts && !entries.is_empty() {
                dbm.add_eq(len_atom, Atom::Zero, distinct_consts.len() as i128);
            }
            env.refinements.dbm = dbm;
        }
        match &ast.expr(expr).value {
            Expr::Tuple(items) => {
                for (i, &item) in items.iter().enumerate() {
                    let mut sub = prefix.clone();
                    sub.path.push(i.to_string());
                    self.seed_place_from_expr(env, &sub, item);
                }
            }
            Expr::Record { fields, .. } => {
                for f in fields {
                    let mut sub = prefix.clone();
                    sub.path.push(f.name.value.clone());
                    if let Some(v) = f.value {
                        self.seed_place_from_expr(env, &sub, v);
                    } else if let Some(src) = self.resolve(f.name.span) {
                        let src_place = Place::local(src);
                        env.refinements
                            .dbm
                            .copy_atom_eq(Atom::Val(sub.clone()), Atom::Val(src_place.clone()));
                        env.refinements
                            .dbm
                            .copy_atom_eq(Atom::Len(sub), Atom::Len(src_place));
                    }
                }
            }
            Expr::Wrap { args, .. } => {
                if let [only] = args.as_slice() {
                    let mut sub = prefix.clone();
                    sub.path.push("#inner".to_owned());
                    self.seed_place_from_expr(env, &sub, only.value);
                }
            }
            _ => {}
        }
    }

    pub(super) fn seed_guard_proofs(&mut self, env: &mut Env, param: &SyntaxParam) {
        let Some(name) = &param.name else { return };
        let Some(param_id) = self.resolve(name.span) else {
            return;
        };
        for &guard_expr in &param.guards {
            if self.hir.is_static_proof_guard(env.file, guard_expr) {
                continue;
            }
            let ast = self.ast(env.file);
            let callee_path = match &ast.expr(guard_expr).value {
                Expr::Path(path) => path,
                Expr::Call { callee, .. } => match &ast.expr(*callee).value {
                    Expr::Path(path) => path,
                    _ => continue,
                },
                _ => continue,
            };
            let Some(guard_def_id) = self.resolve(callee_path.span) else {
                continue;
            };
            let guard_def = self.hir.definition(guard_def_id);
            let Some(stmt_id) = guard_def.stmt else {
                continue;
            };
            let guard_file = guard_def.name.span.file;
            let guard_ast = self.ast(guard_file);
            let StmtKind::Function(guard_fn) = &guard_ast.stmt(stmt_id).value.kind else {
                continue;
            };
            let Some(guard_param_id) = guard_fn
                .signature
                .params
                .first()
                .and_then(|p| p.name.as_ref())
                .and_then(|n| self.resolve(n.span))
            else {
                continue;
            };
            let Some(body_id) = guard_fn.body else {
                continue;
            };
            let inner_expr = match &guard_ast.expr(body_id).value {
                Expr::Block { statements, .. } => {
                    if let [only] = statements.as_slice() {
                        match &guard_ast.stmt(*only).value.kind {
                            StmtKind::Expr(e) => *e,
                            _ => continue,
                        }
                    } else {
                        body_id
                    }
                }
                _ => body_id,
            };
            let Expr::If {
                condition: Condition::Expr(cond_id),
                yes,
                no: Some(no),
                ..
            } = &guard_ast.expr(inner_expr).value
            else {
                continue;
            };
            let is_ok_branch = |branch: ExprId| -> bool {
                let b = match &guard_ast.expr(branch).value {
                    Expr::Block { statements, .. } => {
                        if let [only] = statements.as_slice() {
                            match &guard_ast.stmt(*only).value.kind {
                                StmtKind::Expr(e) => *e,
                                _ => return false,
                            }
                        } else {
                            branch
                        }
                    }
                    _ => branch,
                };
                match &guard_ast.expr(b).value {
                    Expr::Call { callee, .. } => {
                        matches!(&guard_ast.expr(*callee).value, Expr::Path(p)
                            if p.segments.last().is_some_and(|s| matches!(s.name.value.as_str(), "Ok" | "Some")))
                    }
                    _ => false,
                }
            };
            let truth = if is_ok_branch(*yes) && !is_ok_branch(*no) {
                true
            } else if is_ok_branch(*no) && !is_ok_branch(*yes) {
                false
            } else {
                continue;
            };
            let mut g_env = Env::new(guard_file, guard_def.scope);
            self.relate_proofs(&mut g_env, *cond_id, truth);
            let src_val = Atom::Val(Place::local(guard_param_id));
            let dst_val = Atom::Val(Place::local(param_id));
            if let Some(lb) = g_env.refinements.dbm.lb(&src_val)
                && let Some(neg) = lb.checked_neg()
            {
                env.refinements.dbm.add_le(Atom::Zero, dst_val.clone(), neg);
            }
            if let Some(ub) = g_env.refinements.dbm.ub(&src_val) {
                env.refinements.dbm.add_le(dst_val.clone(), Atom::Zero, ub);
            }
            if g_env.refinements.dbm.is_nonzero(&src_val) {
                env.refinements.dbm.add_ne(dst_val, Atom::Zero, 0);
            }
            let src_len = Atom::Len(Place::local(guard_param_id));
            if let Some(lb) = g_env.refinements.dbm.lb(&src_len)
                && lb > 0
                && let Some(neg) = lb.checked_neg()
            {
                env.refinements
                    .dbm
                    .add_le(Atom::Zero, Atom::Len(Place::local(param_id)), neg);
            }
        }
    }

    // -------------------------------------------------------------------------
    // Pure Read-Only DBM Widening Fixpoint for `while` and `for` Loops
    // -------------------------------------------------------------------------

    pub(super) fn compute_while_invariant(
        &self,
        env: &Env,
        condition: &Condition,
        body: ExprId,
    ) -> Dbm {
        let d0 = env.refinements.dbm.clone();
        let fallback = self.loop_fallback_dbm(env, &d0, body);
        let mut w = d0.clone();
        for _ in 0..MAX_WIDEN_ITERS {
            let d_head = w.closed();
            let mut d_body = d_head.clone();
            if let Condition::Expr(test) = condition {
                self.relate_proofs_in_dbm(env, &mut d_body, *test, true);
            }
            let mut breaks = Vec::new();
            let mut continues = Vec::new();
            let falls = self.step_loop_expr(env, &mut d_body, body, &mut breaks, &mut continues, 0);
            let mut d_back: Option<Dbm> = if falls && !d_body.unsat {
                Some(d_body)
            } else {
                None
            };
            for c in continues {
                if !c.unsat {
                    d_back = Some(match d_back {
                        None => c,
                        Some(cur) => Dbm::join(&cur, &c),
                    });
                }
            }
            let mut d_next = match d_back {
                Some(mut back) => {
                    back.forget_temps();
                    Dbm::join(&d0, &back)
                }
                None => d0.clone(),
            };
            d_next.forget_temps();
            if d_next.is_subsumed_by(&d_head) {
                return d_head;
            }
            w = Dbm::widen(&w, &d_next);
        }
        fallback
    }

    pub(super) fn compute_for_invariant(
        &self,
        env: &Env,
        iterable: ExprId,
        pattern: PatternId,
        body: ExprId,
    ) -> (Dbm, Dbm) {
        // Returns `(body_head_dbm, exit_dbm)` so `for 0..count { push(mut out, v) }` and
        // `for xs as x { push(mut out, f(x)) }` prove exact `len(out) == count / len(xs)`!
        let mut d0 = env.refinements.dbm.clone();
        let ast = self.ast(env.file);
        let loop_var = match &ast.pattern(pattern).value {
            Pattern::Binding(_, name) => self.resolve(name.span),
            _ => None,
        };

        // Determine loop trip bounds `(start_atom, end_atom, inclusive, is_range)` frozen before loop entry.
        let mut trip: Option<(Atom, Atom, bool, bool)> = None;
        if let Expr::Range {
            start: Some(start),
            end: Some(end),
            inclusive,
        } = ast.expr(iterable).value
        {
            let s = d0.fresh_temp();
            self.constrain_expr(env, &mut d0, &s, start);
            let e = d0.fresh_temp();
            self.constrain_expr(env, &mut d0, &e, end);
            trip = Some((s, e, inclusive, true));
        } else {
            // Iterating over a collection (`for xs as x`): trip count is `0..len(xs)`.
            let iter_span = ast.expr(iterable).span;
            if self.types.get(&iter_span).is_some_and(|t| {
                matches!(t, Ty::Array(_) | Ty::Map(..)) || t.as_set(self.hir).is_some()
            }) {
                let s = d0.fresh_temp();
                d0.add_eq(s.clone(), Atom::Zero, 0);
                let e = d0.fresh_temp();
                self.constrain_len_expr(env, &mut d0, &e, iterable);
                trip = Some((s, e, false, false));
            }
        }

        // Fast check: are there any mutations inside `body`?
        let mut mutated_vars = HashSet::new();
        let mut resized_colls = HashSet::new();
        let mut has_open = false;
        self.collect_loop_mutations(
            env,
            body,
            &mut mutated_vars,
            &mut resized_colls,
            &mut has_open,
        );
        let fallback_base = self.loop_fallback_dbm(env, &env.refinements.dbm, body);

        // Identify membership fact seeded at the top of each `for` iteration (`for m as (k, _)`,
        // `for s as x`, `for Map::keys(m) as k`, `for Set::to_array(s) as x`), sound when the
        // container is not mutated/resized inside the loop body.
        let loop_membership: Option<(Place, Place)> = (|| {
            let iter_span = ast.expr(iterable).span;
            let iter_ty = self.types.get(&iter_span).map(|t| {
                let norm = self.normalize(t);
                match norm {
                    Ty::Draft(inner) => self.normalize(&inner),
                    other => other,
                }
            });
            let (container, key_id) = if let Some(Ty::Map(..)) = iter_ty {
                let c = self.resolve_place(env, iterable)?;
                let Pattern::Tuple(items) = &ast.pattern(pattern).value else {
                    return None;
                };
                let Pattern::Binding(_, name) = &ast.pattern(*items.first()?).value else {
                    return None;
                };
                (c, self.resolve(name.span)?)
            } else if iter_ty
                .as_ref()
                .is_some_and(|t| t.as_set(self.hir).is_some())
            {
                let c = self.resolve_place(env, iterable)?;
                (c, loop_var?)
            } else if let Expr::Call { callee, args } = &ast.expr(iterable).value
                && let Expr::Path(path) = &ast.expr(*callee).value
                && let Some(id) = self.resolve(path.span)
                && (self.hir.intrinsic(id) == Some(Intrinsic::MapKeys)
                    || self.is_set_stdlib_callee(id, "to_array"))
                && let [arg] = args.as_slice()
            {
                let c = self.resolve_place(env, arg.value)?;
                (c, loop_var?)
            } else {
                return None;
            };
            if resized_colls.contains(&container.root)
                || (has_open
                    && self.live.contains(&container.root)
                    && !(container.path.is_empty()
                        && self.confined_locals.contains(&container.root)))
            {
                return None;
            }
            Some((container, Place::local(key_id)))
        })();

        if let Some((start_a, end_a, inclusive, is_range)) = trip {
            // Synthetic iteration counter `iter_c` starting at `start_a`, incrementing by +1 each step.
            let iter_c = d0.fresh_temp();
            d0.add_eq(iter_c.clone(), start_a.clone(), 0);
            // If `start_a > end_a` (empty range), exit directly with `d0`; otherwise run widening with `iter_c <= end_a`.
            let non_empty_guard = d0.entails_le(&start_a, &end_a, 0);

            let mut w = d0.clone();
            let mut converged: Option<(Dbm, Vec<Dbm>)> = None;
            for _ in 0..MAX_WIDEN_ITERS {
                let d_head = w.closed();
                let mut d_body = d_head.clone();
                // Loop condition: `iter_c < end_a` (or `<= end_a` if inclusive).
                d_body.add_le(
                    iter_c.clone(),
                    end_a.clone(),
                    if inclusive { 0 } else { -1 },
                );
                if is_range && let Some(vid) = loop_var {
                    d_body.add_eq(Atom::Val(Place::local(vid)), iter_c.clone(), 0);
                }
                let mut breaks = Vec::new();
                let mut continues = Vec::new();
                let falls =
                    self.step_loop_expr(env, &mut d_body, body, &mut breaks, &mut continues, 0);
                // Advance `iter_c += 1` along back edges!
                let advance = |mut state: Dbm| -> Dbm {
                    if !state.unsat {
                        state.assign_via_temp(iter_c.clone(), |d, t| {
                            d.add_eq(t.clone(), iter_c.clone(), 1);
                        });
                        if let Some(vid) = loop_var {
                            state.forget(&Atom::Val(Place::local(vid)));
                        }
                    }
                    state
                };
                let mut d_back: Option<Dbm> = if falls && !d_body.unsat {
                    Some(advance(d_body))
                } else {
                    None
                };
                for c in continues {
                    if !c.unsat {
                        let adv = advance(c);
                        d_back = Some(match d_back {
                            None => adv,
                            Some(cur) => Dbm::join(&cur, &adv),
                        });
                    }
                }
                let d_next = match d_back {
                    Some(back) => Dbm::join(&d0, &back),
                    None => d0.clone(),
                };
                if d_next.is_subsumed_by(&d_head) {
                    converged = Some((d_head, breaks));
                    break;
                }
                w = Dbm::widen(&w, &d_next);
            }

            if let Some((d_inv, breaks)) = converged {
                let mut body_head = d_inv.clone();
                body_head.add_le(
                    iter_c.clone(),
                    end_a.clone(),
                    if inclusive { 0 } else { -1 },
                );
                if is_range && let Some(vid) = loop_var {
                    body_head.add_eq(Atom::Val(Place::local(vid)), iter_c.clone(), 0);
                }
                if let Some((ref c, ref k)) = loop_membership {
                    body_head.add_contains(Atom::Val(c.clone()), Atom::Val(k.clone()));
                }
                // Normal loop exit: `iter_c >= end_a` (or `>= end_a + 1` if inclusive).
                let mut normal_exit = d_inv;
                if non_empty_guard {
                    normal_exit.add_le(
                        end_a.clone(),
                        iter_c.clone(),
                        if inclusive { -1 } else { 0 },
                    );
                }
                let mut exit = normal_exit;
                for b in breaks {
                    if !b.unsat {
                        exit = Dbm::join(&exit, &b);
                    }
                }
                body_head.forget_temps();
                exit.forget_temps();
                return (body_head, exit);
            }
        }

        // Fallback if widening did not converge.
        let mut body_head = fallback_base.clone();
        if let Expr::Range {
            start: Some(start),
            end: Some(end),
            inclusive,
        } = ast.expr(iterable).value
            && let Some(vid) = loop_var
        {
            let v_atom = Atom::Val(Place::local(vid));
            let s = self.expr_to_atom(env, &mut body_head, start);
            body_head.add_le(s, v_atom.clone(), 0);
            let e = self.expr_to_atom(env, &mut body_head, end);
            body_head.add_le(v_atom, e, if inclusive { 0 } else { -1 });
            body_head.forget_temps();
        }
        if let Some((ref c, ref k)) = loop_membership {
            body_head.add_contains(Atom::Val(c.clone()), Atom::Val(k.clone()));
        }
        (body_head, fallback_base)
    }

    fn loop_fallback_dbm(&self, env: &Env, base: &Dbm, body: ExprId) -> Dbm {
        let mut mutated_vars = HashSet::new();
        let mut resized_colls = HashSet::new();
        let mut has_open = false;
        self.collect_loop_mutations(
            env,
            body,
            &mut mutated_vars,
            &mut resized_colls,
            &mut has_open,
        );
        let mut out = base.clone();
        for var in mutated_vars {
            out.forget_matching(|a| matches!(a, Atom::Val(p) if p.root == var));
        }
        for coll in resized_colls {
            out.forget_matching(|a| matches!(a, Atom::Len(p) | Atom::Val(p) if p.root == coll));
        }
        if has_open {
            out.forget_matching(|a| match a {
                Atom::Val(p) | Atom::Len(p) => {
                    self.live.contains(&p.root)
                        && !(p.path.is_empty() && self.confined_locals.contains(&p.root))
                }
                _ => false,
            });
        }
        out
    }

    /// Pure read-only abstract step of `expr` on `dbm`. Returns `true` if normal fallthrough is reachable.
    fn step_loop_expr(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        expr: ExprId,
        breaks: &mut Vec<Dbm>,
        continues: &mut Vec<Dbm>,
        depth: usize,
    ) -> bool {
        if dbm.unsat || depth >= MAX_LOOP_DEPTH {
            if depth >= MAX_LOOP_DEPTH {
                *dbm = self.loop_fallback_dbm(env, dbm, expr);
            }
            return !dbm.unsat;
        }
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Block { statements, .. } => {
                let mut locals_in_block = Vec::new();
                let mut reachable = true;
                for &stmt_id in statements {
                    if !reachable || dbm.unsat {
                        break;
                    }
                    let stmt = ast.stmt(stmt_id);
                    match &stmt.value.kind {
                        StmtKind::Binding {
                            pattern,
                            value,
                            fallback,
                            ..
                        } => {
                            if let Some(v) = value {
                                reachable =
                                    self.step_loop_expr(env, dbm, *v, breaks, continues, depth);
                            }
                            if let Some(f) = fallback {
                                let mut fb = dbm.clone();
                                let _ =
                                    self.step_loop_expr(env, &mut fb, *f, breaks, continues, depth);
                            }
                            if reachable
                                && let Pattern::Binding(_, name) = &ast.pattern(*pattern).value
                                && let Some(id) = self.resolve(name.span)
                            {
                                locals_in_block.push(id);
                                if let Some(v) = value {
                                    let target = Atom::Val(Place::local(id));
                                    dbm.assign_via_temp(target, |d, t| {
                                        self.constrain_expr(env, d, t, *v);
                                    });
                                }
                            }
                        }
                        StmtKind::Expr(e) => {
                            reachable = self.step_loop_expr(env, dbm, *e, breaks, continues, depth);
                        }
                        StmtKind::Defer(e) => {
                            *dbm = self.loop_fallback_dbm(env, dbm, *e);
                        }
                        _ => {}
                    }
                }
                if !locals_in_block.is_empty() {
                    let set: HashSet<DefinitionId> = locals_in_block.into_iter().collect();
                    dbm.project_out(|a| match a {
                        Atom::Val(p) | Atom::Len(p) => set.contains(&p.root),
                        _ => false,
                    });
                }
                reachable
            }
            Expr::If {
                condition, yes, no, ..
            } => {
                let mut yes_dbm = dbm.clone();
                let mut no_dbm = dbm.clone();
                if let Condition::Expr(test) = condition {
                    let _ = self.step_loop_expr(env, &mut yes_dbm, *test, breaks, continues, depth);
                    no_dbm = yes_dbm.clone();
                    self.relate_proofs_in_dbm(env, &mut yes_dbm, *test, true);
                    self.relate_proofs_in_dbm(env, &mut no_dbm, *test, false);
                }
                let yes_falls =
                    self.step_loop_expr(env, &mut yes_dbm, *yes, breaks, continues, depth);
                let no_falls = if let Some(no_e) = no {
                    self.step_loop_expr(env, &mut no_dbm, *no_e, breaks, continues, depth)
                } else {
                    true
                };
                match (yes_falls && !yes_dbm.unsat, no_falls && !no_dbm.unsat) {
                    (true, true) => {
                        *dbm = Dbm::join(&yes_dbm, &no_dbm);
                        true
                    }
                    (true, false) => {
                        *dbm = yes_dbm;
                        true
                    }
                    (false, true) => {
                        *dbm = no_dbm;
                        true
                    }
                    (false, false) => false,
                }
            }
            Expr::Binary { op, left, right }
                if matches!(
                    op.value.as_str(),
                    "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | "&=" | "|=" | "^="
                ) =>
            {
                let _ = self.step_loop_expr(env, dbm, *right, breaks, continues, depth);
                self.step_assign_in_dbm(env, dbm, &op.value, *left, *right);
                true
            }
            Expr::Call { callee, args } => {
                for arg in args {
                    let _ = self.step_loop_expr(env, dbm, arg.value, breaks, continues, depth);
                }
                let callee_id = match &ast.expr(*callee).value {
                    Expr::Path(path) => self.resolve(path.span),
                    _ => None,
                };
                if let Some(id) = callee_id {
                    let intr = self.hir.intrinsic(id);
                    if matches!(intr, Some(Intrinsic::ArrayPush | Intrinsic::ArrayInsert))
                        && let Some(first) = args.first()
                        && let Some(coll) = self.resolve_place(env, first.value)
                    {
                        let len_atom = Atom::Len(coll);
                        dbm.assign_via_temp(len_atom.clone(), |d, t| {
                            d.add_eq(t.clone(), len_atom, 1);
                        });
                        return true;
                    }
                    if self.is_length_preserving_callee(id) || intr == Some(Intrinsic::Len) {
                        return true;
                    }
                    if matches!(
                        intr,
                        Some(
                            Intrinsic::ArrayPop | Intrinsic::ArrayPopFront | Intrinsic::ArrayRemove
                        )
                    ) && let Some(first) = args.first()
                        && let Some(coll) = self.resolve_place(env, first.value)
                    {
                        let len_atom = Atom::Len(coll);
                        let ge1 = dbm.lb(&len_atom).is_some_and(|l| l >= 1);
                        dbm.assign_via_temp(len_atom.clone(), |d, t| {
                            d.add_le(Atom::Zero, t.clone(), 0);
                            if ge1 {
                                d.add_eq(t.clone(), len_atom, -1);
                            } else {
                                d.add_le(t.clone(), len_atom, 0);
                            }
                        });
                        return true;
                    }
                    if matches!(intr, Some(Intrinsic::Panic)) {
                        return false;
                    }
                    // Known pure user/stdlib call: check callable effects/state if already declared.
                    if let Some(sig) = self.callables.get(&id)
                        && !sig.open_effects
                        && !sig.direct_open_effects
                        && sig.effect_vars.is_empty()
                        && !sig.open_state
                        && sig.effects.iter().all(|e| e == "io")
                        && sig.state.is_empty()
                    {
                        return true;
                    }
                }
                // Conservative invalidation for unknown / effectful / mutating calls.
                let mut mutated_vars = HashSet::new();
                let mut resized_colls = HashSet::new();
                let mut has_open = false;
                self.collect_loop_mutations(
                    env,
                    expr,
                    &mut mutated_vars,
                    &mut resized_colls,
                    &mut has_open,
                );
                for coll in resized_colls {
                    dbm.forget_matching(|a| matches!(a, Atom::Len(p) if p.root == coll));
                }
                if has_open {
                    dbm.forget_matching(|a| match a {
                        Atom::Val(p) | Atom::Len(p) => {
                            self.live.contains(&p.root)
                                && !(p.path.is_empty() && self.confined_locals.contains(&p.root))
                        }
                        _ => false,
                    });
                }
                true
            }
            Expr::Transfer { kind, value } => {
                if let Some(v) = value {
                    let _ = self.step_loop_expr(env, dbm, *v, breaks, continues, depth);
                }
                match kind {
                    ril_syntax::syntax::Transfer::Break => breaks.push(dbm.clone()),
                    ril_syntax::syntax::Transfer::Continue => continues.push(dbm.clone()),
                    ril_syntax::syntax::Transfer::Return => {}
                }
                false
            }
            Expr::While { body: inner, .. } | Expr::For { body: inner, .. } => {
                *dbm = self.loop_fallback_dbm(env, dbm, *inner);
                true
            }
            Expr::Match { value, arms, .. } => {
                let _ = self.step_loop_expr(env, dbm, *value, breaks, continues, depth);
                let mut acc: Option<Dbm> = None;
                for arm in arms {
                    let mut arm_dbm = dbm.clone();
                    if self.step_loop_expr(env, &mut arm_dbm, arm.body, breaks, continues, depth)
                        && !arm_dbm.unsat
                    {
                        acc = Some(match acc {
                            None => arm_dbm,
                            Some(cur) => Dbm::join(&cur, &arm_dbm),
                        });
                    }
                }
                match acc {
                    Some(joined) => {
                        *dbm = joined;
                        true
                    }
                    None => false,
                }
            }
            Expr::Pipeline { value, target, .. } => {
                let _ = self.step_loop_expr(env, dbm, *value, breaks, continues, depth);
                let _ = self.step_loop_expr(env, dbm, *target, breaks, continues, depth);
                *dbm = self.loop_fallback_dbm(env, dbm, expr);
                true
            }
            _ => true,
        }
    }

    fn step_assign_in_dbm(&self, env: &Env, dbm: &mut Dbm, op: &str, left: ExprId, right: ExprId) {
        if op == "="
            && let Some((base, index)) = self.is_map_indexed_write(env, left)
        {
            if let Some(map_place) = self.resolve_place(env, base) {
                let container = Atom::Val(map_place.clone());
                let key_atom = self.key_expr_to_atom(env, dbm, index);
                let already_in = key_atom
                    .as_ref()
                    .is_some_and(|k| dbm.entails_contains(&container, k));
                let already_out = key_atom
                    .as_ref()
                    .is_some_and(|k| dbm.entails_not_contains(&container, k));
                let seed_key = !self.container_key_contains_f64(env, base);
                // Forget sub-places `m.*` (value at old key may change).
                dbm.forget_matching(|a| match a {
                    Atom::Val(p) | Atom::Len(p) => {
                        p.root == map_place.root
                            && p.path.len() > map_place.path.len()
                            && p.path.starts_with(&map_place.path)
                    }
                    _ => false,
                });
                let len_atom = Atom::Len(map_place);
                if !already_in {
                    dbm.assign_via_temp(len_atom.clone(), |d, t| {
                        d.add_le(Atom::Zero, t.clone(), -1);
                        if already_out {
                            d.add_eq(t.clone(), len_atom, 1);
                        } else {
                            d.add_le(len_atom.clone(), t.clone(), 0);
                            d.add_le(t.clone(), len_atom, 1);
                        }
                    });
                }
                dbm.invalidate_container_insert(&container, key_atom.as_ref(), seed_key);
            } else {
                dbm.forget_matching(|a| match a {
                    Atom::Val(p) | Atom::Len(p) => self.live.contains(&p.root),
                    _ => false,
                });
            }
            return;
        }
        let is_elem = self.is_indexed_subplace(env, left);
        if let Some(place) = self.place(env, left) {
            let target = Atom::Val(place.clone());
            match op {
                "=" => {
                    dbm.assign_via_temp(target, |d, t| {
                        self.constrain_expr(env, d, t, right);
                    });
                    // Invalidate sub-places `place.*` and `Len(place.*)` (preserving parent `xs` if `place` is `xs.0`!).
                    dbm.forget_matching(|a| match a {
                        Atom::Val(p) => p.extends(&place) && p != &place,
                        Atom::Len(p) => p.extends(&place),
                        _ => false,
                    });
                }
                "+=" | "-=" => {
                    let sign_add = op == "+=";
                    let r_atom = self
                        .resolve_place(env, right)
                        .map(Atom::Val)
                        .unwrap_or_else(|| self.expr_to_atom(env, dbm, right));
                    dbm.assign_via_temp(target.clone(), |d, t| {
                        if let Some(c) = d.exact(&r_atom) {
                            let delta = if sign_add { c } else { c.saturating_neg() };
                            d.add_eq(t.clone(), target.clone(), delta);
                        } else if sign_add {
                            if let Some(lb) = d.lb(&r_atom)
                                && let Some(neg) = lb.checked_neg()
                            {
                                d.add_le(target.clone(), t.clone(), neg);
                            }
                            if let Some(ub) = d.ub(&r_atom) {
                                d.add_le(t.clone(), target.clone(), ub);
                            }
                            for (rhs_atom, k) in d.sum_upper_bounds(&target, &r_atom) {
                                d.add_le(t.clone(), rhs_atom, k);
                            }
                        } else {
                            if let Some(lb) = d.lb(&r_atom)
                                && let Some(neg) = lb.checked_neg()
                            {
                                d.add_le(t.clone(), target.clone(), neg);
                            }
                            if let Some(ub) = d.ub(&r_atom) {
                                d.add_le(target.clone(), t.clone(), ub);
                            }
                        }
                    });
                }
                _ => {
                    dbm.forget(&target);
                }
            }
        } else if is_elem {
            // Dynamic indexed write `xs[i] = v`: preserves `Len(xs)`, forgets any sub-places `xs.*`.
            if let Some(root) = self.indexed_root_place(env, left) {
                dbm.forget_matching(|a| match a {
                    Atom::Val(p) | Atom::Len(p) => {
                        p.root == root.root
                            && p.path.len() > root.path.len()
                            && p.path.starts_with(&root.path)
                    }
                    _ => false,
                });
            }
        } else {
            dbm.forget_matching(|a| match a {
                Atom::Val(p) | Atom::Len(p) => self.live.contains(&p.root),
                _ => false,
            });
        }
    }

    // -------------------------------------------------------------------------
    // Write, Call & Live Invalidation + Branch Merge
    // -------------------------------------------------------------------------

    pub(super) fn invalidate_loop_mutations(&self, env: &mut Env, body: ExprId) {
        env.refinements.dbm = self.loop_fallback_dbm(env, &env.refinements.dbm, body);
    }

    pub(super) fn collect_loop_mutations(
        &self,
        env: &Env,
        expr: ExprId,
        mutated_vars: &mut HashSet<DefinitionId>,
        resized_colls: &mut HashSet<DefinitionId>,
        has_open: &mut bool,
    ) {
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Binary { op, left, right } => {
                if matches!(
                    op.value.as_str(),
                    "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | "&=" | "|=" | "^="
                ) {
                    if op.value == "="
                        && let Some((base, _)) = self.is_map_indexed_write(env, *left)
                    {
                        if let Some(p) = self.resolve_place(env, base) {
                            mutated_vars.insert(p.root);
                            resized_colls.insert(p.root);
                        } else {
                            *has_open = true;
                        }
                    } else if let Some(p) = self.place(env, *left) {
                        mutated_vars.insert(p.root);
                        if !self.is_indexed_subplace(env, *left) {
                            resized_colls.insert(p.root);
                        }
                    } else if !self.is_indexed_subplace(env, *left) {
                        *has_open = true;
                    }
                }
                self.collect_loop_mutations(env, *left, mutated_vars, resized_colls, has_open);
                self.collect_loop_mutations(env, *right, mutated_vars, resized_colls, has_open);
            }
            Expr::Call { callee, args } => {
                let length_preserving = match &ast.expr(*callee).value {
                    Expr::Path(path) => self
                        .resolve(path.span)
                        .is_some_and(|id| self.is_length_preserving_callee(id)),
                    _ => false,
                };
                if !length_preserving {
                    for arg in args {
                        if matches!(arg.mode, Mode::Mut | Mode::Shared) {
                            if let Some(id) = self.resolve_local(env, arg.value) {
                                resized_colls.insert(id);
                            }
                            if arg.mode == Mode::Shared {
                                *has_open = true;
                            }
                        }
                    }
                }
                let is_known_safe = match &ast.expr(*callee).value {
                    Expr::Path(path) => self.resolve(path.span).is_some_and(|id| {
                        self.hir.operation_effect(id).is_none()
                            && (self.hir.intrinsic(id).is_some()
                                || self.callables.get(&id).is_some_and(|sig| {
                                    !sig.open_effects
                                        && !sig.direct_open_effects
                                        && sig.effect_vars.is_empty()
                                        && !sig.open_state
                                        && sig.effects.iter().all(|e| e == "io")
                                        && sig.state.is_empty()
                                }))
                    }),
                    _ => false,
                };
                if !is_known_safe && !length_preserving {
                    *has_open = true;
                }
                self.collect_loop_mutations(env, *callee, mutated_vars, resized_colls, has_open);
                for arg in args {
                    self.collect_loop_mutations(
                        env,
                        arg.value,
                        mutated_vars,
                        resized_colls,
                        has_open,
                    );
                }
            }
            Expr::Pipeline { value, target, .. } => {
                *has_open = true;
                self.collect_loop_mutations(env, *value, mutated_vars, resized_colls, has_open);
                self.collect_loop_mutations(env, *target, mutated_vars, resized_colls, has_open);
            }
            Expr::Block { statements, .. } => {
                for &stmt in statements {
                    self.collect_stmt_mutations(env, stmt, mutated_vars, resized_colls, has_open);
                }
            }
            Expr::If {
                condition, yes, no, ..
            } => {
                match condition {
                    Condition::Expr(e) | Condition::Binding { value: e, .. } => {
                        self.collect_loop_mutations(env, *e, mutated_vars, resized_colls, has_open);
                    }
                }
                self.collect_loop_mutations(env, *yes, mutated_vars, resized_colls, has_open);
                if let Some(no) = no {
                    self.collect_loop_mutations(env, *no, mutated_vars, resized_colls, has_open);
                }
            }
            Expr::While { condition, body } => {
                match condition {
                    Condition::Expr(e) | Condition::Binding { value: e, .. } => {
                        self.collect_loop_mutations(env, *e, mutated_vars, resized_colls, has_open);
                    }
                }
                self.collect_loop_mutations(env, *body, mutated_vars, resized_colls, has_open);
            }
            Expr::For { iterable, body, .. } => {
                self.collect_loop_mutations(env, *iterable, mutated_vars, resized_colls, has_open);
                self.collect_loop_mutations(env, *body, mutated_vars, resized_colls, has_open);
            }
            Expr::Match { value, arms, .. } => {
                self.collect_loop_mutations(env, *value, mutated_vars, resized_colls, has_open);
                for arm in arms {
                    if let Some(g) = arm.guard {
                        self.collect_loop_mutations(env, g, mutated_vars, resized_colls, has_open);
                    }
                    self.collect_loop_mutations(
                        env,
                        arm.body,
                        mutated_vars,
                        resized_colls,
                        has_open,
                    );
                }
            }
            Expr::Unary { value, .. }
            | Expr::Cast { value, .. }
            | Expr::Member { base: value, .. }
            | Expr::Transfer {
                value: Some(value), ..
            } => {
                self.collect_loop_mutations(env, *value, mutated_vars, resized_colls, has_open);
            }
            Expr::Index { base, index, .. } => {
                self.collect_loop_mutations(env, *base, mutated_vars, resized_colls, has_open);
                self.collect_loop_mutations(env, *index, mutated_vars, resized_colls, has_open);
            }
            Expr::Range { start, end, .. } => {
                if let Some(s) = start {
                    self.collect_loop_mutations(env, *s, mutated_vars, resized_colls, has_open);
                }
                if let Some(e) = end {
                    self.collect_loop_mutations(env, *e, mutated_vars, resized_colls, has_open);
                }
            }
            Expr::With {
                handlers,
                statements,
                ..
            } => {
                for h in handlers {
                    self.collect_loop_mutations(
                        env,
                        h.value,
                        mutated_vars,
                        resized_colls,
                        has_open,
                    );
                }
                for &stmt in statements {
                    self.collect_stmt_mutations(env, stmt, mutated_vars, resized_colls, has_open);
                }
            }
            Expr::Array(items) | Expr::Tuple(items) => {
                for &item in items {
                    self.collect_loop_mutations(env, item, mutated_vars, resized_colls, has_open);
                }
            }
            Expr::Wrap { args, .. } => {
                for arg in args {
                    self.collect_loop_mutations(
                        env,
                        arg.value,
                        mutated_vars,
                        resized_colls,
                        has_open,
                    );
                }
            }
            Expr::Record { fields, .. } => {
                for f in fields {
                    if let Some(v) = f.value {
                        self.collect_loop_mutations(env, v, mutated_vars, resized_colls, has_open);
                    }
                }
            }
            Expr::Map(entries) => {
                for &(k, v) in entries {
                    self.collect_loop_mutations(env, k, mutated_vars, resized_colls, has_open);
                    self.collect_loop_mutations(env, v, mutated_vars, resized_colls, has_open);
                }
            }
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let ril_syntax::syntax::StringPart::Interpolation(e) = part {
                        self.collect_loop_mutations(env, *e, mutated_vars, resized_colls, has_open);
                    }
                }
            }
            _ => {}
        }
    }

    fn collect_stmt_mutations(
        &self,
        env: &Env,
        stmt: StmtId,
        mutated_vars: &mut HashSet<DefinitionId>,
        resized_colls: &mut HashSet<DefinitionId>,
        has_open: &mut bool,
    ) {
        let ast = self.ast(env.file);
        match &ast.stmt(stmt).value.kind {
            StmtKind::Expr(e) | StmtKind::Defer(e) => {
                self.collect_loop_mutations(env, *e, mutated_vars, resized_colls, has_open);
            }
            StmtKind::Binding {
                value, fallback, ..
            } => {
                if let Some(v) = value {
                    self.collect_loop_mutations(env, *v, mutated_vars, resized_colls, has_open);
                }
                if let Some(f) = fallback {
                    self.collect_loop_mutations(env, *f, mutated_vars, resized_colls, has_open);
                }
            }
            StmtKind::With(h) => {
                self.collect_loop_mutations(env, h.value, mutated_vars, resized_colls, has_open);
            }
            _ => {}
        }
    }

    pub(super) fn note_array_push(&mut self, env: &mut Env, expr: ExprId, cause_span: Span) {
        // Exact monotonic +1 length update: preserves all `< len` / `<= len` bounds and advances `len(xs)` by +1!
        self.writes_place_preserving_len(env, expr, cause_span);
        if let Some(coll) = self.resolve_place(env, expr) {
            let len_atom = Atom::Len(coll);
            env.refinements
                .dbm
                .assign_via_temp(len_atom.clone(), |d, t| {
                    d.add_eq(t.clone(), len_atom, 1);
                });
        }
    }

    pub(super) fn note_array_pop(&mut self, env: &mut Env, expr: ExprId, cause_span: Span) {
        self.writes_place_preserving_len(env, expr, cause_span);
        if let Some(coll) = self.resolve_place(env, expr) {
            let len_atom = Atom::Len(coll);
            let ge1 = env.refinements.dbm.lb(&len_atom).is_some_and(|l| l >= 1);
            env.refinements
                .dbm
                .assign_via_temp(len_atom.clone(), |d, t| {
                    d.add_le(Atom::Zero, t.clone(), 0);
                    if ge1 {
                        d.add_eq(t.clone(), len_atom, -1);
                    } else {
                        d.add_le(t.clone(), len_atom, 0);
                    }
                });
        }
    }

    pub(super) fn note_array_clear(&mut self, env: &mut Env, expr: ExprId, cause_span: Span) {
        self.writes_place(env, expr, cause_span);
        if let Some(coll) = self.resolve_place(env, expr) {
            env.refinements.dbm.add_eq(Atom::Len(coll), Atom::Zero, 0);
        }
    }

    pub(super) fn note_map_insert(
        &mut self,
        env: &mut Env,
        coll_expr: ExprId,
        key_expr: Option<ExprId>,
        cause_span: Span,
    ) {
        self.invalidate_option_writes(env, coll_expr, cause_span);
        if let Some(coll) = self.resolve_place(env, coll_expr) {
            let mut dbm = std::mem::take(&mut env.refinements.dbm);
            let container = Atom::Val(coll.clone());
            let key_atom = key_expr.and_then(|k| self.key_expr_to_atom(env, &mut dbm, k));
            let already_in = key_atom
                .as_ref()
                .is_some_and(|k| dbm.entails_contains(&container, k));
            let already_out = key_atom
                .as_ref()
                .is_some_and(|k| dbm.entails_not_contains(&container, k));
            let seed_key = !self.container_key_contains_f64(env, coll_expr);
            dbm.forget_matching(|a| match a {
                Atom::Val(p) | Atom::Len(p) => {
                    p.root == coll.root
                        && p.path.len() > coll.path.len()
                        && p.path.starts_with(&coll.path)
                }
                _ => false,
            });
            let len_atom = Atom::Len(coll);
            if !already_in {
                dbm.assign_via_temp(len_atom.clone(), |d, t| {
                    d.add_le(Atom::Zero, t.clone(), -1);
                    if already_out {
                        d.add_eq(t.clone(), len_atom, 1);
                    } else {
                        d.add_le(len_atom.clone(), t.clone(), 0);
                        d.add_le(t.clone(), len_atom, 1);
                    }
                });
            }
            dbm.invalidate_container_insert(&container, key_atom.as_ref(), seed_key);
            env.refinements.dbm = dbm;
        } else {
            self.writes_place(env, coll_expr, cause_span);
        }
    }

    pub(super) fn note_map_remove(
        &mut self,
        env: &mut Env,
        coll_expr: ExprId,
        key_expr: Option<ExprId>,
        cause_span: Span,
    ) {
        self.invalidate_option_writes(env, coll_expr, cause_span);
        if let Some(coll) = self.resolve_place(env, coll_expr) {
            let mut dbm = std::mem::take(&mut env.refinements.dbm);
            let container = Atom::Val(coll.clone());
            let key_atom = key_expr.and_then(|k| self.key_expr_to_atom(env, &mut dbm, k));
            let already_in = key_atom
                .as_ref()
                .is_some_and(|k| dbm.entails_contains(&container, k));
            let already_out = key_atom
                .as_ref()
                .is_some_and(|k| dbm.entails_not_contains(&container, k));
            let seed_absent = !self.container_key_contains_f64(env, coll_expr);
            dbm.forget_matching(|a| match a {
                Atom::Val(p) | Atom::Len(p) => {
                    p.root == coll.root
                        && p.path.len() > coll.path.len()
                        && p.path.starts_with(&coll.path)
                }
                _ => false,
            });
            let len_atom = Atom::Len(coll);
            if !already_out {
                dbm.assign_via_temp(len_atom.clone(), |d, t| {
                    d.add_le(Atom::Zero, t.clone(), 0);
                    if already_in {
                        d.add_eq(t.clone(), len_atom, -1);
                    } else {
                        d.add_le(t.clone(), len_atom.clone(), 0);
                        d.add_le(len_atom, t.clone(), 1);
                    }
                });
            }
            dbm.invalidate_container_remove(&container, key_atom.as_ref(), seed_absent);
            env.refinements.dbm = dbm;
        } else {
            self.writes_place(env, coll_expr, cause_span);
        }
    }

    pub(super) fn note_map_pop_entry(
        &mut self,
        env: &mut Env,
        coll_expr: ExprId,
        cause_span: Span,
    ) {
        self.invalidate_option_writes(env, coll_expr, cause_span);
        if let Some(coll) = self.resolve_place(env, coll_expr) {
            let mut dbm = std::mem::take(&mut env.refinements.dbm);
            let container = Atom::Val(coll.clone());
            dbm.forget_matching(|a| match a {
                Atom::Val(p) | Atom::Len(p) => {
                    p.root == coll.root
                        && p.path.len() > coll.path.len()
                        && p.path.starts_with(&coll.path)
                }
                _ => false,
            });
            let len_atom = Atom::Len(coll);
            let ge1 = dbm.lb(&len_atom).is_some_and(|l| l >= 1);
            dbm.assign_via_temp(len_atom.clone(), |d, t| {
                d.add_le(Atom::Zero, t.clone(), 0);
                if ge1 {
                    d.add_eq(t.clone(), len_atom, -1);
                } else {
                    d.add_le(t.clone(), len_atom, 0);
                }
            });
            dbm.invalidate_container_remove(&container, None, false);
            env.refinements.dbm = dbm;
        } else {
            self.writes_place(env, coll_expr, cause_span);
        }
    }

    pub(super) fn note_map_clear(&mut self, env: &mut Env, coll_expr: ExprId, cause_span: Span) {
        self.writes_place(env, coll_expr, cause_span);
        if let Some(coll) = self.resolve_place(env, coll_expr) {
            env.refinements
                .dbm
                .invalidate_container_clear(&Atom::Val(coll.clone()));
            env.refinements.dbm.add_eq(Atom::Len(coll), Atom::Zero, 0);
        }
    }

    pub(super) fn is_length_preserving_callee(&self, id: DefinitionId) -> bool {
        if matches!(self.hir.intrinsic(id), Some(Intrinsic::ArraySwap)) {
            return true;
        }
        let def = self.hir.definition(id);
        self.hir.is_stdlib_file(def.name.span.file)
            && self.hir.primitive_module(id) == Some("Array")
            && def.name.value == "sort"
    }

    pub(super) fn is_array_clear_callee(&self, id: DefinitionId) -> bool {
        let def = self.hir.definition(id);
        self.hir.is_stdlib_file(def.name.span.file)
            && self.hir.primitive_module(id) == Some("Array")
            && def.name.value == "clear"
    }

    pub(super) fn assign_place(
        &mut self,
        env: &mut Env,
        op: &str,
        left: ExprId,
        right: ExprId,
        cause_span: Span,
    ) {
        // 1. Invalidate option narrowings as before.
        self.invalidate_option_writes(env, left, cause_span);
        // 2. Atomic DBM update via `assign_via_temp` (preserving parent `Len` on indexed writes!).
        let mut dbm = std::mem::take(&mut env.refinements.dbm);
        self.step_assign_in_dbm(env, &mut dbm, op, left, right);
        env.refinements.dbm = dbm;
        // 3. Re-seed composite lengths, call return proofs & type invariants on `=` assignments!
        if op == "="
            && let Some(place) = self.place(env, left)
        {
            self.seed_place_from_expr(env, &place, right);
            if let Some(rhs_ty) = self
                .types
                .get(&self.ast(env.file).expr(right).span)
                .cloned()
            {
                self.seed_type_invariants(env, &place, &rhs_ty);
            }
        }
    }

    pub(super) fn writes_place(&mut self, env: &mut Env, expr: ExprId, cause_span: Span) {
        self.writes_place_inner(env, expr, cause_span, false);
    }

    pub(super) fn writes_place_preserving_len(
        &mut self,
        env: &mut Env,
        expr: ExprId,
        cause_span: Span,
    ) {
        self.writes_place_inner(env, expr, cause_span, true);
    }

    fn is_indexed_subplace(&self, env: &Env, mut expr: ExprId) -> bool {
        let ast = self.ast(env.file);
        loop {
            match &ast.expr(expr).value {
                Expr::Index { .. } => return true,
                Expr::Member { base, .. } => expr = *base,
                _ => return false,
            }
        }
    }

    fn indexed_root_place(&self, env: &Env, mut expr: ExprId) -> Option<Place> {
        let ast = self.ast(env.file);
        loop {
            match &ast.expr(expr).value {
                Expr::Index { base, .. } => {
                    if let Some(p) = self.place(env, *base) {
                        return Some(p);
                    }
                    expr = *base;
                }
                Expr::Member { base, .. } => expr = *base,
                _ => return self.place(env, expr),
            }
        }
    }

    fn invalidate_place_proofs(&self, env: &mut Env, target: &Place) {
        env.refinements.dbm.forget_matching(|a| match a {
            Atom::Val(p) | Atom::Len(p) => p.extends(target),
            _ => false,
        });
    }

    fn invalidate_option_writes(&mut self, env: &mut Env, expr: ExprId, cause_span: Span) {
        let is_element_write = self.is_indexed_subplace(env, expr);
        if let Some(place) = self.place(env, expr) {
            let mut dropped = Vec::new();
            for (candidate, fact) in &mut env.refinements.options {
                if candidate.root == place.root
                    && candidate.path.iter().zip(&place.path).all(|(a, b)| a == b)
                {
                    if fact.invalidated.is_none() && fact.depth > 0 {
                        dropped.push(self.format_place(candidate));
                    }
                    fact.invalidated = Some((Code::E0310, cause_span));
                }
            }
            for path in dropped {
                self.narrow_drops.push(NarrowDrop {
                    span: cause_span,
                    path,
                    cause: NarrowDropCause::OverlappingWrite,
                });
            }
        } else if !is_element_write {
            self.invalidate_live(
                env,
                Code::E0310,
                cause_span,
                NarrowDropCause::OverlappingWrite,
            );
        }
    }

    fn writes_place_inner(
        &mut self,
        env: &mut Env,
        expr: ExprId,
        cause_span: Span,
        preserve_len: bool,
    ) {
        self.invalidate_option_writes(env, expr, cause_span);
        let is_element_write = self.is_indexed_subplace(env, expr);
        if let Some(place) = self.resolve_place(env, expr) {
            // Soundness fix: ALWAYS invalidate `Len(place.*)` when `!preserve_len`, even when
            // `place` is an indexed sub-collection `xs.0` (since `p.extends(&place)` preserves
            // parent `xs`'s length while wiping `xs.0` and `xs.0.*`!).
            env.refinements.dbm.forget_matching(|a| match a {
                Atom::Val(p) => p.extends(&place),
                Atom::Len(p) => !preserve_len && p.extends(&place),
                _ => false,
            });
        } else if is_element_write {
            if let Some(root) = self.indexed_root_place(env, expr) {
                env.refinements.dbm.forget_matching(|a| match a {
                    Atom::Val(p) | Atom::Len(p) => {
                        p.root == root.root
                            && p.path.len() > root.path.len()
                            && p.path.starts_with(&root.path)
                    }
                    _ => false,
                });
            }
        } else {
            self.invalidate_live_proofs(env);
        }
    }

    pub(super) fn invalidate_live_proofs(&self, env: &mut Env) {
        env.refinements.dbm.forget_matching(|a| match a {
            Atom::Val(p) | Atom::Len(p) => {
                self.live.contains(&p.root)
                    && !(p.path.is_empty() && self.confined_locals.contains(&p.root))
            }
            _ => false,
        });
    }

    pub(super) fn invalidate_live(
        &mut self,
        env: &mut Env,
        code: Code,
        cause_span: Span,
        cause: NarrowDropCause,
    ) {
        let mut dropped = Vec::new();
        for (place, fact) in &mut env.refinements.options {
            if self.live.contains(&place.root) && fact.invalidated.is_none() {
                if fact.depth > 0 {
                    dropped.push(self.format_place(place));
                }
                fact.invalidated = Some((code, cause_span));
            }
        }
        for path in dropped {
            self.narrow_drops.push(NarrowDrop {
                span: cause_span,
                path,
                cause,
            });
        }
        self.invalidate_live_proofs(env);
    }

    fn format_place(&self, place: &Place) -> String {
        let mut out = self.hir.definition(place.root).name.value.clone();
        for seg in &place.path {
            out.push('.');
            out.push_str(seg);
        }
        out
    }

    pub(super) fn merge_refinements(&self, a: &Env, b: &Env, a_ty: &Ty, b_ty: &Ty) -> Refinements {
        if a_ty == &Ty::Never {
            return b.refinements.clone();
        }
        if b_ty == &Ty::Never {
            return a.refinements.clone();
        }
        self.merge_refinement_states(&a.refinements, &b.refinements)
    }

    pub(super) fn merge_refinement_states(&self, a: &Refinements, b: &Refinements) -> Refinements {
        let mut options = HashMap::new();
        for (place, first) in &a.options {
            if let Some(second) = b.options.get(place) {
                let depth = first.depth.min(second.depth);
                let is_none = first.is_none && second.is_none;
                let invalidated = first.invalidated.or(second.invalidated);
                options.insert(
                    place.clone(),
                    Fact {
                        depth,
                        is_none,
                        invalidated,
                    },
                );
            }
        }
        let dbm = Dbm::join(&a.dbm, &b.dbm);
        Refinements {
            options,
            dbm,
            call_proofs: HashMap::new(),
        }
    }
}
