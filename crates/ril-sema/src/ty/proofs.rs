use std::collections::{HashMap, HashSet};

use num_traits::ToPrimitive;
use ril_hir::{DefinitionId, GuardKind, Intrinsic};
use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_syntax::syntax::{
    self, Condition, Expr, ExprId, Member, Pattern, StmtKind, Type, TypeDefinition,
};
use serde::{Deserialize, Serialize};

use super::{
    GenericValue, Ty, Value,
    check::{Checker, Env, Phase},
    dbm::{Atom, Dbm, KeyConst, Place, ProofAtom, ProofPlace, ProofPred, preds_entail},
    forms::partition_type_fn_params,
};

/// Polarity/modality of a static proof in `.rili` exports and call return proofs.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub(crate) enum ProofKind {
    #[default]
    Plain,
    Reflects,
    Implies,
    Ensures,
}

/// Canonical static proof recorded in `.rili` function exports for ABI hashing and variance checking.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportProof {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) pred: Option<ProofPred<ProofAtom>>,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub(crate) fallback: String,
    #[serde(default)]
    pub(crate) kind: ProofKind,
}

/// Checks whether a set of exported static proofs semantically entails every target exported proof.
pub(crate) fn export_proofs_entail(assumptions: &[ExportProof], targets: &[ExportProof]) -> bool {
    let plain_assumptions: Vec<ProofPred<ProofAtom>> = assumptions
        .iter()
        .filter(|p| p.kind == ProofKind::Plain)
        .filter_map(|p| p.pred.clone())
        .collect();
    let ensures_assumptions: Vec<ProofPred<ProofAtom>> = assumptions
        .iter()
        .filter(|p| p.kind == ProofKind::Ensures)
        .filter_map(|p| p.pred.clone())
        .collect();
    let implies_assumptions: Vec<ProofPred<ProofAtom>> = assumptions
        .iter()
        .filter(|p| matches!(p.kind, ProofKind::Reflects | ProofKind::Implies))
        .filter_map(|p| p.pred.clone())
        .collect();
    let reflects_assumptions: Vec<ProofPred<ProofAtom>> = assumptions
        .iter()
        .filter(|p| p.kind == ProofKind::Reflects)
        .filter_map(|p| p.pred.clone())
        .collect();
    for target in targets {
        if let Some(ref pred) = target.pred {
            let ok = match target.kind {
                ProofKind::Plain => preds_entail(&plain_assumptions, pred),
                ProofKind::Ensures => preds_entail(&ensures_assumptions, pred),
                ProofKind::Implies => preds_entail(&implies_assumptions, pred),
                ProofKind::Reflects => {
                    !reflects_assumptions.is_empty()
                        && preds_entail(&reflects_assumptions, pred)
                        && reflects_assumptions
                            .iter()
                            .all(|a| preds_entail(std::slice::from_ref(pred), a))
                }
            };
            if !ok {
                return false;
            }
        } else if !assumptions
            .iter()
            .any(|a| a.pred.is_none() && a.kind == target.kind && a.fallback == target.fallback)
        {
            return false;
        }
    }
    true
}

/// Cached lowered representation of a decidable proof Type Function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoweredTypeFn {
    pub(crate) pred: ProofPred<ProofAtom>,
    pub(crate) value_param_count: usize,
}

#[derive(Clone, Debug)]
pub(super) struct LowerError {
    pub(super) span: Span,
    pub(super) reason: &'static str,
}

/// An atom inside a call's instantiated return postcondition (stored per call `ExprId`).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum ReturnAtom {
    /// Refers to the call's return value (or its `Some`/`Ok` payload when `is_payload` is true).
    SubjectVal(Vec<String>),
    SubjectLen(Vec<String>),
    /// Refers to an already-resolved caller DBM atom (e.g., `xs` in `SameLen(xs)`).
    Caller(Atom),
}

#[derive(Clone, Debug)]
pub(super) struct CallReturnProof {
    pub(super) pred: ProofPred<ReturnAtom>,
    /// True when the proof constrains the `Some(v)` / `Ok(v)` payload of `?T` / `!<T, E>`.
    pub(super) is_payload: bool,
    pub(super) kind: ProofKind,
}

/// Linear difference expression used when lowering Type-Function bodies and runtime guards.
#[derive(Clone, Debug)]
pub(super) enum LinExpr<A> {
    Const(i128),
    Pos { atom: A, offset: i128 },
    Neg { atom: A, offset: i128 },
    Diff { pos: A, neg: A, offset: i128 },
}

impl<A: Clone + Eq> LinExpr<A> {
    pub(super) fn add(self, other: Self) -> Option<Self> {
        use LinExpr::*;
        match (self, other) {
            (Const(a), Const(b)) => Some(Const(a.checked_add(b)?)),
            (Pos { atom, offset }, Const(c)) | (Const(c), Pos { atom, offset }) => Some(Pos {
                atom,
                offset: offset.checked_add(c)?,
            }),
            (Neg { atom, offset }, Const(c)) | (Const(c), Neg { atom, offset }) => Some(Neg {
                atom,
                offset: offset.checked_add(c)?,
            }),
            (Diff { pos, neg, offset }, Const(c)) | (Const(c), Diff { pos, neg, offset }) => {
                Some(Diff {
                    pos,
                    neg,
                    offset: offset.checked_add(c)?,
                })
            }
            (
                Pos {
                    atom: a,
                    offset: oa,
                },
                Neg {
                    atom: b,
                    offset: ob,
                },
            )
            | (
                Neg {
                    atom: b,
                    offset: ob,
                },
                Pos {
                    atom: a,
                    offset: oa,
                },
            ) => {
                let offset = oa.checked_add(ob)?;
                if a == b {
                    Some(Const(offset))
                } else {
                    Some(Diff {
                        pos: a,
                        neg: b,
                        offset,
                    })
                }
            }
            _ => None,
        }
    }

    pub(super) fn neg(self) -> Option<Self> {
        use LinExpr::*;
        match self {
            Const(c) => Some(Const(c.checked_neg()?)),
            Pos { atom, offset } => Some(Neg {
                atom,
                offset: offset.checked_neg()?,
            }),
            Neg { atom, offset } => Some(Pos {
                atom,
                offset: offset.checked_neg()?,
            }),
            Diff { pos, neg, offset } => Some(Diff {
                pos: neg,
                neg: pos,
                offset: offset.checked_neg()?,
            }),
        }
    }

    pub(super) fn sub(self, other: Self) -> Option<Self> {
        self.add(other.neg()?)
    }

    /// Lower `lhs op rhs` into an NNF `ProofPred<A>`.
    pub(super) fn compare(op: &str, lhs: Self, rhs: Self) -> Option<ProofPred<A>> {
        let delta = lhs.sub(rhs)?;
        // `delta op 0`
        let (a, b, offset) = match delta {
            LinExpr::Const(k) => {
                let holds = match op {
                    "==" => k == 0,
                    "!=" => k != 0,
                    "<" => k < 0,
                    "<=" => k <= 0,
                    ">" => k > 0,
                    ">=" => k >= 0,
                    _ => return None,
                };
                return Some(if holds {
                    ProofPred::True
                } else {
                    ProofPred::False
                });
            }
            LinExpr::Pos { atom, offset } => (Some(atom), None, offset),
            LinExpr::Neg { atom, offset } => (None, Some(atom), offset),
            LinExpr::Diff { pos, neg, offset } => (Some(pos), Some(neg), offset),
        };
        // We have `(a - b) + offset op 0`, i.e., `a - b op -offset`.
        let rhs_c = offset.checked_neg()?;
        Some(match op {
            "<=" => ProofPred::diff_le(a, b, rhs_c),
            "<" => ProofPred::diff_le(a, b, rhs_c.checked_sub(1)?),
            ">=" => ProofPred::diff_le(b, a, offset),
            ">" => ProofPred::diff_le(b, a, offset.checked_sub(1)?),
            "==" => ProofPred::diff_eq(a, b, rhs_c),
            "!=" => ProofPred::diff_ne(a, b, rhs_c),
            _ => return None,
        })
    }
}

#[derive(Clone)]
enum TfLocal {
    Place(ProofPlace),
    Lin(LinExpr<ProofAtom>),
    Pred(ProofPred<ProofAtom>),
    Const(KeyConst),
}

/// An argument supplied to a static proof during instantiation.
#[derive(Clone)]
pub(super) enum ProofArgVal {
    Place(Place),
    Atom(Atom),
    Expr(ExprId),
    TupleExprs(Vec<ExprId>),
    Const(i128),
    KeyConst(KeyConst),
}

impl Checker<'_> {
    // -------------------------------------------------------------------------
    // 1. Type-Function AST -> NNF ProofPred Lowering (cached per DefinitionId)
    // -------------------------------------------------------------------------

    pub(crate) fn lower_type_fn(
        &mut self,
        tf_id: DefinitionId,
    ) -> Result<LoweredTypeFn, LowerError> {
        if let Some(cached) = self.lowered_proof_preds.get(&tf_id) {
            return cached.clone();
        }
        let mut stack = HashSet::new();
        let res = self.lower_type_fn_inner(tf_id, &mut stack);
        self.lowered_proof_preds.insert(tf_id, res.clone());
        res
    }

    fn lower_type_fn_inner(
        &mut self,
        tf_id: DefinitionId,
        stack: &mut HashSet<DefinitionId>,
    ) -> Result<LoweredTypeFn, LowerError> {
        let def = self.hir.definition(tf_id);
        let span = def.name.span;
        if !stack.insert(tf_id) {
            return Err(LowerError {
                span,
                reason: "recursive type function cannot be lowered to a symbolic runtime proof",
            });
        }
        let result = (|| {
            let Some(stmt) = def.stmt else {
                return Err(LowerError {
                    span,
                    reason: "type function has no body",
                });
            };
            let file = def.name.span.file;
            let StmtKind::Type(decl) = &self.ast(file).stmt(stmt).value.kind else {
                return Err(LowerError {
                    span,
                    reason: "expected a type function declaration",
                });
            };
            let TypeDefinition::Function(params, body) = &decl.definition else {
                return Err(LowerError {
                    span,
                    reason: "expected a type function",
                });
            };
            let params = params.clone();
            let body = *body;
            let (_, Some(subject), trailing) = partition_type_fn_params(&params) else {
                return Err(LowerError {
                    span,
                    reason: "proof type function requires a value subject parameter",
                });
            };
            let mut value_params: Vec<&syntax::GenericParam> =
                Vec::with_capacity(1 + trailing.len());
            value_params.push(subject);
            value_params.extend(trailing.iter());

            let mut locals: HashMap<DefinitionId, TfLocal> = HashMap::new();
            for (idx, vp) in value_params.iter().enumerate() {
                if let Some(id) = self.resolve(vp.name.span) {
                    locals.insert(
                        id,
                        TfLocal::Place(ProofPlace {
                            param_idx: idx,
                            path: Vec::new(),
                        }),
                    );
                }
            }

            // Conjoin any `|>` static checks attached directly to the TF's own value parameters.
            let mut conjuncts = Vec::new();
            for (idx, vp) in value_params.iter().enumerate() {
                for guard_path in &vp.guards {
                    if let Some(sub_id) = self.resolve(guard_path.span) {
                        let sub_lowered = self.lower_type_fn_inner(sub_id, stack)?;
                        let mut extra_places: Vec<TfLocal> = Vec::new();
                        extra_places.push(TfLocal::Place(ProofPlace {
                            param_idx: idx,
                            path: Vec::new(),
                        }));
                        if let Some(seg) = guard_path.segments.last() {
                            for arg in &seg.arguments {
                                if let syntax::GenericArg::Value(expr) = arg {
                                    extra_places.push(self.lower_tf_arg(file, *expr, &locals)?);
                                }
                            }
                        }
                        let substituted = substitute_tf_pred(&sub_lowered.pred, &extra_places)
                            .ok_or(LowerError {
                                span: guard_path.span,
                                reason: "could not substitute nested proof constraint",
                            })?;
                        conjuncts.push(substituted);
                    }
                }
            }

            let body_pred = self.lower_tf_body(file, body, &locals, stack)?;
            conjuncts.push(body_pred);
            Ok(LoweredTypeFn {
                pred: ProofPred::and(conjuncts),
                value_param_count: value_params.len(),
            })
        })();
        stack.remove(&tf_id);
        result
    }

    fn lower_tf_body(
        &mut self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
        stack: &mut HashSet<DefinitionId>,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        let ast = self.ast(file);
        let node = ast.expr(expr);
        let span = node.span;
        match &node.value {
            Expr::Quote(ty_id) => self.lower_tf_quote(file, *ty_id, locals, stack, span),
            Expr::Block { statements, .. } => {
                let mut local_env = locals.clone();
                let mut tail_pred = None;
                for (idx, &stmt_id) in statements.iter().enumerate() {
                    let is_last = idx + 1 == statements.len();
                    let stmt = self.ast(file).stmt(stmt_id);
                    match &stmt.value.kind {
                        StmtKind::Binding {
                            pattern,
                            value: Some(rhs),
                            fallback: None,
                            storage,
                            ..
                        } if !storage.variable => {
                            let Pattern::Binding(_, name) = &self.ast(file).pattern(*pattern).value
                            else {
                                return Err(LowerError {
                                    span: stmt.span,
                                    reason: "destructuring binding is outside the decidable proof fragment",
                                });
                            };
                            if let Some(id) = self.resolve(name.span) {
                                let val = self.lower_tf_arg(file, *rhs, &local_env)?;
                                local_env.insert(id, val);
                            }
                        }
                        StmtKind::Expr(e) if is_last => {
                            tail_pred = Some(self.lower_tf_body(file, *e, &local_env, stack)?);
                        }
                        _ => {
                            return Err(LowerError {
                                span: stmt.span,
                                reason: "statement is outside the decidable symbolic proof fragment; use a 'meta' parameter for arbitrary compile-time checks",
                            });
                        }
                    }
                }
                tail_pred.ok_or(LowerError {
                    span,
                    reason: "proof type function block must end with a type-value expression",
                })
            }
            Expr::If {
                condition: Condition::Expr(cond),
                yes,
                no: Some(no),
                ..
            } => {
                let c = self.lower_tf_bool(file, *cond, locals)?;
                let y = self.lower_tf_body(file, *yes, locals, stack)?;
                let n = self.lower_tf_body(file, *no, locals, stack)?;
                Ok(combine_if_pred(c, y, n))
            }
            Expr::Match { value, arms, .. } => {
                let scrut = *value;
                let arms = arms.clone();
                if let Ok(scrut_pred) = self.lower_tf_body(file, scrut, locals, stack) {
                    // Compositional `match <OtherPred<...>> { <never> -> ..., _ -> ... }`.
                    let mut true_branch = None;
                    let mut false_branch = None;
                    for arm in &arms {
                        if arm.guard.is_some() {
                            return Err(LowerError {
                                span,
                                reason: "guarded match arm is outside the decidable proof fragment",
                            });
                        }
                        let body_p = self.lower_tf_body(file, arm.body, locals, stack)?;
                        match &self.ast(file).pattern(arm.pattern).value {
                            Pattern::Type(ty_id) => match &self.ast(file).ty(*ty_id).value {
                                Type::Unit => {
                                    true_branch.get_or_insert(body_p);
                                }
                                Type::Named(path)
                                    if matches!(
                                        path.segments.as_slice(),
                                        [seg] if seg.name.value == "never"
                                    ) =>
                                {
                                    false_branch.get_or_insert(body_p);
                                }
                                _ => {
                                    return Err(LowerError {
                                        span,
                                        reason: "unsupported type pattern in proof type function",
                                    });
                                }
                            },
                            Pattern::Wildcard | Pattern::Binding(_, _) => {
                                true_branch.get_or_insert(body_p.clone());
                                false_branch.get_or_insert(body_p);
                            }
                            _ => {
                                return Err(LowerError {
                                    span,
                                    reason: "unsupported match pattern in proof type function",
                                });
                            }
                        }
                    }
                    let y = true_branch.unwrap_or(ProofPred::False);
                    let n = false_branch.unwrap_or(ProofPred::False);
                    return Ok(combine_if_pred(scrut_pred, y, n));
                }
                // Integer / bool match scrutinee.
                if let Ok(lin) = self.lower_tf_lin(file, scrut, locals) {
                    let mut prior_neg = Vec::new();
                    let mut disj = Vec::new();
                    for arm in &arms {
                        if arm.guard.is_some() {
                            return Err(LowerError {
                                span,
                                reason: "guarded match arm is outside the decidable proof fragment",
                            });
                        }
                        let pat_pred = self.lower_tf_int_pattern(file, arm.pattern, &lin)?;
                        let body_p = self.lower_tf_body(file, arm.body, locals, stack)?;
                        let mut branch = prior_neg.clone();
                        branch.push(pat_pred.clone());
                        branch.push(body_p);
                        disj.push(ProofPred::and(branch));
                        prior_neg.push(pat_pred.negate());
                    }
                    return Ok(ProofPred::or(disj));
                }
                Err(LowerError {
                    span,
                    reason: "match expression is outside the decidable symbolic proof fragment",
                })
            }
            Expr::Call { callee, .. } => {
                // `compile_error` / `compile_error_code` / `panic` -> `False` (never).
                if let Expr::Path(path) = &self.ast(file).expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && matches!(
                        self.hir.intrinsic(id),
                        Some(
                            Intrinsic::CompileError
                                | Intrinsic::CompileErrorCode
                                | Intrinsic::Panic
                        )
                    )
                {
                    return Ok(ProofPred::False);
                }
                Err(LowerError {
                    span,
                    reason: "runtime call in proof type function is outside the decidable fragment",
                })
            }
            _ => Err(LowerError {
                span,
                reason: "expression is outside the decidable symbolic proof fragment; use a 'meta' parameter for arbitrary compile-time checks",
            }),
        }
    }

    fn lower_tf_quote(
        &mut self,
        file: FileId,
        ty_id: syntax::TypeId,
        locals: &HashMap<DefinitionId, TfLocal>,
        stack: &mut HashSet<DefinitionId>,
        span: Span,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        let ty = self.ast(file).ty(ty_id).value.clone();
        match ty {
            Type::Unit => Ok(ProofPred::True),
            Type::Named(path)
                if matches!(
                    path.segments.as_slice(),
                    [seg] if seg.name.value == "never" && seg.arguments.is_empty()
                ) =>
            {
                Ok(ProofPred::False)
            }
            Type::Named(path) => {
                let Some(target_id) = self.resolve(path.span) else {
                    return Err(LowerError {
                        span,
                        reason: "unresolved type inside proof type function",
                    });
                };
                let sub = self.lower_type_fn_inner(target_id, stack)?;
                let mut val_args = Vec::new();
                if let Some(seg) = path.segments.last() {
                    for arg in &seg.arguments {
                        if let syntax::GenericArg::Value(expr) = arg {
                            val_args.push(self.lower_tf_arg(file, *expr, locals)?);
                        }
                    }
                }
                substitute_tf_pred(&sub.pred, &val_args).ok_or(LowerError {
                    span,
                    reason: "could not substitute arguments into nested proof type function",
                })
            }
            Type::Unquote(expr) => self.lower_tf_body(file, expr, locals, stack),
            _ => Err(LowerError {
                span,
                reason: "proof type function must return <()> or <never>",
            }),
        }
    }

    fn lower_tf_arg(
        &self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Result<TfLocal, LowerError> {
        if let Some(place) = self.lower_tf_place(file, expr, locals) {
            return Ok(TfLocal::Place(place));
        }
        if let Ok(lin) = self.lower_tf_lin(file, expr, locals) {
            return Ok(TfLocal::Lin(lin));
        }
        if let Ok(pred) = self.lower_tf_bool(file, expr, locals) {
            return Ok(TfLocal::Pred(pred));
        }
        if let Some(kc) = self.lower_tf_key_const(file, expr) {
            return Ok(TfLocal::Const(kc));
        }
        Err(LowerError {
            span: self.ast(file).expr(expr).span,
            reason: "expression is outside the decidable symbolic proof fragment",
        })
    }

    fn lower_tf_key_const(&self, file: FileId, expr: ExprId) -> Option<KeyConst> {
        let ast = self.ast(file);
        match &ast.expr(expr).value {
            Expr::Unit => Some(KeyConst::Unit),
            Expr::Literal(lit) => match super::literal(lit).ok()? {
                Value::Int(n) => n.to_i128().map(KeyConst::Int),
                Value::Str(s) => Some(KeyConst::Str(s)),
                Value::Bool(b) => Some(KeyConst::Bool(b)),
                Value::Bytes(b) => Some(KeyConst::Bytes(b)),
                _ => None,
            },
            Expr::Unary { op, value } if op.value == "-" => {
                if let Some(KeyConst::Int(c)) = self.lower_tf_key_const(file, *value) {
                    c.checked_neg().map(KeyConst::Int)
                } else {
                    None
                }
            }
            Expr::Path(path) => {
                let id = self.resolve(path.span)?;
                match self.static_constant_value(id)? {
                    Value::Int(n) => n.to_i128().map(KeyConst::Int),
                    Value::Str(s) => Some(KeyConst::Str(s.clone())),
                    Value::Bool(b) => Some(KeyConst::Bool(*b)),
                    Value::Bytes(b) => Some(KeyConst::Bytes(b.clone())),
                    Value::Unit => Some(KeyConst::Unit),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn lower_tf_key_atom(
        &self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Option<ProofAtom> {
        if let Some(place) = self.lower_tf_place(file, expr, locals) {
            return Some(ProofAtom::Val(place));
        }
        if let Some(kc) = self.lower_tf_key_const(file, expr) {
            return Some(ProofAtom::Const(kc));
        }
        None
    }

    fn lower_tf_int_pattern(
        &self,
        file: FileId,
        pat: syntax::PatternId,
        scrut: &LinExpr<ProofAtom>,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        let ast = self.ast(file);
        let node = ast.pattern(pat);
        match &node.value {
            Pattern::Wildcard | Pattern::Binding(_, _) => Ok(ProofPred::True),
            Pattern::Literal(lit) => {
                let Value::Int(n) = super::literal(lit).map_err(|_| LowerError {
                    span: node.span,
                    reason: "non-integer literal pattern in proof type function",
                })?
                else {
                    return Err(LowerError {
                        span: node.span,
                        reason: "non-integer literal pattern in proof type function",
                    });
                };
                let c = n.to_i128().ok_or(LowerError {
                    span: node.span,
                    reason: "integer literal exceeds proof solver width",
                })?;
                LinExpr::compare("==", scrut.clone(), LinExpr::Const(c)).ok_or(LowerError {
                    span: node.span,
                    reason: "non-linear pattern comparison",
                })
            }
            Pattern::Range {
                low,
                high,
                inclusive,
            } => {
                let mut parts = Vec::new();
                if let Value::Int(n) = super::literal(low).map_err(|_| LowerError {
                    span: node.span,
                    reason: "non-integer range pattern",
                })? && let Some(c) = n.to_i128()
                {
                    parts.push(
                        LinExpr::compare(">=", scrut.clone(), LinExpr::Const(c)).ok_or(
                            LowerError {
                                span: node.span,
                                reason: "non-linear range comparison",
                            },
                        )?,
                    );
                }
                if let Value::Int(n) = super::literal(high).map_err(|_| LowerError {
                    span: node.span,
                    reason: "non-integer range pattern",
                })? && let Some(c) = n.to_i128()
                {
                    let op = if *inclusive { "<=" } else { "<" };
                    parts.push(
                        LinExpr::compare(op, scrut.clone(), LinExpr::Const(c)).ok_or(
                            LowerError {
                                span: node.span,
                                reason: "non-linear range comparison",
                            },
                        )?,
                    );
                }
                Ok(ProofPred::and(parts))
            }
            Pattern::Or(items) => {
                let mut alts = Vec::new();
                for &item in items {
                    alts.push(self.lower_tf_int_pattern(file, item, scrut)?);
                }
                Ok(ProofPred::or(alts))
            }
            _ => Err(LowerError {
                span: node.span,
                reason: "unsupported pattern in proof type function",
            }),
        }
    }

    fn lower_tf_bool(
        &self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        let ast = self.ast(file);
        let node = ast.expr(expr);
        let span = node.span;
        match &node.value {
            Expr::Literal(lit) => match super::literal(lit) {
                Ok(Value::Bool(true)) => Ok(ProofPred::True),
                Ok(Value::Bool(false)) => Ok(ProofPred::False),
                _ => Err(LowerError {
                    span,
                    reason: "expected boolean condition in proof type function",
                }),
            },
            Expr::Path(path) => {
                if let Some(id) = self.resolve(path.span)
                    && let Some(TfLocal::Pred(p)) = locals.get(&id)
                {
                    return Ok(p.clone());
                }
                Err(LowerError {
                    span,
                    reason: "boolean variable is outside the decidable proof fragment",
                })
            }
            Expr::Unary { op, value } if op.value == "!" => {
                Ok(self.lower_tf_bool(file, *value, locals)?.negate())
            }
            Expr::Binary { op, left, right } => match op.value.as_str() {
                "&&" => Ok(ProofPred::and(vec![
                    self.lower_tf_bool(file, *left, locals)?,
                    self.lower_tf_bool(file, *right, locals)?,
                ])),
                "||" => Ok(ProofPred::or(vec![
                    self.lower_tf_bool(file, *left, locals)?,
                    self.lower_tf_bool(file, *right, locals)?,
                ])),
                "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                    let l = self.lower_tf_lin(file, *left, locals)?;
                    let r = self.lower_tf_lin(file, *right, locals)?;
                    LinExpr::compare(&op.value, l, r).ok_or(LowerError {
                        span,
                        reason: "non-linear integer comparison is outside the decidable proof fragment",
                    })
                }
                _ => Err(LowerError {
                    span,
                    reason: "unsupported boolean operator in proof type function",
                }),
            },
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && (matches!(
                        self.hir.intrinsic(id),
                        Some(Intrinsic::HasKey | Intrinsic::MapContains)
                    ) || self.is_set_stdlib_callee(id, "contains"))
                    && let [c_arg, k_arg] = args.as_slice()
                    && let Some(c_place) = self.lower_tf_place(file, c_arg.value, locals)
                    && let Some(k_atom) = self.lower_tf_key_atom(file, k_arg.value, locals)
                {
                    return Ok(ProofPred::Contains {
                        container: ProofAtom::Val(c_place),
                        key: k_atom,
                        negated: false,
                    });
                }
                Err(LowerError {
                    span,
                    reason: "condition is outside the decidable symbolic proof fragment",
                })
            }
            _ => Err(LowerError {
                span,
                reason: "condition is outside the decidable symbolic proof fragment",
            }),
        }
    }

    fn lower_tf_place(
        &self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Option<ProofPlace> {
        let ast = self.ast(file);
        match &ast.expr(expr).value {
            Expr::Unary { op, value } if matches!(op.value.as_str(), "ref" | "^mut") => {
                self.lower_tf_place(file, *value, locals)
            }
            Expr::Path(path) => {
                let id = self.resolve(path.span)?;
                match locals.get(&id)? {
                    TfLocal::Place(p) => Some(p.clone()),
                    _ => None,
                }
            }
            Expr::Member {
                base,
                member,
                safe: false,
            } => {
                let mut p = self.lower_tf_place(file, *base, locals)?;
                match member {
                    Member::Name(n) | Member::Index(n) => p.path.push(n.value.clone()),
                    Member::Computed(_) => return None,
                }
                Some(p)
            }
            Expr::Call { callee, args } => {
                let Expr::Path(path) = &ast.expr(*callee).value else {
                    return None;
                };
                let id = self.resolve(path.span)?;
                if self.hir.intrinsic(id) == Some(Intrinsic::Inner)
                    && let [arg] = args.as_slice()
                {
                    let mut p = self.lower_tf_place(file, arg.value, locals)?;
                    p.path.push("#inner".to_owned());
                    return Some(p);
                }
                None
            }
            _ => None,
        }
    }

    fn lower_tf_lin(
        &self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Result<LinExpr<ProofAtom>, LowerError> {
        let ast = self.ast(file);
        let node = ast.expr(expr);
        let span = node.span;
        if let Some(Value::Int(n)) = self.static_values.get(&span)
            && let Some(c) = n.to_i128()
        {
            return Ok(LinExpr::Const(c));
        }
        match &node.value {
            Expr::Literal(lit) => match super::literal(lit) {
                Ok(Value::Int(n)) => n.to_i128().map(LinExpr::Const).ok_or(LowerError {
                    span,
                    reason: "integer literal exceeds proof solver width",
                }),
                _ => Err(LowerError {
                    span,
                    reason: "only integer arithmetic is supported in symbolic runtime proofs",
                }),
            },
            Expr::Path(path) => {
                let Some(id) = self.resolve(path.span) else {
                    return Err(LowerError {
                        span,
                        reason: "unresolved identifier in proof type function",
                    });
                };
                if let Some(local) = locals.get(&id) {
                    return match local {
                        TfLocal::Place(p) => Ok(LinExpr::Pos {
                            atom: ProofAtom::Val(p.clone()),
                            offset: 0,
                        }),
                        TfLocal::Lin(l) => Ok(l.clone()),
                        TfLocal::Pred(_) | TfLocal::Const(_) => Err(LowerError {
                            span,
                            reason: "non-integer value used in integer expression",
                        }),
                    };
                }
                if let Some(Value::Int(n)) = self.static_constant_value(id)
                    && let Some(c) = n.to_i128()
                {
                    return Ok(LinExpr::Const(c));
                }
                Err(LowerError {
                    span,
                    reason: "unsupported identifier in proof type function",
                })
            }
            Expr::Member { safe: false, .. } => {
                let p = self.lower_tf_place(file, expr, locals).ok_or(LowerError {
                    span,
                    reason: "unsupported field access in proof type function",
                })?;
                Ok(LinExpr::Pos {
                    atom: ProofAtom::Val(p),
                    offset: 0,
                })
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                {
                    if self.hir.intrinsic(id) == Some(Intrinsic::Len)
                        && let [arg] = args.as_slice()
                        && let Some(p) = self.lower_tf_place(file, arg.value, locals)
                    {
                        return Ok(LinExpr::Pos {
                            atom: ProofAtom::Len(p),
                            offset: 0,
                        });
                    }
                    if self.hir.intrinsic(id) == Some(Intrinsic::Inner)
                        && let Some(p) = self.lower_tf_place(file, expr, locals)
                    {
                        return Ok(LinExpr::Pos {
                            atom: ProofAtom::Val(p),
                            offset: 0,
                        });
                    }
                }
                Err(LowerError {
                    span,
                    reason: "call expression is outside the decidable symbolic proof fragment",
                })
            }
            Expr::Unary { op, value } if op.value == "-" => self
                .lower_tf_lin(file, *value, locals)?
                .neg()
                .ok_or(LowerError {
                    span,
                    reason: "arithmetic overflow in proof expression",
                }),
            Expr::Binary { op, left, right } if matches!(op.value.as_str(), "+" | "-") => {
                let l = self.lower_tf_lin(file, *left, locals)?;
                let r = self.lower_tf_lin(file, *right, locals)?;
                let combined = if op.value == "+" { l.add(r) } else { l.sub(r) };
                combined.ok_or(LowerError {
                    span,
                    reason: "non-difference arithmetic is outside the decidable symbolic proof fragment",
                })
            }
            _ => Err(LowerError {
                span,
                reason: "non-linear arithmetic is outside the decidable symbolic proof fragment",
            }),
        }
    }
}

#[derive(Clone)]
pub(super) enum CombinatorArg {
    Expr(ExprId),
    TypePath(syntax::Path),
}

impl Checker<'_> {
    // -------------------------------------------------------------------------
    // 2. Guard Extraction & Instantiation Helpers
    // -------------------------------------------------------------------------

    pub(super) fn extract_proof_combinator(
        &self,
        file: FileId,
        guard: ExprId,
    ) -> Option<(ProofKind, CombinatorArg)> {
        let GuardKind::StaticProofPrimitive(id) = self.hir.classify_guard(file, guard) else {
            return None;
        };
        let kind = match self.hir.definition(id).name.value.as_str() {
            "Reflects" => ProofKind::Reflects,
            "Implies" => ProofKind::Implies,
            "Ensures" => ProofKind::Ensures,
            _ => return None,
        };
        let ast = self.ast(file);
        let Expr::Path(path) = &ast.expr(guard).value else {
            return None;
        };
        let seg = path.segments.last()?;
        match seg.arguments.as_slice() {
            [syntax::GenericArg::Value(pred)] => Some((kind, CombinatorArg::Expr(*pred))),
            [syntax::GenericArg::Type(ty_id)] => {
                if let Type::Named(pred_path) = &ast.ty(*ty_id).value {
                    Some((kind, CombinatorArg::TypePath(pred_path.clone())))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn lower_combinator_arg(
        &mut self,
        file: FileId,
        arg: &CombinatorArg,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        match arg {
            CombinatorArg::Expr(expr) => self.lower_combinator_pred(file, *expr, locals),
            CombinatorArg::TypePath(path) => self.lower_combinator_path(file, path, locals),
        }
    }

    fn lower_combinator_path(
        &mut self,
        file: FileId,
        path: &syntax::Path,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        let Some(tf_id) = self.resolve(path.span) else {
            return Err(LowerError {
                span: path.span,
                reason: "unresolved proof combinator predicate",
            });
        };
        if self.hir.definition(tf_id).kind != ril_hir::DefinitionKind::Type {
            return Err(LowerError {
                span: path.span,
                reason: "expected proof type function in combinator",
            });
        }
        let angle_args = path
            .segments
            .last()
            .map(|s| s.arguments.clone())
            .unwrap_or_default();
        let lowered = self.lower_type_fn(tf_id)?;
        let mut sub_args = Vec::with_capacity(lowered.value_param_count);
        for arg in angle_args.iter().take(lowered.value_param_count) {
            let syntax::GenericArg::Value(arg_expr) = arg else {
                return Err(LowerError {
                    span: path.span,
                    reason: "expected value argument in proof combinator",
                });
            };
            sub_args.push(self.lower_tf_arg(file, *arg_expr, locals)?);
        }
        substitute_tf_pred(&lowered.pred, &sub_args).ok_or(LowerError {
            span: path.span,
            reason: "could not substitute proof combinator argument",
        })
    }

    fn lower_combinator_pred(
        &mut self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Result<ProofPred<ProofAtom>, LowerError> {
        let ast = self.ast(file);
        let node = ast.expr(expr);
        match &node.value {
            Expr::Binary { op, left, right } if op.value == "&&" => {
                let l = self.lower_combinator_pred(file, *left, locals)?;
                let r = self.lower_combinator_pred(file, *right, locals)?;
                Ok(ProofPred::and(vec![l, r]))
            }
            Expr::Binary { op, left, right } if op.value == "||" => {
                let l = self.lower_combinator_pred(file, *left, locals)?;
                let r = self.lower_combinator_pred(file, *right, locals)?;
                Ok(ProofPred::or(vec![l, r]))
            }
            Expr::Unary { op, value } if op.value == "!" => {
                Ok(self.lower_combinator_pred(file, *value, locals)?.negate())
            }
            Expr::Path(path) => {
                let path = path.clone();
                if let Some(tf_id) = self.resolve(path.span)
                    && self.hir.definition(tf_id).kind == ril_hir::DefinitionKind::Type
                {
                    return self.lower_combinator_path(file, &path, locals);
                }
                self.lower_tf_bool(file, expr, locals)
            }
            _ => self.lower_tf_bool(file, expr, locals),
        }
    }

    pub(super) fn extract_static_proof_angle_args(
        &self,
        tf_id: DefinitionId,
        angle_args: &[syntax::GenericArg],
    ) -> Option<Vec<Option<ExprId>>> {
        let def = self.hir.definition(tf_id);
        let stmt = def.stmt?;
        let StmtKind::Type(decl) = &self.ast(def.name.span.file).stmt(stmt).value.kind else {
            return None;
        };
        let TypeDefinition::Function(tf_params, _) = &decl.definition else {
            return None;
        };
        let (_, Some(_), trailing) = partition_type_fn_params(tf_params) else {
            return None;
        };
        let mut bound: Vec<Option<ExprId>> = vec![None; trailing.len()];
        for (idx, slot) in bound.iter_mut().enumerate() {
            if let Some(syntax::GenericArg::Value(expr)) = angle_args.get(idx) {
                *slot = Some(*expr);
            }
        }
        Some(bound)
    }

    /// Extract `(tf_id, extra_args_by_trailing_param_idx)` from a static proof guard AST node.
    pub(super) fn extract_static_proof_guard(
        &self,
        file: FileId,
        guard: ExprId,
    ) -> Option<(DefinitionId, Vec<Option<ExprId>>)> {
        let GuardKind::StaticProof(tf_id) = self.hir.classify_guard(file, guard) else {
            return None;
        };
        let ast = self.ast(file);
        let mut node = ast.expr(guard);
        if let Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            node = ast.expr(*value);
        }
        let Expr::Path(path) = &node.value else {
            return None;
        };
        let angle_args = path
            .segments
            .last()
            .map(|s| s.arguments.as_slice())
            .unwrap_or(&[]);
        let bound = self.extract_static_proof_angle_args(tf_id, angle_args)?;
        Some((tf_id, bound))
    }

    // -------------------------------------------------------------------------
    // 3. Callee Entry Seeding & Default Verification
    // -------------------------------------------------------------------------

    pub(super) fn param_static_proofs(
        &self,
        file: FileId,
        param: &syntax::Parameter,
    ) -> Vec<(DefinitionId, Vec<Option<ExprId>>, Span)> {
        let mut out = Vec::new();
        if let Some(ty_id) = param.ty
            && let Some((tf_id, angle_args, span)) = self.bare_proof_type_info(file, ty_id)
            && let Some(extra) = self.extract_static_proof_angle_args(tf_id, &angle_args)
        {
            out.push((tf_id, extra, span));
        }
        for &guard in &param.guards {
            if let Some((tf_id, extra)) = self.extract_static_proof_guard(file, guard) {
                out.push((tf_id, extra, self.ast(file).expr(guard).span));
            }
        }
        out
    }

    fn return_static_proofs(
        &self,
        file: FileId,
        sig: &syntax::Signature,
    ) -> Vec<(DefinitionId, Vec<Option<ExprId>>, Span)> {
        let mut out = Vec::new();
        if let Some((tf_id, angle_args, span)) = self.bare_proof_type_info(file, sig.result)
            && let Some(extra) = self.extract_static_proof_angle_args(tf_id, &angle_args)
        {
            out.push((tf_id, extra, span));
        }
        for &guard in &sig.guards {
            if let Some((tf_id, extra)) = self.extract_static_proof_guard(file, guard) {
                out.push((tf_id, extra, self.ast(file).expr(guard).span));
            }
        }
        out
    }

    pub(super) fn seed_fn_param_proofs(&mut self, env: &mut Env, fun: &syntax::Function) {
        for p in &fun.signature.params {
            if p.is_meta {
                continue;
            }
            let Some(name) = &p.name else { continue };
            let Some(param_id) = self.resolve(name.span) else {
                continue;
            };
            for (tf_id, extra, _) in self.param_static_proofs(env.file, p) {
                let Ok(lowered) = self.lower_type_fn(tf_id) else {
                    continue;
                };
                let mut arg_vals = Vec::with_capacity(1 + extra.len());
                arg_vals.push(ProofArgVal::Place(Place::local(param_id)));
                for opt in extra {
                    if let Some(e) = opt {
                        arg_vals.push(ProofArgVal::Expr(e));
                    } else {
                        arg_vals.push(ProofArgVal::Const(0));
                    }
                }
                let mut scratch = env.refinements.dbm.clone();
                if let Some(pred) =
                    self.instantiate_proof_pred(env, &mut scratch, &lowered.pred, &arg_vals)
                {
                    scratch.assume(&pred);
                    scratch.forget_temps();
                    env.refinements.dbm = scratch;
                }
            }
            self.seed_guard_proofs(env, p);
        }
    }

    pub(super) fn check_default_param_proofs(
        &mut self,
        env: &mut Env,
        fun: &syntax::Function,
        param_idx: usize,
        default_expr: ExprId,
    ) {
        let Some(p) = fun.signature.params.get(param_idx) else {
            return;
        };
        if p.is_meta || env.shadow {
            return;
        }
        let default_span = self.ast(env.file).expr(default_expr).span;
        for (tf_id, extra, guard_span) in self.param_static_proofs(env.file, p) {
            let mut arg_vals = Vec::with_capacity(1 + extra.len());
            arg_vals.push(ProofArgVal::Expr(default_expr));
            for opt in extra {
                if let Some(e) = opt {
                    arg_vals.push(ProofArgVal::Expr(e));
                } else {
                    arg_vals.push(ProofArgVal::Const(0));
                }
            }
            self.verify_proof_obligation(
                env,
                tf_id,
                &arg_vals,
                default_span,
                guard_span,
                "default argument does not satisfy static proof",
            );
        }
    }

    // -------------------------------------------------------------------------
    // 4. Callee Exit Return Proof Verification (with active `defer` invalidation!)
    // -------------------------------------------------------------------------

    pub(super) fn verify_fn_return_proofs(
        &mut self,
        env: &mut Env,
        expr: Option<ExprId>,
        report_span: Span,
    ) {
        if env.shadow || env.return_proofs.is_empty() {
            return;
        }
        if let Some(e) = expr {
            let e_span = self.ast(env.file).expr(e).span;
            if self.types.get(&e_span).is_some_and(|t| *t == Ty::Never) {
                return;
            }
        }
        // Apply active `defer` mutations onto a copy of `env` BEFORE checking return proofs,
        // because `defer` blocks execute after evaluating the return expression and before
        // returning to the caller.
        let mut exit_env = env.clone();
        let defers = exit_env.active_defers.clone();
        for defer_expr in defers {
            self.invalidate_loop_mutations(&mut exit_env, defer_expr);
        }

        let is_fallible_return = exit_env.expected_return.as_ref().is_some_and(|r| {
            let norm = self.normalize(r);
            norm.is_option(self.hir) || norm.is_result(self.hir)
        });

        let return_proofs = exit_env.return_proofs.clone();
        for proof_ref in return_proofs {
            if let super::check::ReturnProofRef::Expr(guard) = proof_ref
                && let Some((kind, pred_arg)) = self.extract_proof_combinator(exit_env.file, guard)
            {
                let guard_span = self.ast(exit_env.file).expr(guard).span;
                let pred_span = match &pred_arg {
                    CombinatorArg::Expr(e) => self.ast(exit_env.file).expr(*e).span,
                    CombinatorArg::TypePath(p) => p.span,
                };
                let mut locals: HashMap<DefinitionId, TfLocal> = HashMap::new();
                let mut arg_vals: Vec<ProofArgVal> = Vec::new();
                for (_, def_id) in self.hir.references_within(pred_span) {
                    if !locals.contains_key(&def_id)
                        && self.hir.definition(def_id).kind == ril_hir::DefinitionKind::Local
                    {
                        let idx = arg_vals.len();
                        locals.insert(
                            def_id,
                            TfLocal::Place(ProofPlace {
                                param_idx: idx,
                                path: Vec::new(),
                            }),
                        );
                        arg_vals.push(ProofArgVal::Place(Place::local(def_id)));
                    }
                }
                let Ok(lowered_pred) = self.lower_combinator_arg(exit_env.file, &pred_arg, &locals)
                else {
                    self.error(
                        Code::E0323,
                        guard_span,
                        "proof combinator predicate is outside the decidable DBM fragment",
                    );
                    continue;
                };
                match kind {
                    ProofKind::Ensures => {
                        let mut scratch = exit_env.refinements.dbm.clone();
                        let ok = self
                            .instantiate_proof_pred(
                                &exit_env,
                                &mut scratch,
                                &lowered_pred,
                                &arg_vals,
                            )
                            .is_some_and(|p| scratch.entails(&p));
                        if !ok {
                            let mut diag = Diagnostic::error(
                                Code::E0323,
                                report_span,
                                "function exit does not satisfy Ensures postcondition",
                            );
                            diag = diag.with_label(guard_span, "required by this Ensures clause");
                            self.diagnostics.push(diag);
                        }
                    }
                    ProofKind::Implies | ProofKind::Reflects => {
                        let Some(ret_expr) = expr else { continue };
                        let mut true_env = exit_env.clone();
                        self.relate(&mut true_env, ret_expr, true);
                        let mut true_scratch = true_env.refinements.dbm.clone();
                        let true_ok = self
                            .instantiate_proof_pred(
                                &true_env,
                                &mut true_scratch,
                                &lowered_pred,
                                &arg_vals,
                            )
                            .is_some_and(|p| true_scratch.entails(&p));
                        if !true_ok {
                            let label = if kind == ProofKind::Reflects {
                                "Reflects"
                            } else {
                                "Implies"
                            };
                            let mut diag = Diagnostic::error(
                                Code::E0323,
                                report_span,
                                format!("true return path does not satisfy {label} predicate"),
                            );
                            diag = diag.with_label(guard_span, "required by this proof guard");
                            self.diagnostics.push(diag);
                        }
                        if kind == ProofKind::Reflects {
                            let mut false_env = exit_env.clone();
                            self.relate(&mut false_env, ret_expr, false);
                            let mut false_scratch = false_env.refinements.dbm.clone();
                            let direct_false_ok = self
                                .instantiate_proof_pred(
                                    &false_env,
                                    &mut false_scratch,
                                    &lowered_pred.negate(),
                                    &arg_vals,
                                )
                                .is_some_and(|p| false_scratch.entails(&p));
                            // Contrapositive check: `!ret => !P` is equivalent to `P => ret`,
                            // which avoids losing conjunctive `&&` facts under negation!
                            let contrapositive_ok = if direct_false_ok {
                                true
                            } else if let Ok(ret_pred) =
                                self.lower_combinator_pred(exit_env.file, ret_expr, &locals)
                            {
                                let mut cp_scratch = exit_env.refinements.dbm.clone();
                                if let Some(inst_p) = self.instantiate_proof_pred(
                                    &exit_env,
                                    &mut cp_scratch,
                                    &lowered_pred,
                                    &arg_vals,
                                ) && let Some(inst_ret) = self.instantiate_proof_pred(
                                    &exit_env,
                                    &mut cp_scratch,
                                    &ret_pred,
                                    &arg_vals,
                                ) {
                                    cp_scratch.assume(&inst_p);
                                    cp_scratch.entails(&inst_ret)
                                } else {
                                    false
                                }
                            } else {
                                false
                            };
                            if !contrapositive_ok {
                                let mut diag = Diagnostic::error(
                                    Code::E0323,
                                    report_span,
                                    "false return path does not satisfy negated Reflects predicate",
                                );
                                diag =
                                    diag.with_label(guard_span, "required by this Reflects guard");
                                self.diagnostics.push(diag);
                            }
                        }
                    }
                    ProofKind::Plain => {}
                }
                continue;
            }
            let (tf_id, extra, guard_span) = match proof_ref {
                super::check::ReturnProofRef::Expr(guard) => {
                    let Some((tf_id, extra)) =
                        self.extract_static_proof_guard(exit_env.file, guard)
                    else {
                        continue;
                    };
                    (tf_id, extra, self.ast(exit_env.file).expr(guard).span)
                }
                super::check::ReturnProofRef::Type(ty_id) => {
                    let Some((tf_id, angle_args, span)) =
                        self.bare_proof_type_info(exit_env.file, ty_id)
                    else {
                        continue;
                    };
                    let Some(extra) = self.extract_static_proof_angle_args(tf_id, &angle_args)
                    else {
                        continue;
                    };
                    (tf_id, extra, span)
                }
            };
            let Some(ret_expr) = expr else { continue };
            let subject_expr = if is_fallible_return {
                match self.extract_fallible_return_payload(&exit_env, ret_expr) {
                    FalliblePayload::Vacuous => continue, // `None` / `Err(...)` satisfies payload proof vacuously
                    FalliblePayload::Payload(inner) => inner,
                    FalliblePayload::PassThrough(whole) => {
                        // Returning a fallible expression directly (e.g., `return other_fn()`):
                        // check if `whole` already carries the payload proof!
                        if self.fallible_expr_entails_return_proof(
                            &mut exit_env,
                            whole,
                            tf_id,
                            &extra,
                        ) {
                            continue;
                        }
                        whole
                    }
                }
            } else {
                ret_expr
            };
            let mut arg_vals = Vec::with_capacity(1 + extra.len());
            arg_vals.push(ProofArgVal::Expr(subject_expr));
            for opt in extra {
                if let Some(e) = opt {
                    arg_vals.push(ProofArgVal::Expr(e));
                } else {
                    arg_vals.push(ProofArgVal::Const(0));
                }
            }
            self.verify_proof_obligation(
                &mut exit_env,
                tf_id,
                &arg_vals,
                report_span,
                guard_span,
                "return value does not satisfy static proof",
            );
        }
    }

    fn extract_fallible_return_payload(&self, env: &Env, expr: ExprId) -> FalliblePayload {
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Path(path) if path.segments.last().is_some_and(|s| s.name.value == "None") => {
                FalliblePayload::Vacuous
            }
            Expr::Call { callee, args } => {
                if let Expr::Path(path) = &ast.expr(*callee).value
                    && let Some(seg) = path.segments.last()
                {
                    match seg.name.value.as_str() {
                        "Err" => return FalliblePayload::Vacuous,
                        "Some" | "Ok" => {
                            if let [arg] = args.as_slice() {
                                return FalliblePayload::Payload(arg.value);
                            }
                        }
                        _ => {}
                    }
                }
                FalliblePayload::PassThrough(expr)
            }
            _ => FalliblePayload::PassThrough(expr),
        }
    }

    fn fallible_expr_entails_return_proof(
        &mut self,
        env: &mut Env,
        expr: ExprId,
        tf_id: DefinitionId,
        extra: &[Option<ExprId>],
    ) -> bool {
        let Some(call_proofs) = env.refinements.call_proofs.get(&expr).cloned() else {
            return false;
        };
        let Ok(lowered) = self.lower_type_fn(tf_id) else {
            return false;
        };
        let mut scratch = env.refinements.dbm.clone();
        let temp_atom = scratch.fresh_temp();
        for cp in &call_proofs {
            if !cp.is_payload {
                continue;
            }
            if let Some(pred) = cp.pred.map_atoms(&mut |ra| match ra {
                ReturnAtom::SubjectVal(p) if p.is_empty() => Some(temp_atom.clone()),
                ReturnAtom::SubjectLen(p) if p.is_empty() => Some(temp_atom.clone()),
                ReturnAtom::Caller(a) => Some(a.clone()),
                _ => None,
            }) {
                scratch.assume(&pred);
            }
        }
        let mut arg_vals = Vec::with_capacity(1 + extra.len());
        arg_vals.push(ProofArgVal::Atom(temp_atom));
        for opt in extra {
            if let Some(e) = opt {
                arg_vals.push(ProofArgVal::Expr(*e));
            } else {
                arg_vals.push(ProofArgVal::Const(0));
            }
        }
        self.instantiate_proof_pred(env, &mut scratch, &lowered.pred, &arg_vals)
            .is_some_and(|goal| scratch.entails(&goal))
    }

    // -------------------------------------------------------------------------
    // 5. Call-Site Precondition Checking & Postcondition Seeding
    // -------------------------------------------------------------------------

    pub(super) fn check_call_param_proofs(
        &mut self,
        env: &mut Env,
        callee_id: DefinitionId,
        arg_by_formal: &[Option<ExprId>],
        call_span: Span,
    ) {
        if env.shadow {
            return;
        }
        let def = self.hir.definition(callee_id);
        let Some(stmt) = def.stmt else { return };
        let def_file = def.name.span.file;
        let StmtKind::Function(fun) = &self.ast(def_file).stmt(stmt).value.kind else {
            return;
        };
        let params = fun.signature.params.clone();

        // Build formal DefinitionId -> caller ExprId mapping (handles named arg reordering!).
        let mut formal_to_caller: HashMap<DefinitionId, ExprId> = HashMap::new();
        for (idx, param) in params.iter().enumerate() {
            if let Some(name) = &param.name
                && let Some(fid) = self.resolve(name.span)
                && let Some(Some(arg_expr)) = arg_by_formal.get(idx)
            {
                formal_to_caller.insert(fid, *arg_expr);
            }
        }

        let is_bounds_intrinsic = matches!(
            self.hir.intrinsic(callee_id),
            Some(
                Intrinsic::ArrayInsert
                    | Intrinsic::ArraySwap
                    | Intrinsic::ArrayRemove
                    | Intrinsic::StringAt
            )
        );
        let failure_code = if is_bounds_intrinsic {
            Code::E0362
        } else {
            Code::E0323
        };
        let mut all_ok = true;
        let mut had_static_proof = false;
        for (idx, param) in params.iter().enumerate() {
            if param.is_meta {
                continue;
            }
            let Some(Some(subject_expr)) = arg_by_formal.get(idx) else {
                continue;
            };
            for (tf_id, extra, guard_span) in self.param_static_proofs(def_file, param) {
                had_static_proof = true;
                let arg_span = self.ast(env.file).expr(*subject_expr).span;
                let mut arg_vals = Vec::with_capacity(1 + extra.len());
                arg_vals.push(ProofArgVal::Expr(*subject_expr));
                // Lower extra guard expressions in `def_file` context, mapping formal params to caller exprs!
                let mut scratch = env.refinements.dbm.clone();
                let mut extra_ok = true;
                for opt in extra {
                    let Some(guard_arg_expr) = opt else {
                        arg_vals.push(ProofArgVal::Const(0));
                        continue;
                    };
                    match self.eval_callee_guard_arg(
                        env,
                        &mut scratch,
                        def_file,
                        guard_arg_expr,
                        &formal_to_caller,
                    ) {
                        Some(val) => arg_vals.push(val),
                        None => {
                            extra_ok = false;
                            break;
                        }
                    }
                }
                if !extra_ok {
                    all_ok = false;
                    let diag = Diagnostic::error(
                        failure_code,
                        arg_span,
                        format!(
                            "argument does not satisfy static proof '{}'",
                            self.hir.definition(tf_id).name.value
                        ),
                    )
                    .with_label(guard_span, "required by this static proof");
                    self.diagnostics.push(diag);
                    continue;
                }
                let ok = self.verify_proof_obligation_with_scratch_code(
                    env,
                    &mut scratch,
                    tf_id,
                    &arg_vals,
                    arg_span,
                    guard_span,
                    "argument does not satisfy static proof",
                    failure_code,
                );
                if !ok {
                    all_ok = false;
                }
            }
        }
        if had_static_proof && all_ok {
            self.proved_ops.insert(call_span);
        }
    }

    pub(super) fn seed_call_return_proofs(
        &mut self,
        env: &mut Env,
        callee_id: DefinitionId,
        arg_by_formal: &[Option<ExprId>],
        call_expr: ExprId,
    ) {
        if env.shadow {
            return;
        }
        let def = self.hir.definition(callee_id);
        let Some(stmt) = def.stmt else { return };
        let def_file = def.name.span.file;
        let StmtKind::Function(fun) = &self.ast(def_file).stmt(stmt).value.kind else {
            return;
        };
        let ret_proofs = self.return_static_proofs(def_file, &fun.signature);
        let ret_combinators: Vec<(ProofKind, CombinatorArg)> = fun
            .signature
            .guards
            .iter()
            .filter_map(|&g| self.extract_proof_combinator(def_file, g))
            .collect();
        if ret_proofs.is_empty() && ret_combinators.is_empty() {
            return;
        }
        let params = fun.signature.params.clone();

        let is_payload = self
            .callables
            .get(&callee_id)
            .map(|c| self.normalize(&c.result))
            .is_some_and(|r| r.is_option(self.hir) || r.is_result(self.hir));

        let mut formal_to_caller: HashMap<DefinitionId, ExprId> = HashMap::new();
        for (idx, param) in params.iter().enumerate() {
            if let Some(name) = &param.name
                && let Some(fid) = self.resolve(name.span)
                && let Some(Some(arg_expr)) = arg_by_formal.get(idx)
            {
                formal_to_caller.insert(fid, *arg_expr);
            }
        }

        let mut instantiated = Vec::new();
        for (tf_id, extra, _) in ret_proofs {
            let Ok(lowered) = self.lower_type_fn(tf_id) else {
                continue;
            };
            // Resolve each extra arg to a caller-side `ReturnAtom` (Place / Const / Len(Place) / Atom).
            let mut extra_resolved: Vec<Option<CallerArgRef>> = Vec::with_capacity(extra.len());
            for opt in extra {
                extra_resolved.push(opt.and_then(|e| {
                    self.resolve_callee_guard_arg_for_return(env, def_file, e, &formal_to_caller)
                }));
            }
            if let Some(pred) = lowered.pred.map_atoms(&mut |atom| match atom {
                ProofAtom::Val(pp) if pp.param_idx == 0 => {
                    Some(ReturnAtom::SubjectVal(pp.path.clone()))
                }
                ProofAtom::Len(pp) if pp.param_idx == 0 => {
                    Some(ReturnAtom::SubjectLen(pp.path.clone()))
                }
                ProofAtom::Val(pp) => {
                    let arg = extra_resolved.get(pp.param_idx - 1)?.as_ref()?;
                    match arg {
                        CallerArgRef::Place(base) => {
                            let mut p = base.clone();
                            p.path.extend(pp.path.iter().cloned());
                            Some(ReturnAtom::Caller(Atom::Val(p)))
                        }
                        CallerArgRef::LenOf(base) if pp.path.is_empty() => {
                            Some(ReturnAtom::Caller(Atom::Len(base.clone())))
                        }
                        CallerArgRef::Const(c) if pp.path.is_empty() => {
                            let t = env.refinements.dbm.fresh_temp();
                            env.refinements.dbm.add_eq(t.clone(), Atom::Zero, *c);
                            Some(ReturnAtom::Caller(t))
                        }
                        CallerArgRef::KeyConst(kc) if pp.path.is_empty() => {
                            Some(ReturnAtom::Caller(Atom::KeyConst(kc.clone())))
                        }
                        CallerArgRef::Atom(a) if pp.path.is_empty() => {
                            Some(ReturnAtom::Caller(a.clone()))
                        }
                        _ => None,
                    }
                }
                ProofAtom::Len(pp) => {
                    let arg = extra_resolved.get(pp.param_idx - 1)?.as_ref()?;
                    match arg {
                        CallerArgRef::Place(base) => {
                            let mut p = base.clone();
                            p.path.extend(pp.path.iter().cloned());
                            Some(ReturnAtom::Caller(Atom::Len(p)))
                        }
                        _ => None,
                    }
                }
                ProofAtom::Const(kc) => Some(ReturnAtom::Caller(Atom::KeyConst(kc.clone()))),
            }) {
                instantiated.push(CallReturnProof {
                    pred,
                    is_payload,
                    kind: ProofKind::Plain,
                });
            }
        }
        if !ret_combinators.is_empty() {
            let mut formal_locals: HashMap<DefinitionId, TfLocal> = HashMap::new();
            let mut caller_resolved: Vec<Option<CallerArgRef>> =
                (0..params.len()).map(|_| None).collect();
            for (idx, param) in params.iter().enumerate() {
                if let Some(name) = &param.name
                    && let Some(fid) = self.resolve(name.span)
                {
                    formal_locals.insert(
                        fid,
                        TfLocal::Place(ProofPlace {
                            param_idx: idx,
                            path: Vec::new(),
                        }),
                    );
                    if let Some(Some(arg_expr)) = arg_by_formal.get(idx)
                        && let Some(slot) = caller_resolved.get_mut(idx)
                    {
                        *slot = if let Some(p) = self.resolve_place(env, *arg_expr) {
                            Some(CallerArgRef::Place(p))
                        } else if let Some(c) =
                            self.const_int_in_dbm(env, &env.refinements.dbm, *arg_expr)
                        {
                            Some(CallerArgRef::Const(c))
                        } else {
                            let mut dbm = std::mem::take(&mut env.refinements.dbm);
                            let a = self
                                .key_expr_to_atom(env, &mut dbm, *arg_expr)
                                .unwrap_or_else(|| self.expr_to_atom(env, &mut dbm, *arg_expr));
                            env.refinements.dbm = dbm;
                            Some(CallerArgRef::Atom(a))
                        };
                    }
                }
            }
            for (kind, pred_arg) in ret_combinators {
                let Ok(lowered) = self.lower_combinator_arg(def_file, &pred_arg, &formal_locals)
                else {
                    continue;
                };
                if let Some(pred) = lowered.map_atoms(&mut |atom| match atom {
                    ProofAtom::Val(pp) => {
                        let arg = caller_resolved.get(pp.param_idx)?.as_ref()?;
                        match arg {
                            CallerArgRef::Place(base) => {
                                let mut p = base.clone();
                                p.path.extend(pp.path.iter().cloned());
                                Some(ReturnAtom::Caller(Atom::Val(p)))
                            }
                            CallerArgRef::LenOf(base) if pp.path.is_empty() => {
                                Some(ReturnAtom::Caller(Atom::Len(base.clone())))
                            }
                            CallerArgRef::Const(c) if pp.path.is_empty() => {
                                let t = env.refinements.dbm.fresh_temp();
                                env.refinements.dbm.add_eq(t.clone(), Atom::Zero, *c);
                                Some(ReturnAtom::Caller(t))
                            }
                            CallerArgRef::KeyConst(kc) if pp.path.is_empty() => {
                                Some(ReturnAtom::Caller(Atom::KeyConst(kc.clone())))
                            }
                            CallerArgRef::Atom(a) if pp.path.is_empty() => {
                                Some(ReturnAtom::Caller(a.clone()))
                            }
                            _ => None,
                        }
                    }
                    ProofAtom::Len(pp) => {
                        let arg = caller_resolved.get(pp.param_idx)?.as_ref()?;
                        match arg {
                            CallerArgRef::Place(base) => {
                                let mut p = base.clone();
                                p.path.extend(pp.path.iter().cloned());
                                Some(ReturnAtom::Caller(Atom::Len(p)))
                            }
                            _ => None,
                        }
                    }
                    ProofAtom::Const(kc) => Some(ReturnAtom::Caller(Atom::KeyConst(kc.clone()))),
                }) {
                    if kind == ProofKind::Ensures {
                        if let Some(caller_pred) = pred.map_atoms(&mut |ra| match ra {
                            ReturnAtom::Caller(a) => Some(a.clone()),
                            _ => None,
                        }) {
                            env.refinements.dbm.assume(&caller_pred);
                            env.refinements.dbm.forget_temps();
                        }
                    } else {
                        instantiated.push(CallReturnProof {
                            pred,
                            is_payload,
                            kind,
                        });
                    }
                }
            }
        }
        if !instantiated.is_empty() {
            env.refinements.call_proofs.insert(call_expr, instantiated);
        }
    }

    pub(super) fn apply_call_proof_to_place(
        &self,
        env: &mut Env,
        target: &Place,
        expr: ExprId,
        unwrapped_payload: bool,
    ) {
        let Some(proofs) = env.refinements.call_proofs.get(&expr).cloned() else {
            return;
        };
        for cp in proofs {
            if cp.kind != ProofKind::Plain || cp.is_payload != unwrapped_payload {
                continue;
            }
            if let Some(pred) = instantiate_call_return_pred(&cp.pred, target) {
                env.refinements.dbm.assume(&pred);
            }
        }
    }

    // -------------------------------------------------------------------------
    // 6. Dual-Mode Verification Core
    // -------------------------------------------------------------------------

    fn verify_proof_obligation(
        &mut self,
        env: &mut Env,
        tf_id: DefinitionId,
        arg_vals: &[ProofArgVal],
        report_span: Span,
        guard_span: Span,
        msg_prefix: &str,
    ) -> bool {
        let mut scratch = env.refinements.dbm.clone();
        self.verify_proof_obligation_with_scratch(
            env,
            &mut scratch,
            tf_id,
            arg_vals,
            report_span,
            guard_span,
            msg_prefix,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_proof_obligation_with_scratch(
        &mut self,
        env: &mut Env,
        scratch: &mut Dbm,
        tf_id: DefinitionId,
        arg_vals: &[ProofArgVal],
        report_span: Span,
        guard_span: Span,
        msg_prefix: &str,
    ) -> bool {
        self.verify_proof_obligation_with_scratch_code(
            env,
            scratch,
            tf_id,
            arg_vals,
            report_span,
            guard_span,
            msg_prefix,
            Code::E0323,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn verify_proof_obligation_with_scratch_code(
        &mut self,
        env: &mut Env,
        scratch: &mut Dbm,
        tf_id: DefinitionId,
        arg_vals: &[ProofArgVal],
        report_span: Span,
        guard_span: Span,
        msg_prefix: &str,
        failure_code: Code,
    ) -> bool {
        // Mode A: If all arguments resolve to compile-time constants, evaluate via static evaluator!
        if let Some(const_values) = self.try_const_proof_args(env, scratch, arg_vals) {
            return self.eval_type_fn_const(
                env,
                tf_id,
                const_values,
                report_span,
                guard_span,
                msg_prefix,
                failure_code,
            );
        }
        // Mode B: Symbolic DBM verification.
        let lowered = match self.lower_type_fn(tf_id) {
            Ok(l) => l,
            Err(err) => {
                let diag = Diagnostic::error(
                    Code::E0306,
                    report_span,
                    format!(
                        "static proof '{}' cannot be checked on a runtime value: {}",
                        self.hir.definition(tf_id).name.value,
                        err.reason
                    ),
                )
                .with_label(err.span, "non-decidable construct here");
                self.diagnostics.push(diag);
                return false;
            }
        };
        let satisfied = self
            .instantiate_proof_pred(env, scratch, &lowered.pred, arg_vals)
            .is_some_and(|goal| scratch.entails(&goal));
        if !satisfied {
            let tf_name = self.hir.definition(tf_id).name.value.clone();
            let mut diag = Diagnostic::error(
                failure_code,
                report_span,
                format!("{msg_prefix} '{tf_name}'"),
            );
            if !self.hir.is_stdlib_file(guard_span.file) {
                diag = diag.with_label(guard_span, "required by this static proof");
            }
            self.diagnostics.push(diag);
        }
        satisfied
    }

    fn try_const_proof_args(
        &self,
        env: &Env,
        dbm: &Dbm,
        arg_vals: &[ProofArgVal],
    ) -> Option<Vec<Value>> {
        let mut out = Vec::with_capacity(arg_vals.len());
        for arg in arg_vals {
            match arg {
                ProofArgVal::Const(c) => out.push(Value::Int((*c).into())),
                ProofArgVal::KeyConst(kc) => out.push(match kc {
                    KeyConst::Int(c) => Value::Int((*c).into()),
                    KeyConst::Str(s) => Value::Str(s.clone()),
                    KeyConst::Bool(b) => Value::Bool(*b),
                    KeyConst::Bytes(b) => Value::Bytes(b.clone()),
                    KeyConst::Unit => Value::Unit,
                }),
                ProofArgVal::Atom(a) => {
                    let c = dbm.exact(a)?;
                    out.push(Value::Int(c.into()));
                }
                ProofArgVal::Place(p) => {
                    let c = dbm.exact(&Atom::Val(p.clone()))?;
                    out.push(Value::Int(c.into()));
                }
                ProofArgVal::Expr(e) => {
                    if let Some(c) = self.const_int_in_dbm(env, dbm, *e) {
                        out.push(Value::Int(c.into()));
                    } else if let Some(val) =
                        self.static_values.get(&self.ast(env.file).expr(*e).span)
                    {
                        out.push(val.clone());
                    } else if let Expr::Literal(lit) = &self.ast(env.file).expr(*e).value
                        && let Ok(val) = super::literal(lit)
                    {
                        out.push(val);
                    } else {
                        return None;
                    }
                }
                ProofArgVal::TupleExprs(exprs) => {
                    let mut elems = Vec::with_capacity(exprs.len());
                    for &e in exprs {
                        if let Some(c) = self.const_int_in_dbm(env, dbm, e) {
                            elems.push(Value::Int(c.into()));
                        } else if let Some(val) =
                            self.static_values.get(&self.ast(env.file).expr(e).span)
                        {
                            elems.push(val.clone());
                        } else if let Expr::Literal(lit) = &self.ast(env.file).expr(e).value
                            && let Ok(val) = super::literal(lit)
                        {
                            elems.push(val);
                        } else {
                            return None;
                        }
                    }
                    out.push(Value::Tuple(elems));
                }
            }
        }
        Some(out)
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_type_fn_const(
        &mut self,
        env: &Env,
        tf_id: DefinitionId,
        const_values: Vec<Value>,
        report_span: Span,
        guard_span: Span,
        msg_prefix: &str,
        failure_code: Code,
    ) -> bool {
        let def = self.hir.definition(tf_id);
        let Some(stmt) = def.stmt else { return true };
        let def_file = def.name.span.file;
        let StmtKind::Type(decl) = &self.ast(def_file).stmt(stmt).value.kind else {
            return true;
        };
        let TypeDefinition::Function(params, body) = &decl.definition else {
            return true;
        };
        let params = params.clone();
        let body = *body;
        let (type_params, Some(subject), trailing) = partition_type_fn_params(&params) else {
            return true;
        };
        let mut local = Env::new(def_file, def.scope);
        local.phase = Phase::TypeEval;
        local.caller_scope = Some(env.effective_scope());
        local.error_span = Some(report_span);
        for tp in type_params {
            if let Some(pid) = self.resolve(tp.name.span) {
                local.generics.insert(pid, GenericValue::Type(self.fresh()));
            }
        }
        if let Some(id) = self.resolve(subject.name.span)
            && let Some(val) = const_values.first()
        {
            local.generics.insert(id, GenericValue::Data(val.clone()));
        }
        for (idx, param) in trailing.iter().enumerate() {
            if let Some(id) = self.resolve(param.name.span)
                && let Some(val) = const_values.get(idx + 1)
            {
                local.generics.insert(id, GenericValue::Data(val.clone()));
            }
        }
        self.stack.push(tf_id);
        let result = self.evaluate_static(&local, body);
        self.stack.pop();
        match result {
            Ok(Value::Type(ref ty)) | Err(super::eval::Signal::Return(Value::Type(ref ty)))
                if **ty == Ty::Unit =>
            {
                true
            }
            Ok(Value::Type(ref ty)) | Err(super::eval::Signal::Return(Value::Type(ref ty)))
                if **ty == Ty::Never =>
            {
                let tf_name = self.hir.definition(tf_id).name.value.clone();
                let mut diag = Diagnostic::error(
                    failure_code,
                    report_span,
                    format!("{msg_prefix} '{tf_name}'"),
                );
                if !self.hir.is_stdlib_file(guard_span.file) {
                    diag = diag.with_label(guard_span, "required by this static proof");
                }
                self.diagnostics.push(diag);
                false
            }
            _ => {
                // Fall back to Mode B if static eval hit a dependent type parameter.
                let Ok(lowered) = self.lower_type_fn(tf_id) else {
                    return true;
                };
                let mut scratch = env.refinements.dbm.clone();
                let arg_vals: Vec<ProofArgVal> = const_values
                    .iter()
                    .filter_map(|v| match v {
                        Value::Int(n) => n.to_i128().map(ProofArgVal::Const),
                        _ => None,
                    })
                    .collect();
                if arg_vals.len() != const_values.len() {
                    return true;
                }
                self.instantiate_proof_pred(env, &mut scratch, &lowered.pred, &arg_vals)
                    .is_some_and(|g| scratch.entails(&g))
            }
        }
    }

    pub(super) fn instantiate_proof_pred(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        pred: &ProofPred<ProofAtom>,
        arg_vals: &[ProofArgVal],
    ) -> Option<ProofPred<Atom>> {
        let mut cache: HashMap<ProofAtom, Atom> = HashMap::new();
        self.instantiate_proof_pred_rec(env, dbm, pred, arg_vals, &mut cache)
    }

    fn instantiate_proof_pred_rec(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        pred: &ProofPred<ProofAtom>,
        arg_vals: &[ProofArgVal],
        cache: &mut HashMap<ProofAtom, Atom>,
    ) -> Option<ProofPred<Atom>> {
        Some(match pred {
            ProofPred::True => ProofPred::True,
            ProofPred::False => ProofPred::False,
            ProofPred::DiffLe { lhs, rhs, bound } => ProofPred::diff_le(
                match lhs {
                    Some(a) => Some(self.resolve_cached_proof_atom(env, dbm, a, arg_vals, cache)?),
                    None => None,
                },
                match rhs {
                    Some(b) => Some(self.resolve_cached_proof_atom(env, dbm, b, arg_vals, cache)?),
                    None => None,
                },
                *bound,
            ),
            ProofPred::DiffNe { lhs, rhs, offset } => ProofPred::diff_ne(
                match lhs {
                    Some(a) => Some(self.resolve_cached_proof_atom(env, dbm, a, arg_vals, cache)?),
                    None => None,
                },
                match rhs {
                    Some(b) => Some(self.resolve_cached_proof_atom(env, dbm, b, arg_vals, cache)?),
                    None => None,
                },
                *offset,
            ),
            ProofPred::Contains {
                container,
                key,
                negated,
            } => ProofPred::Contains {
                container: self.resolve_proof_membership_atom(env, dbm, container, arg_vals)?,
                key: self.resolve_proof_membership_atom(env, dbm, key, arg_vals)?,
                negated: *negated,
            },
            ProofPred::And(ps) => {
                let mut out = Vec::with_capacity(ps.len());
                for p in ps {
                    out.push(self.instantiate_proof_pred_rec(env, dbm, p, arg_vals, cache)?);
                }
                ProofPred::and(out)
            }
            ProofPred::Or(ps) => {
                let mut out = Vec::with_capacity(ps.len());
                for p in ps {
                    out.push(self.instantiate_proof_pred_rec(env, dbm, p, arg_vals, cache)?);
                }
                ProofPred::or(out)
            }
        })
    }

    fn resolve_cached_proof_atom(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        pa: &ProofAtom,
        arg_vals: &[ProofArgVal],
        cache: &mut HashMap<ProofAtom, Atom>,
    ) -> Option<Atom> {
        if let Some(a) = cache.get(pa) {
            return Some(a.clone());
        }
        let atom = match pa {
            ProofAtom::Val(pp) => self.resolve_proof_val_atom(env, dbm, pp, arg_vals)?,
            ProofAtom::Len(pp) => self.resolve_proof_len_atom(env, dbm, pp, arg_vals)?,
            ProofAtom::Const(KeyConst::Int(c)) => {
                let t = dbm.fresh_temp();
                dbm.add_eq(t.clone(), Atom::Zero, *c);
                t
            }
            ProofAtom::Const(kc) => Atom::KeyConst(kc.clone()),
        };
        cache.insert(pa.clone(), atom.clone());
        Some(atom)
    }

    /// Resolves container/key atoms for `ProofPred::Contains` without registering non-integer places in the DBM matrix.
    fn resolve_proof_membership_atom(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        pa: &ProofAtom,
        arg_vals: &[ProofArgVal],
    ) -> Option<Atom> {
        match pa {
            ProofAtom::Const(kc) => Some(Atom::KeyConst(kc.clone())),
            ProofAtom::Len(pp) => self.resolve_proof_len_atom(env, dbm, pp, arg_vals),
            ProofAtom::Val(pp) => {
                let arg = arg_vals.get(pp.param_idx)?;
                match arg {
                    ProofArgVal::Const(c) if pp.path.is_empty() => {
                        Some(Atom::KeyConst(KeyConst::Int(*c)))
                    }
                    ProofArgVal::KeyConst(kc) if pp.path.is_empty() => {
                        Some(Atom::KeyConst(kc.clone()))
                    }
                    ProofArgVal::Atom(a) if pp.path.is_empty() => Some(a.clone()),
                    ProofArgVal::Place(base) => {
                        let mut p = base.clone();
                        p.path.extend(pp.path.iter().cloned());
                        Some(Atom::Val(p))
                    }
                    ProofArgVal::Expr(e) => {
                        if pp.path.is_empty()
                            && let Expr::Call { callee, args } = &self.ast(env.file).expr(*e).value
                            && let Expr::Path(path) = &self.ast(env.file).expr(*callee).value
                            && let Some(id) = self.resolve(path.span)
                            && matches!(
                                self.hir.intrinsic(id),
                                Some(Intrinsic::Inner | Intrinsic::Clone)
                            )
                            && let [arg] = args.as_slice()
                            && let Some(p) = self.resolve_place(env, arg.value)
                        {
                            return Some(Atom::Val(p));
                        }
                        if let Some(p) = self.project_expr_to_place(env, *e, &pp.path) {
                            return Some(Atom::Val(p));
                        }
                        let projected = self.project_expr_path(env, *e, &pp.path)?;
                        self.key_expr_to_atom(env, dbm, projected)
                    }
                    ProofArgVal::TupleExprs(items) => {
                        let (first_seg, rest) = pp.path.split_first()?;
                        let idx: usize = first_seg.parse().ok()?;
                        let item = *items.get(idx)?;
                        if let Some(p) = self.project_expr_to_place(env, item, rest) {
                            return Some(Atom::Val(p));
                        }
                        let projected = self.project_expr_path(env, item, rest)?;
                        self.key_expr_to_atom(env, dbm, projected)
                    }
                    _ => None,
                }
            }
        }
    }

    fn resolve_proof_val_atom(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        pp: &ProofPlace,
        arg_vals: &[ProofArgVal],
    ) -> Option<Atom> {
        let arg = arg_vals.get(pp.param_idx)?;
        match arg {
            ProofArgVal::Const(c) if pp.path.is_empty() => {
                let t = dbm.fresh_temp();
                dbm.add_eq(t.clone(), Atom::Zero, *c);
                Some(t)
            }
            ProofArgVal::Atom(a) if pp.path.is_empty() => {
                dbm.ensure_atom(a.clone());
                Some(a.clone())
            }
            ProofArgVal::Place(base) => {
                let mut p = base.clone();
                p.path.extend(pp.path.iter().cloned());
                dbm.ensure_atom(Atom::Val(p.clone()));
                Some(Atom::Val(p))
            }
            ProofArgVal::Expr(e) => {
                if let Some(p) = self.project_expr_to_place(env, *e, &pp.path) {
                    dbm.ensure_atom(Atom::Val(p.clone()));
                    return Some(Atom::Val(p));
                }
                let projected = self.project_expr_path(env, *e, &pp.path)?;
                if let Some(p) = self.resolve_place(env, projected) {
                    dbm.ensure_atom(Atom::Val(p.clone()));
                    return Some(Atom::Val(p));
                }
                let t = dbm.fresh_temp();
                self.constrain_expr(env, dbm, &t, projected);
                Some(t)
            }
            ProofArgVal::TupleExprs(items) => {
                let (first_seg, rest) = pp.path.split_first()?;
                let idx: usize = first_seg.parse().ok()?;
                let item = *items.get(idx)?;
                if let Some(p) = self.project_expr_to_place(env, item, rest) {
                    dbm.ensure_atom(Atom::Val(p.clone()));
                    return Some(Atom::Val(p));
                }
                let projected = self.project_expr_path(env, item, rest)?;
                if let Some(p) = self.resolve_place(env, projected) {
                    dbm.ensure_atom(Atom::Val(p.clone()));
                    return Some(Atom::Val(p));
                }
                let t = dbm.fresh_temp();
                self.constrain_expr(env, dbm, &t, projected);
                Some(t)
            }
            _ => None,
        }
    }

    fn resolve_proof_len_atom(
        &self,
        env: &Env,
        dbm: &mut Dbm,
        pp: &ProofPlace,
        arg_vals: &[ProofArgVal],
    ) -> Option<Atom> {
        let arg = arg_vals.get(pp.param_idx)?;
        match arg {
            ProofArgVal::Atom(a) if pp.path.is_empty() => {
                dbm.ensure_atom(a.clone());
                Some(a.clone())
            }
            ProofArgVal::Place(base) => {
                let mut p = base.clone();
                p.path.extend(pp.path.iter().cloned());
                dbm.ensure_atom(Atom::Len(p.clone()));
                Some(Atom::Len(p))
            }
            ProofArgVal::Expr(e) => {
                if pp.path.is_empty()
                    && let Expr::Call { callee, args } = &self.ast(env.file).expr(*e).value
                    && let Expr::Path(path) = &self.ast(env.file).expr(*callee).value
                    && let Some(id) = self.resolve(path.span)
                    && matches!(
                        self.hir.intrinsic(id),
                        Some(Intrinsic::Inner | Intrinsic::Clone)
                    )
                    && let [arg] = args.as_slice()
                    && let Some(p) = self.resolve_place(env, arg.value)
                {
                    dbm.ensure_atom(Atom::Len(p.clone()));
                    return Some(Atom::Len(p));
                }
                if let Some(p) = self.project_expr_to_place(env, *e, &pp.path) {
                    dbm.ensure_atom(Atom::Len(p.clone()));
                    return Some(Atom::Len(p));
                }
                let projected = self.project_expr_path(env, *e, &pp.path)?;
                if let Some(p) = self.resolve_place(env, projected) {
                    dbm.ensure_atom(Atom::Len(p.clone()));
                    return Some(Atom::Len(p));
                }
                let t = dbm.fresh_temp();
                self.constrain_len_expr(env, dbm, &t, projected);
                Some(t)
            }
            ProofArgVal::TupleExprs(items) => {
                let (first_seg, rest) = pp.path.split_first()?;
                let idx: usize = first_seg.parse().ok()?;
                let item = *items.get(idx)?;
                if let Some(p) = self.project_expr_to_place(env, item, rest) {
                    dbm.ensure_atom(Atom::Len(p.clone()));
                    return Some(Atom::Len(p));
                }
                let projected = self.project_expr_path(env, item, rest)?;
                if let Some(p) = self.resolve_place(env, projected) {
                    dbm.ensure_atom(Atom::Len(p.clone()));
                    return Some(Atom::Len(p));
                }
                let t = dbm.fresh_temp();
                self.constrain_len_expr(env, dbm, &t, projected);
                Some(t)
            }
            _ => None,
        }
    }

    /// Resolves `expr` + `path` to a `Place` when `expr` is itself a `Place` (e.g. `s` + `["rows"]` -> `s.rows`)
    /// or a record constructor with shorthand field `{ rows }`!
    fn project_expr_to_place(&self, env: &Env, expr: ExprId, path: &[String]) -> Option<Place> {
        if let Some(mut base) = self.resolve_place(env, expr) {
            base.path.extend(path.iter().cloned());
            return Some(base);
        }
        let (first_seg, rest_path) = path.split_first()?;
        let ast = self.ast(env.file);
        match &ast.expr(expr).value {
            Expr::Record { fields, .. } => {
                let field = fields.iter().find(|f| f.name.value == *first_seg)?;
                if let Some(val) = field.value {
                    self.project_expr_to_place(env, val, rest_path)
                } else {
                    let id = self.resolve(field.name.span)?;
                    let mut p = Place::local(id);
                    p.path.extend(rest_path.iter().cloned());
                    Some(p)
                }
            }
            Expr::Wrap { args, .. } => {
                let [only] = args.as_slice() else {
                    return None;
                };
                let rest = if first_seg == "#inner" {
                    rest_path
                } else {
                    path
                };
                self.project_expr_to_place(env, only.value, rest)
            }
            Expr::Tuple(items) => {
                let idx: usize = first_seg.parse().ok()?;
                self.project_expr_to_place(env, *items.get(idx)?, rest_path)
            }
            Expr::Block { statements, .. } => {
                if let Some(&last) = statements.last()
                    && let StmtKind::Expr(tail) = ast.stmt(last).value.kind
                {
                    self.project_expr_to_place(env, tail, path)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Structural projection through `Record`, `Tuple`, `Wrap::(...)`, `Block` tail, and shorthand fields!
    /// Enables `Shelf.{ rows: [r] }` or `let mut rows = []; Array::push(mut rows, r); Shelf.{ rows }`
    /// to directly satisfy `type HasRows = \s: Shelf -> if len(s.rows) > 0 { <()> } else { <never> }`.
    fn project_expr_path(&self, env: &Env, mut expr: ExprId, path: &[String]) -> Option<ExprId> {
        let ast = self.ast(env.file);
        for seg in path {
            loop {
                match &ast.expr(expr).value {
                    Expr::Unary { op, value } if matches!(op.value.as_str(), "ref" | "^mut") => {
                        expr = *value;
                    }
                    Expr::Block { statements, .. } => {
                        if let Some(&last) = statements.last()
                            && let StmtKind::Expr(tail) = ast.stmt(last).value.kind
                        {
                            expr = tail;
                        } else {
                            return None;
                        }
                    }
                    _ => break,
                }
            }
            if seg == "#inner" {
                match &ast.expr(expr).value {
                    Expr::Wrap { args, .. } => {
                        let [only] = args.as_slice() else {
                            return None;
                        };
                        expr = only.value;
                        continue;
                    }
                    _ => return None,
                }
            }
            match &ast.expr(expr).value {
                Expr::Wrap { args, .. } => {
                    let [only] = args.as_slice() else {
                        return None;
                    };
                    // Transparently step inside single-arg nominal wrap for field projection.
                    if let Some(inner) =
                        self.project_expr_path(env, only.value, std::slice::from_ref(seg))
                    {
                        expr = inner;
                        continue;
                    }
                    return None;
                }
                Expr::Record { fields, .. } => {
                    let field = fields.iter().find(|f| f.name.value == *seg)?;
                    expr = field.value?;
                }
                Expr::Tuple(items) => {
                    let idx: usize = seg.parse().ok()?;
                    expr = *items.get(idx)?;
                }
                _ => return None,
            }
        }
        Some(expr)
    }

    /// Evaluate a callee's `GuardArg` expression (in `def_file`, referencing formal parameters)
    /// into a caller-side `ProofArgVal` (supporting `xs`, `s.rows`, `len(xs)`, `0`, `a ± b`).
    pub(super) fn eval_callee_guard_arg(
        &self,
        env: &Env,
        scratch: &mut Dbm,
        def_file: FileId,
        guard_arg: ExprId,
        formal_to_caller: &HashMap<DefinitionId, ExprId>,
    ) -> Option<ProofArgVal> {
        let ast = self.ast(def_file);
        match &ast.expr(guard_arg).value {
            Expr::Unary { op, value } if matches!(op.value.as_str(), "ref" | "^mut") => {
                self.eval_callee_guard_arg(env, scratch, def_file, *value, formal_to_caller)
            }
            Expr::Literal(lit) => match super::literal(lit).ok()? {
                Value::Int(n) => Some(ProofArgVal::Const(n.to_i128()?)),
                Value::Str(s) => Some(ProofArgVal::KeyConst(KeyConst::Str(s))),
                Value::Bool(b) => Some(ProofArgVal::KeyConst(KeyConst::Bool(b))),
                Value::Bytes(b) => Some(ProofArgVal::KeyConst(KeyConst::Bytes(b))),
                _ => None,
            },
            Expr::Unit => Some(ProofArgVal::KeyConst(KeyConst::Unit)),
            Expr::Path(path) => {
                let id = self.resolve(path.span)?;
                if let Some(&caller_expr) = formal_to_caller.get(&id) {
                    return Some(ProofArgVal::Expr(caller_expr));
                }
                if let Some(Value::Int(n)) = self.static_constant_value(id) {
                    return Some(ProofArgVal::Const(n.to_i128()?));
                }
                None
            }
            Expr::Member {
                base,
                member,
                safe: false,
            } => {
                let base_val =
                    self.eval_callee_guard_arg(env, scratch, def_file, *base, formal_to_caller)?;
                let seg = match member {
                    Member::Name(n) | Member::Index(n) => n.value.clone(),
                    Member::Computed(_) => return None,
                };
                match base_val {
                    ProofArgVal::Place(mut p) => {
                        p.path.push(seg);
                        Some(ProofArgVal::Place(p))
                    }
                    ProofArgVal::Expr(e) => {
                        if let Some(mut p) = self.resolve_place(env, e) {
                            p.path.push(seg);
                            Some(ProofArgVal::Place(p))
                        } else {
                            self.project_expr_path(env, e, &[seg])
                                .map(ProofArgVal::Expr)
                        }
                    }
                    ProofArgVal::Const(_)
                    | ProofArgVal::KeyConst(_)
                    | ProofArgVal::Atom(_)
                    | ProofArgVal::TupleExprs(_) => None,
                }
            }
            Expr::Call { callee, args } => {
                let Expr::Path(path) = &ast.expr(*callee).value else {
                    return None;
                };
                let id = self.resolve(path.span)?;
                if self.hir.intrinsic(id) == Some(Intrinsic::Len)
                    && let [arg] = args.as_slice()
                {
                    let inner = self.eval_callee_guard_arg(
                        env,
                        scratch,
                        def_file,
                        arg.value,
                        formal_to_caller,
                    )?;
                    let len_atom = match inner {
                        ProofArgVal::Atom(_) => return None,
                        ProofArgVal::Place(p) => {
                            scratch.ensure_atom(Atom::Len(p.clone()));
                            Atom::Len(p)
                        }
                        ProofArgVal::Expr(e) => {
                            if let Some(p) = self.resolve_place(env, e) {
                                scratch.ensure_atom(Atom::Len(p.clone()));
                                Atom::Len(p)
                            } else {
                                let t = scratch.fresh_temp();
                                self.constrain_len_expr(env, scratch, &t, e);
                                t
                            }
                        }
                        ProofArgVal::Const(_)
                        | ProofArgVal::KeyConst(_)
                        | ProofArgVal::TupleExprs(_) => return None,
                    };
                    if let Some(c) = scratch.exact(&len_atom) {
                        return Some(ProofArgVal::Const(c));
                    }
                    return Some(ProofArgVal::Atom(len_atom));
                }
                None
            }
            Expr::Unary { op, value } if op.value == "-" => {
                let inner =
                    self.eval_callee_guard_arg(env, scratch, def_file, *value, formal_to_caller)?;
                match inner {
                    ProofArgVal::Const(c) => Some(ProofArgVal::Const(c.checked_neg()?)),
                    _ => None,
                }
            }
            Expr::Binary { op, left, right } if matches!(op.value.as_str(), "+" | "-") => {
                let l =
                    self.eval_callee_guard_arg(env, scratch, def_file, *left, formal_to_caller)?;
                let r =
                    self.eval_callee_guard_arg(env, scratch, def_file, *right, formal_to_caller)?;
                match (l, r) {
                    (ProofArgVal::Const(a), ProofArgVal::Const(b)) => {
                        let v = if op.value == "+" {
                            a.checked_add(b)?
                        } else {
                            a.checked_sub(b)?
                        };
                        Some(ProofArgVal::Const(v))
                    }
                    (lhs, ProofArgVal::Const(c)) => {
                        let offset = if op.value == "+" { c } else { c.checked_neg()? };
                        let base_atom = match lhs {
                            ProofArgVal::Atom(a) => a,
                            ProofArgVal::Place(p) => Atom::Val(p),
                            ProofArgVal::Expr(e) => {
                                if let Some(p) = self.resolve_place(env, e) {
                                    Atom::Val(p)
                                } else {
                                    let t = scratch.fresh_temp();
                                    self.constrain_expr(env, scratch, &t, e);
                                    t
                                }
                            }
                            ProofArgVal::Const(_)
                            | ProofArgVal::KeyConst(_)
                            | ProofArgVal::TupleExprs(_) => return None,
                        };
                        let t = scratch.fresh_temp();
                        scratch.add_eq(t.clone(), base_atom, offset);
                        Some(ProofArgVal::Atom(t))
                    }
                    (lhs, rhs) if op.value == "-" => {
                        let to_atom = |v: ProofArgVal, dbm: &mut Dbm| -> Option<Atom> {
                            match v {
                                ProofArgVal::Atom(a) => Some(a),
                                ProofArgVal::Place(p) => Some(Atom::Val(p)),
                                ProofArgVal::Expr(e) => {
                                    if let Some(p) = self.resolve_place(env, e) {
                                        Some(Atom::Val(p))
                                    } else {
                                        let t = dbm.fresh_temp();
                                        self.constrain_expr(env, dbm, &t, e);
                                        Some(t)
                                    }
                                }
                                ProofArgVal::Const(c) => {
                                    let t = dbm.fresh_temp();
                                    dbm.add_eq(t.clone(), Atom::Zero, c);
                                    Some(t)
                                }
                                ProofArgVal::KeyConst(_) | ProofArgVal::TupleExprs(_) => None,
                            }
                        };
                        let la = to_atom(lhs, scratch)?;
                        let ra = to_atom(rhs, scratch)?;
                        let t = scratch.fresh_temp();
                        scratch.add_diff_eq(t.clone(), la, ra, 0);
                        Some(ProofArgVal::Atom(t))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn resolve_callee_guard_arg_for_return(
        &self,
        env: &mut Env,
        def_file: FileId,
        guard_arg: ExprId,
        formal_to_caller: &HashMap<DefinitionId, ExprId>,
    ) -> Option<CallerArgRef> {
        let ast = self.ast(def_file);
        match &ast.expr(guard_arg).value {
            Expr::Unary { op, value } if matches!(op.value.as_str(), "ref" | "^mut") => {
                self.resolve_callee_guard_arg_for_return(env, def_file, *value, formal_to_caller)
            }
            Expr::Literal(lit) => match super::literal(lit).ok()? {
                Value::Int(n) => Some(CallerArgRef::Const(n.to_i128()?)),
                Value::Str(s) => Some(CallerArgRef::KeyConst(KeyConst::Str(s))),
                Value::Bool(b) => Some(CallerArgRef::KeyConst(KeyConst::Bool(b))),
                Value::Bytes(b) => Some(CallerArgRef::KeyConst(KeyConst::Bytes(b))),
                _ => None,
            },
            Expr::Unit => Some(CallerArgRef::KeyConst(KeyConst::Unit)),
            Expr::Path(path) => {
                let id = self.resolve(path.span)?;
                if let Some(&caller_expr) = formal_to_caller.get(&id) {
                    if let Some(p) = self.resolve_place(env, caller_expr) {
                        return Some(CallerArgRef::Place(p));
                    }
                    if let Expr::Call { callee, args } = &self.ast(env.file).expr(caller_expr).value
                        && let Expr::Path(cpath) = &self.ast(env.file).expr(*callee).value
                        && let Some(cid) = self.resolve(cpath.span)
                        && matches!(
                            self.hir.intrinsic(cid),
                            Some(Intrinsic::Inner | Intrinsic::Clone)
                        )
                        && let [carg] = args.as_slice()
                        && let Some(p) = self.resolve_place(env, carg.value)
                    {
                        return Some(CallerArgRef::Place(p));
                    }
                    if let Some(c) = self.const_int(env, caller_expr) {
                        return Some(CallerArgRef::Const(c));
                    }
                    if self.is_int_expr(env, caller_expr) {
                        let t = env.refinements.dbm.fresh_temp();
                        let mut dbm = std::mem::take(&mut env.refinements.dbm);
                        self.constrain_expr(env, &mut dbm, &t, caller_expr);
                        env.refinements.dbm = dbm;
                        return Some(CallerArgRef::Atom(t));
                    }
                } else if let Some(Value::Int(n)) = self.static_constant_value(id) {
                    return Some(CallerArgRef::Const(n.to_i128()?));
                }
                None
            }
            Expr::Call { callee, args } => {
                let Expr::Path(path) = &ast.expr(*callee).value else {
                    return None;
                };
                let id = self.resolve(path.span)?;
                if self.hir.intrinsic(id) == Some(Intrinsic::Len)
                    && let [arg] = args.as_slice()
                {
                    let inner = self.resolve_callee_guard_arg_for_return(
                        env,
                        def_file,
                        arg.value,
                        formal_to_caller,
                    )?;
                    if let CallerArgRef::Place(p) = inner {
                        return Some(CallerArgRef::LenOf(p));
                    }
                }
                None
            }
            Expr::Unary { op, value } if op.value == "-" => {
                let CallerArgRef::Const(c) = self.resolve_callee_guard_arg_for_return(
                    env,
                    def_file,
                    *value,
                    formal_to_caller,
                )?
                else {
                    return None;
                };
                Some(CallerArgRef::Const(c.checked_neg()?))
            }
            Expr::Binary { op, left, right } if matches!(op.value.as_str(), "+" | "-") => {
                let l = self.resolve_callee_guard_arg_for_return(
                    env,
                    def_file,
                    *left,
                    formal_to_caller,
                )?;
                let r = self.resolve_callee_guard_arg_for_return(
                    env,
                    def_file,
                    *right,
                    formal_to_caller,
                )?;
                match (l, r) {
                    (CallerArgRef::Const(a), CallerArgRef::Const(b)) => {
                        let v = if op.value == "+" {
                            a.checked_add(b)?
                        } else {
                            a.checked_sub(b)?
                        };
                        Some(CallerArgRef::Const(v))
                    }
                    (lhs, CallerArgRef::Const(c)) => {
                        let offset = if op.value == "+" { c } else { c.checked_neg()? };
                        let base = match lhs {
                            CallerArgRef::Place(p) => Atom::Val(p),
                            CallerArgRef::LenOf(p) => Atom::Len(p),
                            CallerArgRef::Atom(a) => a,
                            _ => return None,
                        };
                        let t = env.refinements.dbm.fresh_temp();
                        env.refinements.dbm.add_eq(t.clone(), base, offset);
                        Some(CallerArgRef::Atom(t))
                    }
                    (lhs, rhs) if op.value == "-" => {
                        let to_atom = |v: CallerArgRef, dbm: &mut Dbm| -> Option<Atom> {
                            match v {
                                CallerArgRef::Place(p) => Some(Atom::Val(p)),
                                CallerArgRef::LenOf(p) => Some(Atom::Len(p)),
                                CallerArgRef::Atom(a) => Some(a),
                                CallerArgRef::Const(c) => {
                                    let t = dbm.fresh_temp();
                                    dbm.add_eq(t.clone(), Atom::Zero, c);
                                    Some(t)
                                }
                                CallerArgRef::KeyConst(_) => None,
                            }
                        };
                        let la = to_atom(lhs, &mut env.refinements.dbm)?;
                        let ra = to_atom(rhs, &mut env.refinements.dbm)?;
                        let t = env.refinements.dbm.fresh_temp();
                        env.refinements.dbm.add_diff_eq(t.clone(), la, ra, 0);
                        Some(CallerArgRef::Atom(t))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

enum FalliblePayload {
    Vacuous,
    Payload(ExprId),
    PassThrough(ExprId),
}

enum CallerArgRef {
    Place(Place),
    LenOf(Place),
    Const(i128),
    KeyConst(KeyConst),
    Atom(Atom),
}

pub(super) fn instantiate_call_return_pred(
    pred: &ProofPred<ReturnAtom>,
    target: &Place,
) -> Option<ProofPred<Atom>> {
    pred.map_atoms(&mut |ra| match ra {
        ReturnAtom::SubjectVal(path) => {
            let mut p = target.clone();
            p.path.extend(path.iter().cloned());
            Some(Atom::Val(p))
        }
        ReturnAtom::SubjectLen(path) => {
            let mut p = target.clone();
            p.path.extend(path.iter().cloned());
            Some(Atom::Len(p))
        }
        ReturnAtom::Caller(a) => Some(a.clone()),
    })
}

fn combine_if_pred(
    c: ProofPred<ProofAtom>,
    y: ProofPred<ProofAtom>,
    n: ProofPred<ProofAtom>,
) -> ProofPred<ProofAtom> {
    match (&y, &n) {
        (ProofPred::True, ProofPred::False) => c,
        (ProofPred::False, ProofPred::True) => c.negate(),
        (ProofPred::True, _) => ProofPred::or(vec![c, n]),
        (_, ProofPred::False) => ProofPred::and(vec![c, y]),
        (ProofPred::False, _) => ProofPred::and(vec![c.negate(), n]),
        (_, ProofPred::True) => ProofPred::or(vec![c.negate(), y]),
        _ => ProofPred::or(vec![
            ProofPred::and(vec![c.clone(), y]),
            ProofPred::and(vec![c.negate(), n]),
        ]),
    }
}

fn substitute_tf_pred(
    pred: &ProofPred<ProofAtom>,
    args: &[TfLocal],
) -> Option<ProofPred<ProofAtom>> {
    fn subst_atom(opt: &Option<ProofAtom>, args: &[TfLocal]) -> Option<LinExpr<ProofAtom>> {
        let Some(atom) = opt else {
            return Some(LinExpr::Const(0));
        };
        match atom {
            ProofAtom::Val(pp) => match args.get(pp.param_idx)? {
                TfLocal::Place(base) => {
                    let mut p = base.clone();
                    p.path.extend(pp.path.iter().cloned());
                    Some(LinExpr::Pos {
                        atom: ProofAtom::Val(p),
                        offset: 0,
                    })
                }
                TfLocal::Lin(lin) if pp.path.is_empty() => Some(lin.clone()),
                _ => None,
            },
            ProofAtom::Len(pp) => match args.get(pp.param_idx)? {
                TfLocal::Place(base) => {
                    let mut p = base.clone();
                    p.path.extend(pp.path.iter().cloned());
                    Some(LinExpr::Pos {
                        atom: ProofAtom::Len(p),
                        offset: 0,
                    })
                }
                _ => None,
            },
            ProofAtom::Const(KeyConst::Int(c)) => Some(LinExpr::Const(*c)),
            ProofAtom::Const(_) => None,
        }
    }
    fn subst_raw_atom(atom: &ProofAtom, args: &[TfLocal]) -> Option<ProofAtom> {
        match atom {
            ProofAtom::Const(kc) => Some(ProofAtom::Const(kc.clone())),
            ProofAtom::Val(pp) => match args.get(pp.param_idx)? {
                TfLocal::Place(base) => {
                    let mut p = base.clone();
                    p.path.extend(pp.path.iter().cloned());
                    Some(ProofAtom::Val(p))
                }
                TfLocal::Const(kc) if pp.path.is_empty() => Some(ProofAtom::Const(kc.clone())),
                TfLocal::Lin(LinExpr::Const(c)) if pp.path.is_empty() => {
                    Some(ProofAtom::Const(KeyConst::Int(*c)))
                }
                TfLocal::Lin(LinExpr::Pos {
                    atom: ProofAtom::Val(p),
                    offset: 0,
                }) if pp.path.is_empty() => Some(ProofAtom::Val(p.clone())),
                _ => None,
            },
            ProofAtom::Len(pp) => match args.get(pp.param_idx)? {
                TfLocal::Place(base) => {
                    let mut p = base.clone();
                    p.path.extend(pp.path.iter().cloned());
                    Some(ProofAtom::Len(p))
                }
                _ => None,
            },
        }
    }
    Some(match pred {
        ProofPred::True => ProofPred::True,
        ProofPred::False => ProofPred::False,
        ProofPred::DiffLe { lhs, rhs, bound } => {
            let l = subst_atom(lhs, args)?;
            let r = subst_atom(rhs, args)?.add(LinExpr::Const(*bound))?;
            LinExpr::compare("<=", l, r)?
        }
        ProofPred::DiffNe { lhs, rhs, offset } => {
            let l = subst_atom(lhs, args)?;
            let r = subst_atom(rhs, args)?.add(LinExpr::Const(*offset))?;
            LinExpr::compare("!=", l, r)?
        }
        ProofPred::Contains {
            container,
            key,
            negated,
        } => ProofPred::Contains {
            container: subst_raw_atom(container, args)?,
            key: subst_raw_atom(key, args)?,
            negated: *negated,
        },
        ProofPred::And(ps) => {
            let mut out = Vec::with_capacity(ps.len());
            for p in ps {
                out.push(substitute_tf_pred(p, args)?);
            }
            ProofPred::and(out)
        }
        ProofPred::Or(ps) => {
            let mut out = Vec::with_capacity(ps.len());
            for p in ps {
                out.push(substitute_tf_pred(p, args)?);
            }
            ProofPred::or(out)
        }
    })
}

impl Checker<'_> {
    /// Collects canonical `.rili` exported parameter and return static proofs for a function.
    pub(super) fn collect_export_proofs(
        &mut self,
        file: FileId,
        fn_id: DefinitionId,
        fun: &syntax::Function,
    ) {
        let mut param_locals: HashMap<DefinitionId, TfLocal> = HashMap::new();
        let mut return_locals: HashMap<DefinitionId, TfLocal> = HashMap::new();
        for (idx, param) in fun.signature.params.iter().enumerate() {
            if let Some(name) = &param.name
                && let Some(def_id) = self.resolve(name.span)
            {
                param_locals.insert(
                    def_id,
                    TfLocal::Place(ProofPlace {
                        param_idx: idx,
                        path: Vec::new(),
                    }),
                );
                return_locals.insert(
                    def_id,
                    TfLocal::Place(ProofPlace {
                        param_idx: idx + 1,
                        path: Vec::new(),
                    }),
                );
            }
        }

        let mut param_proofs = Vec::new();
        for (idx, param) in fun.signature.params.iter().enumerate() {
            let subject = TfLocal::Place(ProofPlace {
                param_idx: idx,
                path: Vec::new(),
            });
            if let Some(ty_id) = param.ty
                && let Some((tf_id, angle_args, _)) = self.bare_proof_type_info(file, ty_id)
                && let Some(extra) = self.extract_static_proof_angle_args(tf_id, &angle_args)
            {
                let mut sub_args = Vec::with_capacity(1 + extra.len());
                sub_args.push(subject.clone());
                let mut all_ok = true;
                for opt in extra {
                    if let Some(arg_expr) = opt {
                        if let Ok(local_val) = self.lower_tf_arg(file, arg_expr, &param_locals) {
                            sub_args.push(local_val);
                        } else {
                            all_ok = false;
                            break;
                        }
                    } else {
                        all_ok = false;
                        break;
                    }
                }
                let pred = if all_ok {
                    self.lower_type_fn(tf_id)
                        .ok()
                        .and_then(|l| substitute_tf_pred(&l.pred, &sub_args))
                } else {
                    None
                };
                let fallback = self.hir.definition(tf_id).name.value.clone();
                param_proofs.push(ExportProof {
                    pred,
                    fallback,
                    kind: ProofKind::Plain,
                });
            }
            for &guard in &param.guards {
                if !self.hir.is_static_proof_guard(file, guard) {
                    continue;
                }
                param_proofs.push(self.export_single_guard(
                    file,
                    guard,
                    subject.clone(),
                    &param_locals,
                ));
            }
        }

        let mut return_proofs = Vec::new();
        let ret_subject = TfLocal::Place(ProofPlace {
            param_idx: 0,
            path: Vec::new(),
        });
        if let Some((tf_id, angle_args, _)) = self.bare_proof_type_info(file, fun.signature.result)
            && let Some(extra) = self.extract_static_proof_angle_args(tf_id, &angle_args)
        {
            let mut sub_args = Vec::with_capacity(1 + extra.len());
            sub_args.push(ret_subject.clone());
            let mut all_ok = true;
            for opt in extra {
                if let Some(arg_expr) = opt {
                    if let Ok(local_val) = self.lower_tf_arg(file, arg_expr, &return_locals) {
                        sub_args.push(local_val);
                    } else {
                        all_ok = false;
                        break;
                    }
                } else {
                    all_ok = false;
                    break;
                }
            }
            let pred = if all_ok {
                self.lower_type_fn(tf_id)
                    .ok()
                    .and_then(|l| substitute_tf_pred(&l.pred, &sub_args))
            } else {
                None
            };
            let fallback = self.hir.definition(tf_id).name.value.clone();
            return_proofs.push(ExportProof {
                pred,
                fallback,
                kind: ProofKind::Plain,
            });
        }
        for &guard in &fun.signature.guards {
            if !self.hir.is_static_proof_guard(file, guard) {
                continue;
            }
            return_proofs.push(self.export_single_guard(
                file,
                guard,
                ret_subject.clone(),
                &return_locals,
            ));
        }

        if !param_proofs.is_empty() {
            self.exported_param_proofs.insert(fn_id, param_proofs);
        }
        if !return_proofs.is_empty() {
            self.exported_return_proofs.insert(fn_id, return_proofs);
        }
    }

    pub(super) fn collect_type_invariant_exports(
        &mut self,
        file: FileId,
        type_id: DefinitionId,
        decl: &syntax::TypeDecl,
    ) {
        let mut proofs = Vec::new();
        let empty = HashMap::new();
        for &guard in &decl.guards {
            if !self.hir.is_static_proof_guard(file, guard) {
                continue;
            }
            let subject = TfLocal::Place(ProofPlace {
                param_idx: 0,
                path: Vec::new(),
            });
            proofs.push(self.export_single_guard(file, guard, subject, &empty));
        }
        if !proofs.is_empty() {
            self.exported_type_invariants.insert(type_id, proofs);
        }
    }

    /// Verifies every static invariant `|> Guard` declared on `adt` against the constructor payload.
    pub(super) fn verify_type_invariants(
        &mut self,
        env: &mut Env,
        adt: &super::Adt,
        subject: ProofArgVal,
        report_span: Span,
    ) {
        let def = self.hir.definition(adt.definition);
        let Some(stmt) = def.stmt else { return };
        let def_file = def.name.span.file;
        let StmtKind::Type(decl) = &self.ast(def_file).stmt(stmt).value.kind else {
            return;
        };
        if decl.guards.is_empty() {
            return;
        }
        let guards = decl.guards.clone();
        let empty_formals = HashMap::new();
        let mut all_ok = true;
        for guard in guards {
            let Some((tf_id, extra)) = self.extract_static_proof_guard(def_file, guard) else {
                continue;
            };
            let guard_span = self.ast(def_file).expr(guard).span;
            let mut scratch = env.refinements.dbm.clone();
            let mut arg_vals = Vec::with_capacity(1 + extra.len());
            arg_vals.push(subject.clone());
            let mut extra_ok = true;
            for opt in extra {
                let Some(guard_arg_expr) = opt else {
                    arg_vals.push(ProofArgVal::Const(0));
                    continue;
                };
                match self.eval_callee_guard_arg(
                    env,
                    &mut scratch,
                    def_file,
                    guard_arg_expr,
                    &empty_formals,
                ) {
                    Some(val) => arg_vals.push(val),
                    None => {
                        extra_ok = false;
                        break;
                    }
                }
            }
            if !extra_ok {
                all_ok = false;
                let diag = Diagnostic::error(
                    Code::E0323,
                    report_span,
                    format!(
                        "constructor payload does not satisfy type invariant '{}'",
                        self.hir.definition(tf_id).name.value
                    ),
                )
                .with_label(guard_span, "required by this type invariant");
                self.diagnostics.push(diag);
                continue;
            }
            let ok = self.verify_proof_obligation_with_scratch_code(
                env,
                &mut scratch,
                tf_id,
                &arg_vals,
                report_span,
                guard_span,
                "constructor payload does not satisfy type invariant",
                Code::E0323,
            );
            if !ok {
                all_ok = false;
            }
        }
        if all_ok {
            self.proved_ops.insert(report_span);
        }
    }

    /// Auto-seeds static type invariants into `env.refinements.dbm` when a value of type `ty`
    /// is bound or received (cycle-safe, depth-bounded, atom-cap-safe).
    pub(super) fn seed_type_invariants(&mut self, env: &mut Env, place: &Place, ty: &Ty) {
        let mut seen = HashSet::new();
        self.seed_type_invariants_rec(env, place, ty, 0, &mut seen);
    }

    fn seed_type_invariants_rec(
        &mut self,
        env: &mut Env,
        place: &Place,
        ty: &Ty,
        depth: usize,
        seen: &mut HashSet<DefinitionId>,
    ) {
        if depth > 4 || env.refinements.dbm.unsat || env.refinements.dbm.atom_count() >= 56 {
            return;
        }
        let norm = self.normalize(ty);
        match norm {
            Ty::Adt(adt) => {
                if adt.kind == super::AdtKind::Opaque && adt.defining_scope != env.scope {
                    return;
                }
                let rep = if matches!(adt.kind, super::AdtKind::Nominal | super::AdtKind::Opaque) {
                    self.representation(env, &adt)
                } else {
                    None
                };
                if self.has_type_invariants(adt.definition) {
                    let is_composite_rep = matches!(
                        rep.as_ref().map(|r| self.normalize(r)),
                        Some(Ty::Record(..) | Ty::Tuple(_))
                    );
                    let mut inner_place = place.clone();
                    inner_place.path.push("#inner".to_owned());
                    let targets: Vec<Place> = if is_composite_rep {
                        vec![place.clone(), inner_place.clone()]
                    } else {
                        vec![inner_place.clone()]
                    };
                    let def = self.hir.definition(adt.definition);
                    if let Some(stmt) = def.stmt {
                        let def_file = def.name.span.file;
                        let guards = match &self.ast(def_file).stmt(stmt).value.kind {
                            StmtKind::Type(decl) => decl.guards.clone(),
                            _ => Vec::new(),
                        };
                        let empty_formals = HashMap::new();
                        for guard in guards {
                            let Some((tf_id, extra)) =
                                self.extract_static_proof_guard(def_file, guard)
                            else {
                                continue;
                            };
                            let Ok(lowered) = self.lower_type_fn(tf_id) else {
                                continue;
                            };
                            for target in &targets {
                                if env.refinements.dbm.atom_count() >= 56 {
                                    break;
                                }
                                let mut scratch = env.refinements.dbm.clone();
                                let mut arg_vals = Vec::with_capacity(1 + extra.len());
                                arg_vals.push(ProofArgVal::Place(target.clone()));
                                let mut ok = true;
                                for opt in &extra {
                                    if let Some(e) = opt {
                                        if let Some(v) = self.eval_callee_guard_arg(
                                            env,
                                            &mut scratch,
                                            def_file,
                                            *e,
                                            &empty_formals,
                                        ) {
                                            arg_vals.push(v);
                                        } else {
                                            ok = false;
                                            break;
                                        }
                                    } else {
                                        arg_vals.push(ProofArgVal::Const(0));
                                    }
                                }
                                if ok
                                    && let Some(pred) = self.instantiate_proof_pred(
                                        env,
                                        &mut scratch,
                                        &lowered.pred,
                                        &arg_vals,
                                    )
                                {
                                    scratch.assume(&pred);
                                    scratch.forget_temps();
                                    env.refinements.dbm = scratch;
                                }
                            }
                        }
                    }
                }
                if let Some(rep_ty) = rep
                    && seen.insert(adt.definition)
                {
                    let rep_norm = self.normalize(&rep_ty);
                    match &rep_norm {
                        Ty::Record(fields, _) => {
                            for (fname, m) in fields {
                                let mut sub = place.clone();
                                sub.path.push(fname.clone());
                                self.seed_type_invariants_rec(env, &sub, &m.ty, depth + 1, seen);
                            }
                        }
                        Ty::Tuple(items) => {
                            for (i, m) in items.iter().enumerate() {
                                let mut sub = place.clone();
                                sub.path.push(i.to_string());
                                self.seed_type_invariants_rec(env, &sub, &m.ty, depth + 1, seen);
                            }
                        }
                        Ty::Adt(_) => {
                            let mut sub = place.clone();
                            sub.path.push("#inner".to_owned());
                            self.seed_type_invariants_rec(env, &sub, &rep_norm, depth + 1, seen);
                        }
                        _ => {}
                    }
                    seen.remove(&adt.definition);
                }
            }
            Ty::Record(fields, _) => {
                for (fname, m) in fields {
                    let mut sub = place.clone();
                    sub.path.push(fname);
                    self.seed_type_invariants_rec(env, &sub, &m.ty, depth + 1, seen);
                }
            }
            Ty::Tuple(items) => {
                for (i, m) in items.into_iter().enumerate() {
                    let mut sub = place.clone();
                    sub.path.push(i.to_string());
                    self.seed_type_invariants_rec(env, &sub, &m.ty, depth + 1, seen);
                }
            }
            _ => {}
        }
    }

    fn export_single_guard(
        &mut self,
        file: FileId,
        guard: ExprId,
        subject: TfLocal,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> ExportProof {
        if let Some((kind, pred_arg)) = self.extract_proof_combinator(file, guard) {
            if let Ok(pred) = self.lower_combinator_arg(file, &pred_arg, locals) {
                return ExportProof {
                    pred: Some(pred),
                    fallback: String::new(),
                    kind,
                };
            }
            let span = self.ast(file).expr(guard).span;
            let tokens: Vec<_> = self.hir.file(file).token_text(span).collect();
            return ExportProof {
                pred: None,
                fallback: tokens.join(" "),
                kind,
            };
        }
        if let Some((tf_id, extra)) = self.extract_static_proof_guard(file, guard)
            && let Ok(lowered) = self.lower_type_fn(tf_id)
        {
            let mut tf_args = Vec::with_capacity(1 + extra.len());
            tf_args.push(subject);
            let mut all_lowered = true;
            for opt in extra {
                if let Some(expr) = opt
                    && let Some(val) = self.lower_export_arg(file, expr, locals)
                {
                    tf_args.push(val);
                } else {
                    all_lowered = false;
                    break;
                }
            }
            if all_lowered && let Some(pred) = substitute_tf_pred(&lowered.pred, &tf_args) {
                return ExportProof {
                    pred: Some(pred),
                    fallback: String::new(),
                    kind: ProofKind::Plain,
                };
            }
        }
        let span = self.ast(file).expr(guard).span;
        let head = self
            .extract_static_proof_guard(file, guard)
            .map(|(tf_id, _)| self.hir.export_name(tf_id))
            .unwrap_or_default();
        let tokens: Vec<_> = self.hir.file(file).token_text(span).collect();
        ExportProof {
            pred: None,
            fallback: format!("{head}:{}", tokens.join(" ")),
            kind: ProofKind::Plain,
        }
    }

    fn lower_export_arg(
        &self,
        file: FileId,
        expr: ExprId,
        locals: &HashMap<DefinitionId, TfLocal>,
    ) -> Option<TfLocal> {
        if let Some(place) = self.lower_tf_place(file, expr, locals) {
            return Some(TfLocal::Place(place));
        }
        if let Ok(lin) = self.lower_tf_lin(file, expr, locals) {
            return Some(TfLocal::Lin(lin));
        }
        self.lower_tf_key_const(file, expr).map(TfLocal::Const)
    }
}
