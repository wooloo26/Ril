use std::collections::HashMap;

use ril_hir::DefinitionId;
use ril_source::diag::Code;
use ril_syntax::syntax::{Condition, Expr, ExprId, Member};

use super::{
    NarrowDrop, NarrowDropCause, Ty, Value,
    check::{Checker, Env},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Place {
    root: DefinitionId,
    path: Vec<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Fact {
    depth: usize,
    is_none: bool,
    invalidated: Option<(Code, ril_source::span::Span)>,
}

#[derive(Clone, Default)]
pub(super) struct Refinements(HashMap<Place, Fact>);

impl Checker<'_> {
    fn place(&self, env: &Env, expr: ExprId) -> Option<Place> {
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
            && let Some(fact) = env.refinements.0.get(&place)
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
                .0
                .get(&place)
                .is_some_and(|fact| fact.invalidated.is_none() && fact.is_none)
        })
    }

    pub(super) fn assumption(&mut self, env: &mut Env, condition: &Condition, truth: bool) {
        let Condition::Expr(expr) = condition else {
            return;
        };
        self.relate(env, *expr, truth);
    }

    pub(super) fn relate(&mut self, env: &mut Env, test: ExprId, truth: bool) {
        let ast = self.ast(env.file);
        let node = ast.expr(test);
        match &node.value {
            Expr::Unary { op, value } if op.value == "!" => self.relate(env, *value, !truth),
            Expr::Binary { op, left, right }
                if op.value == "&&" && truth || op.value == "||" && !truth =>
            {
                self.relate(env, *left, truth);
                self.relate(env, *right, truth);
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
                        let depth = env
                            .refinements
                            .0
                            .get(&place)
                            .filter(|f| f.invalidated.is_none())
                            .map_or(1, |f| f.depth + 1);
                        env.refinements.0.insert(
                            place,
                            Fact {
                                depth,
                                is_none: false,
                                invalidated: None,
                            },
                        );
                    } else {
                        let depth = env
                            .refinements
                            .0
                            .get(&place)
                            .filter(|f| f.invalidated.is_none())
                            .map_or(0, |f| f.depth);
                        env.refinements.0.insert(
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

    pub(super) fn writes_place(
        &mut self,
        env: &mut Env,
        expr: ExprId,
        cause_span: ril_source::span::Span,
    ) {
        if let Some(place) = self.place(env, expr) {
            let mut dropped = Vec::new();
            for (candidate, fact) in &mut env.refinements.0 {
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
        } else {
            self.invalidate_live(
                env,
                Code::E0310,
                cause_span,
                NarrowDropCause::OverlappingWrite,
            );
        }
    }

    pub(super) fn invalidate_live(
        &mut self,
        env: &mut Env,
        code: Code,
        cause_span: ril_source::span::Span,
        cause: NarrowDropCause,
    ) {
        let mut dropped = Vec::new();
        for (place, fact) in &mut env.refinements.0 {
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
        let mut result = HashMap::new();
        for (place, first) in &a.refinements.0 {
            if let Some(second) = b.refinements.0.get(place) {
                let depth = first.depth.min(second.depth);
                let is_none = first.is_none && second.is_none;
                let invalidated = first.invalidated.or(second.invalidated);
                result.insert(
                    place.clone(),
                    Fact {
                        depth,
                        is_none,
                        invalidated,
                    },
                );
            }
        }
        Refinements(result)
    }
}
