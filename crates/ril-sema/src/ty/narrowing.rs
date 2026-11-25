use std::collections::HashMap;

use ril_hir::DefinitionId;
use ril_source::diag::Code;
use ril_syntax::syntax::{Condition, Expr, ExprId, Member};

use super::{
    Ty, Value,
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
    invalidated: Option<Code>,
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
            if let Some(code) = fact.invalidated {
                self.narrow_errors.insert(span, code);
            } else {
                for _ in 0..fact.depth {
                    if let Ty::Option(inner) = ty {
                        ty = *inner;
                    } else {
                        return ty;
                    }
                }
                self.narrowings.insert(span, fact.depth);
            }
        }
        ty
    }

    pub(super) fn assumption(&mut self, env: &mut Env, condition: &Condition, truth: bool) {
        let Condition::Expr(expr) = condition else {
            return;
        };
        self.relate(env, *expr, truth);
    }

    fn relate(&mut self, env: &mut Env, test: ExprId, truth: bool) {
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
            Expr::Binary { op, left, right }
                if matches!((op.value.as_str(), truth), ("==", false) | ("!=", true)) =>
            {
                let compared = if self.is_none(env, *left) {
                    *right
                } else if self.is_none(env, *right) {
                    *left
                } else {
                    return;
                };
                let span = ast.expr(compared).span;
                if matches!(self.types.get(&span), Some(Ty::Option(_)))
                    && let Some(place) = self.place(env, compared)
                {
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
                            invalidated: None,
                        },
                    );
                }
            }
            _ => {}
        }
    }

    pub(super) fn writes_place(&self, env: &mut Env, expr: ExprId) {
        if let Some(place) = self.place(env, expr) {
            for (candidate, fact) in &mut env.refinements.0 {
                if candidate.root == place.root
                    && candidate.path.iter().zip(&place.path).all(|(a, b)| a == b)
                {
                    fact.invalidated = Some(Code::E0310);
                }
            }
        } else {
            self.invalidate_live(env, Code::E0310);
        }
    }

    pub(super) fn invalidate_live(&self, env: &mut Env, code: Code) {
        for (place, fact) in &mut env.refinements.0 {
            if self.live.contains(&place.root) && fact.invalidated.is_none() {
                fact.invalidated = Some(code);
            }
        }
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
                let invalidated = first.invalidated.or(second.invalidated);
                result.insert(place.clone(), Fact { depth, invalidated });
            }
        }
        Refinements(result)
    }
}
