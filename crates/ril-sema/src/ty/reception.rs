use ril_frontend::syntax::{ExprId, Mode};

use super::{
    Member, Ty,
    check::{Checker, Env},
};

#[derive(Clone, Debug)]
pub(crate) enum Step {
    Field(String),
    Position(usize),
    Elements,
}

#[derive(Clone)]
pub(crate) struct Adjustment {
    pub(crate) path: Vec<Step>,
    pub(crate) mode: Mode,
}

impl Checker<'_> {
    pub(super) fn receive(&mut self, env: &mut Env, expression: ExprId, expected: &Ty) -> Ty {
        let actual = self.expr(env, expression, Some(expected));
        if self.fits(env, &actual, expected) {
            return actual;
        }
        let span = self.ast(env.file).expr(expression).span;
        let mut adjustments = Vec::new();
        if self.adjustments(
            env,
            &self.normalize(&actual),
            &self.normalize(expected),
            &mut Vec::new(),
            &mut adjustments,
        ) && !adjustments.is_empty()
        {
            self.receptions.insert(span, adjustments);
        } else {
            self.require(env, span, &actual, expected);
        }
        actual
    }

    fn adjustments(
        &mut self,
        env: &Env,
        actual: &Ty,
        expected: &Ty,
        path: &mut Vec<Step>,
        adjustments: &mut Vec<Adjustment>,
    ) -> bool {
        match (actual, expected) {
            (Ty::Array(a), Ty::Array(b)) => {
                path.push(Step::Elements);
                let equivalent = self.member_adjustments(env, a, b, path, adjustments);
                path.pop();
                equivalent
            }
            (Ty::Map(ka, a), Ty::Map(kb, b))
                if self.fits(env, ka, kb) && self.fits(env, kb, ka) =>
            {
                path.push(Step::Elements);
                let equivalent = self.member_adjustments(env, a, b, path, adjustments);
                path.pop();
                equivalent
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                a.iter().zip(b).enumerate().all(|(index, (from, to))| {
                    path.push(Step::Position(index));
                    let equivalent = self.member_adjustments(env, from, to, path, adjustments);
                    path.pop();
                    equivalent
                })
            }
            (Ty::Record(a, false), Ty::Record(b, false)) if a.len() == b.len() => {
                a.iter().all(|(key, from)| {
                    let Some(to) = b.get(key) else { return false };
                    path.push(Step::Field(key.clone()));
                    let equivalent = self.member_adjustments(env, from, to, path, adjustments);
                    path.pop();
                    equivalent
                })
            }
            _ => self.fits(env, actual, expected),
        }
    }

    fn member_adjustments(
        &mut self,
        env: &Env,
        actual: &Member,
        expected: &Member,
        path: &mut Vec<Step>,
        adjustments: &mut Vec<Adjustment>,
    ) -> bool {
        if actual.mode.variable != expected.mode.variable {
            return false;
        }
        if actual.mode.mode != expected.mode.mode && expected.mode.mode != Mode::Via {
            adjustments.push(Adjustment {
                path: path.clone(),
                mode: expected.mode.mode,
            });
        }
        self.adjustments(env, &actual.ty, &expected.ty, path, adjustments)
    }
}
