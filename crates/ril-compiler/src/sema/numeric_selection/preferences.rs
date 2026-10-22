//! A bounded, borrowed view of rigid preferences. This is neither a selection
//! nor another stored numeric truth; one application owns this temporary memo.
use super::solve::charge;
use super::*;

#[derive(Clone, Copy)]
struct Preference {
    rigid: Option<NumberType>,
    float_only: bool,
}

pub(crate) struct NumericPreferences(BTreeMap<NumericHoleId, Preference>);
impl NumericPreferences {
    pub(crate) fn get(
        &self,
        id: NumericHoleId,
        defaults: bool,
    ) -> Result<Option<Ty>, SourceTypesError> {
        let preference = self.0.get(&id).ok_or(SourceTypesError::MissingNode)?;
        Ok(preference
            .rigid
            .or_else(|| (defaults && preference.float_only).then_some(NumberType::F64))
            .map(selected_ty))
    }
}

pub(crate) fn preferences(
    holes: &[NumericHole],
    roots: &[NumericHoleId],
    work: &mut usize,
) -> Result<NumericPreferences, SourceTypesError> {
    struct Query<'a, 'w> {
        holes: &'a [NumericHole],
        work: &'w mut usize,
        memo: BTreeMap<NumericHoleId, Preference>,
        active: BTreeSet<NumericHoleId>,
    }
    impl Query<'_, '_> {
        fn operand(
            &mut self,
            operand: &NumericOperand,
            depth: usize,
        ) -> Result<Option<NumberType>, SourceTypesError> {
            charge(self.work, 16)?;
            match operand.ty {
                Ty::NumericHole(id) => Ok(self.hole(id, depth + 1)?.rigid),
                _ => Ok(number_type(&operand.ty)),
            }
        }
        fn hole(
            &mut self,
            id: NumericHoleId,
            depth: usize,
        ) -> Result<Preference, SourceTypesError> {
            charge(
                self.work,
                2 + self.memo.len().checked_ilog2().unwrap_or(0) as usize,
            )?;
            if depth >= 128 {
                return Err(SourceTypesError::BudgetExceeded);
            }
            if let Some(value) = self.memo.get(&id) {
                return Ok(*value);
            }
            if !self.active.insert(id) {
                return Err(SourceTypesError::Unresolved);
            }
            let holes = self.holes;
            let hole = holes
                .get(id.0 as usize)
                .filter(|hole| hole.id == id)
                .ok_or(SourceTypesError::MissingNode)?;
            let rigid = match &hole.term {
                NumericTerm::Literal(_) => None,
                NumericTerm::Unary { operand, .. } => self.operand(operand, depth)?,
                NumericTerm::Binary { left, right, .. } => match self.operand(left, depth)? {
                    Some(value) => Some(value),
                    None => self.operand(right, depth)?,
                },
                NumericTerm::Join(_) => return Err(SourceTypesError::Unresolved),
            };
            let preference = Preference {
                rigid,
                float_only: hole.domain == NumericDomain::FloatOnly,
            };
            charge(self.work, 2)?;
            self.active.remove(&id);
            self.memo.insert(id, preference);
            Ok(preference)
        }
    }
    charge(work, 1 + roots.len().saturating_mul(2))?;
    let mut query = Query {
        holes,
        work,
        memo: BTreeMap::new(),
        active: BTreeSet::new(),
    };
    for root in roots {
        query.hole(*root, 0)?;
    }
    Ok(NumericPreferences(query.memo))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn shared_dags_pay_for_each_hole_once_and_budget_failures_are_errors() {
        let source =
            ril_test::case_bytes("tests/conformance/numeric.ril::deferred-arithmetic-safe");
        let verified = crate::Session::new(source.to_vec()).verify().unwrap();
        let facts = verified.facts();
        let mut holes = facts.numeric_holes.clone();
        let child = holes
            .iter()
            .position(|hole| matches!(hole.term, NumericTerm::Literal(_)))
            .unwrap();
        let model = holes
            .iter()
            .find_map(|hole| match &hole.term {
                NumericTerm::Binary { left, .. } => Some((hole.clone(), (**left).clone())),
                _ => None,
            })
            .unwrap();
        let mut root = NumericHoleId(child as u32);
        for _ in 0..40 {
            let mut hole = model.0.clone();
            let mut operand = model.1.clone();
            operand.ty = Ty::NumericHole(root);
            operand.hole = Some(root);
            hole.id = NumericHoleId(holes.len() as u32);
            hole.term = NumericTerm::Binary {
                operator: "+".into(),
                left: Box::new(operand.clone()),
                right: Box::new(operand),
            };
            root = hole.id;
            holes.push(hole);
        }
        let mut work = 20_000;
        assert!(
            preferences(&holes, &[root, root], &mut work)
                .unwrap()
                .get(root, false)
                .unwrap()
                .is_none()
        );
        assert!(work > 10_000, "a shared DAG must not be expanded as a tree");
        assert!(matches!(
            preferences(&holes, &[root], &mut 0),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            preferences(&holes, &[root], &mut 16),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }
}
