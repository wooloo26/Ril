//! Pure row-shape entailment. No value, permission or resource proof is issued.
#[cfg(test)]
use super::model::rows::RowTail;
use super::model::rows::{Fields, OpenTail, Row, RowError, Solver};

/// The caller first checks field types using complete scoped type evidence and
/// uses their solved common representation as F. The solver still checks exact
/// slot modes, declared absences and every shared residual equation.
///
/// `residual.identity` is flexible for this application. Caller open tails stay
/// rigid and require independently declared lacks; they are never closed here.
pub(crate) fn entail<F: Clone + Eq>(
    solver: &mut Solver<F>,
    required: &Fields<F>,
    residual: Option<&OpenTail>,
    actual: &Row<F>,
) -> Result<Row<F>, RowError> {
    let mut trial = solver.clone();
    let expected = match residual {
        Some(tail) => Row::open(required.clone(), tail.clone()),
        None => Row::closed(required.clone()),
    };
    trial.unify(&expected, actual)?;
    let remainder = match residual {
        Some(tail) => trial.normalize(&Row::open(Fields::new(), tail.clone()))?,
        None => Row::closed(Fields::new()),
    };
    *solver = trial;
    Ok(remainder)
}

/// An open remainder has no closed actual Type witness, even with zero known
/// fields. This is deliberately distinct from an empty closed record.
#[cfg(test)]
fn closed_remainder<F>(row: &Row<F>) -> Option<&Fields<F>> {
    matches!(row.tail, RowTail::Closed).then_some(&row.fields)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::model::rows::RowIdentity;
    use std::collections::BTreeSet;

    fn identity(name: &str) -> RowIdentity {
        RowIdentity::Binder(name.into())
    }
    fn tail(name: &str, lacks: &[&str]) -> OpenTail {
        OpenTail {
            identity: identity(name),
            lacks: lacks.iter().map(|name| (*name).into()).collect(),
        }
    }
    fn fields(values: &[(&str, bool, &str)]) -> Fields<String> {
        values
            .iter()
            .map(|(name, mode, ty)| ((*name).into(), (*mode, (*ty).into())))
            .collect()
    }

    #[test]
    fn closed_actual_selects_the_exact_extra_fields_and_slot_modes() {
        let residual = tail("callee:R", &["id"]);
        let mut solver = Solver::new("call", [residual.identity.clone()]);
        let actual = Row::closed(fields(&[("id", false, "int"), ("tag", true, "str")]));
        let selected = entail(
            &mut solver,
            &fields(&[("id", false, "int")]),
            Some(&residual),
            &actual,
        )
        .unwrap();
        assert_eq!(
            closed_remainder(&selected),
            Some(&fields(&[("tag", true, "str")]))
        );
    }

    #[test]
    fn a_declared_rigid_open_parameter_preserves_its_unknown_tail() {
        let caller = tail("caller:S", &["id", "tag"]);
        let residual = tail("callee:R", &["id"]);
        let mut solver = Solver::new("call", [residual.identity.clone()]);
        solver
            .declare_rigid(caller.identity.clone(), caller.lacks.clone())
            .unwrap();
        let actual = Row::open(
            fields(&[("id", false, "int"), ("tag", false, "str")]),
            caller.clone(),
        );
        let selected = entail(
            &mut solver,
            &fields(&[("id", false, "int")]),
            Some(&residual),
            &actual,
        )
        .unwrap();
        assert_eq!(selected.fields, fields(&[("tag", false, "str")]));
        assert!(matches!(&selected.tail, RowTail::Open(tail) if tail.identity == caller.identity));
        assert!(closed_remainder(&selected).is_none());
    }

    #[test]
    fn an_unknown_row_does_not_supply_a_missing_required_field() {
        let caller = tail("caller:S", &[]);
        let residual = tail("callee:R", &["id"]);
        let mut solver = Solver::new("call", [residual.identity.clone()]);
        solver
            .declare_rigid(caller.identity.clone(), BTreeSet::new())
            .unwrap();
        assert!(
            entail(
                &mut solver,
                &fields(&[("id", false, "int")]),
                Some(&residual),
                &Row::open(Fields::new(), caller)
            )
            .is_err()
        );
    }

    #[test]
    fn shared_residuals_are_not_rebound_independently_per_parameter() {
        let residual = tail("callee:R", &["id", "flag"]);
        let mut solver = Solver::new("call", [residual.identity.clone()]);
        entail(
            &mut solver,
            &fields(&[("id", false, "int")]),
            Some(&residual),
            &Row::closed(fields(&[("id", false, "int"), ("tag", false, "str")])),
        )
        .unwrap();
        assert!(
            entail(
                &mut solver,
                &fields(&[("flag", false, "bool")]),
                Some(&residual),
                &Row::closed(fields(&[("flag", false, "bool"), ("tag", false, "int")]))
            )
            .is_err()
        );
    }

    #[test]
    fn slot_mode_and_unproved_rigid_lacks_are_not_erased() {
        let residual = tail("callee:R", &["id", "flag"]);
        let mut solver = Solver::new("call", [residual.identity.clone()]);
        assert!(
            entail(
                &mut solver,
                &fields(&[("id", false, "int")]),
                Some(&residual),
                &Row::closed(fields(&[("id", true, "int")]))
            )
            .is_err()
        );
        let caller = tail("caller:S", &["id"]);
        solver
            .declare_rigid(caller.identity.clone(), caller.lacks.clone())
            .unwrap();
        assert!(
            entail(
                &mut solver,
                &fields(&[("id", false, "int")]),
                Some(&residual),
                &Row::open(fields(&[("id", false, "int")]), caller)
            )
            .is_err()
        );
    }
}
