//! Temporary recursion admission shared by numeric and original Source queries.
//! Entries live only while a query is running; they certify no semantic fact.
use super::source_types::SourceTypesError;
use ril_compiler_core::ids::EvaluationOccurrenceId;
use std::{cell::RefCell, collections::BTreeSet, rc::Rc};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum QueryKind {
    Source,
    Numeric,
}

#[derive(Default)]
pub(crate) struct SourceQuery {
    active: RefCell<BTreeSet<(QueryKind, EvaluationOccurrenceId)>>,
}

pub(crate) struct QueryScope {
    query: Rc<SourceQuery>,
    key: (QueryKind, EvaluationOccurrenceId),
}

fn charge(work: &mut usize, amount: usize) -> Result<(), SourceTypesError> {
    match work.checked_sub(amount) {
        Some(remaining) => {
            *work = remaining;
            Ok(())
        }
        None => {
            *work = 0;
            Err(SourceTypesError::BudgetExceeded)
        }
    }
}

impl SourceQuery {
    pub(crate) fn enter(
        self: &Rc<Self>,
        kind: QueryKind,
        observation: EvaluationOccurrenceId,
        work: &mut usize,
    ) -> Result<QueryScope, SourceTypesError> {
        charge(work, 3)?;
        let mut active = self
            .active
            .try_borrow_mut()
            .map_err(|_| SourceTypesError::Unresolved)?;
        // The scope's eventual removal is paid here as well, so cleanup can
        // release its active key even after the caller exhausts its work.
        charge(
            work,
            2 * (active.len().checked_ilog2().unwrap_or(0) as usize + 1),
        )?;
        if active.len() >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let key = (kind, observation);
        if !active.insert(key) {
            return Err(SourceTypesError::CyclicSubstitution);
        }
        Ok(QueryScope {
            query: self.clone(),
            key,
        })
    }
}

impl Drop for QueryScope {
    fn drop(&mut self) {
        self.query.active.borrow_mut().remove(&self.key);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_numeric_recursion_keeps_actual_observations_and_releases_scopes() {
        let query = Rc::new(SourceQuery::default());
        let observation = EvaluationOccurrenceId(7);
        let mut work = 4096;
        let source = query
            .enter(QueryKind::Source, observation, &mut work)
            .unwrap();
        let numeric = query
            .enter(QueryKind::Numeric, observation, &mut work)
            .unwrap();
        assert_eq!(
            query.enter(QueryKind::Source, observation, &mut work).err(),
            Some(SourceTypesError::CyclicSubstitution)
        );
        assert_eq!(query.active.borrow().len(), 2);
        drop(numeric);
        assert_eq!(query.active.borrow().len(), 1);
        drop(source);
        assert!(query.active.borrow().is_empty());
        query
            .enter(QueryKind::Source, observation, &mut work)
            .unwrap();
        assert!(query.active.borrow().is_empty());
    }

    #[test]
    fn query_depth_is_finite_and_failed_entry_does_not_erase_outer_scopes() {
        let query = Rc::new(SourceQuery::default());
        let mut work = 100_000;
        let scopes: Vec<_> = (0..64)
            .map(|id| {
                query
                    .enter(QueryKind::Source, EvaluationOccurrenceId(id), &mut work)
                    .unwrap()
            })
            .collect();
        assert_eq!(
            query
                .enter(QueryKind::Numeric, EvaluationOccurrenceId(65), &mut work)
                .err(),
            Some(SourceTypesError::BudgetExceeded)
        );
        assert_eq!(query.active.borrow().len(), 64);
        drop(scopes);
        assert!(query.active.borrow().is_empty());
    }

    #[test]
    fn failed_query_admission_never_resets_work_or_publishes_an_active_key() {
        let query = Rc::new(SourceQuery::default());
        for units in 0..5 {
            let mut work = units;
            assert_eq!(
                query
                    .enter(QueryKind::Source, EvaluationOccurrenceId(1), &mut work)
                    .err(),
                Some(SourceTypesError::BudgetExceeded)
            );
            assert_eq!(work, 0);
            assert!(query.active.borrow().is_empty());
        }
        let mut exact = 5;
        let scope = query
            .enter(QueryKind::Source, EvaluationOccurrenceId(1), &mut exact)
            .unwrap();
        assert_eq!(exact, 0);
        drop(scope);
        assert!(query.active.borrow().is_empty());
    }
}
