//! Language events and interpreter resource usage are independent limits.
use super::{Failure, Result};
use std::num::NonZeroU64;

pub const DEFAULT_STATIC_BUDGET: NonZeroU64 = NonZeroU64::new(100_000).unwrap();
const WORK_ALLOWANCE: u64 = 10_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Event {
    FunctionEntry,
    TypeFunctionEntry,
    CallbackEntry,
    LoopIteration,
}

pub(super) struct Budget {
    configured: NonZeroU64,
    remaining: Option<u64>,
    work_remaining: std::cell::Cell<u64>,
}

impl Budget {
    pub(super) fn with_work(units: u64) -> Self {
        Self {
            work_remaining: std::cell::Cell::new(units),
            ..Self::default()
        }
    }

    pub(super) fn work_remaining(&self) -> u64 {
        self.work_remaining.get()
    }

    /// A caller can narrow an already opened root's implementation allowance.
    /// Neither this restriction nor a nested root replenishes prior work.
    pub(super) fn restrict_work(&self, units: u64) {
        self.work_remaining
            .set(self.work_remaining.get().min(units));
    }

    pub fn new(configured: NonZeroU64) -> Self {
        Self {
            configured,
            remaining: None,
            work_remaining: std::cell::Cell::new(WORK_ALLOWANCE),
        }
    }

    /// Nested evaluation inherits the existing root; only its owner closes it.
    pub fn enter_root(&mut self) -> bool {
        if self.remaining.is_some() {
            return false;
        }
        self.remaining = Some(self.configured.get());
        self.work_remaining.set(WORK_ALLOWANCE);
        true
    }

    pub fn leave_root(&mut self, owner: bool) {
        if owner {
            self.remaining = None;
        }
    }

    pub fn event(&mut self, event: Event) -> Result<()> {
        let remaining = self
            .remaining
            .as_mut()
            .ok_or_else(|| Failure::Unsupported("static event has no evaluation root".into()))?;
        *remaining = remaining.checked_sub(1).ok_or_else(|| {
            Failure::Diagnostic(
                "E0811",
                format!("static evaluation budget exhausted before {event:?}"),
            )
        })?;
        Ok(())
    }

    pub fn work(&self, units: u64) -> Result<()> {
        let remaining = self
            .work_remaining
            .get()
            .checked_sub(units)
            .ok_or_else(|| {
                Failure::Unsupported("static interpreter work allowance exhausted".into())
            })?;
        self.work_remaining.set(remaining);
        Ok(())
    }
}

impl Default for Budget {
    fn default() -> Self {
        Self::new(DEFAULT_STATIC_BUDGET)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_roots_never_refill_the_language_budget() {
        let mut budget = Budget::new(NonZeroU64::new(1).unwrap());
        let outer = budget.enter_root();
        assert!(outer);
        assert!(budget.event(Event::FunctionEntry).is_ok());
        let nested = budget.enter_root();
        assert!(!nested);
        assert!(matches!(
            budget.event(Event::CallbackEntry),
            Err(Failure::Diagnostic("E0811", _))
        ));
        budget.leave_root(nested);
        assert!(budget.event(Event::LoopIteration).is_err());
        budget.leave_root(outer);
        assert!(budget.enter_root());
        assert!(budget.event(Event::TypeFunctionEntry).is_ok());
    }

    #[test]
    fn work_neither_spends_nor_refills_language_events() {
        let mut budget = Budget::new(NonZeroU64::new(1).unwrap());
        budget.enter_root();
        assert!(budget.work(WORK_ALLOWANCE).is_ok());
        assert!(budget.event(Event::FunctionEntry).is_ok());
        assert!(matches!(budget.work(1), Err(Failure::Unsupported(_))));
        assert!(matches!(
            budget.event(Event::CallbackEntry),
            Err(Failure::Diagnostic("E0811", _))
        ));
    }

    #[test]
    fn nested_roots_and_larger_restrictions_never_refill_outer_work() {
        let mut budget = Budget::default();
        let outer = budget.enter_root();
        budget.restrict_work(7);
        assert!(budget.work(5).is_ok());
        let nested = budget.enter_root();
        assert!(!nested);
        budget.restrict_work(100);
        assert_eq!(budget.work_remaining(), 2);
        assert!(matches!(budget.work(3), Err(Failure::Unsupported(_))));
        budget.leave_root(nested);
        assert_eq!(budget.work_remaining(), 2);
        assert!(budget.work(2).is_ok());
        assert!(matches!(budget.work(1), Err(Failure::Unsupported(_))));
        budget.leave_root(outer);
    }
}
