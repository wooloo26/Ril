//! Dynamic allowance ownership. Charge decisions describe abstract language
//! events; continuation creation, dispatch and GC never consume allowance.
use crate::{
    heap::Handle,
    value::{Result, RuntimeError},
};
use ril_runtime_api::abi::BudgetEvent;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BudgetId(u64);
#[derive(Debug)]
struct Frame {
    id: BudgetId,
    remaining: u64,
    boundary: Handle,
    paused: usize,
}
#[derive(Debug, Default)]
pub struct Allowances {
    frames: Vec<Frame>,
    next: u64,
}
#[derive(Debug)]
pub struct CleanupMask {
    owners: Vec<BudgetId>,
}
#[derive(Debug, PartialEq, Eq)]
pub struct Exhaustion {
    pub owner: BudgetId,
    pub boundary: Handle,
    pub abandoned: Vec<(BudgetId, Handle)>,
}
#[derive(Debug, PartialEq, Eq)]
pub enum Decision {
    Execute,
    Exhaust(Exhaustion),
}
impl Allowances {
    /// Establish only after charging entry to the already-active outer stack.
    /// A zero allowance belongs to this new boundary; the caller immediately
    /// abandons it without invoking the action or its defaults.
    pub fn begin(&mut self, limit: u64, boundary: Handle) -> Result<BudgetId> {
        self.next = self
            .next
            .checked_add(1)
            .ok_or_else(|| RuntimeError::internal("budget identity exhausted"))?;
        let id = BudgetId(self.next);
        self.frames.push(Frame {
            id,
            remaining: limit,
            boundary,
            paused: 0,
        });
        Ok(id)
    }
    pub fn charge(&mut self, _event: BudgetEvent) -> Decision {
        if let Some(index) = self
            .frames
            .iter()
            .position(|frame| frame.paused == 0 && frame.remaining == 0)
        {
            return Decision::Exhaust(self.take(index));
        }
        for frame in &mut self.frames {
            if frame.paused == 0 {
                frame.remaining -= 1;
            }
        }
        Decision::Execute
    }
    fn take(&mut self, index: usize) -> Exhaustion {
        let removed: Vec<_> = self.frames.drain(index..).collect();
        let owner = removed[0].id;
        let boundary = removed[0].boundary;
        Exhaustion {
            owner,
            boundary,
            abandoned: removed
                .into_iter()
                .map(|frame| (frame.id, frame.boundary))
                .collect(),
        }
    }
    pub fn exhaust_zero(&mut self, id: BudgetId) -> Result<Exhaustion> {
        let index = self
            .frames
            .iter()
            .position(|frame| frame.id == id)
            .ok_or_else(|| RuntimeError::internal("budget boundary is no longer active"))?;
        if index + 1 != self.frames.len()
            || self.frames[index].remaining != 0
            || self.frames[index].paused != 0
        {
            return Err(RuntimeError::internal(
                "invalid immediate budget exhaustion",
            ));
        }
        Ok(self.take(index))
    }
    pub fn finish(&mut self, id: BudgetId) -> Result<()> {
        if self.frames.last().map(|frame| frame.id) != Some(id) {
            return Err(RuntimeError::internal(
                "budget completion is not in dynamic stack order",
            ));
        }
        self.frames.pop();
        Ok(())
    }
    pub fn suspend_for_cleanup(&mut self) -> CleanupMask {
        let owners = self
            .frames
            .iter_mut()
            .map(|frame| {
                frame.paused += 1;
                frame.id
            })
            .collect();
        CleanupMask { owners }
    }
    pub fn restore_after_cleanup(&mut self, mask: CleanupMask) {
        for frame in &mut self.frames {
            if mask.owners.contains(&frame.id) {
                frame.paused -= 1;
            }
        }
    }
    pub fn roots(&self) -> impl Iterator<Item = Handle> + '_ {
        self.frames
            .iter()
            .map(|frame| frame.boundary)
            .filter(|handle| *handle != Handle::INVALID)
    }
    pub fn is_active(&self) -> bool {
        self.frames.iter().any(|frame| frame.paused == 0)
    }
    pub(crate) fn depth(&self) -> usize {
        self.frames.len()
    }
    pub(crate) fn abandon_since(&mut self, depth: usize) -> Result<Vec<Handle>> {
        if depth > self.frames.len() {
            return Err(RuntimeError::internal(
                "continuation outlived its allowance owner",
            ));
        }
        Ok(self
            .frames
            .drain(depth..)
            .map(|frame| frame.boundary)
            .collect())
    }
}

#[cfg(test)]
#[path = "budget_tests.rs"]
mod tests;
