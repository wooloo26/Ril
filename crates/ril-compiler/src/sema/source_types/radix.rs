//! Persistent storage for the one Source arena. A builder owns the only writer;
//! immutable snapshots share branches and never acquire mutable node payloads.
use super::{SourceNode, SourceTypesError, WorkLimit};
use std::sync::Arc;

const WIDTH: usize = 16;
const BITS: usize = 4;
pub(super) const LIMIT: usize = 65_536;
const MAX_HEIGHT: u8 = 4;
// Pay for pointer initialization/copy and eventual release before allocation.
const BRANCH_WORK: usize = 2 * WIDTH + 1;

#[derive(Debug, Clone)]
enum Branch {
    Leaf([Option<Arc<SourceNode>>; WIDTH]),
    Inner([Option<Arc<Branch>>; WIDTH]),
}

impl Branch {
    fn empty(height: u8) -> Self {
        if height == 1 {
            Self::Leaf(std::array::from_fn(|_| None))
        } else {
            Self::Inner(std::array::from_fn(|_| None))
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct Nodes {
    root: Option<Arc<Branch>>,
    height: u8,
    len: usize,
}

pub(super) struct WritePlan {
    height: u8,
    branches: usize,
}

impl WritePlan {
    pub(super) fn retained_bytes(&self) -> usize {
        self.branches * (std::mem::size_of::<Branch>() + 2 * std::mem::size_of::<usize>())
    }
}

fn digit(index: usize, height: u8) -> usize {
    (index >> (BITS * (height as usize - 1))) & (WIDTH - 1)
}

impl Nodes {
    pub(super) fn len(&self) -> usize {
        self.len
    }

    /// Reservation has no payload and allocates no tree path. Definitions may
    /// arrive out of order, including finite recursive forward/back references.
    pub(super) fn reserve(&mut self) -> Result<usize, SourceTypesError> {
        if self.len >= LIMIT {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let index = self.len;
        self.len += 1;
        Ok(index)
    }

    pub(super) fn cancel_reservation(&mut self, index: usize) {
        debug_assert_eq!(index + 1, self.len);
        debug_assert!(self.get(index).is_none());
        self.len -= 1;
    }

    /// At most four pointer steps under the unchanged arena node limit.
    pub(super) fn get(&self, index: usize) -> Option<&Arc<SourceNode>> {
        if index >= self.len || self.height == 0 {
            return None;
        }
        if index >= (1usize << (BITS * self.height as usize)) {
            return None;
        }
        let mut branch = self.root.as_deref()?;
        let mut height = self.height;
        loop {
            let offset = digit(index, height);
            match branch {
                Branch::Leaf(items) if height == 1 => return items[offset].as_ref(),
                Branch::Inner(items) if height > 1 => {
                    branch = items[offset].as_deref()?;
                    height -= 1;
                }
                _ => return None,
            }
        }
    }

    /// Admit the complete edit before touching any shared branch. If an
    /// ancestor is copied, its child becomes shared even if it was unique
    /// before that copy; the plan accounts for the entire affected path.
    pub(super) fn prepare_define(
        &self,
        index: usize,
        work: &mut WorkLimit,
    ) -> Result<WritePlan, SourceTypesError> {
        work.charge(1 + 2 * self.height as usize)?;
        if index >= self.len {
            return Err(SourceTypesError::MissingNode);
        }
        if self.get(index).is_some() {
            return Err(SourceTypesError::AlreadyDefined);
        }
        let mut required = 1;
        while index >= (1usize << (BITS * required as usize)) {
            required += 1;
        }
        if required > MAX_HEIGHT {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let height = required.max(self.height);
        let branches = if self.root.is_none() {
            height as usize
        } else if height > self.height {
            // New root wrappers retain the old tree under child zero. The
            // new highest nonzero digit needs a separate fresh suffix.
            (height - self.height) as usize + height as usize - 1
        } else {
            let mut current = self.root.as_ref();
            let mut level = height;
            let mut inherited = false;
            let mut copies = 0;
            loop {
                let Some(branch) = current else {
                    copies += level as usize;
                    break;
                };
                let shared = inherited || Arc::strong_count(branch) != 1;
                copies += usize::from(shared);
                if level == 1 {
                    break;
                }
                let Branch::Inner(items) = branch.as_ref() else {
                    return Err(SourceTypesError::MissingNode);
                };
                current = items[digit(index, level)].as_ref();
                inherited = shared;
                level -= 1;
            }
            copies
        };
        work.charge(branches * BRANCH_WORK + height as usize)?;
        Ok(WritePlan { height, branches })
    }

    /// Only the preflighted writer calls this. No fallible operation remains
    /// after mutation starts; payload nodes themselves are never cloned.
    pub(super) fn define(&mut self, index: usize, node: Arc<SourceNode>, plan: WritePlan) {
        if self.root.is_none() {
            self.root = Some(Arc::new(Branch::empty(plan.height)));
            self.height = plan.height;
        }
        while self.height < plan.height {
            let mut children = std::array::from_fn(|_| None);
            children[0] = self.root.take();
            self.root = Some(Arc::new(Branch::Inner(children)));
            self.height += 1;
        }
        Self::define_at(
            self.root.as_mut().expect("admitted radix root"),
            self.height,
            index,
            node,
        );
    }

    fn define_at(branch: &mut Arc<Branch>, height: u8, index: usize, node: Arc<SourceNode>) {
        let offset = digit(index, height);
        match Arc::make_mut(branch) {
            Branch::Leaf(items) => {
                debug_assert_eq!(height, 1);
                debug_assert!(items[offset].is_none());
                items[offset] = Some(node);
            }
            Branch::Inner(items) => {
                debug_assert!(height > 1);
                let child =
                    items[offset].get_or_insert_with(|| Arc::new(Branch::empty(height - 1)));
                Self::define_at(child, height - 1, index, node);
            }
        }
    }
}
