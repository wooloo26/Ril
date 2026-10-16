//! Stable heap entries and primitive total-order comparators. Generated Core
//! invokes heap callbacks; private sift state only accepts their order results.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use std::cmp::Ordering;
#[path = "heap_transaction.rs"]
mod transaction;
pub use transaction::HeapMutation;
#[derive(Debug, Clone, PartialEq)]
pub struct PriorityHeap {
    pub(crate) compare: Handle,
    pub(crate) entries: Vec<(u128, Handle)>,
    pub(crate) next: u128,
}
impl PriorityHeap {
    pub(crate) fn references(&self) -> Vec<Handle> {
        std::iter::once(self.compare)
            .chain(self.entries.iter().map(|(_, value)| *value))
            .collect()
    }
    pub(crate) fn map_references(&self, mut map: impl FnMut(Handle) -> Handle) -> Self {
        Self {
            compare: map(self.compare),
            entries: self
                .entries
                .iter()
                .map(|(index, value)| (*index, map(*value)))
                .collect(),
            next: self.next,
        }
    }
}
impl Runtime {
    pub(crate) fn order_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing ordering argument"))
        };
        let order = match name {
            "Order::compare_int" => self.as_integer(arg(0)?)?.cmp(&self.as_integer(arg(1)?)?),
            "Order::compare_str" => self.as_string(arg(0)?)?.cmp(self.as_string(arg(1)?)?),
            "Order::compare_bytes" => self.as_bytes(arg(0)?)?.cmp(self.as_bytes(arg(1)?)?),
            "Order::total_f64" => {
                let (Object::Float { value: a, bits: 64 }, Object::Float { value: b, bits: 64 }) =
                    (self.heap.get(arg(0)?)?, self.heap.get(arg(1)?)?)
                else {
                    return Err(RuntimeError::internal("expected f64 comparison operands"));
                };
                match (a.is_nan(), b.is_nan()) {
                    (true, true) => Ordering::Equal,
                    (true, false) => Ordering::Greater,
                    (false, true) => Ordering::Less,
                    _ => a.total_cmp(b),
                }
            }
            _ => {
                return Err(RuntimeError::internal(
                    "ordering callback requires a native invocation bridge",
                ));
            }
        };
        self.variant(
            match order {
                Ordering::Less => "Order::Ordering::Less",
                Ordering::Equal => "Order::Ordering::Equal",
                Ordering::Greater => "Order::Ordering::Greater",
            },
            vec![],
        )
    }
}
