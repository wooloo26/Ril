//! Ordinary opaque deque storage. Snapshots copy the shell and retain elements.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
impl Runtime {
    pub(crate) fn deque_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing deque argument"))
        };
        if name == "Deque::new" {
            return self.allocate(Object::Deque(Default::default()));
        }
        let receiver = arg(0)?;
        if name == "Deque::values" {
            let Object::Deque(values) = self.heap.get(receiver)? else {
                return Err(RuntimeError::internal("expected Deque"));
            };
            return self.allocate(Object::Array(values.iter().copied().collect()));
        }
        let Object::Deque(values) = self.heap.get_mut(receiver)? else {
            return Err(RuntimeError::internal("expected Deque"));
        };
        match name {
            "Deque::len" => {
                let length = values.len();
                self.int(length as i128)
            }
            "Deque::push_front" => {
                values.push_front(arg(1)?);
                self.unit()
            }
            "Deque::push_back" => {
                values.push_back(arg(1)?);
                self.unit()
            }
            "Deque::pop_front" | "Deque::pop_back" => {
                let value = if name == "Deque::pop_front" {
                    values.pop_front()
                } else {
                    values.pop_back()
                };
                self.variant(
                    if value.is_some() { "Some" } else { "None" },
                    value.into_iter().collect(),
                )
            }
            _ => Err(RuntimeError::internal("unknown deque operation")),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn deque_snapshots_keep_order_and_clone_separates_nested_storage() {
        let mut runtime = Runtime::default();
        let deque = runtime.deque_builtin("Deque::new", &[]).unwrap();
        let child = runtime.allocate(Object::Array(vec![])).unwrap();
        runtime
            .deque_builtin("Deque::push_front", &[deque, child])
            .unwrap();
        runtime
            .deque_builtin("Deque::push_back", &[deque, child])
            .unwrap();
        let snapshot = runtime.deque_builtin("Deque::values", &[deque]).unwrap();
        let copy = runtime.copy(deque).unwrap();
        runtime.deque_builtin("Deque::pop_back", &[deque]).unwrap();
        assert_eq!(runtime.sequence(snapshot).unwrap(), vec![child, child]);
        let copied = runtime.deque_builtin("Deque::values", &[copy]).unwrap();
        let values = runtime.sequence(copied).unwrap();
        assert_eq!(values[0], values[1]);
        assert_ne!(values[0], child);
    }
}
