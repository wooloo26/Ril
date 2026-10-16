//! Private heap sift state. This module never invokes a comparator: generated
//! Core owns each callback edge and submits its result before the next request.
use super::*;

#[derive(Debug, Clone, PartialEq)]
enum Phase {
    Push(usize),
    Pop(usize),
    Select {
        index: usize,
        left: usize,
        right: usize,
    },
    Check {
        index: usize,
        child: usize,
    },
    Done,
}
#[derive(Debug, Clone, PartialEq)]
pub struct HeapMutation {
    receiver: Handle,
    original: PriorityHeap,
    state: PriorityHeap,
    phase: Phase,
    pending: Option<(usize, usize)>,
    // None means push's unit result; Some(None) means popping an empty heap.
    output: Option<Option<Handle>>,
    committed: bool,
}
impl HeapMutation {
    pub(crate) fn references(&self) -> Vec<Handle> {
        std::iter::once(self.receiver)
            .chain(self.original.references())
            .chain(self.state.references())
            .chain(self.output.flatten())
            .collect()
    }
    fn next(&mut self) -> Result<Option<(Handle, Handle, Handle)>> {
        if self.committed || self.pending.is_some() {
            return Err(RuntimeError::internal(
                "heap comparison request was replayed",
            ));
        }
        if let Phase::Pop(index) = self.phase {
            let left = index.checked_mul(2).and_then(|index| index.checked_add(1));
            self.phase = match left.filter(|&left| left < self.state.entries.len()) {
                Some(left) if left + 1 < self.state.entries.len() => Phase::Select {
                    index,
                    left,
                    right: left + 1,
                },
                Some(child) => Phase::Check { index, child },
                None => Phase::Done,
            };
        }
        let pair = match self.phase {
            Phase::Push(0) => {
                self.phase = Phase::Done;
                None
            }
            Phase::Push(index) => Some((index, (index - 1) / 2)),
            Phase::Select { left, right, .. } => Some((right, left)),
            Phase::Check { index, child } => Some((child, index)),
            Phase::Done => None,
            Phase::Pop(_) => unreachable!("pop state normalized"),
        };
        self.pending = pair;
        Ok(pair.map(|(left, right)| {
            (
                self.state.compare,
                self.state.entries[left].1,
                self.state.entries[right].1,
            )
        }))
    }
    fn accept(&mut self, order: Ordering) -> Result<()> {
        if self.committed {
            return Err(RuntimeError::internal("heap transaction already committed"));
        }
        let (left, right) = self
            .pending
            .take()
            .ok_or_else(|| RuntimeError::internal("heap comparison reply has no request"))?;
        let order =
            order.then_with(|| self.state.entries[left].0.cmp(&self.state.entries[right].0));
        match self.phase {
            Phase::Push(index) => {
                if order == Ordering::Less {
                    self.state.entries.swap(left, right);
                    self.phase = Phase::Push((index - 1) / 2);
                } else {
                    self.phase = Phase::Done;
                }
            }
            Phase::Select { index, left, right } => {
                self.phase = Phase::Check {
                    index,
                    child: if order == Ordering::Less { right } else { left },
                };
            }
            Phase::Check { index, child } => {
                if order == Ordering::Less {
                    self.state.entries.swap(index, child);
                    self.phase = Phase::Pop(child);
                } else {
                    self.phase = Phase::Done;
                }
            }
            Phase::Done | Phase::Pop(_) => {
                return Err(RuntimeError::internal(
                    "heap comparison reply has an invalid phase",
                ));
            }
        }
        Ok(())
    }
}

impl Runtime {
    pub(crate) fn heap_transaction_builtin(
        &mut self,
        name: &str,
        args: &[Handle],
    ) -> Result<Handle> {
        let arity = if matches!(name, "\0ril.heap.begin_push" | "\0ril.heap.accept") {
            2
        } else {
            1
        };
        if args.len() != arity {
            return Err(RuntimeError::internal(
                "private heap operation has invalid arity",
            ));
        }
        match name {
            "\0ril.heap.new" => {
                let compare = self.field(args[0], "compare")?;
                let environment = match self.heap.get(compare)? {
                    Object::Builtin(_) => None,
                    Object::Closure { environment, .. }
                    | Object::CpsClosure { environment, .. }
                    | Object::BudgetClosure { environment, .. } => Some(*environment),
                    _ => {
                        return Err(RuntimeError::internal(
                            "heap comparator has no environment-free callable witness",
                        ));
                    }
                };
                if let Some(environment) = environment
                    && !matches!(self.heap.get(environment)?, Object::Unit)
                    && !matches!(self.heap.get(environment)?, Object::Record(fields) if fields.is_empty())
                {
                    return Err(RuntimeError::internal(
                        "heap comparator retains a nonempty environment",
                    ));
                }
                self.allocate(Object::PriorityHeap(PriorityHeap {
                    compare,
                    entries: vec![],
                    next: 0,
                }))
            }
            "\0ril.heap.begin_push" | "\0ril.heap.begin_pop" => {
                let Object::PriorityHeap(original) = self.heap.get(args[0])? else {
                    return Err(RuntimeError::internal("expected Heap"));
                };
                let mut state = original.clone();
                let (phase, output) = if name.ends_with("begin_push") {
                    let entry = (state.next, args[1]);
                    state.next = state
                        .next
                        .checked_add(1)
                        .ok_or_else(|| RuntimeError::panic("heap insertion sequence exhausted"))?;
                    state.entries.push(entry);
                    (Phase::Push(state.entries.len() - 1), None)
                } else if state.entries.is_empty() {
                    (Phase::Done, Some(None))
                } else {
                    let first = state.entries.swap_remove(0);
                    (Phase::Pop(0), Some(Some(first.1)))
                };
                let transaction = HeapMutation {
                    receiver: args[0],
                    original: original.clone(),
                    state,
                    phase,
                    pending: None,
                    output,
                    committed: false,
                };
                self.allocate(Object::HeapMutation(Box::new(transaction)))
            }
            "\0ril.heap.next" => {
                let Object::HeapMutation(transaction) = self.heap.get_mut(args[0])? else {
                    return Err(RuntimeError::internal("expected private heap transaction"));
                };
                match transaction.next()? {
                    Some((compare, left, right)) => {
                        let payload = self.allocate(Object::Tuple(vec![compare, left, right]))?;
                        self.variant("Some", vec![payload])
                    }
                    None => self.variant("None", vec![]),
                }
            }
            "\0ril.heap.accept" => {
                let Object::Variant { tag, fields } = self.heap.get(args[1])? else {
                    return Err(RuntimeError::internal("comparator did not return Ordering"));
                };
                if !fields.is_empty() {
                    return Err(RuntimeError::internal("comparator returned a payload"));
                }
                let order = match tag.as_str() {
                    "Order::Ordering::Less" => Ordering::Less,
                    "Order::Ordering::Equal" => Ordering::Equal,
                    "Order::Ordering::Greater" => Ordering::Greater,
                    _ => {
                        return Err(RuntimeError::internal(
                            "comparator returned another constructor",
                        ));
                    }
                };
                let Object::HeapMutation(transaction) = self.heap.get_mut(args[0])? else {
                    return Err(RuntimeError::internal("expected private heap transaction"));
                };
                transaction.accept(order)?;
                self.unit()
            }
            "\0ril.heap.commit" => {
                let Object::HeapMutation(transaction) = self.heap.get(args[0])? else {
                    return Err(RuntimeError::internal("expected private heap transaction"));
                };
                if transaction.committed
                    || transaction.pending.is_some()
                    || transaction.phase != Phase::Done
                {
                    return Err(RuntimeError::internal(
                        "heap transaction is not ready to commit",
                    ));
                }
                let Object::PriorityHeap(current) = self.heap.get(transaction.receiver)? else {
                    return Err(RuntimeError::internal("heap transaction lost its receiver"));
                };
                // Static comparison contracts exclude mutation of the receiver.
                // Defend against stale/reentrant commits instead of overwriting it.
                if current != &transaction.original {
                    return Err(RuntimeError::internal("heap changed during comparison"));
                }
                let (receiver, state, output) = (
                    transaction.receiver,
                    transaction.state.clone(),
                    transaction.output,
                );
                let Object::HeapMutation(transaction) = self.heap.get_mut(args[0])? else {
                    unreachable!()
                };
                transaction.committed = true;
                *self.heap.get_mut(receiver)? = Object::PriorityHeap(state);
                match output {
                    None => self.unit(),
                    Some(value) => self.variant(
                        if value.is_some() { "Some" } else { "None" },
                        value.into_iter().collect(),
                    ),
                }
            }
            _ => Err(RuntimeError::internal("unknown private heap operation")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn heap(runtime: &mut Runtime) -> Handle {
        let compare = runtime
            .allocate(Object::Builtin("Order::compare_int".into()))
            .unwrap();
        let ops = runtime
            .allocate(Object::Record([("compare".into(), compare)].into()))
            .unwrap();
        let heap = runtime
            .heap_transaction_builtin("\0ril.heap.new", &[ops])
            .unwrap();
        runtime.root(0, heap).unwrap();
        heap
    }
    fn complete(
        runtime: &mut Runtime,
        transaction: Handle,
        trace: &mut Vec<(i128, i128)>,
    ) -> Handle {
        runtime.root(1, transaction).unwrap();
        let unit = runtime.unit().unwrap();
        runtime.root(0, unit).unwrap();
        runtime.statement_end();
        runtime.collect().unwrap();
        loop {
            let request = runtime
                .heap_transaction_builtin("\0ril.heap.next", &[transaction])
                .unwrap();
            let Object::Variant { tag, fields } = runtime.heap.get(request).unwrap() else {
                panic!("request")
            };
            if tag == "None" {
                break;
            }
            let fields = runtime.sequence(fields[0]).unwrap();
            trace.push((
                runtime.as_integer(fields[1]).unwrap(),
                runtime.as_integer(fields[2]).unwrap(),
            ));
            runtime.statement_end();
            runtime.collect().unwrap();
            let order = runtime
                .order_builtin("Order::compare_int", &fields[1..])
                .unwrap();
            runtime
                .heap_transaction_builtin("\0ril.heap.accept", &[transaction, order])
                .unwrap();
        }
        runtime.statement_end();
        runtime.collect().unwrap();
        runtime
            .heap_transaction_builtin("\0ril.heap.commit", &[transaction])
            .unwrap()
    }
    #[test]
    fn comparisons_keep_existing_sift_order_and_gc_roots() {
        let mut runtime = Runtime::default();
        let heap = heap(&mut runtime);
        let mut trace = vec![];
        for value in [5, 3, 4, 1, 2] {
            let value = runtime.int(value).unwrap();
            let transaction = runtime
                .heap_transaction_builtin("\0ril.heap.begin_push", &[heap, value])
                .unwrap();
            complete(&mut runtime, transaction, &mut trace);
        }
        assert_eq!(trace, vec![(3, 5), (4, 3), (1, 5), (1, 3), (2, 3), (2, 1)]);
        trace.clear();
        for expected in 1..=5 {
            let transaction = runtime
                .heap_transaction_builtin("\0ril.heap.begin_pop", &[heap])
                .unwrap();
            let value = complete(&mut runtime, transaction, &mut trace);
            let Object::Variant { tag, fields } = runtime.heap.get(value).unwrap() else {
                panic!("result")
            };
            assert_eq!(tag, "Some");
            assert_eq!(runtime.as_integer(fields[0]).unwrap(), expected);
        }
        assert_eq!(trace, vec![(4, 2), (2, 3), (5, 3), (4, 3), (3, 5), (5, 4)]);
        let transaction = runtime
            .heap_transaction_builtin("\0ril.heap.begin_pop", &[heap])
            .unwrap();
        let value = complete(&mut runtime, transaction, &mut trace);
        assert!(
            matches!(runtime.heap.get(value),Ok(Object::Variant{tag,fields})if tag=="None"&&fields.is_empty())
        );
    }
    #[test]
    fn uncommitted_comparison_cannot_mutate_heap_or_overwrite_reentrant_changes() {
        let mut runtime = Runtime::default();
        let heap = heap(&mut runtime);
        let first = runtime.int(1).unwrap();
        let stale = runtime
            .heap_transaction_builtin("\0ril.heap.begin_push", &[heap, first])
            .unwrap();
        runtime.root(2, stale).unwrap();
        assert!(runtime.copy(stale).is_err());
        let schema = ril_runtime_api::foreign::Signature {
            arena: vec![ril_runtime_api::foreign::TypeNode::Unit],
            parameters: vec![0],
            result: 0,
            callbacks: vec![],
        };
        assert!(crate::foreign_codec::encode(&runtime, &schema, &[(stale, 0)]).is_err());
        assert!(
            matches!(runtime.heap.get(heap),Ok(Object::PriorityHeap(heap))if heap.entries.is_empty()&&heap.next==0)
        );
        let second = runtime.int(2).unwrap();
        let current = runtime
            .heap_transaction_builtin("\0ril.heap.begin_push", &[heap, second])
            .unwrap();
        complete(&mut runtime, current, &mut vec![]);
        runtime
            .heap_transaction_builtin("\0ril.heap.next", &[stale])
            .unwrap();
        assert_eq!(
            runtime
                .heap_transaction_builtin("\0ril.heap.commit", &[stale])
                .unwrap_err()
                .message,
            "heap changed during comparison"
        );
        assert!(
            matches!(runtime.heap.get(heap),Ok(Object::PriorityHeap(heap))if heap.entries==vec![(0,second)]&&heap.next==1)
        );
    }
    #[test]
    fn abandoned_pop_and_empty_reentrant_roundtrip_preserve_snapshot_checks() {
        let mut runtime = Runtime::default();
        let heap = heap(&mut runtime);
        for value in [1, 2, 3] {
            let value = runtime.int(value).unwrap();
            let transaction = runtime
                .heap_transaction_builtin("\0ril.heap.begin_push", &[heap, value])
                .unwrap();
            complete(&mut runtime, transaction, &mut vec![]);
        }
        let original = runtime.heap.get(heap).unwrap().clone();
        let abandoned = runtime
            .heap_transaction_builtin("\0ril.heap.begin_pop", &[heap])
            .unwrap();
        let request = runtime
            .heap_transaction_builtin("\0ril.heap.next", &[abandoned])
            .unwrap();
        assert!(
            matches!(runtime.heap.get(request), Ok(Object::Variant { tag, .. }) if tag == "Some")
        );
        let order = runtime.variant("Order::Ordering::Less", vec![]).unwrap();
        runtime
            .heap_transaction_builtin("\0ril.heap.accept", &[abandoned, order])
            .unwrap();
        assert_eq!(runtime.heap.get(heap).unwrap(), &original);
        assert!(
            runtime
                .heap_transaction_builtin("\0ril.heap.accept", &[abandoned, order])
                .is_err()
        );

        // A nested push followed by pop can restore the same visible entries,
        // but still consumes a stable sequence number and invalidates a snapshot.
        let empty = self::heap(&mut runtime);
        let value = runtime.int(7).unwrap();
        let stale = runtime
            .heap_transaction_builtin("\0ril.heap.begin_push", &[empty, value])
            .unwrap();
        runtime.root(2, stale).unwrap();
        let nested = runtime
            .heap_transaction_builtin("\0ril.heap.begin_push", &[empty, value])
            .unwrap();
        complete(&mut runtime, nested, &mut vec![]);
        let nested = runtime
            .heap_transaction_builtin("\0ril.heap.begin_pop", &[empty])
            .unwrap();
        complete(&mut runtime, nested, &mut vec![]);
        runtime
            .heap_transaction_builtin("\0ril.heap.next", &[stale])
            .unwrap();
        assert_eq!(
            runtime
                .heap_transaction_builtin("\0ril.heap.commit", &[stale])
                .unwrap_err()
                .message,
            "heap changed during comparison"
        );
        assert!(
            matches!(runtime.heap.get(empty), Ok(Object::PriorityHeap(heap)) if heap.entries.is_empty() && heap.next == 1)
        );
    }
    #[test]
    fn cps_label_alone_does_not_certify_an_environment_free_comparator() {
        let mut runtime = Runtime::default();
        let value = runtime.int(7).unwrap();
        let environment = runtime
            .allocate(Object::Record([("captured".into(), value)].into()))
            .unwrap();
        let callback = runtime
            .allocate(Object::CpsClosure {
                function: 0,
                environment,
            })
            .unwrap();
        let ops = runtime
            .allocate(Object::Record([("compare".into(), callback)].into()))
            .unwrap();
        assert!(
            runtime
                .heap_transaction_builtin("\0ril.heap.new", &[ops])
                .is_err()
        );
    }
}
