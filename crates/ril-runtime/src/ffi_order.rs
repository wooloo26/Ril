use super::*;
use std::cmp::Ordering;

fn compare(callback: Handle, left: Handle, right: Handle) -> Option<Ordering> {
    let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![left, right])));
    let result = invoke_callable(callback.0, args);
    if result == 0 {
        return None;
    }
    let order = guarded(|runtime| match runtime.heap.get(Handle(result))? {
        Object::Variant { tag, fields } if fields.is_empty() => Ok(Some(match tag.as_str() {
            "Order::Ordering::Less" => Ordering::Less,
            "Order::Ordering::Equal" => Ordering::Equal,
            "Order::Ordering::Greater" => Ordering::Greater,
            _ => {
                return Err(RuntimeError::internal(
                    "comparator returned another constructor",
                ));
            }
        })),
        _ => Err(RuntimeError::internal("comparator did not return Ordering")),
    });
    ril_rt_statement_end();
    order
}
fn entry_compare(
    callback: Handle,
    left: (u128, Handle),
    right: (u128, Handle),
) -> Option<Ordering> {
    compare(callback, left.1, right.1).map(|order| order.then_with(|| left.0.cmp(&right.0)))
}
pub(super) fn invoke(name: &str, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let args: Option<Vec<Handle>> =
        guarded(|runtime| runtime.sequence(Handle(arguments)).map(Some));
    let Some(args) = args else {
        return ril_rt_leave(0);
    };
    let result = if name.starts_with("Heap::") {
        heap(name, &args)
    } else {
        ordering(name, &args)
    };
    ril_rt_leave(result)
}
fn ordering(name: &str, args: &[Handle]) -> u64 {
    let minimum = if name == "Order::sorted" { 2 } else { 3 };
    if args.len() != minimum {
        return handle(|_| Err(RuntimeError::internal("invalid ordering argument count")));
    }
    let items: Option<Vec<Handle>> = guarded(|runtime| runtime.sequence(args[0]).map(Some));
    let Some(mut items) = items else {
        return 0;
    };
    let callback = handle(|runtime| runtime.field(args[minimum - 1], "compare"));
    if callback == 0 {
        return 0;
    }
    // The operation record remains rooted for the entire native callback loop.
    let callback = Handle(callback);
    if name == "Order::sorted" {
        let mut buffer = items.clone();
        let mut width = 1usize;
        while width < items.len() {
            let mut start = 0;
            while start < items.len() {
                let middle = start.saturating_add(width).min(items.len());
                let end = middle.saturating_add(width).min(items.len());
                let (mut left, mut right) = (start, middle);
                for destination in &mut buffer[start..end] {
                    let choose_left = if left == middle {
                        false
                    } else if right == end {
                        true
                    } else {
                        let Some(order) = compare(callback, items[left], items[right]) else {
                            return 0;
                        };
                        order != Ordering::Greater
                    };
                    *destination = if choose_left {
                        let value = items[left];
                        left += 1;
                        value
                    } else {
                        let value = items[right];
                        right += 1;
                        value
                    };
                }
                start = end;
            }
            std::mem::swap(&mut items, &mut buffer);
            width = width.saturating_mul(2);
        }
        handle(|runtime| runtime.allocate(Object::Array(items)))
    } else {
        let (mut low, mut high) = (0, items.len());
        while low < high {
            let middle = low + (high - low) / 2;
            let Some(order) = compare(callback, items[middle], args[1]) else {
                return 0;
            };
            if order == Ordering::Less {
                low = middle + 1;
            } else {
                high = middle;
            }
        }
        let found = if low < items.len() {
            let Some(order) = compare(callback, items[low], args[1]) else {
                return 0;
            };
            order == Ordering::Equal
        } else {
            false
        };
        handle(|runtime| {
            let index = runtime.int(low as i128)?;
            runtime.variant(if found { "Ok" } else { "Err" }, vec![index])
        })
    }
}
fn heap(name: &str, args: &[Handle]) -> u64 {
    if name == "Heap::new" {
        return handle(|runtime| {
            let record = *args
                .first()
                .ok_or_else(|| RuntimeError::internal("missing heap comparator"))?;
            let compare = runtime.field(record, "compare")?;
            let eligible = match runtime.heap.get(compare)? {
                Object::Builtin(_) => true,
                Object::Closure { environment, .. } => {
                    matches!(runtime.heap.get(*environment)?, Object::Unit)
                        || matches!(runtime.heap.get(*environment)?,Object::Record(fields)if fields.is_empty())
                }
                _ => false,
            };
            if !eligible {
                return Err(RuntimeError::internal(
                    "heap comparator must be environment-free and synchronous",
                ));
            }
            runtime.allocate(Object::PriorityHeap(crate::order::PriorityHeap {
                compare,
                entries: vec![],
                next: 0,
            }))
        });
    }
    let Some(&receiver) = args.first() else {
        return handle(|_| Err(RuntimeError::internal("missing heap receiver")));
    };
    let state: Option<crate::order::PriorityHeap> =
        guarded(|runtime| match runtime.heap.get(receiver)? {
            Object::PriorityHeap(heap) => Ok(Some(heap.clone())),
            _ => Err(RuntimeError::internal("expected Heap")),
        });
    let Some(mut state) = state else {
        return 0;
    };
    if name == "Heap::len" {
        return handle(|runtime| runtime.int(state.entries.len() as i128));
    }
    if name == "Heap::peek" || name == "Heap::pop" && state.entries.is_empty() {
        return handle(|runtime| {
            runtime.variant(
                if state.entries.is_empty() {
                    "None"
                } else {
                    "Some"
                },
                state
                    .entries
                    .first()
                    .map(|(_, value)| *value)
                    .into_iter()
                    .collect(),
            )
        });
    }
    let popped = if name == "Heap::push" {
        let Some(&value) = args.get(1) else {
            return handle(|_| Err(RuntimeError::internal("missing heap element")));
        };
        let entry = (state.next, value);
        let Some(next) = state.next.checked_add(1) else {
            return handle(|_| Err(RuntimeError::panic("heap insertion sequence exhausted")));
        };
        state.next = next;
        state.entries.push(entry);
        let mut index = state.entries.len() - 1;
        while index > 0 {
            let parent = (index - 1) / 2;
            let Some(order) =
                entry_compare(state.compare, state.entries[index], state.entries[parent])
            else {
                return 0;
            };
            if order != Ordering::Less {
                break;
            }
            state.entries.swap(index, parent);
            index = parent;
        }
        None
    } else if name == "Heap::pop" {
        let first = state.entries.swap_remove(0);
        let mut index = 0usize;
        while let Some(left) = index
            .checked_mul(2)
            .and_then(|value| value.checked_add(1))
            .filter(|left| *left < state.entries.len())
        {
            let right = left + 1;
            let child = if right < state.entries.len() {
                let Some(order) =
                    entry_compare(state.compare, state.entries[right], state.entries[left])
                else {
                    return 0;
                };
                if order == Ordering::Less { right } else { left }
            } else {
                left
            };
            let Some(order) =
                entry_compare(state.compare, state.entries[child], state.entries[index])
            else {
                return 0;
            };
            if order != Ordering::Less {
                break;
            }
            state.entries.swap(index, child);
            index = child;
        }
        Some(first.1)
    } else {
        return handle(|_| Err(RuntimeError::internal("unknown heap operation")));
    };
    handle(|runtime| {
        *runtime.heap.get_mut(receiver)? = Object::PriorityHeap(state);
        if let Some(value) = popped {
            runtime.variant("Some", vec![value])
        } else {
            runtime.unit()
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
    static COMPARISONS: AtomicUsize = AtomicUsize::new(0);
    extern "C" fn rank(_environment: u64, arguments: u64) -> u64 {
        COMPARISONS.fetch_add(1, AtomicOrdering::Relaxed);
        handle(|runtime| {
            let args = runtime.sequence(Handle(arguments))?;
            let left = runtime.sequence(args[0])?[0];
            let right = runtime.sequence(args[1])?[0];
            runtime.order_builtin("Order::compare_int", &[left, right])
        })
    }
    fn setup() -> (Handle, Handle, Vec<Handle>) {
        ril_rt_init();
        ril_rt_enter();
        let result: Option<(Handle, Handle, Vec<Handle>)> = guarded(|runtime| {
            let empty = runtime.unit()?;
            let callback = runtime.allocate(Object::Closure {
                function: rank as *const () as usize as u64,
                environment: empty,
            })?;
            let ops = runtime.allocate(Object::Record([("compare".into(), callback)].into()))?;
            let mut items = vec![];
            for (rank, label) in [(2, "z"), (1, "a"), (1, "b")] {
                let rank = runtime.int(rank)?;
                let label = runtime.string(label.into())?;
                items.push(runtime.allocate(Object::Tuple(vec![rank, label]))?);
            }
            let array = runtime.allocate(Object::Array(items.clone()))?;
            runtime.root(0, array)?;
            runtime.root(1, ops)?;
            Ok(Some((array, ops, items)))
        });
        result.unwrap()
    }
    #[test]
    fn sort_is_stable_search_uses_lower_bound_and_callbacks_keep_source_roots() {
        let (array, ops, items) = setup();
        let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![array, ops])));
        let sorted = invoke("Order::sorted", args);
        assert_ne!(sorted, 0);
        with_runtime(|runtime| {
            assert_eq!(
                runtime.sequence(Handle(sorted)).unwrap(),
                vec![items[1], items[2], items[0]]
            );
            runtime.root(2, Handle(sorted)).unwrap();
            runtime.collect().unwrap();
        });
        let args =
            handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(sorted), items[2], ops])));
        let result = invoke("Order::binary_search", args);
        with_runtime(|runtime| {
            let Object::Variant { tag, fields } = runtime.heap.get(Handle(result)).unwrap() else {
                panic!("Result")
            };
            assert_eq!(tag, "Ok");
            assert_eq!(runtime.as_integer(fields[0]).unwrap(), 0);
        });
        ril_rt_leave(result);
    }
    #[test]
    fn heap_keeps_earliest_equal_element_and_clone_preserves_its_comparator() {
        let (_array, ops, items) = setup();
        let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![ops])));
        let heap = invoke("Heap::new", args);
        ril_rt_root(2, heap);
        for item in &items {
            let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(heap), *item])));
            assert_ne!(invoke("Heap::push", args), 0);
        }
        let copy = handle(|runtime| runtime.copy(Handle(heap)));
        ril_rt_root(3, copy);
        for expected in [items[1], items[2], items[0]] {
            let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(heap)])));
            let result = invoke("Heap::pop", args);
            with_runtime(|runtime| {
                let Object::Variant { tag, fields } = runtime.heap.get(Handle(result)).unwrap()
                else {
                    panic!("Option")
                };
                assert_eq!(tag, "Some");
                assert_eq!(fields[0], expected);
                runtime.collect().unwrap();
            });
        }
        let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(copy)])));
        let length = invoke("Heap::len", args);
        with_runtime(|runtime| assert_eq!(runtime.as_integer(Handle(length)).unwrap(), 3));
        ril_rt_leave(length);
    }
}
