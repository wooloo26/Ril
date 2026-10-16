//! Heap budget coverage follows the retained callback of this exact receiver.
//! A type, a partial member schema or another heap never supplies that proof.
use super::*;

impl Checker {
    fn heap_budget_comparator(&self, source: &Value) -> Option<Value> {
        if source.origins.nodes.len() != 1
            || source.origins.choices.values().any(|alternatives| {
                alternatives
                    .iter()
                    .any(|nodes| nodes != &source.origins.nodes)
            })
        {
            return None;
        }
        let node = *source.origins.nodes.iter().next()?;
        let complete = self.heap.nodes[node.0 as usize].multiplicity == Multiplicity::One
            && self
                .fields
                .get(&(node, Slot::Field("$members".into())))
                .is_some_and(|witness| {
                    witness.ty == Ty::Unit && witness.constant == Some(Constant::Unit)
                })
            && !self
                .uncertain_slots
                .iter()
                .any(|(origin, _)| *origin == node);
        complete
            .then(|| {
                self.fields
                    .get(&(node, Slot::Field("$compare".into())))
                    .cloned()
            })
            .flatten()
    }

    pub(super) fn budget_heap_comparison(
        &mut self,
        source: &Value,
        element: &Ty,
        span: Span,
        frame: &mut Frame,
    ) {
        if self.budget_coverage.is_empty() {
            return;
        }
        let comparator = self.heap_budget_comparator(source);
        let Some(callback) = comparator else {
            self.budget_heap_comparison_coverage(span, &[source.cause], false);
            return;
        };
        let independent = !callback.mutable_environment
            && !callback.observer_environment
            && callback.callables.len() == 1
            && callback.callables.iter().all(|target| {
                !self.has_retained_handlers(target)
                    && match target {
                        Callable::Named(id) => {
                            self.functions[*id].captures.is_empty()
                                && self.functions[*id].syntax.body.is_some()
                        }
                        Callable::Closure(id) => self.closures[*id].captures.is_empty(),
                        Callable::Builtin(name) => matches!(
                            name.as_str(),
                            "Order::compare_int"
                                | "Order::compare_str"
                                | "Order::compare_bytes"
                                | "Order::total_f64"
                        ),
                        _ => false,
                    }
            });
        let finite = self.callable_termination(&callback, span, &BTreeMap::new());
        let covered = independent
            && !finite.may_diverge
            && !finite.unresolved
            && finite.callable_parameters.is_empty();
        if covered {
            // The closed, immutable comparator contract admits repeated calls.
            // Rechecking with formal read operands records its actual callback,
            // selected local handlers, cleanup and transitive budget entries.
            self.order_comparator(&callback, element, span, frame, true);
        }
        self.budget_heap_comparison_coverage(span, &[source.cause, callback.cause], covered);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn span(start: u32) -> Span {
        Span {
            file: FileId(0),
            start,
            end: start + 1,
        }
    }
    fn source(checker: &mut Checker, frame: &Frame, start: u32) -> Value {
        let node = checker.allocate(span(start), 0, frame.owner);
        Value::reference(
            Ty::Applied {
                constructor: "Heap::Heap".into(),
                arguments: vec![TypeArgument::Type(Box::new(Ty::Int("int".into())))],
            },
            node,
            checker.heap.nodes[node.0 as usize].cause,
        )
    }
    fn complete(checker: &mut Checker, source: &Value, start: u32) {
        let node = *source.origins.nodes.first().unwrap();
        checker.record_opaque_collection_members(node, span(start));
        let mut comparator = Value::scalar(
            Ty::Callable(
                vec![Ty::Int("int".into()); 2],
                Box::new(Ty::Named("Order::Ordering".into())),
            ),
            None,
            source.cause,
        );
        comparator.callables = vec![Callable::Builtin("Order::compare_int".into())];
        checker.store_field(node, Slot::Field("$compare".into()), comparator);
    }
    #[test]
    fn coverage_never_borrows_another_heap_or_repairs_an_uncertain_member_family() {
        let mut checker = Checker::new(FileId(0));
        let frame = checker.frame(Env::new(), false);
        let first = source(&mut checker, &frame, 1);
        let second = source(&mut checker, &frame, 2);
        complete(&mut checker, &first, 1);
        assert!(checker.heap_budget_comparator(&first).is_some());
        assert!(checker.heap_budget_comparator(&second).is_none());
        complete(&mut checker, &second, 2);
        assert!(checker.heap_budget_comparator(&second).is_some());
        let mut partial = first.clone();
        partial
            .origins
            .choices
            .insert(0, vec![first.origins.nodes.clone(), BTreeSet::new()]);
        assert!(checker.heap_budget_comparator(&partial).is_none());
        let mut joined = first.clone();
        joined.origins.nodes.extend(&second.origins.nodes);
        assert!(checker.heap_budget_comparator(&joined).is_none());
        let first_node = *first.origins.nodes.first().unwrap();
        checker.heap.nodes[first_node.0 as usize].multiplicity = Multiplicity::MayMany;
        assert!(checker.heap_budget_comparator(&first).is_none());
        checker.heap.nodes[first_node.0 as usize].multiplicity = Multiplicity::One;
        checker.mark_heap_uncertain(std::slice::from_ref(&first));
        assert!(checker.heap_budget_comparator(&first).is_none());
        assert!(checker.heap_budget_comparator(&second).is_some());
        complete(&mut checker, &first, 1);
        assert!(
            checker.heap_budget_comparator(&first).is_none(),
            "restoring observed fields does not clear the unknown-write obligation"
        );
    }
}
