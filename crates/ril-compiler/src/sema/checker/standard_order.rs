//! Ordered and opaque collections retain their element and comparator identity.
use super::*;
#[path = "heap_budget.rs"]
mod budget;
pub(super) fn is_order_builtin(name: &str) -> bool {
    matches!(
        name,
        "Order::compare_int"
            | "Order::compare_str"
            | "Order::compare_bytes"
            | "Order::total_f64"
            | "Order::sorted"
            | "Order::binary_search"
            | "Deque::new"
            | "Deque::len"
            | "Deque::push_front"
            | "Deque::push_back"
            | "Deque::pop_front"
            | "Deque::pop_back"
            | "Deque::values"
            | "Heap::new"
            | "Heap::len"
            | "Heap::push"
            | "Heap::pop"
            | "Heap::peek"
    )
}

pub(super) fn order_constant(name: &str) -> Option<Ty> {
    matches!(
        name,
        "Order::Ordering::Less" | "Order::Ordering::Equal" | "Order::Ordering::Greater"
    )
    .then(|| Ty::Named("Order::Ordering".into()))
}
fn instance(family: &str, element: TypeArgument) -> Ty {
    Ty::Applied {
        constructor: format!("{family}::{family}"),
        arguments: vec![element],
    }
}
fn ops(element: Ty) -> Ty {
    Ty::Record(
        [(
            "compare".into(),
            (
                false,
                Ty::Callable(
                    vec![element.clone(), element],
                    Box::new(Ty::Named("Order::Ordering".into())),
                ),
            ),
        )]
        .into(),
    )
}
fn concrete(ty: &Ty) -> bool {
    match ty {
        Ty::Unknown | Ty::Generic(_) => false,
        Ty::Applied { arguments, .. } => arguments.iter().all(|argument| {
            matches!(argument,TypeArgument::Type(ty)|TypeArgument::CanonicalType{ty,..} if concrete(ty))
                || matches!(argument, TypeArgument::Static(_))
        }),
        Ty::Array(inner)
        | Ty::Set(inner)
        | Ty::Optional(inner)
        | Ty::Immutable(inner)
        | Ty::Range(inner) => concrete(inner),
        Ty::Map(a, b) | Ty::Result(a, b) => concrete(a) && concrete(b),
        Ty::Tuple(items) => items.iter().all(concrete),
        Ty::Record(fields) => fields.values().all(|(_, ty)| concrete(ty)),
        Ty::Callable(inputs, result) => inputs.iter().all(concrete) && concrete(result),
        _ => true,
    }
}
impl Checker {
    pub(super) fn standard_order_generic(
        &mut self,
        value: &mut Value,
        arguments: &[TypeExpr],
        span: Span,
    ) -> bool {
        let Some(name) = value.callables.iter().find_map(|callable| match callable {
            Callable::Builtin(name) if matches!(name.as_str(), "Deque::new" | "Heap::new") => {
                Some(name.clone())
            }
            _ => None,
        }) else {
            return false;
        };
        if arguments.len() != 1 {
            self.error(
                "E0340",
                span,
                "collection constructor requires one element type",
                [value.cause],
            );
            return true;
        }
        let element = self.ty(&arguments[0]);
        self.require_type_argument_identity(&arguments[0]);
        if !concrete(&element) {
            self.unsupported(
                span,
                "opaque collection requires an instantiated element type proof",
            );
        }
        let family = name.split("::").next().unwrap();
        value.ty = Ty::Callable(
            if family == "Heap" {
                vec![ops(element.clone())]
            } else {
                vec![]
            },
            Box::new(instance(
                family,
                self.canonical_type_argument(&arguments[0], element),
            )),
        );
        value.callables = vec![Callable::Builtin(format!(
            "{family}::__new_{}_{}_{}",
            span.file.0, span.start, span.end
        ))];
        true
    }
    pub(super) fn standard_order_typed(
        &mut self,
        callee: &Value,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let family = if name == "Deque::new" || name.starts_with("Deque::__new_") {
            "Deque"
        } else if name == "Heap::new" || name.starts_with("Heap::__new_") {
            "Heap"
        } else {
            return None;
        };
        let Ty::Callable(_, result) = &callee.ty else {
            self.unsupported(span, "opaque collection construction needs an element type");
            return Some(self.unit(span));
        };
        let Ty::Applied {
            constructor,
            arguments,
        } = &**result
        else {
            self.unsupported(
                span,
                "opaque collection construction needs an applied result identity",
            );
            return Some(self.unit(span));
        };
        if constructor != &format!("{family}::{family}") || arguments.len() != 1 {
            self.unsupported(
                span,
                "opaque collection construction has no matching typed result",
            );
            return Some(self.unit(span));
        }
        let (TypeArgument::Type(element) | TypeArgument::CanonicalType { ty: element, .. }) =
            &arguments[0]
        else {
            self.unsupported(span, "opaque collection element is not a data type");
            return Some(self.unit(span));
        };
        if !concrete(element) {
            self.unsupported(span, "opaque collection element remains symbolic");
        }
        let expected = if family == "Heap" {
            vec![ops(*element.clone())]
        } else {
            vec![]
        };
        self.standard_arguments(name, args, &expected, expected.len(), span);
        let mut comparator = None;
        if family == "Heap"
            && let Some((_, operations, argument_span)) = args.first()
        {
            let callback = self.project(
                operations,
                Slot::Field("compare".into()),
                *argument_span,
                frame,
                true,
            );
            // Construction validates the retained callback's independent
            // contract but does not execute it inside the active allowance.
            let outer_budget = std::mem::take(&mut self.budget_coverage);
            self.order_comparator(&callback, element, span, frame, true);
            self.budget_coverage = outer_budget;
            comparator = Some(callback);
        }
        let node = self.allocate(span, 0, frame.owner);
        self.record_opaque_collection_members(node, span);
        if let Some(mut comparator) = comparator {
            self.standard_read_handle(&mut comparator);
            self.store_field(node, Slot::Field("$compare".into()), comparator);
        }
        let cause = self.heap.nodes[node.0 as usize].cause;
        Some(Value::reference(*result.clone(), node, cause))
    }
    pub(super) fn standard_order_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_order_builtin(name) {
            return None;
        }
        if !self.check_storage_intrinsic_inputs(name, args, span, frame) {
            return Some(self.unit(span));
        }
        if matches!(
            name,
            "Order::compare_int"
                | "Order::compare_str"
                | "Order::compare_bytes"
                | "Order::total_f64"
        ) {
            let ty = match name {
                "Order::compare_int" => integer("int"),
                "Order::compare_str" => Ty::Str,
                "Order::compare_bytes" => Ty::Bytes,
                _ => float("f64"),
            };
            self.standard_arguments(name, args, &[ty.clone(), ty], 2, span);
            let cause = self.cause(
                CauseKind::Source,
                span,
                "finite standard ordering comparator",
                [],
            );
            return Some(Value::scalar(
                Ty::Named("Order::Ordering".into()),
                None,
                cause,
            ));
        }
        if name.starts_with("Order::") {
            return Some(self.order_operation(name, args, span, frame));
        }
        if matches!(name, "Deque::new" | "Heap::new") {
            self.unsupported(
                span,
                "collection construction requires a typed generic callee",
            );
            return Some(self.unit(span));
        }
        let family = if name.starts_with("Deque::") {
            "Deque"
        } else {
            "Heap"
        };
        let writes = matches!(
            name,
            "Deque::push_front"
                | "Deque::push_back"
                | "Deque::pop_front"
                | "Deque::pop_back"
                | "Heap::push"
                | "Heap::pop"
        );
        let inserts = matches!(
            name,
            "Deque::push_front" | "Deque::push_back" | "Heap::push"
        );
        let arity = if inserts { 2 } else { 1 };
        if args.len() != arity {
            self.error("E0314", span, "wrong opaque collection argument count", []);
            return Some(self.unit(span));
        }
        let (mode, source, source_span) = &args[0];
        let Ty::Applied {
            constructor,
            arguments,
        } = self.expanded(&source.ty, &mut BTreeSet::new())
        else {
            self.error(
                "E0301",
                *source_span,
                "operation requires its opaque collection instance",
                [source.cause],
            );
            return Some(self.unit(span));
        };
        let element = match arguments.as_slice() {
            [TypeArgument::Type(element) | TypeArgument::CanonicalType { ty: element, .. }]
                if constructor == format!("{family}::{family}") =>
            {
                *element.clone()
            }
            _ => {
                self.error(
                    "E0301",
                    *source_span,
                    "opaque collection instance differs",
                    [source.cause],
                );
                return Some(self.unit(span));
            }
        };
        if !concrete(&element) {
            self.unsupported(span, "opaque collection element type is unresolved");
        }
        if *mode
            != if writes {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            }
        {
            self.error(
                "E0405",
                *source_span,
                "opaque collection receiver mode mismatch",
                [source.cause],
            );
        }
        let comparator_recency = self.recency_moves.len();
        if family == "Heap" && writes {
            self.budget_heap_comparison(source, &element, span, frame);
        }
        // The actual comparator's static invocation may age an allocation
        // site. Continue with these same evaluated arguments after that move.
        let mut current_args = args.to_vec();
        for (_, value, _) in &mut current_args {
            self.transport_value_since(value, comparator_recency);
        }
        let args = current_args.as_slice();
        let (_, source, source_span) = &args[0];
        if writes {
            self.standard_structural_write(source, *source_span, frame);
        } else {
            self.access(source, None, Mode::Read, *source_span, frame);
        }
        if inserts {
            if args[1].0 != ParameterMode::Read {
                self.error(
                    "E0405",
                    args[1].2,
                    "opaque collection insertion retains no writable argument",
                    [args[1].1.cause],
                );
            }
            self.require_type(&args[1].1, &element, args[1].2);
            if !args[1].1.results.is_empty() {
                self.unsupported(
                    span,
                    "opaque collection Result membership and removal coverage",
                );
            }
            if family == "Heap" {
                self.require_type(&args[1].1, &Ty::Immutable(Box::new(element)), args[1].2);
            }
            let mut inserted = args[1].1.clone();
            inserted.unsuffixed_numeric = false;
            inserted.literal_number = false;
            self.standard_read_handle(&mut inserted);
            if family == "Heap" {
                inserted.publication = Publication::Immutable;
            }
            for node in &source.origins.nodes {
                let summary = if let Some(old) = self.fields.get(&(*node, Slot::AnyIndex)).cloned()
                {
                    old.join(&inserted, self.choice(), source.cause)
                } else {
                    inserted.clone()
                };
                self.store_field(*node, Slot::AnyIndex, summary);
            }
            return Some(self.unit(span));
        }
        if name.ends_with("::len") {
            return Some(self.standard_value(integer("int"), span, frame.owner, 0));
        }
        let mut children: Vec<Value> = source
            .origins
            .nodes
            .iter()
            .filter_map(|node| self.fields.get(&(*node, Slot::AnyIndex)).cloned())
            .collect();
        for child in &mut children {
            self.standard_read_handle(child);
            child.unsuffixed_numeric = false;
            child.literal_number = false;
            child.sources.extend(&source.sources);
            child.participants.extend(&source.participants);
            child.permission = child.permission.meet(source.permission);
            child.retention_result = false;
            child.through_return |= source.through_return;
        }
        let exact_empty =
            children.is_empty()
                && !source.origins.nodes.is_empty()
                && source.origins.nodes.iter().all(|node| {
                    matches!(self.heap.nodes[node.0 as usize].kind, OriginKind::Fresh(_))
                });
        if children.is_empty() && !exact_empty {
            self.unsupported(
                span,
                "opaque collection has no proved element storage schema",
            );
        }
        if name == "Deque::values" {
            return Some(self.standard_array_with_children(element, children, span, frame.owner));
        }
        if children.iter().any(|child| !child.results.is_empty()) {
            self.unsupported(
                span,
                "opaque collection removal requires exact Result membership proof",
            );
        }
        let mut payload = if let Some(value) = children.pop() {
            value
        } else {
            Value::scalar(element.clone(), None, source.cause)
        };
        for child in children {
            payload = payload.join(&child, self.choice(), source.cause);
        }
        // No public member is exposed: this is the stored constituent witness.
        Some(self.standard_option(payload, exact_empty.then_some(false), span, frame.owner))
    }
    fn order_operation(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let arity = if name == "Order::sorted" { 2 } else { 3 };
        if args.len() != arity {
            self.error("E0314", span, "wrong ordering argument count", []);
            return self.unit(span);
        }
        let Ty::Array(element) = self.expanded(&args[0].1.ty, &mut BTreeSet::new()) else {
            self.error(
                "E0301",
                args[0].2,
                "ordering requires array data",
                [args[0].1.cause],
            );
            return self.unit(span);
        };
        let operations = args.last().unwrap();
        self.standard_arguments(
            name,
            args,
            &if arity == 2 {
                vec![Ty::Array(element.clone()), ops(*element.clone())]
            } else {
                vec![
                    Ty::Array(element.clone()),
                    *element.clone(),
                    ops(*element.clone()),
                ]
            },
            arity,
            span,
        );
        let callback = self.project(
            &operations.1,
            Slot::Field("compare".into()),
            operations.2,
            frame,
            true,
        );
        self.order_comparator(&callback, &element, span, frame, false);
        self.deep_read(&args[0].1, span, frame);
        if name == "Order::sorted" {
            self.standard_copy_array(
                std::slice::from_ref(&args[0].1),
                *element,
                false,
                span,
                frame,
            )
        } else {
            self.standard_result(integer("int"), integer("int"), span, frame.owner)
        }
    }
    fn order_comparator(
        &mut self,
        callback: &Value,
        element: &Ty,
        span: Span,
        frame: &mut Frame,
        retained: bool,
    ) {
        if callback.mutable_environment || callback.observer_environment {
            self.error(
                "E0534",
                span,
                "ordering requires an immutable effect and state free comparator",
                [callback.cause],
            );
        }
        if callback.callables.iter().any(|callable| matches!(callable,Callable::Named(id) if self.functions[*id].syntax.annotations.iter().any(|annotation| annotation.text != "@{}" && annotation.text != "&{}"))) {
            self.error("E0534",span,"ordering comparator retains a nonempty invocation row",[callback.cause]);
        }
        if retained
            && callback.callables.iter().any(|callable| match callable {
                Callable::Closure(id) => !self.closures[*id].captures.is_empty(),
                Callable::Named(id) => !self.functions[*id].captures.is_empty(),
                _ => false,
            })
        {
            self.error(
                "E0534",
                span,
                "Heap comparator must be environment free",
                [callback.cause],
            );
        }
        let program = Program {
            statements: self
                .functions
                .iter()
                .map(|info| Stmt {
                    hir_id: None,
                    kind: StmtKind::Function(info.syntax.clone()),
                    span: info.syntax.span,
                })
                .collect(),
        };
        for callable in &callback.callables {
            let expression = match callable {
                Callable::Builtin(name)
                    if matches!(
                        name.as_str(),
                        "Order::compare_int"
                            | "Order::compare_str"
                            | "Order::compare_bytes"
                            | "Order::total_f64"
                    ) =>
                {
                    continue;
                }
                Callable::Named(id) => Some(Expr {
                    hir_id: None,
                    kind: ExprKind::Name(self.functions[*id].syntax.name.clone()),
                    span,
                }),
                Callable::Closure(id) => Some(Expr {
                    hir_id: None,
                    kind: ExprKind::Lambda {
                        parameters: self.closures[*id].parameters.clone(),
                        return_type: None,
                        annotations: vec![],
                        body: Box::new(self.closures[*id].body.clone()),
                    },
                    span,
                }),
                _ => None,
            };
            if let Some(expression) = expression {
                let judgment = crate::termination::analyze_expression(&program, &expression);
                if judgment.may_diverge {
                    self.error(
                        "E0534",
                        span,
                        "ordering comparator must have a finite termination proof",
                        [callback.cause],
                    );
                }
                if judgment.unresolved || !judgment.callable_parameters.is_empty() {
                    self.unsupported(
                        span,
                        "ordering comparator finite dependency proof is unresolved",
                    );
                }
            } else {
                self.unsupported(span, "ordering comparator has an abstract callable target");
            }
        }
        let before = self.snapshot_flow();
        let mut context = self.frame(frame.env.clone(), true);
        let mut left = self.formal_value(element.clone(), 0, span, &mut BTreeSet::new());
        let mut right = self.formal_value(element.clone(), 1, span, &mut BTreeSet::new());
        self.standard_read_handle(&mut left);
        self.standard_read_handle(&mut right);
        let result = self.invoke_generated_values(
            callback,
            vec![
                (ParameterMode::Read, left, span),
                (ParameterMode::Read, right, span),
            ],
            span,
            &mut context,
        );
        self.require_type(&result, &Ty::Named("Order::Ordering".into()), span);
        if !context.obligations.effects.is_empty()
            || context.obligations.parameter_write
            || context.obligations.retention
            || context.obligations.capture
            || context.obligations.symbolic
            || context.obligations.named.iter().any(|(binding, mode)| {
                *mode != Mode::Read
                    || self.bindings[*binding].mode.is_reassignable()
                    || self.bindings[*binding].value.publication != Publication::Immutable
            })
        {
            self.error(
                "E0534",
                span,
                "ordering comparator violates its closed invocation contract",
                [callback.cause],
            );
        }
        self.restore_definition_state(&before);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn ordered_and_opaque_collections_preserve_element_instance_identity() {
        for source in [
            "fn example() { let mut queue = Deque::new<int>(); Deque::push_front(mut queue,1); Deque::push_back(mut queue,2); let values: []int = Deque::values(queue); assert(values == [1,2]); let result = Deque::pop_front(mut queue) }",
            "fn example() { let mut heap = Heap::new<int>(.{ compare: Order::compare_int }); Heap::push(mut heap,2); Heap::push(mut heap,1); let result = Heap::pop(mut heap) }",
            "fn example() { let values = Order::sorted([3,1,2],.{compare: Order::compare_int}); let index = Order::binary_search(values,1,.{compare:Order::compare_int}); assert(index is Ok(_)); assert(Order::total_f64(-0.0,0.0) == Order::Ordering::Less) }",
        ] {
            let output = check(source);
            assert!(
                output.program.is_some(),
                "{source}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
        let output = check(
            "fn example() { let mut queue = Deque::new<int>(); Deque::push_back(mut queue,\"wrong\") }",
        );
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?}",
            output.diagnostics
        );
    }
    #[test]
    fn opaque_collection_storage_and_comparison_never_grant_payload_authority() {
        for (source, code) in [
            (
                "type Cell = {mut value:int}\nfn example() { let source=Cell.{value:1}; let mut queue=Deque::new<Cell>(); Deque::push_back(mut queue,source); let Some(item)=Deque::pop_front(mut queue) else {return}; let mut alias=item; alias.value+=1 }",
                "E0520",
            ),
            (
                "type Cell = {mut value:int}\nfn example() { let mut source=Cell.{value:1}; source.value+=1; let mut heap=Heap::new<Cell>(.{compare:\\a,b -> Order::compare_int(a.value,b.value)}); Heap::push(mut heap,source) }",
                "E0535",
            ),
            (
                "fn example() { let bias=1; let mut heap=Heap::new<int>(.{compare:\\a,b -> Order::compare_int(a+bias,b)}); Heap::push(mut heap,1) }",
                "E0534",
            ),
            (
                "fn spin(left:int,right:int)->Order::Ordering {loop {}}\nfn example() {let sorted=Order::sorted([1,2],.{compare:spin})}",
                "E0534",
            ),
        ] {
            let output = check(source);
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{source} expected {code}: {:?} {:?}",
                output.diagnostics,
                output.unsupported
            );
        }
    }
}
