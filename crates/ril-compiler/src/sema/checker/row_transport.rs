//! Validate nested row transport against existing value edges. This checker
//! never allocates a row family or derives object identity from a row binder.
use super::*;

impl Checker {
    pub(super) fn require_nested_row_transport(
        &mut self,
        source: &Value,
        expected: &Ty,
        span: Span,
    ) {
        let mut work = vec![(source.clone(), expected.clone())];
        let mut seen = BTreeSet::new();
        let mut visits = 0;
        while let Some((value, expected)) = work.pop() {
            visits += 1;
            if visits > 4096 {
                self.unsupported(
                    span,
                    "nested row transport graph exceeded its finite proof budget",
                );
                return;
            }
            if value.ty == Ty::Never {
                continue;
            }
            let mut actual = self.call_inference_type(&value.ty);
            let mut expected = self.call_inference_type(&expected);
            if matches!(expected, Ty::Immutable(_)) {
                if value.publication != Publication::Immutable
                    || self.has_writer(&value)
                    || value.mutable_environment
                    || value.observer_environment
                {
                    self.error(
                        "E0535",
                        span,
                        "nested immutable row requires complete reachable writer exclusion",
                        [value.cause],
                    );
                    continue;
                }
                if let Ty::Immutable(inner) = expected {
                    expected = *inner;
                }
            }
            if let Ty::Immutable(inner) = actual {
                actual = *inner;
            }
            if !actual.contains_open_row() && !expected.contains_open_row() {
                let mut selected = value.clone();
                selected.ty = actual;
                self.require_type(&selected, &expected, span);
                continue;
            }
            let nodes: Vec<_> = value
                .origins
                .nodes
                .iter()
                .copied()
                .filter(|node| {
                    seen.insert((
                        *node,
                        format!("{actual:?}"),
                        format!("{expected:?}"),
                        value.permission,
                        value.results.clone(),
                    ))
                })
                .collect();
            if !value.origins.nodes.is_empty() && nodes.is_empty() {
                continue;
            }
            match (&actual, &expected) {
                (Ty::Record(_) | Ty::OpenRecord { .. }, Ty::Record(_) | Ty::OpenRecord { .. }) => {
                    let (Some(actual_row), Some(expected_row)) =
                        (self.value_row(&actual), self.value_row(&expected))
                    else {
                        unreachable!("selected structural row");
                    };
                    // Label and slot-mutability equations are independent of
                    // constituent transport. Neither establishes reference
                    // permissions, member origins, nor copy eligibility.
                    let erase = |row: &Row<Ty>| Row {
                        fields: row
                            .fields
                            .iter()
                            .map(|(name, (mode, _))| (name.clone(), (*mode, ())))
                            .collect(),
                        tail: row.tail.clone(),
                    };
                    let mut solver = Solver::new("nested value row", []);
                    for (identity, lacks) in &self.generic_row_lacks {
                        solver
                            .declare_rigid(identity.clone(), lacks.iter().cloned())
                            .expect("rigid declaration");
                    }
                    if solver
                        .unify(&erase(&actual_row), &erase(&expected_row))
                        .is_err()
                    {
                        self.row_transport_mismatch(&value, span);
                        continue;
                    }
                    if let RowTail::Open(row) = &actual_row.tail {
                        self.carried_row_tail(&value, row, span);
                    }
                    for (name, (_, ty)) in expected_row.fields {
                        self.enqueue_row_field(
                            &value,
                            &nodes,
                            &Slot::Field(name),
                            &ty,
                            span,
                            &mut work,
                        );
                    }
                }
                (Ty::Tuple(actual_items), Ty::Tuple(expected_items))
                    if actual_items.len() == expected_items.len() =>
                {
                    for (index, ty) in expected_items.iter().enumerate() {
                        self.enqueue_row_field(
                            &value,
                            &nodes,
                            &Slot::Tuple(index as u32),
                            ty,
                            span,
                            &mut work,
                        );
                    }
                }
                (Ty::Array(actual_element), Ty::Array(element))
                | (Ty::Set(actual_element), Ty::Set(element))
                    if self.compatible(actual_element, element) =>
                {
                    self.enqueue_row_elements(&value, &nodes, element, span, &mut work);
                }
                (Ty::Map(actual_key, actual_element), Ty::Map(key, element))
                    if self.compatible(actual_key, key)
                        && self.compatible(actual_element, element) =>
                {
                    self.enqueue_row_elements(&value, &nodes, element, span, &mut work);
                    for node in &nodes {
                        if self
                            .fields
                            .contains_key(&(*node, Slot::Field("key".into())))
                        {
                            self.enqueue_row_field(
                                &value,
                                &[*node],
                                &Slot::Field("key".into()),
                                key,
                                span,
                                &mut work,
                            );
                        } else if self.array_lengths.get(node) != Some(&Some(0)) {
                            self.unsupported(
                                span,
                                "nested row map transport requires the stored key family witness",
                            );
                        }
                    }
                }
                (Ty::Optional(actual_inner), Ty::Optional(inner))
                    if self.compatible(actual_inner, inner) =>
                {
                    if value.option_tag == Some(false) {
                        continue;
                    }
                    if let Some(payload) = &value.option_payload {
                        self.enqueue_row_child(&value, payload, inner, span, &mut work);
                    } else {
                        self.unsupported(
                            span,
                            "nested row optional transport requires its actual payload witness",
                        );
                    }
                }
                (Ty::Result(actual_ok, actual_error), Ty::Result(ok, error))
                    if self.compatible(actual_ok, ok) && self.compatible(actual_error, error) =>
                {
                    for (tag, ty, payload) in [
                        (true, ok, &value.result_success),
                        (false, error, &value.result_error),
                    ] {
                        if value.result_tag.is_some_and(|selected| selected != tag) {
                            continue;
                        }
                        let payload = payload.as_ref().or_else(|| {
                            (value.result_tag == Some(tag))
                                .then_some(value.result_payload.as_ref())
                                .flatten()
                        });
                        if let Some(payload) = payload {
                            self.enqueue_row_child(&value, payload, ty, span, &mut work);
                        } else if ty.contains_open_row() {
                            self.unsupported(span, "nested row Result transport requires a tag-specific payload and family witness");
                        }
                    }
                }
                _ if self.compatible(&actual, &expected) => self.unsupported(
                    span,
                    "nested row transport requires a complete callable, nominal or opaque carrier template",
                ),
                _ => self.row_transport_mismatch(&value, span),
            }
        }
    }

    fn row_transport_mismatch(&mut self, value: &Value, span: Span) {
        self.error(
            "E0301",
            span,
            "nested containers do not preserve the same selected types and rigid row tail",
            [value.cause],
        );
    }

    fn enqueue_row_field(
        &mut self,
        value: &Value,
        nodes: &[NodeId],
        slot: &Slot,
        expected: &Ty,
        span: Span,
        work: &mut Vec<(Value, Ty)>,
    ) {
        if nodes.is_empty() {
            self.unsupported(
                span,
                "nested row member transport has no actual source origin",
            );
        }
        for node in nodes {
            if let Some(child) = self.fields.get(&(*node, slot.clone())).cloned() {
                self.enqueue_row_child(value, &child, expected, span, work);
            } else {
                self.unsupported(span, "nested row member transport requires every source alternative's stored constituent witness");
            }
        }
    }

    fn enqueue_row_elements(
        &mut self,
        value: &Value,
        nodes: &[NodeId],
        expected: &Ty,
        span: Span,
        work: &mut Vec<(Value, Ty)>,
    ) {
        if nodes.is_empty() {
            self.unsupported(
                span,
                "nested row collection transport has no actual source origin",
            );
        }
        for node in nodes {
            let children: Vec<_> = self
                .fields
                .iter()
                .filter_map(|((parent, slot), child)| {
                    (*parent == *node && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                        .then_some(child.clone())
                })
                .collect();
            if children.is_empty() && self.array_lengths.get(node) != Some(&Some(0)) {
                self.unsupported(span, "nested row collection transport requires its complete element family or an empty witness");
            }
            for child in children {
                self.enqueue_row_child(value, &child, expected, span, work);
            }
        }
    }

    fn enqueue_row_child(
        &mut self,
        parent: &Value,
        child: &Value,
        expected: &Ty,
        span: Span,
        work: &mut Vec<(Value, Ty)>,
    ) {
        if !child.results.is_subset(&parent.results) {
            self.unsupported(
                span,
                "nested row container lacks its constituent Result family membership",
            );
            return;
        }
        let mut child = child.clone();
        child.permission = child.permission.meet(parent.permission);
        child.construction &= parent.construction;
        child.publication = if parent.publication == Publication::Immutable
            || child.publication == Publication::Immutable
        {
            Publication::Immutable
        } else if parent.publication == Publication::Live {
            Publication::Live
        } else {
            child.publication
        };
        child.sources.extend(&parent.sources);
        child.participants.extend(&parent.participants);
        child.scoped.extend(&parent.scoped);
        work.push((child, expected.clone()));
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
    fn complete_nested_container_witnesses_preserve_the_rigid_member_family() {
        for source in [
            "fn nested<R>(item:{payload:{..R}})->{payload:{..R}}{item}",
            "fn list<R>(items:[]{..R})->[]{..R}{items}",
            "fn pair<R>(items:({..R},{..R}))->({..R},{..R}){items}",
            "fn optional<R>(item:?{..R})->?{..R}{item}",
            "fn mapped<R>(items:[str:{..R}])->[str:{..R}]{items}",
            "fn boxed<R>(item:{..R})->{payload:[]{..R}}{.{payload:[item]}}",
            "fn wrapped<R>(item:{..R})->Result<{..R},str>{Ok(item)}",
            "fn carry<R>(item:{..R})->[]{..R}{[item]}\nfn example(){let view item=carry(.{answer:Ok(1)});assert(item[0].answer is Ok(1))}",
            "type Cell={mut value:int}\nfn carry<R>(item:{..R})->[]{..R}{[item]}\nfn example(){let mut shared=Cell.{value:0};let view isolated=carry(.{child:clone_immut(shared)});let _=Parallel::join(\\->{shared.value+=1},\\->isolated[0].child.value)}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_some(),
                "{source}\n{:?}\n{:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }

    #[test]
    fn nested_transport_keeps_aliases_readonly_paths_and_uninspected_duties() {
        for (source, code) in [
            (
                "type Cell={mut value:int}\nfn carry<R>(item:{..R})->[]{..R}{[item]}\nfn example(){let mut shared=Cell.{value:0};let view observed=carry(.{child:^mut shared});let _=Parallel::join(\\->{shared.value+=1},\\->observed[0].child.value)}",
                "E0619",
            ),
            (
                "type Cell={mut value:int}\nfn carry<R>(item:{..R})->[]{..R}{[item]}\nfn example(){let mut shared=Cell.{value:0};shared.value+=1;let view observed=shared;let mut items=carry(.{child:observed});items[0].child.value=2}",
                "E0522",
            ),
            (
                "fn carry<R>(item:{..R})->[]{..R}{[item]}\nfn example(){let _=carry(.{answer:Ok(1)})}",
                "E0720",
            ),
            ("fn freeze<R>(item:[]{..R})->[]Immut<{..R}>{item}", "E0301"),
            ("fn change<R,S>(item:[]{..R})->[]{..S}{item}", "E0301"),
            (
                "fn select<R>(item:[]{..R})->[]{value:int,..R}{item}",
                "E0301",
            ),
            (
                "fn wrong<R>()->[]{..R}{let numbers:[]int=[];numbers}",
                "E0301",
            ),
            (
                "fn wrong<R>()->?{..R}{let number:?int=None;number}",
                "E0301",
            ),
            (
                "type Guard={on_close:fn()->()}\nfn carry<R>(item:{..R})->[]{..R}{[item]}\nfn escape()->[]{guard:Guard}{let scoped guard=Guard.{on_close:\\->()};carry(.{guard:guard})}",
                "E0604",
            ),
        ] {
            let result = check(source);
            assert!(
                result.diagnostics.iter().any(|error| error.code == code),
                "{source}: expected {code}\n{:?}\n{:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        for source in [
            "fn copy<R>(item:[]{..R})->[]{..R}{clone(item)}",
            "fn transport<R>(item:Result<{..R},str>)->Result<{..R},str>{item}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_none(),
                "an unknown constituent proof is required"
            );
        }
    }

    #[test]
    fn transport_neither_invents_nodes_nor_changes_any_concrete_alias_partition() {
        let span = Span {
            file: FileId(0),
            start: 1,
            end: 2,
        };
        let row = OpenTail {
            identity: RowIdentity::Binder("R".into()),
            lacks: BTreeSet::new(),
        };
        let row_type = Ty::OpenRecord {
            fields: BTreeMap::new(),
            row: row.clone(),
        };
        for shared in [false, true] {
            for readonly in [false, true] {
                let mut checker = Checker::new(FileId(0));
                let first = checker.formal_value(row_type.clone(), 0, span, &mut BTreeSet::new());
                let second = if shared {
                    first.clone()
                } else {
                    checker.formal_value(row_type.clone(), 1, span, &mut BTreeSet::new())
                };
                let root = checker.allocate(span, 0, ScopeId(0));
                let ty = Ty::Array(Box::new(row_type.clone()));
                let mut source = Value::reference(ty.clone(), root, first.cause);
                source.results.extend(&first.results);
                source.results.extend(&second.results);
                if readonly {
                    source.permission = Permission::Read;
                    source.publication = Publication::Live;
                }
                checker.store_field(root, Slot::Index(0), first);
                checker.store_field(root, Slot::Index(1), second);
                checker.array_lengths.insert(root, Some(2));
                let nodes = checker.heap.nodes.clone();
                let fields = format!("{:?}", checker.fields);
                let relations: Vec<_> = checker.heap.relations().collect();
                checker.require_nested_row_transport(&source, &ty, span);
                assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
                assert!(checker.unsupported.is_empty(), "{:?}", checker.unsupported);
                assert_eq!(checker.heap.nodes, nodes);
                assert_eq!(checker.heap.relations().collect::<Vec<_>>(), relations);
                assert_eq!(format!("{:?}", checker.fields), fields);
            }
        }
    }

    #[test]
    fn a_schema_without_its_member_edge_or_result_family_is_not_a_transport_proof() {
        let span = Span {
            file: FileId(0),
            start: 1,
            end: 2,
        };
        let row = OpenTail {
            identity: RowIdentity::Binder("R".into()),
            lacks: BTreeSet::new(),
        };
        let ty = Ty::Tuple(vec![
            Ty::OpenRecord {
                fields: BTreeMap::new(),
                row: row.clone(),
            },
            Ty::Int("int".into()),
        ]);
        for missing_edge in [false, true] {
            let mut checker = Checker::new(FileId(0));
            let mut source = checker.formal_value(ty.clone(), 0, span, &mut BTreeSet::new());
            if missing_edge {
                let root = *source.origins.nodes.first().unwrap();
                let child = *checker.fields[&(root, Slot::Tuple(0))]
                    .origins
                    .nodes
                    .first()
                    .unwrap();
                checker
                    .fields
                    .remove(&(child, Slot::RowTail(row.identity.clone())));
            } else {
                source.results.clear();
            }
            let nodes = checker.heap.nodes.len();
            checker.require_nested_row_transport(&source, &ty, span);
            assert!(
                !checker.unsupported.is_empty(),
                "a member schema alone cannot authorize transport"
            );
            assert_eq!(checker.heap.nodes.len(), nodes);
        }
    }
}
