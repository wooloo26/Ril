//! Concrete graph oracle for the production batch copier. The oracle enumerates
//! object edges, independently of copy-class identity and abstract reachability.
use super::*;

#[test]
fn different_observed_fields_never_prove_distinct_source_objects() {
    let mut checker = Checker::new(FileId(0));
    let span = Span {
        file: FileId(0),
        start: 100,
        end: 110,
    };
    let ty = Ty::Record(
        [
            ("a".into(), (true, Ty::Int("int".into()))),
            ("b".into(), (true, Ty::Int("int".into()))),
        ]
        .into(),
    );
    let left = checker.heap.symbolic(Pivot(0), ScopeId(0), CauseId(0));
    let right = checker.heap.symbolic(Pivot(1), ScopeId(0), CauseId(0));
    checker.heap.set_relation(left, right, Relation::EQUAL);
    checker.store_field(
        left,
        Slot::Field("a".into()),
        Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
    );
    checker.store_field(
        right,
        Slot::Field("b".into()),
        Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
    );
    let root = checker.allocate(span, 0, ScopeId(0));
    checker.store_field(
        root,
        Slot::Tuple(0),
        Value::reference(ty.clone(), left, CauseId(0)),
    );
    checker.store_field(
        root,
        Slot::Tuple(1),
        Value::reference(ty.clone(), right, CauseId(0)),
    );
    let source = Value::reference(Ty::Tuple(vec![ty.clone(), ty]), root, CauseId(0));
    let copied = checker
        .canonical_ordinary_clone(&source, span, ScopeId(0), false)
        .unwrap();
    let copied_root = *copied.origins.nodes.first().unwrap();
    let left_copy = *checker.fields[&(copied_root, Slot::Tuple(0))]
        .origins
        .nodes
        .first()
        .unwrap();
    let right_copy = *checker.fields[&(copied_root, Slot::Tuple(1))]
        .origins
        .nodes
        .first()
        .unwrap();
    assert_eq!(
        checker.heap.relation(left_copy, right_copy),
        Relation::EQUAL
    );
    assert!(copied.internal_aliases);
    assert!(checker.clone_relations(&[(left, left_copy), (right, right_copy)].into()));
    assert_eq!(
        checker.heap.relation(left_copy, right_copy),
        Relation::EQUAL
    );
}

#[test]
fn production_batches_preserve_concrete_edges_under_every_binary_quotient() {
    let declaration = ril_syntax::parse("type Node={mut following:?Node}");
    assert!(declaration.is_ok());
    let node_type = Ty::Named("Node".into());
    let span = Span {
        file: FileId(0),
        start: 100,
        end: 110,
    };
    let slot = Slot::Field("following".into());
    // Exhaust all concrete two-object functional graphs and binary class
    // maps. The independent pure oracle additionally covers all three-node
    // directed graphs; this one exercises the production representation.
    for graph in 0u8..9 {
        let targets = [graph % 3, graph / 3];
        for assignment in 0u8..4 {
            let mut checker = Checker::new(FileId(0));
            checker.run(&declaration.program);
            // These are concrete representatives of a historical source
            // summary; equal source classes never assert concrete equality.
            let nodes: Vec<_> = (0..2)
                .map(|index| {
                    checker.heap.insert(HeapNode {
                        kind: OriginKind::Older(SiteId(((assignment >> index) & 1).into())),
                        multiplicity: Multiplicity::MayMany,
                        owner: ScopeId(0),
                        fields: BTreeMap::new(),
                        writable_roots: BTreeSet::new(),
                        escaping: false,
                        cause: CauseId(0),
                    })
                })
                .collect();
            checker.next_site = 2;
            for a in 0..2 {
                let mut value =
                    Value::scalar(Ty::Optional(Box::new(node_type.clone())), None, CauseId(0));
                if targets[a] < 2 {
                    value.origins = Origins::one(nodes[targets[a] as usize]);
                    value.permission = Permission::Write;
                    value.publication = Publication::Live;
                }
                checker.store_field(nodes[a], slot.clone(), value);
            }
            let root = checker.allocate(span, 0, ScopeId(0));
            let mut source =
                Value::reference(Ty::Array(Box::new(node_type.clone())), root, CauseId(0));
            for (index, node) in nodes.iter().enumerate() {
                checker.store_field(
                    root,
                    Slot::Index(index as i64),
                    Value::reference(node_type.clone(), *node, CauseId(0)),
                );
            }
            checker.array_lengths.insert(root, Some(2));
            // Repeated copies at the same expression must remain finite and
            // distinct from the old graph, including after site recycling.
            for _ in 0..4 {
                let mut old = checker.heap.reachable(source.origins.nodes.iter().copied());
                let cursor = checker.recency_moves.len();
                let output = checker
                    .canonical_ordinary_clone(&source, span, ScopeId(0), false)
                    .unwrap();
                loop_graph::transport_nodes(&mut old, &checker.recency_moves[cursor..]);
                let output_root = *output.origins.nodes.first().unwrap();
                let selected: Vec<_> = (0..2)
                    .map(|index| {
                        checker.fields[&(output_root, Slot::Index(index))]
                            .origins
                            .nodes
                            .clone()
                    })
                    .collect();
                for a in 0..2 {
                    for b in 0..2 {
                        if targets[a] as usize == b {
                            for copied in &selected[a] {
                                let actual =
                                    &checker.fields[&(*copied, slot.clone())].origins.nodes;
                                assert!(
                                    !actual.is_disjoint(&selected[b]),
                                    "lost concrete edge {a}->{b}"
                                );
                            }
                        }
                        if a != b && !selected[a].is_disjoint(&selected[b]) {
                            for node in selected[a].intersection(&selected[b]) {
                                assert_ne!(
                                    checker.heap.relation(*node, *node).equal,
                                    Condition::TRUE
                                );
                            }
                        }
                    }
                }
                for copied in checker.heap.reachable(output.origins.nodes.iter().copied()) {
                    for old in &old {
                        assert_eq!(
                            checker.heap.relation(copied, *old).disjoint,
                            Condition::TRUE
                        );
                    }
                }
                source = output;
            }
            assert!(
                checker.heap.nodes.len() <= 9,
                "class identities grew with copy depth"
            );
            assert!(checker.unsupported.is_empty());
        }
    }
}
