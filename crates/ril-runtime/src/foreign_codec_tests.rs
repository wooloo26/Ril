use super::*;
use ril_runtime_api::foreign::VariantShape;
fn signature(arena: Vec<TypeNode>, parameters: Vec<TypeRef>, result: TypeRef) -> Signature {
    Signature {
        arena,
        parameters,
        result,
        callbacks: vec![],
    }
}
fn int(value: i64) -> Node {
    Node::Integer {
        decimal: value.to_string(),
        bits: 64,
        signed: true,
    }
}
#[test]
fn static_arguments_keep_phantom_values_and_validate_their_own_representations() {
    let schema = signature(vec![TypeNode::Unit], vec![], 0);
    let phantom = StaticArgument {
        name: "n".into(),
        value: StaticArgumentValue::Value {
            identity: "int:7".into(),
            value: StaticValue::Integer {
                decimal: "7".into(),
                bits: 64,
                signed: true,
            },
        },
    };
    let ty = StaticArgument {
        name: "T".into(),
        value: StaticArgumentValue::Type {
            identity: "unit".into(),
            schema: Some(0),
        },
    };
    validate_static_arguments(&schema, &[ty.clone(), phantom.clone()]).unwrap();
    assert!(validate_static_arguments(&schema, &[phantom.clone(), phantom]).is_err());
    for value in [
        StaticArgumentValue::Type {
            identity: "unit".into(),
            schema: Some(1),
        },
        StaticArgumentValue::Value {
            identity: "u8:256".into(),
            value: StaticValue::Integer {
                decimal: "256".into(),
                bits: 8,
                signed: false,
            },
        },
        StaticArgumentValue::Effects {
            identities: vec!["Read".into(), "Read".into()],
        },
        StaticArgumentValue::Capabilities {
            identities: vec![String::new()],
        },
    ] {
        assert!(
            validate_static_arguments(
                &schema,
                &[StaticArgument {
                    name: "x".into(),
                    value
                }]
            )
            .is_err()
        );
    }
}

#[test]
fn typed_graph_roundtrip_preserves_aliases_cycles_and_collection_roots() {
    let schema = signature(
        vec![
            TypeNode::Record([("next".into(), 1), ("value".into(), 2)].into()),
            TypeNode::Variant(vec![VariantShape {
                wire_tag: "Some".into(),
                runtime_tag: "Some".into(),
                fields: vec![0],
            }]),
            TypeNode::Integer {
                bits: 64,
                signed: true,
            },
        ],
        vec![0, 0],
        0,
    );
    validate_signature(&schema).unwrap();
    let graph = Graph {
        roots: vec![0, 0],
        nodes: vec![
            Node::Record(vec![
                Field {
                    name: "value".into(),
                    node: 2,
                },
                Field {
                    name: "next".into(),
                    node: 1,
                },
            ]),
            Node::Variant {
                tag: "Some".into(),
                fields: vec![0],
            },
            int(42),
        ],
    };
    let mut runtime = Runtime::default();
    let values = decode(&mut runtime, &schema, &graph, &[0, 0]).unwrap();
    assert_eq!(values[0], values[1]);
    runtime.root(0, values[0]).unwrap();
    runtime.statement_end();
    runtime.collect().unwrap();
    let next = runtime.field(values[0], "next").unwrap();
    assert!(
        matches!(runtime.heap.get(next).unwrap(), Object::Variant { fields, .. } if fields == &[values[0]])
    );
    let output = encode(&runtime, &schema, &[(values[0], 0), (values[1], 0)]).unwrap();
    assert_eq!(output.roots[0], output.roots[1]);
    assert_eq!(output.nodes.len(), 3);
    let copied = decode(&mut runtime, &schema, &output, &[0, 0]).unwrap();
    assert_ne!(values[0], copied[0]);
    assert!(
        runtime
            .heap
            .structurally_equal(values[0], copied[0])
            .unwrap()
    );
}

#[test]
fn opaque_and_plain_views_share_the_same_representation_after_decode_and_clone() {
    let schema = signature(
        vec![
            TypeNode::Record([("value".into(), 1)].into()),
            TypeNode::Integer {
                bits: 64,
                signed: true,
            },
            TypeNode::OpaqueData {
                wire_tag: "types::Secret".into(),
                runtime_tag: "RilSecret".into(),
                representation: 0,
            },
        ],
        vec![2, 0],
        0,
    );
    let mut runtime = Runtime::default();
    let value = runtime.int(42).unwrap();
    let record = runtime
        .allocate(Object::Record([("value".into(), value)].into()))
        .unwrap();
    let graph = encode(&runtime, &schema, &[(record, 2), (record, 0)]).unwrap();
    let values = decode(&mut runtime, &schema, &graph, &[2, 0]).unwrap();
    assert_eq!(values[0], values[1]);
    let pair = runtime.allocate(Object::Tuple(values)).unwrap();
    let copy = runtime.copy(pair).unwrap();
    let values = runtime.sequence(copy).unwrap();
    let changed = runtime.int(99).unwrap();
    runtime
        .set_field(values[0], "value".into(), changed)
        .unwrap();
    assert_eq!(runtime.field(values[1], "value").unwrap(), changed);
    assert_eq!(runtime.field(record, "value").unwrap(), value);
}

#[test]
fn deep_opaque_envelopes_resolve_once_and_share_one_managed_representation() {
    const DEPTH: u32 = 20_000;
    let mut arena = Vec::new();
    let mut nodes = Vec::new();
    for index in 0..DEPTH {
        let tag = format!("Layer{index}");
        arena.push(TypeNode::OpaqueData {
            wire_tag: tag.clone(),
            runtime_tag: tag.clone(),
            representation: index + 1,
        });
        nodes.push(Node::Nominal {
            tag,
            payload: index + 1,
        });
    }
    arena.push(TypeNode::Integer {
        bits: 64,
        signed: true,
    });
    nodes.push(int(42));
    let schema = signature(arena, vec![0, 0, DEPTH], DEPTH);
    let graph = Graph {
        nodes,
        roots: vec![0, 0, DEPTH],
    };
    let mut runtime = Runtime::default();
    let values = decode(&mut runtime, &schema, &graph, &[0, 0, DEPTH]).unwrap();
    assert_eq!(values, vec![values[0]; 3]);
    assert_eq!(runtime.heap.live_objects(), 1);
    runtime.root(0, values[0]).unwrap();
    runtime.statement_end();
    runtime.collect().unwrap();
    assert_eq!(runtime.as_integer(values[0]).unwrap(), 42);
}

#[test]
fn an_opaque_cycle_in_a_later_root_is_rejected_before_any_managed_allocation() {
    let schema = signature(
        vec![
            TypeNode::Unit,
            TypeNode::OpaqueData {
                wire_tag: "Loop".into(),
                runtime_tag: "Loop".into(),
                representation: 1,
            },
        ],
        vec![0, 1],
        0,
    );
    let graph = Graph {
        roots: vec![0, 1],
        nodes: vec![
            Node::Unit,
            Node::Nominal {
                tag: "Loop".into(),
                payload: 2,
            },
            Node::Nominal {
                tag: "Loop".into(),
                payload: 1,
            },
        ],
    };
    let mut runtime = Runtime::default();
    assert!(decode(&mut runtime, &schema, &graph, &[0, 1]).is_err());
    assert_eq!(runtime.heap.live_objects(), 0);
}

#[test]
fn malformed_and_under_refined_graphs_are_rejected_before_allocation() {
    let schema = signature(
        vec![
            TypeNode::Array {
                element: 1,
                length: Some(2),
            },
            TypeNode::Integer {
                bits: 64,
                signed: true,
            },
        ],
        vec![0],
        0,
    );
    let mut runtime = Runtime::default();
    let before = runtime.heap.live_objects();
    for graph in [
        Graph {
            nodes: vec![Node::Array(vec![1]), int(2)],
            roots: vec![0],
        },
        Graph {
            nodes: vec![Node::Array(vec![1, 1]), Node::String("not int".into())],
            roots: vec![0],
        },
        Graph {
            nodes: vec![Node::Array(vec![2, 2])],
            roots: vec![0],
        },
    ] {
        assert!(decode(&mut runtime, &schema, &graph, &[0]).is_err());
    }
    assert_eq!(runtime.heap.live_objects(), before);
    let looped = signature(vec![TypeNode::Immutable(0)], vec![0], 0);
    assert!(validate_signature(&looped).is_err());
    let opaque = signature(
        vec![TypeNode::OpaqueData {
            wire_tag: "loop".into(),
            runtime_tag: "loop".into(),
            representation: 0,
        }],
        vec![0],
        0,
    );
    assert!(
        decode(
            &mut runtime,
            &opaque,
            &Graph {
                nodes: vec![Node::Nominal {
                    tag: "loop".into(),
                    payload: 0
                }],
                roots: vec![0]
            },
            &[0]
        )
        .is_err()
    );
}

#[test]
fn cyclic_provider_map_keys_fail_without_recursive_key_construction() {
    let schema = signature(
        vec![
            TypeNode::Map { key: 1, value: 2 },
            TypeNode::Nominal {
                wire_tag: "Key".into(),
                runtime_tag: "Key".into(),
                payload: 1,
            },
            TypeNode::Unit,
        ],
        vec![0],
        0,
    );
    let graph = Graph {
        roots: vec![0],
        nodes: vec![
            Node::Map(vec![(1, 2)]),
            Node::Nominal {
                tag: "Key".into(),
                payload: 1,
            },
            Node::Unit,
        ],
    };
    let error = decode(&mut Runtime::default(), &schema, &graph, &[0]).unwrap_err();
    assert_eq!(error.tag, ril_runtime_api::abi::OutcomeTag::LanguagePanic);
    let mut runtime = Runtime::default();
    let mut value = runtime.heap.allocate(Object::Unit).unwrap();
    for _ in 0..20_000 {
        value = runtime
            .heap
            .allocate(Object::Nominal {
                tag: "Key".into(),
                payload: value,
            })
            .unwrap();
    }
    let key = runtime.key(value).unwrap();
    let mut map = OrderedMap::default();
    map.set(key.clone(), value, value);
    assert_eq!(map.get(&key), Some(value));
}

#[test]
fn maps_sets_and_ranges_keep_order_and_reject_duplicate_value_keys() {
    let schema = signature(
        vec![
            TypeNode::Map { key: 1, value: 2 },
            TypeNode::String,
            TypeNode::Range(3),
            TypeNode::Integer {
                bits: 64,
                signed: true,
            },
            TypeNode::Set(1),
        ],
        vec![0, 4],
        0,
    );
    let graph = Graph {
        roots: vec![0, 5],
        nodes: vec![
            Node::Map(vec![(1, 3), (2, 3)]),
            Node::String("b".into()),
            Node::String("a".into()),
            Node::Range {
                lower: Some(4),
                upper: None,
                inclusive: false,
            },
            int(7),
            Node::Set(vec![2, 1]),
        ],
    };
    let mut runtime = Runtime::default();
    let values = decode(&mut runtime, &schema, &graph, &[0, 4]).unwrap();
    let Object::Map(map) = runtime.heap.get(values[0]).unwrap() else {
        panic!("map");
    };
    let entries: Vec<_> = map.iter().collect();
    assert_eq!(runtime.as_string(*entries[0].0).unwrap(), "b");
    assert_eq!(entries[0].1, entries[1].1);
    let output = encode(&runtime, &schema, &[(values[0], 0), (values[1], 4)]).unwrap();
    assert!(decode(&mut runtime, &schema, &output, &[0, 4]).is_ok());
    let mut duplicate = graph;
    duplicate.nodes[2] = Node::String("b".into());
    assert!(decode(&mut runtime, &schema, &duplicate, &[0, 4]).is_err());
}
