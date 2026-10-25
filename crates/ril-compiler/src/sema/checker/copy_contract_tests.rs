use super::*;

#[test]
fn bound_builtin_capture_graph_is_not_an_environment_free_copy_certificate() {
    for (field, ty, permission) in [
        (
            "fork",
            Ty::Named("Concurrent::Scope".into()),
            Permission::Write,
        ),
        (
            "fork",
            Ty::Named("Concurrent::Scope".into()),
            Permission::Read,
        ),
        (
            "join",
            Ty::Applied {
                constructor: "Concurrent::Task".into(),
                arguments: vec![TypeArgument::Type(Box::new(Ty::Int("int".into())))],
            },
            Permission::Read,
        ),
    ] {
        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(Env::new(), false);
        let mut receiver = checker.formal_value(ty, 0, span(), &mut BTreeSet::new());
        receiver.permission = permission;
        let bound = checker
            .concurrent_receiver(&receiver, field, span(), &mut frame)
            .unwrap();
        let root = *bound.origins.nodes.first().unwrap();
        checker.clone_value(&bound, span(), &mut frame, false);
        let proof = checker.copy_boundaries.last().unwrap();
        assert_eq!(
            proof.constituents[0].qualification,
            Constituent::Rejected(Rejection::RetainedEnvironment)
        );
        assert!(proof.output.is_none() && proof.output_nodes.is_empty());
        let captured = proof
            .nodes
            .iter()
            .find(|node| node.origin == root)
            .unwrap()
            .fields
            .iter()
            .find(|(slot, _)| *slot == Slot::Capture(0))
            .unwrap();
        assert_eq!(captured.1.origins, receiver.origins);
        assert_eq!(captured.1.permission, permission);
        assert_eq!(captured.1.ty, receiver.ty);
        assert!(
            proof
                .constituents
                .iter()
                .any(|part| part.qualification == Constituent::Rejected(Rejection::Resource)),
            "the captured receiver is still checked independently"
        );

        // The same builtin identity without any captured receiver is a
        // different value. Names alone prove neither case's environment.
        let mut unbound = Value::scalar(Ty::Callable(vec![], Box::new(Ty::Unit)), None, CauseId(0));
        unbound.callables = bound.callables.clone();
        assert_eq!(
            checker.copy_shallow_qualification(&unbound, &unbound.ty),
            Constituent::EnvironmentFreeCallable
        );
    }
}

#[test]
fn opaque_collection_members_require_a_complete_witness_and_survive_no_unknown_write() {
    let mut checker = Checker::new(FileId(0));
    let frame = checker.frame(Env::new(), false);
    let element = Ty::Int("int".into());
    let node = checker.allocate(span(), 0, frame.owner);
    let source = Value::reference(
        Ty::Applied {
            constructor: "Deque::Deque".into(),
            arguments: vec![TypeArgument::Type(Box::new(element.clone()))],
        },
        node,
        CauseId(0),
    );
    checker.store_field(
        node,
        Slot::AnyIndex,
        Value::scalar(element, None, CauseId(0)),
    );
    assert!(
        !checker
            .copy_boundary(&source, span(), &frame, false)
            .requirements
            .is_empty(),
        "an observed element and a fresh shell are not a whole-member witness"
    );
    checker.store_field(
        node,
        Slot::Field("$members".into()),
        Value::scalar(Ty::Unit, Some(Constant::Unit), CauseId(0)),
    );
    assert!(
        checker
            .copy_boundary(&source, span(), &frame, false)
            .requirements
            .is_empty()
    );
    checker.mark_heap_uncertain(std::slice::from_ref(&source));
    assert!(
        !checker
            .copy_boundary(&source, span(), &frame, false)
            .requirements
            .is_empty()
    );
    checker.store_field(
        node,
        Slot::AnyIndex,
        Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
    );
    assert!(
        !checker
            .copy_boundary(&source, span(), &frame, false)
            .requirements
            .is_empty(),
        "one known insertion cannot repair an unobserved older family"
    );
}

#[test]
fn opaque_membership_witness_does_not_remove_comparator_or_multiplicity_requirements() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let node = checker.allocate(span(), 0, frame.owner);
    let mut source = Value::reference(
        Ty::Applied {
            constructor: "Heap::Heap".into(),
            arguments: vec![TypeArgument::Type(Box::new(Ty::Int("int".into())))],
        },
        node,
        CauseId(0),
    );
    checker.store_field(
        node,
        Slot::Field("$members".into()),
        Value::scalar(Ty::Unit, Some(Constant::Unit), CauseId(0)),
    );
    assert!(
        !checker
            .copy_boundary(&source, span(), &frame, false)
            .requirements
            .is_empty(),
        "Heap retains a real comparator witness"
    );
    let mut comparator = Value::scalar(
        Ty::Callable(
            vec![Ty::Int("int".into()); 2],
            Box::new(Ty::Named("Order::Ordering".into())),
        ),
        None,
        CauseId(0),
    );
    comparator.callables.push(Callable::Symbolic(0, vec![]));
    checker.store_field(node, Slot::Field("$compare".into()), comparator);
    assert!(
        checker
            .copy_boundary(&source, span(), &frame, false)
            .constituents
            .iter()
            .any(|part| part.qualification
                == Constituent::Deferred(AbstractMember::CallableEnvironment))
    );
    source.ty = Ty::Applied {
        constructor: "Deque::Deque".into(),
        arguments: vec![TypeArgument::Type(Box::new(Ty::Record(BTreeMap::new())))],
    };
    checker
        .fields
        .remove(&(node, Slot::Field("$compare".into())));
    checker.heap.nodes[node.0 as usize]
        .fields
        .remove(&Slot::Field("$compare".into()));
    let child = checker.heap.symbolic(Pivot(1), frame.owner, CauseId(0));
    checker.heap.set_relation(child, child, Relation::UNKNOWN);
    checker.store_field(
        node,
        Slot::AnyIndex,
        Value::reference(Ty::Record(BTreeMap::new()), child, CauseId(0)),
    );
    checker.clone_value(&source, span(), &mut frame, false);
    assert!(checker.copy_boundaries.last().unwrap().output.is_none());
    assert_eq!(checker.heap.relation(child, child), Relation::UNKNOWN);
    assert!(
        checker
            .unsupported
            .iter()
            .any(|feature| feature.description.contains("summarized nonordinary graph"))
    );
}

fn span() -> Span {
    Span {
        file: FileId(0),
        start: 1,
        end: 2,
    }
}

#[test]
fn generic_copy_retains_identity_and_has_no_verified_output() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    frame.definition = Some(DefinitionId(7));
    let source = checker.formal_value(
        Ty::Generic("owner:T".into()),
        0,
        span(),
        &mut BTreeSet::new(),
    );
    checker.clone_value(&source, span(), &mut frame, false);
    let boundary = checker.copy_boundaries.last().unwrap();
    assert_eq!(boundary.owner, Some(DefinitionId(7)));
    assert_eq!(boundary.source.origins, source.origins);
    assert!(boundary.output.is_none());
    assert!(boundary.constituents.iter().any(|part| part.qualification
        == crate::sema::copy_eligibility::Constituent::Deferred(
            crate::sema::copy_eligibility::AbstractMember::DataBinder("owner:T".into())
        )));
    assert!(frame.obligations.copy_boundaries.contains(&boundary.id));
}

#[test]
fn missing_result_payloads_keep_each_latent_or_forbidden_member() {
    let mut checker = Checker::new(FileId(0));
    let frame = checker.frame(Env::new(), false);
    let payload = Ty::Record(
        [
            ("a".into(), (false, Ty::Generic("A".into()))),
            ("b".into(), (false, Ty::Generic("B".into()))),
            (
                "call".into(),
                (false, Ty::Callable(vec![], Box::new(Ty::Unit))),
            ),
            ("file".into(), (false, Ty::Named("File::Handle".into()))),
        ]
        .into(),
    );
    // This control deliberately models a partial Result. Ordinary formal
    // construction now retains both payload graphs, so it is not a missing
    // payload fixture anymore.
    let source = checker.formal_result(Ty::Result(Box::new(payload), Box::new(Ty::Str)), span());
    assert!(source.result_success.is_none() && source.result_error.is_none());
    let boundary = checker.copy_boundary(&source, span(), &frame, false);
    for qualification in [
        Constituent::Deferred(AbstractMember::DataBinder("A".into())),
        Constituent::Deferred(AbstractMember::DataBinder("B".into())),
        Constituent::Deferred(AbstractMember::CallableEnvironment),
        Constituent::Rejected(Rejection::Resource),
    ] {
        assert!(
            boundary
                .constituents
                .iter()
                .any(|part| part.qualification == qualification),
            "{qualification:?}"
        );
    }
    assert!(
        boundary
            .constituents
            .iter()
            .filter(|part| !matches!(part.qualification, Constituent::Ordinary))
            .all(|part| part.path.contains(&CopyProjection::ResultSuccess))
    );
    assert!(boundary.output.is_none());
}

#[test]
fn one_observed_collection_member_cannot_certify_unobserved_callable_environments() {
    let mut checker = Checker::new(FileId(0));
    let frame = checker.frame(Env::new(), false);
    let node = checker.heap.symbolic(Pivot(0), frame.owner, CauseId(0));
    let callable = Ty::Callable(vec![], Box::new(Ty::Unit));
    let mut observed = Value::scalar(callable.clone(), None, CauseId(0));
    observed.callables.push(Callable::Builtin("assert".into()));
    checker.store_field(node, Slot::Index(0), observed);
    let source = Value::reference(Ty::Array(Box::new(callable)), node, CauseId(0));
    let incomplete = checker.copy_boundary(&source, span(), &frame, false);
    assert!(incomplete.constituents.iter().any(
        |part| part.qualification == Constituent::Deferred(AbstractMember::CallableEnvironment)
    ));
    checker.array_lengths.insert(node, Some(1));
    let complete = checker.copy_boundary(&source, span(), &frame, false);
    assert!(complete.requirements.is_empty());
}

#[test]
fn production_qualification_matches_all_three_object_graphs() {
    // Independent transitive-closure oracle: object types and edges are chosen
    // concretely, not from the qualifier's graph walk or copy-class identity.
    for bits in 0u16..512 {
        for forbidden in 0..3 {
            let mut checker = Checker::new(FileId(0));
            let frame = checker.frame(Env::new(), false);
            let nodes: Vec<_> = (0..3)
                .map(|index| checker.heap.symbolic(Pivot(index), frame.owner, CauseId(0)))
                .collect();
            let kind = |index| {
                if index == forbidden {
                    Ty::Named("File::Handle".into())
                } else {
                    Ty::Record(BTreeMap::new())
                }
            };
            let mut reach = [[false; 3]; 3];
            for a in 0..3 {
                reach[a][a] = true;
                for b in 0..3 {
                    if bits & (1 << (a * 3 + b)) != 0 {
                        reach[a][b] = true;
                        let mut child = Value::reference(kind(b), nodes[b], CauseId(0));
                        child.permission = Permission::Read;
                        checker.store_field(nodes[a], Slot::Field(format!("edge{b}")), child);
                    }
                }
            }
            for mid in 0..3 {
                for a in 0..3 {
                    for b in 0..3 {
                        reach[a][b] |= reach[a][mid] && reach[mid][b];
                    }
                }
            }
            for root in 0..3 {
                let source = Value::reference(kind(root), nodes[root], CauseId(0));
                let boundary = checker.copy_boundary(&source, span(), &frame, false);
                let rejected = boundary
                    .constituents
                    .iter()
                    .any(|part| part.qualification == Constituent::Rejected(Rejection::Resource));
                assert_eq!(
                    rejected, reach[root][forbidden],
                    "edges={bits}, root={root}, forbidden={forbidden}"
                );
                assert!(
                    boundary
                        .nodes
                        .iter()
                        .flat_map(|node| &node.fields)
                        .all(|(_, field)| field.permission == Permission::Read)
                );
            }
        }
    }
}

#[test]
fn pending_copy_identity_survives_fresh_shells_projections_and_lost_sum_witnesses() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let abstract_source =
        checker.formal_value(Ty::Generic("T".into()), 0, span(), &mut BTreeSet::new());
    let conditional = checker.clone_value(&abstract_source, span(), &mut frame, false);
    let dependency = *conditional.pending_copies.first().unwrap();
    let mut scalar = Value::scalar(Ty::Int("int".into()), None, CauseId(0));
    scalar.pending_copies.insert(dependency);
    let node = checker.allocate(span(), 0, frame.owner);
    checker.store_field(node, Slot::Field("item".into()), scalar.clone());
    let shell = Value::reference(
        Ty::Record([("item".into(), (false, scalar.ty.clone()))].into()),
        node,
        CauseId(0),
    );
    assert_eq!(
        checker.pending_copy_dependencies(&shell),
        [dependency].into()
    );
    assert!(!checker.construction_can_publish(&shell));
    let projected = checker.project(&shell, Slot::Field("item".into()), span(), &mut frame, true);
    assert_eq!(projected.pending_copies, [dependency].into());
    assert!(!checker.require_copy_dependencies(&shell, span(), "parallel transfer"));

    let mut option = Value::scalar(Ty::Optional(Box::new(scalar.ty.clone())), None, CauseId(0));
    option.option_payload = Some(Box::new(scalar));
    let unknown = Value::scalar(option.ty.clone(), None, CauseId(0));
    let joined = option.join(&unknown, 1, CauseId(0));
    assert!(joined.option_payload.is_none());
    assert_eq!(joined.pending_copies, [dependency].into());
    let result = checker.clone_value(&joined, span(), &mut frame, false);
    assert!(result.pending_copies.contains(&dependency));
    let copied = checker.copy_boundaries.last().unwrap();
    assert!(copied.output.is_none());
    assert!(
        copied
            .requirements
            .iter()
            .any(|requirement| requirement.kind == CopyRequirementKind::PriorBoundary(dependency))
    );
}
