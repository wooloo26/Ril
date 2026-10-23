use super::*;
use crate::sema::source_types::{SourceSchema, SourceTypeQueries};

#[test]
fn snapshots_share_payloads_and_keep_every_old_prefix_across_radix_heights() {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(4_000_000);
    let mut saved = Vec::new();
    for ordinal in 0..4100 {
        let scalar = if ordinal % 2 == 0 {
            SourceScalar::I8
        } else {
            SourceScalar::Bool
        };
        let id = builder
            .insert(SourceNode::Scalar(scalar), &mut work)
            .unwrap();
        assert_eq!(id.index as usize, ordinal);
        if matches!(
            ordinal,
            0 | 14 | 15 | 16 | 254 | 255 | 256 | 4094 | 4095 | 4096 | 4099
        ) {
            saved.push((
                id,
                scalar,
                builder.snapshot(&mut WorkLimit::new(2)).unwrap(),
            ));
        }
    }
    for (id, scalar, snapshot) in saved {
        assert_eq!(snapshot.get(id), Ok(&SourceNode::Scalar(scalar)));
        assert!(std::ptr::eq(
            snapshot.get(id).unwrap(),
            builder.get(id).unwrap()
        ));
        assert_eq!(snapshot.indexed_nodes().len(), id.index as usize + 1);
        assert_eq!(
            snapshot.get(SourceTypeId {
                index: id.index + 1,
                ..id
            }),
            Err(SourceTypesError::MissingNode)
        );
    }
    let before = builder.checkpoint();
    for _ in 0..64 {
        assert_eq!(
            builder
                .snapshot(&mut WorkLimit::new(2))
                .unwrap()
                .indexed_nodes()
                .len(),
            4100
        );
    }
    assert_eq!(builder.checkpoint(), before);
    assert!(matches!(
        builder.snapshot(&mut WorkLimit::new(0)),
        Err(SourceTypesError::BudgetExceeded)
    ));
}

fn shared_pending_leaf() -> (SourceBuilder, SourceTypes, SourceTypeId, SourceTypeId) {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(4096);
    let old = builder
        .insert(SourceNode::Scalar(SourceScalar::Bool), &mut work)
        .unwrap();
    let snapshot = builder.snapshot(&mut work).unwrap();
    let pending = builder.reserve(&mut work).unwrap();
    (builder, snapshot, old, pending)
}

#[test]
fn shared_path_definition_is_prepaid_atomic_and_accepts_the_exact_allowance() {
    let (mut builder, snapshot, old, pending) = shared_pending_leaf();
    assert!(matches!(
        builder.snapshot(&mut WorkLimit::new(2)),
        Err(SourceTypesError::MissingNode)
    ));
    let initial = 4096;
    let mut work = WorkLimit::new(initial);
    builder
        .define(pending, SourceNode::Scalar(SourceScalar::I8), &mut work)
        .unwrap();
    let used = initial - work.remaining();
    assert!(
        used > 16,
        "a shared pointer array must be admitted before copying it"
    );
    assert!(std::ptr::eq(
        snapshot.get(old).unwrap(),
        builder.get(old).unwrap()
    ));
    assert_eq!(snapshot.get(pending), Err(SourceTypesError::MissingNode));
    for units in 0..=used {
        let (mut builder, snapshot, old, pending) = shared_pending_leaf();
        let before = builder.checkpoint();
        let mut work = WorkLimit::new(units);
        let result = builder.define(pending, SourceNode::Scalar(SourceScalar::I8), &mut work);
        if units < used {
            assert_eq!(result, Err(SourceTypesError::BudgetExceeded));
            assert_eq!(builder.checkpoint(), before);
            assert_eq!(builder.get(pending), Err(SourceTypesError::MissingNode));
        } else {
            assert_eq!(result, Ok(()));
            assert_eq!(work.remaining(), 0);
            builder.snapshot(&mut WorkLimit::new(2)).unwrap();
        }
        assert!(std::ptr::eq(
            snapshot.get(old).unwrap(),
            builder.get(old).unwrap()
        ));
    }
}

#[test]
fn transactions_publish_only_after_commit_and_keep_recursive_shared_edges() {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(4096);
    let old = builder
        .insert(SourceNode::Scalar(SourceScalar::Bool), &mut work)
        .unwrap();
    let prefix = builder.snapshot(&mut work).unwrap();
    let transaction = builder.begin_transaction(&mut work).unwrap();
    assert!(matches!(
        builder.begin_transaction(&mut work),
        Err(SourceTypesError::TransactionOpen)
    ));
    let root = builder.reserve(&mut work).unwrap();
    builder
        .define(root, SourceNode::Tuple(vec![root, old, old]), &mut work)
        .unwrap();
    assert!(matches!(
        builder.snapshot(&mut work),
        Err(SourceTypesError::TransactionOpen)
    ));
    builder.commit_transaction(transaction).unwrap();
    let snapshot = builder.snapshot(&mut work).unwrap();
    assert!(
        matches!(snapshot.get(root), Ok(SourceNode::Tuple(items)) if items == &[root, old, old])
    );
    assert_eq!(snapshot.reachable([root], &mut work).unwrap().len(), 2);
    assert!(std::ptr::eq(
        prefix.get(old).unwrap(),
        snapshot.get(old).unwrap()
    ));
    let schema = SourceSchema::frozen_view(&snapshot, root, None, &mut work).unwrap();
    assert!(schema.equivalent(&schema, &mut work).unwrap());
}

#[test]
fn rollback_reuses_only_unpublished_ordinals_and_same_arena_import_checks_payload_identity() {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(4096);
    let old = builder
        .insert(SourceNode::Scalar(SourceScalar::Bool), &mut work)
        .unwrap();
    let prefix = builder.snapshot(&mut work).unwrap();
    let before = builder.checkpoint();
    let transaction = builder.begin_transaction(&mut work).unwrap();
    let tentative = builder
        .insert(SourceNode::Scalar(SourceScalar::I8), &mut work)
        .unwrap();
    assert!(matches!(
        builder.snapshot(&mut work),
        Err(SourceTypesError::TransactionOpen)
    ));
    // Deliberately bypass the private publication boundary to model a forged
    // same-arena snapshot. No public builder API can create this handle.
    let forged = SourceTypes {
        arena: builder.arena,
        nodes: builder.nodes.clone(),
    };
    builder.rollback_transaction(transaction).unwrap();
    assert_eq!(builder.checkpoint(), before);
    let reused = builder
        .insert(SourceNode::Scalar(SourceScalar::Str), &mut work)
        .unwrap();
    assert_eq!(tentative, reused);
    assert_eq!(prefix.get(tentative), Err(SourceTypesError::MissingNode));
    assert_eq!(
        builder.import_frozen(&forged, tentative, &mut work),
        Err(SourceTypesError::ForeignIdentity)
    );
    assert_eq!(builder.import_frozen(&prefix, old, &mut work), Ok(old));
    assert!(std::ptr::eq(
        prefix.get(old).unwrap(),
        builder.get(old).unwrap()
    ));
}

#[test]
fn same_arena_reads_and_reimports_never_append_nodes_or_waive_work() {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(4096);
    let root = builder.reserve(&mut work).unwrap();
    let leaf = builder
        .insert(SourceNode::Scalar(SourceScalar::I8), &mut work)
        .unwrap();
    builder
        .define(root, SourceNode::Tuple(vec![leaf, root, leaf]), &mut work)
        .unwrap();
    let snapshot = builder.snapshot(&mut work).unwrap();
    let before = builder.checkpoint();
    for _ in 0..128 {
        assert_eq!(
            builder.import_frozen(&snapshot, root, &mut WorkLimit::new(4)),
            Ok(root)
        );
    }
    assert_eq!(builder.checkpoint(), before);
    assert_eq!(
        builder.import_frozen(&snapshot, root, &mut WorkLimit::new(0)),
        Err(SourceTypesError::BudgetExceeded)
    );
    let other = SourceBuilder::new().unwrap().freeze(&mut work).unwrap();
    assert_eq!(
        builder.import_frozen(&other, root, &mut work),
        Err(SourceTypesError::ForeignIdentity)
    );
}

#[test]
fn failed_insert_cannot_leave_an_undefined_reservation_or_replace_a_published_node() {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(4096);
    let root = builder
        .insert(SourceNode::Scalar(SourceScalar::Bool), &mut work)
        .unwrap();
    let snapshot = builder.snapshot(&mut work).unwrap();
    let before = builder.checkpoint();
    assert_eq!(
        builder.insert(SourceNode::Scalar(SourceScalar::I8), &mut WorkLimit::new(1)),
        Err(SourceTypesError::BudgetExceeded)
    );
    assert_eq!(builder.checkpoint(), before);
    assert_eq!(
        builder.define(root, SourceNode::Scalar(SourceScalar::I8), &mut work),
        Err(SourceTypesError::AlreadyDefined)
    );
    assert!(std::ptr::eq(
        snapshot.get(root).unwrap(),
        builder.get(root).unwrap()
    ));
    builder.snapshot(&mut work).unwrap();
}

#[test]
fn reservation_limit_does_not_grow_and_incomplete_reservations_cannot_publish() {
    let mut builder = SourceBuilder::new().unwrap();
    let mut work = WorkLimit::new(100_000);
    for ordinal in 0..65_536 {
        assert_eq!(builder.reserve(&mut work).unwrap().index as usize, ordinal);
    }
    assert_eq!(
        builder.reserve(&mut work),
        Err(SourceTypesError::BudgetExceeded)
    );
    assert!(matches!(
        builder.snapshot(&mut work),
        Err(SourceTypesError::MissingNode)
    ));
}
