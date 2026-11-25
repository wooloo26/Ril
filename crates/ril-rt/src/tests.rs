use crate::{GcRuntime, Object, Runtime, Value};
use num_bigint::BigInt;

#[test]
fn small_int_arithmetic_promotes_and_demotes_without_allocating_in_range() {
    let mut gc = GcRuntime::new(true);
    let minimum: Value = gc.int(BigInt::from(-(1_i64 << 62))).into();
    let maximum: Value = gc.int(BigInt::from((1_i64 << 62) - 1)).into();
    let one: Value = gc.int(BigInt::from(1)).into();
    assert_eq!(minimum.small_int(), Some(-(1_i64 << 62)));
    assert_eq!(maximum.small_int(), Some((1_i64 << 62) - 1));
    assert_eq!(
        gc.binary("+", minimum, maximum).unwrap().small_int(),
        Some(-1)
    );
    assert_eq!(gc.binary("/", minimum, one).unwrap(), minimum);
    assert_eq!(gc.unary("~", minimum).unwrap(), maximum);
    assert_eq!(gc.live_objects(), 0);

    let promoted = gc.binary("+", maximum, one).unwrap();
    assert!(
        matches!(gc.object(promoted), Some(Object::Int(number)) if *number == BigInt::from(1_i64 << 62))
    );
    assert_eq!(gc.binary("-", promoted, one).unwrap(), maximum);
    let demoted = gc.binary(">>", promoted, one).unwrap();
    assert_eq!(demoted.small_int(), Some(1_i64 << 61));
    gc.safepoint();
    assert_eq!(gc.live_objects(), 0);
}

#[test]
fn rooted_cycle_survives_allocations_and_reclaims_after_unpin() {
    let mut gc = GcRuntime::new(true);
    let first = gc.alloc(Object::Array(Vec::new()));
    gc.pin(first);
    let second = gc.alloc(Object::Array(vec![first]));
    if let Some(Object::Array(values)) = gc.object_mut(first) {
        values.push(second);
    } else {
        panic!("cycle root was collected while rooted");
    }
    gc.safepoint();
    assert_eq!(gc.live_objects(), 2);
    let copy = gc.clone_graph(first).unwrap();
    gc.pin(copy);
    assert_ne!(copy, first);
    assert!(gc.equal(copy, first).unwrap());
    let Some(Object::Array(parts)) = gc.object(copy) else {
        panic!("no copy after cloning")
    };
    let [other] = parts.as_slice() else {
        panic!("invalid clone shape")
    };
    assert_ne!(*other, second);
    let Some(Object::Array(children)) = gc.object(*other) else {
        panic!("no interior copy")
    };
    assert_eq!(children, &[copy]);
    assert_eq!(gc.inspect(copy), "[[...]]");
    gc.unpin(first);
    gc.unpin(copy);
    gc.safepoint();
    assert_eq!(gc.live_objects(), 0);
}

#[test]
fn deep_graph_clone_and_equality_use_explicit_worklists() {
    let mut gc = GcRuntime::new(false);
    let mut root = Value::UNIT;
    let depth = if cfg!(miri) { 64 } else { 4096 };
    for _ in 0..depth {
        root = gc.alloc(Object::Array(vec![root]));
    }
    let copy = gc.clone_graph(root).unwrap();
    assert_ne!(root, copy);
    assert!(gc.equal(root, copy).unwrap());
    gc.collect(Vec::new());
    assert_eq!(gc.live_objects(), 0);
}

#[test]
fn cloned_data_keeps_a_callable_and_its_environment_alive() {
    let mut gc = GcRuntime::new(true);
    let handler = gc.alloc(Object::Closure {
        function: std::ptr::without_provenance(1),
        arity: 0,
        environment: Value::UNIT,
        evidence: Value::UNIT,
    });
    let evidence = gc.alloc(Object::Evidence {
        parent: Value::UNIT,
        operation: 1,
        handler,
    });
    gc.pin(evidence);
    let captured = gc.alloc(Object::Tuple(vec![Value::TRUE]));
    let closure = gc.alloc(Object::Closure {
        function: std::ptr::without_provenance(2),
        arity: 0,
        environment: captured,
        evidence,
    });
    assert!(gc.clone_graph(closure).is_err());
    let original = gc.alloc(Object::Array(vec![closure]));
    let copy = gc.clone_graph(original).unwrap();
    gc.unpin(evidence);
    gc.pin(copy);
    gc.safepoint();
    assert!(gc.object(original).is_none());
    assert!(matches!(gc.object(copy), Some(Object::Array(values)) if values == &[closure]));
    assert!(gc.object(captured).is_some());
    assert!(gc.object(evidence).is_some());
    assert!(gc.object(handler).is_some());
    gc.unpin(copy);
    gc.safepoint();
    assert_eq!(gc.live_objects(), 0);
}

#[test]
fn drafts_update_an_isolated_graph() {
    let mut gc = GcRuntime::new(true);
    let base = gc.alloc(Object::Array(vec![Value::TRUE]));
    gc.pin(base);
    let draft = gc.draft_begin(base).unwrap();
    gc.pin(draft);
    let copy = gc.draft_read(draft).unwrap();
    let Some(Object::Array(items)) = gc.object_mut(copy) else {
        panic!("draft is not a copy of the array")
    };
    items.push(Value::FALSE);
    let committed = gc.draft_commit(draft).unwrap();
    gc.pin(committed);
    gc.safepoint();
    assert_eq!(gc.inspect(base), "[true]");
    assert_eq!(gc.inspect(committed), "[true, false]");
    assert!(gc.draft_read(draft).is_err());
    gc.unpin(base);
    gc.unpin(draft);
    gc.unpin(committed);
}

#[test]
fn draft_copy_through_a_cycle_keeps_the_original_suffix() {
    use crate::draft::DraftSlot;

    let mut gc = GcRuntime::new(true);
    let base = gc.alloc(Object::Tuple(vec![Value::UNIT, Value::FALSE]));
    gc.pin(base);
    let Some(Object::Tuple(slots)) = gc.object_mut(base) else {
        panic!("base is not a tuple");
    };
    slots[0] = base;

    let draft = gc.draft_begin(base).unwrap();
    gc.pin(draft);
    let root = gc.draft_read(draft).unwrap();
    let nested = gc.draft_child(root, DraftSlot::Element(0), base).unwrap();
    assert_ne!(root, nested);
    assert_ne!(base, nested);
    assert_eq!(
        gc.draft_child(root, DraftSlot::Element(0), nested),
        Some(nested)
    );
    let Some(Object::Tuple(slots)) = gc.object_mut(nested) else {
        panic!("updated occurrence is not a tuple");
    };
    slots[1] = Value::TRUE;

    let published = gc.draft_commit(draft).unwrap();
    gc.pin(published);
    gc.safepoint();
    assert!(
        matches!(gc.object(base), Some(Object::Tuple(slots)) if slots == &[base, Value::FALSE])
    );
    assert!(
        matches!(gc.object(nested), Some(Object::Tuple(slots)) if slots == &[base, Value::TRUE])
    );
    assert!(
        matches!(gc.object(published), Some(Object::Tuple(slots)) if slots == &[nested, Value::FALSE])
    );
    assert!(gc.draft_nodes.is_empty());
    gc.unpin(base);
    gc.unpin(draft);
    gc.unpin(published);
}

#[test]
fn cleanup_can_run_with_a_suspended_unwind() {
    let mut runtime = Runtime::default();
    runtime.raise("first");
    runtime.enter_cleanup();
    assert_eq!(runtime.unwinding, 0);
    runtime.enter_cleanup();
    runtime.leave_cleanup();
    assert_eq!(runtime.unwinding, 0);
    runtime.leave_cleanup();
    assert_eq!(runtime.unwinding, 1);
    assert_eq!(runtime.take_panic().as_deref(), Some("first"));
}

#[test]
#[allow(
    unsafe_code,
    reason = "verify intrusive stack RootFrameHeader tracing under Miri"
)]
fn intrusive_stack_root_frame_preserves_heap_objects_and_low_bit_tags() {
    #[repr(C)]
    struct Frame2 {
        header: crate::RootFrameHeader,
        slots: [Value; 2],
    }

    let mut gc = GcRuntime::new(true);
    let min_small = -(1_i64 << 62);
    let max_small = (1_i64 << 62) - 1;
    assert_eq!(
        Value::from_small_int(min_small).and_then(Value::small_int),
        Some(min_small)
    );
    assert_eq!(
        Value::from_small_int(max_small).and_then(Value::small_int),
        Some(max_small)
    );
    assert_eq!(Value::from_small_int(min_small - 1), None);
    assert_eq!(Value::from_small_int(max_small + 1), None);
    assert_eq!(Value::UNIT.0 & 0b111, 0);
    assert_eq!(Value::FALSE.0 & 0b111, 0b010);
    assert_eq!(Value::TRUE.0 & 0b111, 0b110);

    let keep = gc.alloc(Object::Str("kept".into()));
    assert_eq!(keep.0 & 0b111, 0);
    assert_ne!(keep.0, 0);
    let mut frame = Frame2 {
        header: crate::RootFrameHeader {
            prev: std::ptr::null_mut(),
            count: 2,
        },
        slots: [keep, Value::UNIT],
    };
    gc.top_frame = (&raw mut frame).cast::<crate::RootFrameHeader>();
    let _garbage = gc.alloc(Object::Str("ephemeral".into()));
    gc.collect(Vec::new());
    assert!(matches!(gc.object(keep), Some(Object::Str(s)) if s.as_str() == "kept"));
    gc.top_frame = std::ptr::null_mut();
    gc.collect(Vec::new());
    assert!(gc.object(keep).is_none());
}

#[test]
fn bisimulation_invariant_map_hash_and_slab_recycling() {
    let mut gc = GcRuntime::new(false);

    // 1-node cycle `a = [a]` and 2-node cycle `b1 = [b2], b2 = [b1]` are coinductively equal.
    let a = gc.alloc(Object::Array(Vec::new()));
    gc.pin(a);
    if let Some(Object::Array(items)) = gc.object_mut(a) {
        items.push(a);
    }
    let b1 = gc.alloc(Object::Array(Vec::new()));
    gc.pin(b1);
    let b2 = gc.alloc(Object::Array(Vec::new()));
    gc.pin(b2);
    if let Some(Object::Array(items)) = gc.object_mut(b1) {
        items.push(b2);
    }
    if let Some(Object::Array(items)) = gc.object_mut(b2) {
        items.push(b1);
    }

    assert_eq!(gc.equal(a, b1), Ok(true));
    assert_eq!(gc.bisim_hash(a), gc.bisim_hash(b1));

    // Inserting under `a` and looking up with `b1` MUST hit the exact same bucket in RilMap!
    let mut map = crate::RilMap::new();
    let ha = gc.bisim_hash(a);
    let val = gc.int_i64(42);
    map.push_new(ha, a, val);
    let hb = gc.bisim_hash(b1);
    let found = map.find_index(hb, |stored| gc.equal(stored, b1).unwrap_or(false));
    assert_eq!(found, Some(0));
    assert_eq!(map.get_entry(0), Some((a, val)));

    // Verify O(1) RilStr metadata cache for ASCII and multi-byte UTF-8.
    let ascii = crate::RilStr::new("hello world".into());
    assert!(ascii.is_ascii());
    assert_eq!(ascii.scalar_len(), 11);
    assert_eq!(ascii.scalar_at(6), Some('w'));
    assert_eq!(ascii.slice_scalars(0, 5).as_deref(), Some("hello"));

    let utf8 = crate::RilStr::new("a中b".into());
    assert!(!utf8.is_ascii());
    assert_eq!(utf8.scalar_len(), 3);
    assert_eq!(utf8.scalar_at(1), Some('中'));
    assert_eq!(utf8.slice_scalars(1, 3).as_deref(), Some("中b"));

    // Verify slab slot recycling reclaims unreachable objects without unbounded growth.
    gc.unpin(a);
    gc.unpin(b1);
    gc.unpin(b2);
    gc.collect(Vec::new());
    assert_eq!(gc.live_objects(), 0);
    for _ in 0..200 {
        let _ = gc.alloc(Object::Str("ephemeral".into()));
    }
    gc.collect(Vec::new());
    assert_eq!(gc.live_objects(), 0);
}
