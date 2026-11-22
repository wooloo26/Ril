use crate::{GcRuntime, Object, Runtime, TypeDesc, Value};

#[test]
fn rooted_cycle_survives_allocations_and_reclaims_after_pop() {
    let mut gc = GcRuntime::new(true);
    gc.push_frame(2);
    let first = gc.alloc(Object::Array(Vec::new()));
    assert!(gc.set_root(0, first));
    let second = gc.alloc(Object::Array(vec![first]));
    if let Some(Object::Array(values)) = gc.object_mut(first) {
        values.push(second);
    } else {
        panic!("cycle root was collected while rooted");
    }
    gc.safepoint();
    assert_eq!(gc.live_objects(), 2);
    let copy = gc.clone_graph(first).unwrap();
    assert!(gc.set_root(1, copy));
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
    gc.pop_frame();
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
fn descriptors_trace_only_managed_words() {
    let mut gc = GcRuntime::new(true);
    gc.push_frame(2);
    let kept = gc.alloc(Object::Str("kept".into()));
    assert!(gc.set_root(0, kept));
    let dead = gc.alloc(Object::Str("dead".into()));
    let object = gc.alloc(Object::Words {
        layout: TypeDesc { reference_mask: 1 },
        words: vec![kept, dead],
    });
    assert!(gc.set_root(0, Value::UNIT));
    assert!(gc.set_root(1, object));
    gc.safepoint();
    assert!(gc.object(kept).is_some());
    assert!(gc.object(dead).is_none());
}

#[test]
fn drafts_update_an_isolated_graph() {
    let mut gc = GcRuntime::new(true);
    gc.push_frame(3);
    let base = gc.alloc(Object::Array(vec![Value::TRUE]));
    assert!(gc.set_root(0, base));
    let draft = gc.draft_begin(base).unwrap();
    assert!(gc.set_root(1, draft));
    let copy = gc.draft_read(draft).unwrap();
    let Some(Object::Array(items)) = gc.object_mut(copy) else {
        panic!("draft is not a copy of the array")
    };
    items.push(Value::FALSE);
    let committed = gc.draft_commit(draft).unwrap();
    assert!(gc.set_root(2, committed));
    gc.safepoint();
    assert_eq!(gc.inspect(base), "[true]");
    assert_eq!(gc.inspect(committed), "[true, false]");
    assert!(gc.draft_read(draft).is_err());
}

#[test]
fn draft_copy_through_a_cycle_keeps_the_original_suffix() {
    use crate::draft::DraftSlot;

    let mut gc = GcRuntime::new(true);
    gc.push_frame(3);
    let base = gc.alloc(Object::Tuple(vec![Value::UNIT, Value::FALSE]));
    assert!(gc.set_root(0, base));
    let Some(Object::Tuple(slots)) = gc.object_mut(base) else {
        panic!("base is not a tuple");
    };
    slots[0] = base;

    let draft = gc.draft_begin(base).unwrap();
    assert!(gc.set_root(1, draft));
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
    assert!(gc.set_root(2, published));
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
