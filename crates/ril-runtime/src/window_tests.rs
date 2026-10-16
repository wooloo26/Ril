use super::*;
fn range(
    runtime: &mut Runtime,
    lower: Option<i128>,
    upper: Option<i128>,
    inclusive: bool,
) -> Handle {
    let lower = lower.map(|value| runtime.int(value).unwrap());
    let upper = upper.map(|value| runtime.int(value).unwrap());
    runtime
        .allocate(Object::Range {
            lower,
            upper,
            inclusive,
        })
        .unwrap()
}
#[test]
fn nested_windows_observe_replacement_and_keep_fixed_length_through_collection() {
    let mut runtime = Runtime::default();
    let values = [1, 2, 3]
        .into_iter()
        .map(|value| runtime.int(value).unwrap())
        .collect();
    let source = runtime.allocate(Object::Array(values)).unwrap();
    let full = range(&mut runtime, None, None, false);
    let window = runtime.index(source, full, false).unwrap();
    let middle = range(&mut runtime, Some(1), Some(1), true);
    let selected = runtime.index(window, middle, false).unwrap();
    runtime.root(0, selected).unwrap();
    let one = runtime.int(1).unwrap();
    let replacement = runtime.int(9).unwrap();
    runtime.set_index(source, one, replacement).unwrap();
    runtime.statement_end();
    runtime.collect().unwrap();
    let zero = runtime.int(0).unwrap();
    assert_eq!(runtime.index(selected, zero, false).unwrap(), replacement);
    assert_eq!(runtime.length(selected).unwrap(), 1);
    assert_eq!(runtime.format(selected).unwrap(), "[9]");
    let contained = runtime.contains(replacement, selected).unwrap();
    assert!(runtime.truth(contained).unwrap());
    let cursor = runtime.iterator(selected).unwrap();
    assert_eq!(runtime.iterator_next(cursor).unwrap(), Some(replacement));
    assert_eq!(runtime.iterator_next(cursor).unwrap(), None);
    let array = runtime.allocate(Object::Array(vec![replacement])).unwrap();
    assert!(runtime.heap.structurally_equal(selected, array).unwrap());
    let Object::ArrayWindow {
        backing,
        start,
        len,
    } = runtime.heap.get(selected).unwrap()
    else {
        panic!("window");
    };
    assert_eq!((*backing, *start, *len), (source, 1, 1));
}
#[test]
fn bounds_are_not_clamped_and_omitted_inclusive_end_is_exclusive() {
    let mut runtime = Runtime::default();
    let one = runtime.int(1).unwrap();
    let source = runtime.allocate(Object::Array(vec![one; 3])).unwrap();
    for (lower, upper, inclusive) in [
        (Some(-1), Some(1), false),
        (Some(2), Some(1), false),
        (Some(0), Some(4), false),
        (Some(0), Some(3), true),
    ] {
        let index = range(&mut runtime, lower, upper, inclusive);
        assert_eq!(
            runtime.index(source, index, false).unwrap_err().tag,
            ril_runtime_api::abi::OutcomeTag::LanguagePanic
        );
    }
    for (lower, upper, inclusive, length) in [
        (None, Some(2), false, 2),
        (Some(1), None, true, 2),
        (Some(3), Some(3), false, 0),
        (Some(3), None, true, 0),
    ] {
        let index = range(&mut runtime, lower, upper, inclusive);
        let window = runtime.index(source, index, false).unwrap();
        assert_eq!(runtime.length(window).unwrap(), length);
    }
}
#[test]
fn cloning_a_selected_graph_keeps_its_cycles_and_internal_sharing() {
    let mut runtime = Runtime::default();
    let child = runtime
        .allocate(Object::Record(Default::default()))
        .unwrap();
    runtime.set_field(child, "self".into(), child).unwrap();
    let source = runtime.allocate(Object::Array(vec![child, child])).unwrap();
    let index = range(&mut runtime, None, None, false);
    let window = runtime.index(source, index, false).unwrap();
    let copied = runtime.copy(window).unwrap();
    let selected = runtime.sequence(copied).unwrap();
    assert_eq!(selected[0], selected[1]);
    assert_ne!(selected[0], child);
    assert_eq!(runtime.field(selected[0], "self").unwrap(), selected[0]);
    let extra = runtime.int(4).unwrap();
    runtime.append(copied, extra).unwrap();
    assert_eq!(runtime.length(copied).unwrap(), 3);
    assert_eq!(runtime.length(source).unwrap(), 2);
    let combined = runtime
        .allocate(Object::Tuple(vec![source, window]))
        .unwrap();
    assert_eq!(
        runtime.heap.deep_clone(combined),
        Err(crate::heap::HeapError::NonClonable)
    );
}
