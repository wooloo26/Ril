use ril_ir::{
    TargetSpec,
    layout::{Alignment, FloatType, IntegerType, LayoutError, ValueRepr},
};

#[test]
fn scalar_and_managed_values_use_target_layouts() {
    use IntegerType::*;
    for target in TargetSpec::ABSTRACT {
        let pointer = u64::from(target.pointer_bytes());
        for (repr, size, alignment, roots) in [
            (ValueRepr::Unit, 0, 1, vec![]),
            (ValueRepr::Never, 0, 1, vec![]),
            (ValueRepr::Bool, 1, 1, vec![]),
            (ValueRepr::Integer(I8), 1, 1, vec![]),
            (ValueRepr::Integer(U8), 1, 1, vec![]),
            (ValueRepr::Integer(I16), 2, 2, vec![]),
            (ValueRepr::Integer(U16), 2, 2, vec![]),
            (ValueRepr::Integer(I32), 4, 4, vec![]),
            (ValueRepr::Integer(U32), 4, 4, vec![]),
            (ValueRepr::Integer(I64), 8, 8, vec![]),
            (ValueRepr::Integer(U64), 8, 8, vec![]),
            (ValueRepr::Float(FloatType::F32), 4, 4, vec![]),
            (ValueRepr::Float(FloatType::F64), 8, 8, vec![]),
            (
                ValueRepr::Integer(BigInt),
                pointer,
                target.pointer_bytes().into(),
                vec![0],
            ),
            (
                ValueRepr::Text,
                pointer,
                target.pointer_bytes().into(),
                vec![0],
            ),
            (
                ValueRepr::Bytes,
                pointer,
                target.pointer_bytes().into(),
                vec![0],
            ),
            (
                ValueRepr::SharedObject,
                pointer,
                target.pointer_bytes().into(),
                vec![0],
            ),
            (
                ValueRepr::Callable,
                pointer * 2,
                target.pointer_bytes().into(),
                vec![pointer],
            ),
        ] {
            let layout = target.value_layout(repr);
            assert_eq!(
                (
                    layout.size(),
                    layout.alignment().bytes(),
                    layout.trace_offsets()
                ),
                (size, alignment, roots.as_slice()),
                "{target:?} {repr:?}"
            );
        }
    }
}

#[test]
fn ranges_keep_integer_endpoints_flag_padding_and_managed_bigint_roots() {
    use IntegerType::*;
    for target in TargetSpec::ABSTRACT {
        for (integer, size, align) in [
            (I8, 3, 1),
            (U8, 3, 1),
            (I16, 6, 2),
            (U16, 6, 2),
            (I32, 12, 4),
            (U32, 12, 4),
            (I64, 24, 8),
            (U64, 24, 8),
        ] {
            let layout = target.value_layout(ValueRepr::IntegerRange(integer));
            assert_eq!((layout.size(), layout.alignment().bytes()), (size, align));
            assert!(layout.trace_offsets().is_empty());
        }
        let layout = target.value_layout(ValueRepr::IntegerRange(BigInt));
        let pointer = u64::from(target.pointer_bytes());
        assert_eq!(layout.size(), pointer * 3);
        assert_eq!(layout.trace_offsets(), [0, pointer]);
    }
}

#[test]
fn fields_and_roots_include_alignment_and_the_untraced_object_header() {
    let fields = [
        ValueRepr::Bool,
        ValueRepr::Integer(IntegerType::I64),
        ValueRepr::Text,
        ValueRepr::Callable,
        ValueRepr::IntegerRange(IntegerType::BigInt),
        ValueRepr::Unit,
    ];
    for (target, offsets, roots, payload, size) in [
        (
            TargetSpec::Pointer32,
            [8, 16, 24, 28, 36, 48],
            [24, 32, 36, 40],
            8,
            48,
        ),
        (
            TargetSpec::Pointer64,
            [16, 24, 32, 40, 56, 80],
            [32, 48, 56, 64],
            16,
            80,
        ),
    ] {
        let object = target.object_layout(fields).unwrap();
        let layout = object.storage();
        assert_eq!(object.payload_offset(), payload);
        assert_eq!(layout.size(), size);
        assert_eq!(layout.alignment().bytes(), 8);
        assert_eq!(layout.trace_offsets(), roots);
        assert_eq!(
            layout
                .fields()
                .iter()
                .map(|field| field.offset())
                .collect::<Vec<_>>(),
            offsets
        );
        for (field, representation) in layout.fields().iter().zip(fields) {
            assert_eq!(field.representation(), representation);
            assert_eq!(
                field.offset() % u64::from(field.value().alignment().bytes()),
                0
            );
        }
    }
}

#[test]
fn repeated_trace_plans_include_callable_environments_and_both_range_endpoints() {
    for (target, count_offset, data_offset, callable_roots, range_roots) in [
        (TargetSpec::Pointer32, 8, 16, [20, 28, 36], [16, 20, 28, 32]),
        (
            TargetSpec::Pointer64,
            16,
            24,
            [32, 48, 64],
            [24, 32, 48, 56],
        ),
    ] {
        let buffer = target.buffer_layout(ValueRepr::Callable, 3).unwrap();
        assert_eq!(buffer.count_offset(), count_offset);
        assert_eq!(buffer.elements_offset(), data_offset);
        assert_eq!(buffer.trace_offsets().collect::<Vec<_>>(), callable_roots);
        assert_eq!(
            buffer.size(),
            if target == TargetSpec::Pointer32 {
                40
            } else {
                72
            }
        );
        let range = target
            .buffer_layout(ValueRepr::IntegerRange(IntegerType::BigInt), 2)
            .unwrap();
        assert_eq!(range.trace_offsets().collect::<Vec<_>>(), range_roots);
    }
}

#[test]
fn zero_sized_values_and_leaf_buffers_do_not_expand_trace_descriptors() {
    for target in TargetSpec::ABSTRACT {
        let unit = target
            .buffer_layout(ValueRepr::Unit, i64::MAX as u64)
            .unwrap();
        assert_eq!(unit.count(), i64::MAX as u64);
        assert_eq!(unit.size(), unit.elements_offset());
        assert_eq!(unit.element().size(), 0);
        assert_eq!(unit.trace_offsets().next(), None);
        let leaf = target
            .buffer_layout(ValueRepr::Integer(IntegerType::U8), 1_000_000)
            .unwrap();
        assert_eq!(leaf.trace_offsets().next(), None);
    }
}

#[test]
fn extents_alignment_and_target_capacity_fail_without_wrapping() {
    assert_eq!(Alignment::new(0), None);
    assert_eq!(Alignment::new(3), None);
    let alignment = Alignment::new(8).unwrap();
    assert_eq!(alignment.round_up(17), Ok(24));
    assert_eq!(
        alignment.round_up(u64::MAX),
        Err(LayoutError::ArithmeticOverflow)
    );
    assert!(matches!(
        TargetSpec::Pointer64.buffer_layout(ValueRepr::Unit, i64::MAX as u64 + 1),
        Err(LayoutError::ExtentExceeded { .. })
    ));
    assert_eq!(
        TargetSpec::Pointer64
            .buffer_layout(ValueRepr::IntegerRange(IntegerType::I64), i64::MAX as u64),
        Err(LayoutError::ArithmeticOverflow)
    );

    let last_aligned_size = u64::from(u32::MAX) - 7;
    let count = last_aligned_size - 16;
    assert_eq!(
        TargetSpec::Pointer32
            .buffer_layout(ValueRepr::Bool, count)
            .unwrap()
            .size(),
        last_aligned_size
    );
    assert!(matches!(
        TargetSpec::Pointer32.buffer_layout(ValueRepr::Bool, count + 1),
        Err(LayoutError::AddressSpaceExceeded { .. })
    ));
}

#[test]
fn native_layouts_share_the_explicit_pointer64_contract() {
    let fields = [
        ValueRepr::Bool,
        ValueRepr::Text,
        ValueRepr::Callable,
        ValueRepr::Integer(IntegerType::I64),
    ];
    let expected = TargetSpec::Pointer64.object_layout(fields).unwrap();
    for native in TargetSpec::NATIVE {
        assert_eq!(native.object_layout(fields).unwrap(), expected);
        assert_eq!(
            native.buffer_layout(ValueRepr::Callable, 7),
            TargetSpec::Pointer64.buffer_layout(ValueRepr::Callable, 7)
        );
    }
}
