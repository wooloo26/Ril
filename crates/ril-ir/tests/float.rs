use ril_ir::float::{F32Value, F64Value};
use std::cmp::Ordering;

#[test]
fn nan_payload_sign_and_signaling_bits_do_not_enter_static_identity() {
    for bits in [
        0x7f80_0001,
        0x7fc0_0000,
        0x7fff_ffff,
        0xff80_0001,
        0xffff_ffff,
    ] {
        let nan = F32Value::from_bits(bits);
        assert_eq!(nan.to_bits(), 0x7fc0_0000);
        assert!(!nan.ieee_eq(nan));
        assert_eq!(nan.ieee_cmp(nan), None);
        assert_eq!((-nan).to_bits(), 0x7fc0_0000);
        assert_eq!(F64Value::from(nan).to_bits(), 0x7ff8_0000_0000_0000);
    }
    for bits in [
        0x7ff0_0000_0000_0001,
        0x7ff8_0000_0000_0000,
        0x7fff_ffff_ffff_ffff,
        0xfff0_0000_0000_0001,
        0xffff_ffff_ffff_ffff,
    ] {
        let nan = F64Value::from_bits(bits);
        assert_eq!(nan.to_bits(), 0x7ff8_0000_0000_0000);
        assert_eq!(nan.key(), F64Value::from_float(f64::NAN).key());
        assert!(!nan.ieee_eq(nan));
        assert_eq!(nan.ieee_cmp(nan), None);
        assert_eq!((-nan).to_bits(), 0x7ff8_0000_0000_0000);
        assert_eq!(nan.round_to_f32().to_bits(), 0x7fc0_0000);
    }
}

#[test]
fn signed_zeros_compare_equal_but_have_different_static_keys() {
    let zero = F32Value::from_float(0.0);
    let negative = -zero;
    assert_eq!(negative.to_bits(), 0x8000_0000);
    assert!(zero.ieee_eq(negative));
    assert_eq!(zero.ieee_cmp(negative), Some(Ordering::Equal));
    assert_ne!(zero.key(), negative.key());
    let wide_zero = F64Value::from_float(0.0);
    let wide_negative = -wide_zero;
    assert_eq!(wide_negative.to_bits(), 0x8000_0000_0000_0000);
    assert!(wide_zero.ieee_eq(wide_negative));
    assert_ne!(wide_zero.key(), wide_negative.key());
    assert_ne!(zero.key(), wide_zero.key());
}

#[test]
fn safe_division_checks_both_zero_signs_and_retains_other_ieee_outcomes() {
    let one = F32Value::from_float(1.0);
    let zero = F32Value::from_float(0.0);
    for denominator in [zero, -zero] {
        assert!(one.safe_div(denominator).is_none());
        assert!(one.safe_rem(denominator).is_none());
    }
    assert_eq!((one / zero).to_bits(), 0x7f80_0000);
    assert_eq!((zero / zero).to_bits(), 0x7fc0_0000);
    assert_eq!((one % zero).to_bits(), 0x7fc0_0000);
    assert_eq!(
        F32Value::from_bits(0xff80_0001)
            .safe_div(one)
            .unwrap()
            .to_bits(),
        0x7fc0_0000
    );

    let one = F64Value::from_float(1.0);
    let zero = F64Value::from_float(0.0);
    assert!(one.safe_div(zero).is_none());
    assert!(one.safe_div(-zero).is_none());
    assert!(one.safe_rem(zero).is_none());
    assert_eq!((one / -zero).to_bits(), 0xfff0_0000_0000_0000);
    assert_eq!((zero / zero).to_bits(), 0x7ff8_0000_0000_0000);
}

#[test]
fn operations_keep_subnormals_round_ties_to_even_and_do_not_fuse() {
    let two = F32Value::from_float(2.0);
    assert_eq!((F32Value::from_bits(1) / two).to_bits(), 0);
    assert_eq!((F32Value::from_bits(3) / two).to_bits(), 2);
    assert_eq!(
        (F32Value::from_bits(1) + F32Value::from_bits(1)).to_bits(),
        2
    );
    let a = F32Value::from_bits(0x3f80_0001);
    let b = F32Value::from_bits(0x3f7f_fffe);
    assert_eq!((a * b - F32Value::from_float(1.0)).to_bits(), 0);
    assert_eq!(
        (F32Value::from_float(f32::MAX) * two).to_bits(),
        0x7f80_0000
    );

    let two = F64Value::from_float(2.0);
    assert_eq!((F64Value::from_bits(1) / two).to_bits(), 0);
    assert_eq!((F64Value::from_bits(3) / two).to_bits(), 2);
    let a = F64Value::from_bits(0x3ff0_0000_0000_0001);
    let b = F64Value::from_bits(0x3fef_ffff_ffff_fffe);
    assert_eq!((a * b - F64Value::from_float(1.0)).to_bits(), 0);
}
