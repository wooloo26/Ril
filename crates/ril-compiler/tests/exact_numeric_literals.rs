use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use ril_compiler::numeric_literals::{
    EncodedNumber, Error, ExactLiteral, FloatFormat, NumberType, ParseLimit,
};
use ril_compiler_core::target::TargetLayout;
use std::{cmp::Ordering, collections::BTreeSet};

const LIMIT: ParseLimit = ParseLimit { max_bytes: 16_384 };

fn integer(text: &str, negative: bool) -> ExactLiteral {
    ExactLiteral::integer(text, negative, LIMIT).unwrap()
}

fn float_bits(value: EncodedNumber, format: FloatFormat) -> u64 {
    let EncodedNumber::Float(value) = value else {
        panic!("not a float: {value:?}")
    };
    assert_eq!(value.format(), format);
    match format {
        FloatFormat::F32 => assert_eq!(u64::from((value.as_f64() as f32).to_bits()), value.bits()),
        FloatFormat::F64 => assert_eq!(value.as_f64().to_bits(), value.bits()),
    }
    value.bits()
}

fn select_float(value: &ExactLiteral, format: FloatFormat, layout: TargetLayout) -> u64 {
    float_bits(
        value
            .select(
                match format {
                    FloatFormat::F32 => NumberType::F32,
                    FloatFormat::F64 => NumberType::F64,
                },
                layout,
            )
            .unwrap(),
        format,
    )
}

#[test]
fn parsing_preserves_arbitrary_magnitude_radix_case_separators_and_immediate_sign() {
    let magnitude = (BigUint::one() << 200usize) + BigUint::from(0xfeedu32);
    for (radix, prefixes) in [
        (10, vec![""]),
        (16, vec!["0x", "0X"]),
        (8, vec!["0o", "0O"]),
        (2, vec!["0b", "0B"]),
    ] {
        let digits = magnitude.to_str_radix(radix).to_uppercase();
        let separated = digits
            .chars()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("_");
        for prefix in prefixes {
            for spelling in [&digits, &separated] {
                let text = format!("{prefix}{spelling}");
                for negative in [false, true] {
                    let exact = integer(&text, negative);
                    assert_eq!(exact.magnitude(), Some(&magnitude));
                    assert_eq!(exact.is_negative(), negative);
                    assert_eq!(exact.written_type(), None);
                    let EncodedNumber::BigInteger(actual) = exact
                        .select(NumberType::BigInt, TargetLayout::POINTER32)
                        .unwrap()
                    else {
                        panic!()
                    };
                    let expected = BigInt::from(magnitude.clone());
                    assert_eq!(actual, if negative { -expected } else { expected });
                    assert_eq!(
                        exact.select(NumberType::U64, TargetLayout::POINTER64),
                        Err(Error::OutOfRange)
                    );
                }
            }
        }
    }
}

#[test]
fn range_checks_follow_the_selected_type_and_explicit_target_layout() {
    for layout in [TargetLayout::POINTER32, TargetLayout::POINTER64] {
        for (ty, bits, signed) in [
            (NumberType::Int, layout.pointer_bits, true),
            (NumberType::I8, 8, true),
            (NumberType::I16, 16, true),
            (NumberType::I32, 32, true),
            (NumberType::I64, 64, true),
            (NumberType::U8, 8, false),
            (NumberType::U16, 16, false),
            (NumberType::U32, 32, false),
            (NumberType::U64, 64, false),
        ] {
            let bound = 1i128 << if signed { bits - 1 } else { bits };
            let maximum = integer(&(bound - 1).to_string(), false)
                .select(ty, layout)
                .unwrap();
            assert_eq!(
                maximum,
                EncodedNumber::Integer {
                    value: bound - 1,
                    ty,
                    bits,
                    signed
                }
            );
            assert_eq!(
                integer(&bound.to_string(), false).select(ty, layout),
                Err(Error::OutOfRange)
            );
            if signed {
                assert_eq!(
                    integer(&bound.to_string(), true)
                        .select(ty, layout)
                        .unwrap(),
                    EncodedNumber::Integer {
                        value: -bound,
                        ty,
                        bits,
                        signed
                    }
                );
                assert_eq!(
                    integer(&(bound + 1).to_string(), true).select(ty, layout),
                    Err(Error::OutOfRange)
                );
            } else {
                assert_eq!(
                    integer("1", true).select(ty, layout),
                    Err(Error::OutOfRange)
                );
                assert_eq!(
                    integer("0", true).select(ty, layout).unwrap(),
                    EncodedNumber::Integer {
                        value: 0,
                        ty,
                        bits,
                        signed
                    }
                );
            }
        }
        let value = integer("18446744073709551615", false);
        assert!(matches!(
            value.select(NumberType::U64, layout),
            Ok(EncodedNumber::Integer {
                value: 18_446_744_073_709_551_615,
                bits: 64,
                signed: false,
                ..
            })
        ));
        assert_eq!(
            value.select(NumberType::Int, layout),
            Err(Error::OutOfRange)
        );
    }
    assert_eq!(
        integer("1", false).select(NumberType::Int, TargetLayout { pointer_bits: 16 }),
        Err(Error::UnsupportedTarget)
    );
}

#[test]
fn suffixes_lock_nominal_types_even_when_representations_have_the_same_width() {
    for (suffix, ty) in [
        ("int", NumberType::Int),
        ("i8", NumberType::I8),
        ("i16", NumberType::I16),
        ("i32", NumberType::I32),
        ("i64", NumberType::I64),
        ("u8", NumberType::U8),
        ("u16", NumberType::U16),
        ("u32", NumberType::U32),
        ("u64", NumberType::U64),
        ("bigint", NumberType::BigInt),
    ] {
        for separator in ["", "_"] {
            let literal = integer(&format!("0X1{separator}{suffix}"), false);
            assert_eq!(literal.written_type(), Some(ty));
            literal.select(ty, TargetLayout::POINTER64).unwrap();
            assert_eq!(
                literal.select(NumberType::F32, TargetLayout::POINTER64),
                Err(Error::IncompatibleSelection)
            );
            let other = if ty == NumberType::Int {
                NumberType::I64
            } else {
                NumberType::Int
            };
            assert_eq!(
                literal.select(other, TargetLayout::POINTER64),
                Err(Error::IncompatibleSelection)
            );
        }
    }
    let value = ExactLiteral::decimal("1.0_f32", false, LIMIT).unwrap();
    assert_eq!(
        value.select(NumberType::F64, TargetLayout::POINTER64),
        Err(Error::IncompatibleSelection)
    );
    assert_eq!(
        ExactLiteral::decimal("1.0", false, LIMIT)
            .unwrap()
            .select(NumberType::Int, TargetLayout::POINTER64),
        Err(Error::IncompatibleSelection)
    );
}

#[test]
fn malformed_spellings_and_implementation_limits_are_distinct_from_range_errors() {
    for text in [
        "", "+1", "-1", " 1", "1 ", "1__0", "1_", "_1", "0x", "0X_FF", "0B102", "0O8", "0XGG",
        "1u7", "1.0", "1e2", "1__int", "１",
    ] {
        assert_eq!(
            ExactLiteral::integer(text, false, LIMIT),
            Err(Error::InvalidSyntax),
            "{text}"
        );
    }
    for text in [
        "1", ".1", "1.", "1._0", "1_.0", "1.0e", "1.0e+", "1.0e1_2", "1.0e+1e2", "1.0int", "nan",
        "inf", "+1.0", "-1.0", "1.0__f64",
    ] {
        assert_eq!(
            ExactLiteral::decimal(text, false, LIMIT),
            Err(Error::InvalidSyntax),
            "{text}"
        );
    }
    for parse in [ExactLiteral::integer, ExactLiteral::decimal] {
        assert_eq!(
            parse("123456789", false, ParseLimit { max_bytes: 8 }),
            Err(Error::ResourceLimit)
        );
    }
    assert_eq!(
        integer("256", false).select(NumberType::U8, TargetLayout::POINTER64),
        Err(Error::OutOfRange)
    );
}

#[test]
fn integer_and_decimal_float_selection_round_once_and_preserve_negative_zero() {
    for (text, expected, via_f64) in [
        ("18014399583223809", 0x5a80_0001, 0x5a80_0000),
        (
            "170141193601674033557522515689509748737",
            0x7f00_0001,
            0x7f00_0000,
        ),
    ] {
        assert_eq!(
            u64::from((text.parse::<f64>().unwrap() as f32).to_bits()),
            via_f64
        );
        let magnitude = BigUint::parse_bytes(text.as_bytes(), 10).unwrap();
        for (radix, prefix) in [(10, ""), (16, "0X"), (8, "0O"), (2, "0B")] {
            let spelling = format!("{prefix}{}", magnitude.to_str_radix(radix));
            for layout in [TargetLayout::POINTER32, TargetLayout::POINTER64] {
                assert_eq!(
                    select_float(&integer(&spelling, false), FloatFormat::F32, layout),
                    expected
                );
                assert_eq!(
                    select_float(&integer(&spelling, true), FloatFormat::F32, layout),
                    expected | 1 << 31
                );
            }
        }
    }
    let decimal = "1.0000000596046447753906250000000001";
    let value = ExactLiteral::decimal(decimal, false, LIMIT).unwrap();
    assert_eq!(
        select_float(&value, FloatFormat::F32, TargetLayout::POINTER64),
        0x3f80_0001
    );
    assert_eq!(
        (decimal.parse::<f64>().unwrap() as f32).to_bits(),
        0x3f80_0000
    );
    for (format, sign) in [(FloatFormat::F32, 1 << 31), (FloatFormat::F64, 1 << 63)] {
        for value in [
            integer("0", true),
            ExactLiteral::decimal("0.0", true, LIMIT).unwrap(),
        ] {
            assert_eq!(select_float(&value, format, TargetLayout::POINTER64), sign);
        }
    }
    let subnormal=ExactLiteral::decimal("0.00000000000000000000000000000000000000000000140129846432481707092372958328991613128026194187651577175706828388979108268586060148663818836212158203125",false,LIMIT).unwrap();
    assert_eq!(
        select_float(&subnormal, FloatFormat::F32, TargetLayout::POINTER64),
        1
    );
    let exponent = ExactLiteral::decimal("1_0.0_5E-2_f32", false, LIMIT).unwrap();
    assert_eq!(
        select_float(&exponent, FloatFormat::F32, TargetLayout::POINTER64),
        u64::from(0.1005f32.to_bits())
    );
    let smallest = ExactLiteral::decimal("4.9406564584124654e-324", false, LIMIT).unwrap();
    assert_eq!(
        select_float(&smallest, FloatFormat::F64, TargetLayout::POINTER64),
        1
    );
    for (format, infinity, sign) in [
        (FloatFormat::F32, 0x7f80_0000, 1 << 31),
        (FloatFormat::F64, 0x7ff0_0000_0000_0000, 1 << 63),
    ] {
        let huge = ExactLiteral::decimal("1.0e10000", true, LIMIT).unwrap();
        assert_eq!(
            select_float(&huge, format, TargetLayout::POINTER64),
            infinity | sign
        );
        for text in ["1.0e-10000", "0.0e10000"] {
            let zero = ExactLiteral::decimal(text, true, LIMIT).unwrap();
            assert_eq!(select_float(&zero, format, TargetLayout::POINTER64), sign);
        }
    }
}

// Independent oracle: binary-search adjacent representable floats, decode them
// as exact dyadic rationals, then compare distances. It does not truncate the
// input significand or share the production quotient/remainder algorithm.
struct Dyadic {
    coefficient: BigUint,
    exponent: i32,
}

fn format_parts(format: FloatFormat) -> (u32, i32, u64, u64) {
    match format {
        FloatFormat::F32 => (23, 127, 0x7f7f_ffff, 0x7f80_0000),
        FloatFormat::F64 => (52, 1023, 0x7fef_ffff_ffff_ffff, 0x7ff0_0000_0000_0000),
    }
}

fn dyadic(bits: u64, format: FloatFormat) -> Dyadic {
    let (fraction, bias, _, infinity) = format_parts(format);
    if bits == infinity {
        return Dyadic {
            coefficient: BigUint::one(),
            exponent: bias + 1,
        };
    }
    let encoded = (bits >> fraction) as i32;
    let coefficient =
        (bits & ((1u64 << fraction) - 1)) | if encoded == 0 { 0 } else { 1u64 << fraction };
    Dyadic {
        coefficient: BigUint::from(coefficient),
        exponent: if encoded == 0 {
            1 - bias - fraction as i32
        } else {
            encoded - bias - fraction as i32
        },
    }
}

fn compare(value: &Dyadic, integer: &BigUint) -> Ordering {
    if value.exponent >= 0 {
        (&value.coefficient << value.exponent as usize).cmp(integer)
    } else {
        value
            .coefficient
            .cmp(&(integer << (-value.exponent) as usize))
    }
}

fn neighbor_oracle(value: &BigUint, format: FloatFormat) -> u64 {
    let (_, _, maximum, infinity) = format_parts(format);
    let (mut low, mut high) = (0, maximum);
    while low < high {
        let middle = low + (high - low).div_ceil(2);
        if compare(&dyadic(middle, format), value).is_gt() {
            high = middle - 1;
        } else {
            low = middle;
        }
    }
    let lower = dyadic(low, format);
    if compare(&lower, value).is_eq() {
        return low;
    }
    let upper_bits = if low == maximum { infinity } else { low + 1 };
    let upper = dyadic(upper_bits, format);
    // Above the virtual overflow neighbor always rounds to infinity.
    if compare(&upper, value).is_lt() {
        return infinity;
    }
    let common = 0.min(lower.exponent).min(upper.exponent);
    let scaled = value << (-common) as usize;
    let down = &scaled - (lower.coefficient << (lower.exponent - common) as usize);
    let up = (upper.coefficient << (upper.exponent - common) as usize) - scaled;
    if down < up || down == up && low & 1 == 0 {
        low
    } else {
        upper_bits
    }
}

#[test]
fn integer_rounding_matches_exact_neighbor_distances_at_binades_ties_and_overflow() {
    let mut inputs = BTreeSet::from([
        BigUint::zero(),
        BigUint::one(),
        BigUint::from(3u8),
        BigUint::one() << 2048usize,
    ]);
    for format in [FloatFormat::F32, FloatFormat::F64] {
        let (fraction, bias, maximum, infinity) = format_parts(format);
        for exponent in [
            fraction as i32,
            fraction as i32 + 1,
            54,
            100,
            127,
            128,
            512,
            1023,
        ] {
            if exponent > bias {
                continue;
            }
            for fraction_value in [0, 1, 2, (1u64 << fraction) - 2, (1u64 << fraction) - 1] {
                let lower_bits = ((exponent + bias) as u64) << fraction | fraction_value;
                let upper_bits = if lower_bits == maximum {
                    infinity
                } else {
                    lower_bits + 1
                };
                let lower = dyadic(lower_bits, format);
                let upper = dyadic(upper_bits, format);
                let lower = lower.coefficient << lower.exponent as usize;
                let upper = upper.coefficient << upper.exponent as usize;
                let middle = (&lower + &upper) >> 1usize;
                inputs.extend([lower, upper, &middle - 1u32, middle.clone(), middle + 1u32]);
            }
        }
    }
    for value in inputs {
        for format in [FloatFormat::F32, FloatFormat::F64] {
            let expected = neighbor_oracle(&value, format);
            for negative in [false, true] {
                let expected = expected
                    | if negative {
                        match format {
                            FloatFormat::F32 => 1 << 31,
                            FloatFormat::F64 => 1 << 63,
                        }
                    } else {
                        0
                    };
                let actual = select_float(
                    &integer(&value.to_str_radix(10), negative),
                    format,
                    TargetLayout::POINTER32,
                );
                assert_eq!(
                    actual, expected,
                    "format {format:?}, negative {negative}, magnitude {value}"
                );
            }
        }
    }
}

#[test]
fn written_and_stored_numeric_types_cannot_be_reselected() {
    for source in [
        "fn example(){let value:f32=16777217int}",
        "fn example(){let original:u64=18446744073709551615u64;let value:f32=original}",
        "fn example(){let value:bigint=1int}",
    ] {
        assert!(
            matches!(
                ril_compiler::Session::new(source.as_bytes().to_vec()).check(),
                ril_compiler::CompilationOutcome::Rejected { .. }
            ),
            "committed numeric type was changed: {source}"
        );
    }
}
