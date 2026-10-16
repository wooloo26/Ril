use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use ril_compiler_core::target::TargetLayout;

fn check(source: &str, bits: u8) -> Result<ril_compiler::hir::VerifiedProgram, CompilationOutcome> {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: format!("pointer{bits}"),
            ..Default::default()
        },
    )
    .verify()
}

fn reject(source: &str, bits: u8, code: &str) {
    let Err(CompilationOutcome::Rejected { diagnostics }) = check(source, bits) else {
        panic!("expected {code}: pointer{bits}: {source}")
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == code),
        "{source}: {diagnostics:?}"
    );
}

#[test]
fn every_radix_case_preserves_pointer_sized_and_fixed_width_ranges() {
    for bits in [32u8, 64] {
        let layout = if bits == 32 {
            TargetLayout::POINTER32
        } else {
            TargetLayout::POINTER64
        };
        let maximum = (1u128 << (bits - 1)) - 1;
        let magnitude = maximum + 1;
        for (prefix, maximum, magnitude) in [
            ("0x", format!("{maximum:X}"), format!("{magnitude:X}")),
            ("0X", format!("{maximum:X}"), format!("{magnitude:X}")),
            ("0o", format!("{maximum:o}"), format!("{magnitude:o}")),
            ("0O", format!("{maximum:o}"), format!("{magnitude:o}")),
            ("0b", format!("{maximum:b}"), format!("{magnitude:b}")),
            ("0B", format!("{maximum:b}"), format!("{magnitude:b}")),
        ] {
            for suffix in ["", "_int"] {
                let source = format!(
                    "fn example(){{let maximum={prefix}{maximum}{suffix};let minimum=-{prefix}{magnitude}{suffix}}}"
                );
                let verified =
                    check(&source, bits).unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"));
                let core = ril_compiler::lower::lower_core_for(&verified, layout).unwrap();
                for (index, expected) in
                    [(0, (1i128 << (bits - 1)) - 1), (1, -(1i128 << (bits - 1)))]
                {
                    let ril_ir::core::Statement::Bind { value, .. } =
                        &core.functions[0].body.statements[index]
                    else {
                        panic!("missing numeric binding")
                    };
                    assert!(
                        matches!(value.kind, ril_ir::core::ExprKind::Literal(ril_ir::core::Literal::Integer { value, bits: actual, signed: true }) if value == expected && actual == bits),
                        "{value:?}"
                    );
                }
                reject(
                    &format!("fn example(){{let overflow={prefix}{magnitude}{suffix}}}"),
                    bits,
                    "E0326",
                );
                let source = format!(
                    "meta let MAX={prefix}{maximum}{suffix}\nmeta let MIN=-{prefix}{magnitude}{suffix}\nfn example() &{{MAX,MIN}}{{assert(MAX>=MIN)}}"
                );
                let verified =
                    check(&source, bits).unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"));
                ril_compiler::lower::lower_core_for(&verified, layout).unwrap();
                reject(
                    &format!("meta let OVERFLOW={prefix}{magnitude}{suffix}"),
                    bits,
                    "E0326",
                );
            }
        }
        let source = "fn example(){let minimum=-0X80i8;let maximum=0B11111111u8;let wide=0XFFFFFFFFFFFFFFFFu64}";
        let verified = check(source, bits).unwrap();
        ril_compiler::lower::lower_core_for(&verified, layout).unwrap();
        for source in [
            "fn example(){let value=0O400u8}",
            "fn example(){let value=-0B1u8}",
            "fn example(){let value=0X100000000000000000000000000000000}",
        ] {
            reject(source, bits, "E0326");
        }
    }
}

#[test]
fn prefix_letters_and_hex_e_do_not_change_lexical_classification() {
    for source in [
        "fn example(){assert(0X1E+1==31 && 0X1E-1==29)}",
        "fn example(){let x:[0X2]int=[1,2];assert(x[0B1]==2)}",
        "meta let _=assert(0X1E+1==31 && 0O17==15 && 0B10==2)",
    ] {
        for bits in [32, 64] {
            check(source, bits).unwrap();
        }
    }
    for source in [
        "fn example(){let value=0X_G}",
        "fn example(){let value=0B102}",
        "meta let BAD=0O8",
        "fn example(){let value=0X1__F}",
        "fn example(){let value=0X1u7}",
    ] {
        reject(source, 64, "E0111");
    }
}

#[test]
fn recursive_prefix_constants_still_require_valid_ranges_and_operand_types() {
    for source in [
        "halt fn down(n:int)->int{if n>0B0{down(n-0O1)}else{0X0}}",
        "halt fn down(n:int)->int{if n>0b0{down(n-0o1)}else{0x0}}",
    ] {
        for bits in [32, 64] {
            check(source, bits).unwrap();
        }
    }
    reject(
        "halt fn down(n:int)->int{if n>0B0{down(n-0O1u8)}else{0X0}}",
        64,
        "E0301",
    );
    reject(
        "halt fn down(n:i8)->i8{if n>0B0{down(n-0X80i8)}else{0X0}}",
        64,
        "E0326",
    );
}
