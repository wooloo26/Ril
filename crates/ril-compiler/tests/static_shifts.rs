use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn static_shifts_accept_independent_counts_and_preserve_left_integer_rules() {
    let source = r#"
meta let _=assert(1u8<<2i16==4u8)
meta let _=assert(128u8<<1==0u8)
meta let _=assert(-2i8>>1u64 == -1i8)
meta let _=assert(1bigint<<100==1267650600228229401496703205376bigint)
meta let _=assert(1u16<<2bigint==4u16)
meta let _=assert(-8bigint>>1267650600228229401496703205376bigint == -1bigint)
meta let _=assert(1<<63 == -9223372036854775808)
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn static_shift_limits_use_the_left_width_even_when_the_value_is_zero() {
    for expression in ["0<<64", "0u8<<8", "1u16<<-1i8", "1bigint<<-1"] {
        let source = format!("meta let INVALID={expression}");
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0831")),
            "{expression}: {outcome:?}"
        );
    }
}

#[test]
fn abstract_pointer_layout_controls_static_int_shift_width() {
    let check = |source: &str, target: &str| {
        Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..CheckOptions::default()
            },
        )
        .check()
    };
    let outcome = check("meta let _=assert(1<<31 == -2147483648)", "pointer32");
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let outcome = check("meta let VALUE=0<<32", "pointer32");
    assert!(
        matches!(outcome, CompilationOutcome::Rejected { ref diagnostics }
        if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0831")),
        "{outcome:?}"
    );
    let outcome = check("meta let VALUE=0<<32", "pointer64");
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let outcome = check("meta let _=assert(1u64<<32==4294967296u64)", "pointer32");
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}
