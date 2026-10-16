//! Exhausting a member projection cannot turn a receiving obligation off.
//! The large input is a non-authorization regression, not a language NI pass.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn source(long_member: bool) -> String {
    let last = if long_member {
        format!("target_{}", "x".repeat(600))
    } else {
        "target".into()
    };
    let fields = (0..300)
        .map(|index| format!("a{index}:int"))
        .chain(std::iter::once(format!("{last}:[0][2]int")))
        .collect::<Vec<_>>()
        .join(",");
    let values = (0..300)
        .map(|index| format!("a{index}:0"))
        .chain(std::iter::once(format!("{last}:stored")))
        .collect::<Vec<_>>()
        .join(",");
    let mut source = String::from("fn example(){let stored:[0][3]int=[];let holder:{");
    source.push_str(&fields);
    source.push_str("}=.{");
    source.push_str(&values);
    source.push_str("}}");
    source
}

fn check(source: &str, target: &str) -> CompilationOutcome {
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    assert!(ril_syntax::validate_program(&parsed.program).is_empty());
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..CheckOptions::default()
        },
    )
    .check()
}

#[test]
fn bounded_projection_preserves_the_unpaid_original_member_schema() {
    for target in ["pointer32", "pointer64"] {
        // Same fields and mismatch without the long lookup key. This confirms
        // the generated syntax reaches the actual source-dimension check.
        let control = check(&source(false), target);
        assert!(
            matches!(&control, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{target}: short-key control: {control:?}"
        );
        let outcome = check(&source(true), target);
        assert!(
            matches!(&outcome, CompilationOutcome::NotImplemented { .. })
                || matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{target}: long-key input must not verify: {outcome:?}"
        );
    }
}
