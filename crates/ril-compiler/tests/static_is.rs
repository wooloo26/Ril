use ril_compiler::{CompilationOutcome, Session};

fn check(source: &str) -> CompilationOutcome {
    Session::new(source.as_bytes().to_vec()).check()
}

#[test]
fn static_value_tests_check_expected_calls_and_full_array_equality() {
    let source = "meta fn expected()->int{2}\nmeta let _=assert(Some(2) is Some(expected()))\nmeta let _=assert(3 is 1+2)\nmeta let _=assert([1,2] is Array::reverse([2,1]))\nmeta let _=assert(!([1] is [1,2]))";
    let outcome = check(source);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn static_constructor_tests_keep_single_layer_tuple_and_nullary_rules() {
    let source = "meta let _=assert(Some((1,2)) is Some(1,2))\nmeta let _=assert(Some(1,2) is Some((1,2)))\nmeta let _=assert(Some(()) is Some())\nmeta let _=assert(Some() is Some(()))\nmeta let _=assert(type<int> is (type<int>))";
    let outcome = check(source);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    for (source, code) in [
        ("meta let _=assert(Some(2) is Some())", "E0314"),
        ("meta let _=assert(None is None())", "E0353"),
        ("meta let _=assert(Some(((1,2),3)) is Some(1,2,3))", "E0314"),
    ] {
        let outcome = check(source);
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn static_value_tests_skip_later_components_after_the_first_mismatch() {
    let skipped = "meta fn skipped()->int{assert(false);99}\n";
    for test in [
        "None is Some(skipped())",
        "(1,2) is (0,skipped())",
        "Some((1,2)) is Some((0,skipped()))",
        "(.{first:1,second:2}) is .{first:0,second:skipped()}",
    ] {
        let outcome = check(&format!("{skipped}meta let _=assert(!({test}))"));
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{test}: {outcome:?}"
        );
    }
    let outcome = check(&format!(
        "{skipped}meta let _=assert((1,2) is (1,skipped()))"
    ));
    assert!(
        matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0830")),
        "{outcome:?}"
    );
}

#[test]
fn skipped_value_test_leaves_still_require_type_and_termination_proofs() {
    for source in [
        "meta let _=assert(!(None is Some(1)+\"bad\"))",
        "meta let _=assert(!((1,2) is (0,\"bad\")))",
        "meta let _=assert(Some(2) is Some(2)|Some(\"bad\"))",
    ] {
        let outcome = check(source);
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{source}: {outcome:?}"
        );
    }
    let outcome = check(
        "meta fn unknown()->int{unknown()}\nmeta halt fn tested()->bool{None is Some(unknown())}",
    );
    assert!(
        !matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn ordinary_value_test_leaves_keep_their_evaluation_family() {
    let source =
        "meta fn expected()->int{2}\nfn example(value:?int){assert(value is Some(expected()))}";
    let outcome = check(source);
    assert!(
        matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0810")),
        "{outcome:?}"
    );
    let source = "fn example(value:?int){meta let EXPECTED=2;assert(value is Some((EXPECTED)))}";
    let outcome = check(source);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}
