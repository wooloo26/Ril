use ril_test::{CaseRegistry, parse_bundle};

fn shared() -> &'static str {
    "--@ source: common\n--@ file: input.ril\npub fn test_one(){}\npub fn test_two(){}\n--@ end-file\n--@ end-source\n\
--@ case: first\n--@ mode: run-pass\n--@ spec: SPEC#diagnostic-classification\n--@ entry: test_one\n--@ use-source: common\n--@ end-case\n\
--@ case: second\n--@ mode: run-pass\n--@ spec: SPEC#diagnostic-classification\n--@ entry: test_two\n--@ use-source: common\n--@ end-case\n"
}

#[test]
fn one_source_has_independent_case_identity_and_entry_metadata() {
    let cases = parse_bundle(shared(), "tests/example/shared.ril").unwrap();
    assert_eq!(cases.len(), 2);
    assert_eq!(cases[0].files, cases[1].files);
    assert_ne!(cases[0].id, cases[1].id);
    assert_eq!(cases[0].meta.entry.as_deref(), Some("test_one"));
    assert_eq!(cases[1].meta.entry.as_deref(), Some("test_two"));
    let registry = CaseRegistry::new(cases.clone()).unwrap();
    assert_eq!(registry.get(&cases[0].id).unwrap(), &cases[0]);
    assert!(registry.get("first").is_err());
    assert!(CaseRegistry::new([cases[0].clone(), cases[0].clone()]).is_err());
}

#[test]
fn shared_source_framing_cannot_hide_missing_duplicate_or_nested_programs() {
    for bad in [
        shared().replace("--@ use-source: common", "--@ use-source: absent"),
        shared().replacen("--@ source: common", "--@ source: ../escape", 1),
        shared().replacen("--@ end-source", "--@ source: nested\n--@ end-source", 1),
        shared().replacen(
            "--@ use-source: common",
            "--@ use-source: common\n--@ use-source: common",
            1,
        ),
        shared().to_owned()
            + "--@ source: unused\n--@ file: input.ril\nx\n--@ end-file\n--@ end-source\n",
        shared().to_owned()
            + "--@ source: common\n--@ file: input.ril\nx\n--@ end-file\n--@ end-source\n",
    ] {
        assert!(
            parse_bundle(&bad, "tests/example/shared.ril").is_err(),
            "{bad}"
        );
    }
}

#[test]
fn readable_source_can_preserve_the_absence_of_a_final_newline() {
    let text = "--@ case: exact\n--@ mode: check-pass\n--@ spec: SPEC#diagnostic-classification\n--@ file: source.ril no-final-newline\nfn example(){}\n--@ end-file\n--@ end-case\n";
    let case = parse_bundle(text, "tests/example/exact.ril")
        .unwrap()
        .remove(0);
    assert_eq!(case.files[0].bytes, b"fn example(){}");
    assert!(
        parse_bundle(
            &text.replace("no-final-newline", "hex no-final-newline"),
            "tests/example/exact.ril"
        )
        .is_err()
    );
}
