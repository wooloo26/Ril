use proptest::prelude::*;
use ril_test::*;
use std::{
    fs,
    path::{Path, PathBuf},
};

struct Fixture<'a> {
    name: &'a str,
    mode: &'a str,
    meta: &'a str,
    annotations: &'a str,
    source: &'a str,
    extra: &'a str,
}
impl Default for Fixture<'_> {
    fn default() -> Self {
        Self {
            name: "one",
            mode: "check-pass",
            meta: "",
            annotations: "",
            source: "fn example() {}",
            extra: "",
        }
    }
}
fn fixture(f: Fixture<'_>) -> String {
    let mode = if f.mode.is_empty() {
        String::new()
    } else {
        format!("--@ mode: {}\n", f.mode)
    };
    format!(
        "--@ case: {}\n{mode}--@ spec: SPEC#diagnostic-classification\n{}\n{}\n--@ file: root.ril\n{}\n--@ end-file\n{}\n--@ end-case\n",
        f.name, f.meta, f.annotations, f.source, f.extra
    )
}
fn parse(text: &str) -> Result<Vec<Case>> {
    parse_bundle(text, "tests/example.ril")
}
fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn independent_cases_and_auxiliary_files_keep_identity() {
    let first = fixture(Fixture {
        name: "accept",
        source: "use helper",
        extra: "--@ file: helper.d.ril\npub fn answer() -> int\n--@ end-file",
        ..Fixture::default()
    });
    let second = fixture(Fixture {
        name: "reject",
        mode: "check-fail",
        annotations: "-- Error [E0301]",
        source: "fn example() { let value: str = 1 }",
        ..Fixture::default()
    });
    let cases = parse(&(first + &second)).unwrap();
    assert_eq!(cases.len(), 2);
    assert_eq!(cases[0].id, "tests/example.ril::accept");
    assert_eq!(cases[1].meta.mode, Mode::CheckFail);
    assert_eq!(cases[0].root, "root.ril");
    assert_eq!(cases[0].files[1].name, "helper.d.ril");
}

#[test]
fn malformed_ril_cannot_swallow_a_case() {
    let text = fixture(Fixture {
        name: "bad-string",
        mode: "check-fail",
        annotations: "-- Error [E0107]",
        source: "let VALUE = \"unterminated",
        ..Fixture::default()
    }) + &fixture(Fixture {
        name: "bad-comment",
        mode: "check-fail",
        annotations: "-- Error [E0106]",
        source: "{- unterminated",
        ..Fixture::default()
    }) + &fixture(Fixture::default());
    assert_eq!(parse(&text).unwrap().len(), 3);
}

#[test]
fn escaped_delimiters_and_virtual_headers_are_source_text() {
    let source = "fn example() { let value = \u{60}\n--@@ end-file\n--@@ case: literal\n\u{60} }\n--@@@ original";
    let cases = parse(&fixture(Fixture {
        source,
        ..Fixture::default()
    }))
    .unwrap();
    assert_eq!(
        cases[0].files[0].bytes,
        (source.replace("--@@", "--@") + "\n").as_bytes()
    );
    let cases = parse(&fixture(Fixture {
        source: "--@@ mode: check-pass\nfn example() {}",
        ..Fixture::default()
    }))
    .unwrap();
    assert_eq!(
        cases[0].files[0].bytes,
        b"--@ mode: check-pass\nfn example() {}\n"
    );
}

#[test]
fn bytes_and_line_endings_are_preserved() {
    let text = fixture(Fixture { extra: "--@ file: bytes.bin hex\n61 0d 0a\n--@ end-file\n--@ file: empty.bin hex\n--@ end-file\n--@ file: eof.bin hex\n61\n--@ end-file", ..Fixture::default() }).replace('\n', "\r\n");
    let cases = parse(&text).unwrap();
    assert_eq!(cases[0].files[0].bytes, b"fn example() {}\n");
    assert_eq!(cases[0].files[1].bytes, b"a\r\n");
    assert!(cases[0].files[2].bytes.is_empty());
    assert_eq!(cases[0].files[3].bytes, b"a");
    let raw = fixture(Fixture {
        mode: "check-fail",
        annotations: "-- Error [E0104]",
        ..Fixture::default()
    })
    .replace(
        "--@ file: root.ril\nfn example() {}",
        "--@ file: root.ril hex\nff",
    );
    assert_eq!(parse(&raw).unwrap()[0].files[0].bytes, [0xff]);
    assert!(parse(&(fixture(Fixture::default()) + "\r")).is_err());
}

#[test]
fn rejects_invalid_hex_paths_and_collisions() {
    for hex in ["f", "ffg0", "0xff", "ff-00"] {
        let extra = format!("--@ file: bytes.bin hex\n{hex}\n--@ end-file");
        assert!(
            parse(&fixture(Fixture {
                extra: &extra,
                ..Fixture::default()
            }))
            .is_err(),
            "{hex}"
        );
    }
    for file in [
        "../escape.ril",
        "/absolute.ril",
        "C:/escape.ril",
        "a\\b.ril",
        "a/../b.ril",
        "NUL",
        "file.",
        "a//b",
        "a:stream",
        "COM1.txt",
        "LPT9",
    ] {
        assert!(
            parse(
                &fixture(Fixture::default())
                    .replace("--@ file: root.ril", &format!("--@ file: {file}"))
            )
            .is_err(),
            "{file}"
        );
    }
    for name in ["root.ril", "ROOT.ril", "root.ril/nested"] {
        let extra = format!("--@ file: {name}\ntext\n--@ end-file");
        assert!(
            parse(&fixture(Fixture {
                extra: &extra,
                ..Fixture::default()
            }))
            .is_err()
        );
    }
}

#[test]
fn rejects_malformed_framing_and_missing_expectations() {
    for source in ["--@ case: nested", "--@ file: nested.ril", "--@ end-case"] {
        assert!(
            parse(&fixture(Fixture {
                source,
                ..Fixture::default()
            }))
            .is_err()
        );
    }
    let text = fixture(Fixture::default());
    for broken in [
        text.replace("--@ end-case\n", ""), text.replace("--@ end-file\n", ""),
        "--@ case: empty\n--@ mode: check-pass\n--@ spec: SPEC#diagnostic-classification\n--@ end-case\n".into(),
        fixture(Fixture { extra: "--@ seed: 1", ..Fixture::default() }), "fn example() {}\n".into(),
        text.clone() + &text, fixture(Fixture { mode: "", ..Fixture::default() }),
        fixture(Fixture { meta: "--@ modde: check-fail", ..Fixture::default() }),
        fixture(Fixture { meta: "--@ mode: check-fail", ..Fixture::default() }),
        fixture(Fixture { mode: "run-pass", source: "pub fn test_example() {}", ..Fixture::default() }),
        fixture(Fixture { mode: "check-fail", ..Fixture::default() }),
        fixture(Fixture { mode: "run-program", source: "pub fn main() {}", meta: "--@ exit: 0\n--@ stdout: absent.stdout", ..Fixture::default() }),
    ] { assert!(parse(&broken).is_err(), "{broken}"); }
}

#[test]
fn metadata_is_data_and_all_inputs_must_exist() {
    let text = fixture(Fixture {
        mode: "run-program",
        source: "pub fn main() {}",
        meta: "--@ exit: 0\n--@ args: [\"a b\", \"\", \"$(literal)\"]\n--@ env: RIL_TEST_EMPTY=\n--@ unset-env: RIL_TEST_ABSENT\n--@ build: child.ril -> app.exe\n--@ stdin: input.bin\n--@ requires: process, filesystem",
        extra: "--@ file: child.ril\npub fn main() {}\n--@ end-file\n--@ file: input.bin hex\n00 ff\n--@ end-file",
        ..Fixture::default()
    });
    let case = &parse(&text).unwrap()[0];
    assert_eq!(case.meta.args.as_ref().unwrap(), &["a b", "", "$(literal)"]);
    assert_eq!(case.meta.env.as_ref().unwrap(), &["RIL_TEST_EMPTY="]);
    assert_eq!(
        case.meta.build.as_ref().unwrap()[0],
        HelperBuild {
            source: "child.ril".into(),
            output: "app.exe".into()
        }
    );
    for meta in [
        "--@ args: [1]",
        "--@ args: null",
        "--@ args: [\"\\u0000\"]",
        "--@ target: invented",
        "--@ requires: process-helper",
        "--@ seed: -1",
        "--@ env: =value",
        "--@ build: missing.ril -> app.exe",
        "--@ unit: object",
        "--@ stdin: missing.bin",
        "--@ requires: windows, posix",
        "--@ env: A=1\n--@ env: a=2",
        "--@ env: A=1\n--@ unset-env: a",
    ] {
        assert!(
            parse(&fixture(Fixture {
                meta,
                ..Fixture::default()
            }))
            .is_err(),
            "{meta}"
        );
    }
}

#[test]
fn validates_spec_references_and_companions() {
    let text = fixture(Fixture {
        name: "accept",
        meta: "--@ companion: reject",
        ..Fixture::default()
    }) + &fixture(Fixture {
        name: "reject",
        meta: "--@ companion: accept",
        ..Fixture::default()
    });
    assert_eq!(
        validate_corpus(&parse(&text).unwrap(), &repo().join("doc"), false)
            .unwrap()
            .cases,
        2
    );
    for text in [
        fixture(Fixture {
            meta: "--@ companion: missing",
            ..Fixture::default()
        }),
        fixture(Fixture {
            meta: "--@ companion: one",
            ..Fixture::default()
        }),
        fixture(Fixture::default()).replace("SPEC#diagnostic-classification", "SPEC#missing"),
        fixture(Fixture {
            mode: "check-fail",
            annotations: "-- Error [E9999]",
            ..Fixture::default()
        }),
    ] {
        assert!(validate_corpus(&parse(&text).unwrap(), &repo().join("doc"), false).is_err());
    }
}

#[test]
fn literal_text_is_not_an_expectation() {
    let expressions = [
        r#""nested {"-- Error [E0301] -- Warning [W0001]"}""#,
        r#""outer {"middle {"-- Error [E0301]"}"}""#,
        "\"value {\u{60}-- Error [E0301]\u{60}}\"",
        r#""size {len(b"{-- Error [E0301]")}""#,
        r#""{{ -- Error [E0301] }}""#,
        r#""\u{41} {"-- Error [E0301]"}""#,
        r#""value {"\"-- Error [E0301]"}""#,
        r#""value {.{ value: "-- Error [E0301]" }.value}""#,
        r#""value {String::trim("-- Error [E0301]")}""#,
        r#""{len(["-- Error [E0301]"]):">8}""#,
        "\"{1:\u{60}>8}\"",
    ];
    for expression in expressions {
        let source = format!("fn example() {{ let text = {expression} }}");
        let cases = parse(&fixture(Fixture {
            source: &source,
            ..Fixture::default()
        }))
        .unwrap();
        assert!(cases[0].errors.is_empty(), "{expression}");
        assert!(cases[0].warnings.is_empty());
        let source = source + "\nlet VALUE: str = 1 -- Error [E0301]\n-- Warning [W0001]";
        let cases = parse(&fixture(Fixture {
            mode: "check-fail",
            source: &source,
            ..Fixture::default()
        }))
        .unwrap();
        assert_eq!(cases[0].errors, ["E0301"], "{expression}");
        assert_eq!(cases[0].warnings, ["W0001"]);
    }
    let fake = fixture(Fixture {
        mode: "run-panic",
        meta: "--@ entry: test_nested",
        source: r#"pub fn test_nested() { let text = "nested {"-- Panics"}" }"#,
        ..Fixture::default()
    });
    assert!(parse(&fake).is_err());
}

#[test]
fn interpolation_comments_and_invalid_formats_keep_diagnostics() {
    for source in [
        "fn example() { let text = \"{ {\n {- outer {- -- Error [E9999] -} -- Warning [W9999] -}\n let value: str = 1 -- Error [E0301]\n \"-- Warning [W9999]\"\n} }\" }",
        "fn consume(action: fn(int) -> int) -> int { action(1) }\nfn example() { let text = \"{consume \\value: int -> {\n let text: str = 1 -- Error [E0301]\n value\n}}\" }",
    ] {
        let case = &parse(&fixture(Fixture {
            mode: "check-fail",
            source,
            ..Fixture::default()
        }))
        .unwrap()[0];
        assert_eq!(case.errors, ["E0301"]);
        assert!(case.warnings.is_empty());
    }
    for expression in ["\"{1:\">8q}\"", "\"{1:\u{60}>8q}\"", "\"{1:(>8q}\""] {
        let source = format!("fn example() {{ let text = {expression} }} -- Error [E0112]");
        assert_eq!(
            parse(&fixture(Fixture {
                mode: "check-fail",
                source: &source,
                ..Fixture::default()
            }))
            .unwrap()[0]
                .errors,
            ["E0112"]
        );
    }
}

#[test]
fn extracts_exact_bytes_and_isolates_workspaces() {
    let temp = tempfile::tempdir().unwrap();
    let case = &parse(&fixture(Fixture { extra: "--@ file: nested/helper.d.ril\npub type Value\n--@ end-file\n--@ file: raw.bin hex\nff 0d 0a\n--@ end-file", ..Fixture::default() })).unwrap()[0];
    let first = extract_case(case, &temp.path().join("first")).unwrap();
    let second = extract_case(case, &temp.path().join("second")).unwrap();
    assert_eq!(
        fs::read(first.directory.join("raw.bin")).unwrap(),
        [255, 13, 10]
    );
    assert!(first.directory.join("nested/helper.d.ril").exists());
    assert!(extract_case(case, &first.directory).is_err());
    fs::write(first.root, b"changed").unwrap();
    assert_eq!(fs::read(second.root).unwrap(), case.files[0].bytes);
    let file = temp.path().join("file");
    fs::write(&file, "keep").unwrap();
    assert!(extract_case(case, &file).is_err());
    assert_eq!(fs::read(file).unwrap(), b"keep");
}

#[test]
fn discovery_is_strict_and_inventory_matches_the_migration_baseline() {
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir(temp.path().join("conformance")).unwrap();
    fs::write(
        temp.path().join("conformance/one.ril"),
        fixture(Fixture::default()),
    )
    .unwrap();
    assert_eq!(discover_cases(temp.path()).unwrap().len(), 1);
    fs::write(
        temp.path().join("conformance/old.case"),
        "--@ mode: check-pass",
    )
    .unwrap();
    assert!(discover_cases(temp.path()).is_err());
    let cases = discover_cases(&repo().join("tests")).unwrap();
    let stats = validate_corpus(&cases, &repo().join("doc"), true).unwrap();
    assert_eq!(
        (
            stats.bundles,
            stats.cases,
            stats.diagnostic_codes,
            stats.companions
        ),
        (84, 1067, 176, 811)
    );
    assert_eq!(
        Mode::ALL.map(|mode| stats.modes[&mode]),
        [342, 369, 296, 52, 8]
    );
    assert!(validate_corpus(&[], &repo().join("doc"), true).is_err());
}

#[cfg(unix)]
#[test]
fn symlinks_cannot_redirect_discovery_or_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let destination = temp.path().join("destination");
    fs::create_dir(&destination).unwrap();
    let link = temp.path().join("link");
    std::os::unix::fs::symlink(&destination, &link).unwrap();
    let case = &parse(&fixture(Fixture::default())).unwrap()[0];
    assert!(extract_case(case, &link).is_err());
    assert!(extract_case(case, &link.join("nested")).is_err());
    assert!(discover_cases(&link).is_err());
}

#[cfg(windows)]
#[test]
fn windows_directory_links_cannot_redirect_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let target = temp.path().join("destination");
    fs::create_dir(&target).unwrap();
    let link = temp.path().join("link");
    junction::create(&target, &link).unwrap();
    let case = &parse(&fixture(Fixture::default())).unwrap()[0];
    assert!(extract_case(case, &link).is_err());
    assert!(extract_case(case, &link.join("nested")).is_err());
    assert!(discover_cases(&link).is_err());
    junction::delete(&link).unwrap();
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]
    #[test]
    fn arbitrary_bytes_round_trip_through_hex(bytes in proptest::collection::vec(any::<u8>(), 0..2048)) {
        let hex: String = bytes.iter().map(|byte| format!("{byte:02x} ")).collect();
        let extra = format!("--@ file: payload.bin hex\n{hex}\n--@ end-file");
        let cases = parse(&fixture(Fixture { extra: &extra, ..Fixture::default() })).unwrap();
        prop_assert_eq!(&cases[0].files[1].bytes, &bytes);
        let temp = tempfile::tempdir().unwrap();
        let extracted = extract_case(&cases[0], &temp.path().join("case")).unwrap();
        prop_assert_eq!(fs::read(extracted.directory.join("payload.bin")).unwrap(), bytes);
    }
    #[test]
    fn arbitrary_container_text_never_panics(text in ".{0,2048}") {
        let _ = parse(&text);
        let _ = parse(&fixture(Fixture { source: &text, ..Fixture::default() }));
    }
}
