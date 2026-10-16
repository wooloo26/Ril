use ril_test::{CaseRegistry, Mode, case_by_id, case_bytes, case_source, parse_bundle};
use serde::Deserialize;
use std::{collections::BTreeSet, fs, path::Path};

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

#[test]
fn extracted_rust_programs_keep_case_links_and_expectations() {
    #[derive(Deserialize)]
    struct Inline {
        rust: String,
        case: String,
        mode: Mode,
        diagnostic: Option<String>,
    }
    let rows: Vec<Inline> =
        serde_json::from_str(include_str!("data/inline-source-migration.json")).unwrap();
    assert_eq!(rows.len(), 19);
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut ids = BTreeSet::new();
    for row in rows {
        assert!(
            ids.insert(row.case.clone()),
            "duplicate migration: {}",
            row.case
        );
        let case = case_by_id(&row.case);
        assert_eq!(case.id, row.case);
        assert_eq!(case.meta.mode, row.mode, "{}", row.case);
        assert_eq!(
            case.errors,
            row.diagnostic.into_iter().collect::<Vec<_>>(),
            "{}",
            row.case
        );
        let rust = fs::read_to_string(root.join(&row.rust)).unwrap();
        // Two formerly invalid positive fixtures remain negative corpus
        // cases; their original Rust tests use the explicit corrected pair.
        let corrected = case
            .meta
            .companion
            .as_ref()
            .map(|name| format!("{}::{name}", case.bundle));
        assert!(
            rust.contains(&row.case) || corrected.is_some_and(|id| rust.contains(&id)),
            "{} no longer references its migrated case or explicit companion {}",
            row.rust,
            row.case
        );
    }
}

#[derive(Deserialize)]
struct Manifest {
    baseline: Vec<Baseline>,
    fixtures: Vec<Fixture>,
    counts: Counts,
}
#[derive(Deserialize)]
struct Baseline {
    path: String,
    cases: usize,
}
#[derive(Deserialize)]
struct Fixture {
    original: String,
    case: String,
    cases: Vec<Expected>,
}
#[derive(Deserialize)]
struct Expected {
    id: String,
    mode: Mode,
    entry: Option<String>,
    diagnostic: Option<String>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Counts {
    original_fixtures: usize,
    original_ril: usize,
    pending: usize,
    unique_sources: usize,
    new_bundles: usize,
    new_cases: usize,
}

#[test]
fn migrated_fixtures_keep_case_expectations_entry_counts_and_source_reuse() {
    let manifest: Manifest =
        serde_json::from_str(include_str!("data/fixture-migration.json")).unwrap();
    assert_eq!(
        (
            manifest.counts.original_fixtures,
            manifest.counts.original_ril,
            manifest.counts.pending
        ),
        (149, 144, 5)
    );
    assert_eq!(manifest.fixtures.len(), manifest.counts.original_fixtures);
    let mut originals = BTreeSet::new();
    let mut unique_sources = BTreeSet::new();
    let mut cases = BTreeSet::new();
    let mut bundles = BTreeSet::new();
    for fixture in &manifest.fixtures {
        assert!(originals.insert(&fixture.original));
        assert!(
            !Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(&fixture.original)
                .exists(),
            "migrated fixture was reintroduced outside its bundle: {}",
            fixture.original
        );
        let source = case_by_id(&fixture.case);
        let bytes = case_bytes(&fixture.case);
        unique_sources.insert(&fixture.case);
        assert!(
            fixture
                .cases
                .iter()
                .any(|expected| expected.id == fixture.case),
            "migration lost its primary case: {}",
            fixture.original
        );
        let mut fixture_ids = BTreeSet::new();
        let mut entries = BTreeSet::new();
        for expected in &fixture.cases {
            assert!(
                fixture_ids.insert(&expected.id),
                "duplicate case: {}",
                expected.id
            );
            let case = case_by_id(&expected.id);
            assert_eq!(case.id, expected.id);
            assert_eq!(case.meta.mode, expected.mode, "{}", expected.id);
            assert_eq!(case.meta.entry, expected.entry, "{}", expected.id);
            assert_eq!(
                case.errors,
                expected.diagnostic.iter().cloned().collect::<Vec<_>>(),
                "{}",
                expected.id
            );
            assert_eq!(case_bytes(&expected.id), bytes, "{}", expected.id);
            assert_eq!(case.files, source.files, "{}", expected.id);
            if let Some(entry) = &expected.entry {
                assert!(
                    entries.insert(entry),
                    "duplicated native entry for {}: {entry}",
                    fixture.original
                );
            }
            cases.insert(&expected.id);
            bundles.insert(&case.bundle);
        }
    }
    assert_eq!(unique_sources.len(), manifest.counts.unique_sources);
    assert_eq!(cases.len(), manifest.counts.new_cases);
    assert_eq!(bundles.len(), manifest.counts.new_bundles);
    assert_eq!(
        case_source("tests/regressions/source-receiving.ril::source-receiving-native").as_bytes(),
        case_bytes("tests/regressions/source-receiving.ril::source-receiving-native")
    );
}

#[test]
fn the_original_corpus_bundles_and_case_inventory_are_retained() {
    let manifest: Manifest =
        serde_json::from_str(include_str!("data/fixture-migration.json")).unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    assert_eq!(manifest.baseline.len(), 84);
    let mut ids = BTreeSet::new();
    for bundle in &manifest.baseline {
        let bytes = fs::read(root.join(&bundle.path)).unwrap();
        let cases = parse_bundle(std::str::from_utf8(&bytes).unwrap(), &bundle.path).unwrap();
        assert_eq!(cases.len(), bundle.cases, "{}", bundle.path);
        for case in cases {
            assert_eq!(case_by_id(&case.id), &case);
            assert!(ids.insert(case.id));
        }
    }
    assert_eq!(ids.len(), 1067);
}
