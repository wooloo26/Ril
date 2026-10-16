//! Run all well-formed positive sources through the real parser. Semantic
//! failures are included too except cases deliberately testing syntax errors.
use std::path::Path;

#[test]
fn positive_corpus_has_real_lossless_syntax() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let cases = ril_test::discover_cases(&root.join("tests")).unwrap();
    let mut failures = vec![];
    let mut selected = 0;
    for case in cases {
        if case.meta.mode == ril_test::Mode::CheckFail {
            continue;
        }
        for file in &case.files {
            if !file.name.ends_with(".ril") {
                continue;
            }
            let text = std::str::from_utf8(&file.bytes).unwrap();
            let parsed = ril_syntax::parse(text);
            selected += 1;
            assert_eq!(
                parsed.syntax().to_string(),
                text,
                "{} {}",
                case.id,
                file.name
            );
            if parsed.is_err() {
                let errors: Vec<_> = parsed
                    .diagnostics
                    .iter()
                    .take(4)
                    .map(|d| format!("{} at {}: {}", d.code, d.labels[0].span.start, d.message))
                    .collect();
                failures.push(format!(
                    "{} / {}: {}",
                    case.id,
                    file.name,
                    errors.join("; ")
                ));
            }
        }
    }
    assert!(selected > 500);
    assert!(
        failures.is_empty(),
        "{} of {selected} sources failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn negative_lexical_and_syntax_corpus_reports_required_codes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let cases = ril_test::discover_cases(&root.join("tests")).unwrap();
    let mut failures = vec![];
    let mut selected = 0;
    for case in cases {
        let expected: Vec<_> = case
            .errors
            .iter()
            .filter(|code| code.as_str() >= "E0105" && code.as_str() <= "E0124")
            .collect();
        if expected.is_empty() {
            continue;
        }
        let mut codes = vec![];
        for file in &case.files {
            if !file.name.ends_with(".ril") {
                continue;
            }
            let Ok(text) = std::str::from_utf8(&file.bytes) else {
                continue;
            };
            let parsed = ril_syntax::parse(text);
            selected += 1;
            assert_eq!(
                parsed.syntax().to_string(),
                text,
                "{} {}",
                case.id,
                file.name
            );
            codes.extend(parsed.diagnostics.into_iter().map(|d| d.code));
        }
        for expected in expected {
            if !codes.contains(expected) {
                failures.push(format!("{} expected {expected}, got {codes:?}", case.id));
            }
        }
    }
    assert!(selected > 30);
    assert!(
        failures.is_empty(),
        "{} cases failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn source_type_boundaries_report_specific_diagnostics() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let cases = ril_test::discover_cases(&root.join("tests")).unwrap();
    let mut failures = vec![];
    for case in cases {
        let expected: Vec<_> = case
            .errors
            .iter()
            .filter(|code| {
                matches!(
                    code.as_str(),
                    "E0330" | "E0331" | "E0332" | "E0333" | "E0334" | "E0335" | "E0613"
                )
            })
            .collect();
        if expected.is_empty() {
            continue;
        }
        let mut codes = vec![];
        for file in case.files.iter().filter(|file| file.name.ends_with(".ril")) {
            let parsed = ril_syntax::parse(std::str::from_utf8(&file.bytes).unwrap());
            codes.extend(
                parsed
                    .diagnostics
                    .into_iter()
                    .map(|diagnostic| diagnostic.code),
            );
        }
        for code in expected {
            if !codes.contains(code) {
                failures.push(format!("{} expected {code}, got {codes:?}", case.id));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} cases failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
