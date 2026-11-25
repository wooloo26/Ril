#![forbid(unsafe_code)]

use std::path::Path;

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_test::{
    Activation, CheckResult, Milestone, Stage, TestDriver, VirtualPackage, parse_suite, run_case,
};

struct FakeDriver;

impl TestDriver for FakeDriver {
    fn check_stage(&self, pkg: &VirtualPackage, _upto: Stage) -> CheckResult {
        let mut result = CheckResult::default();
        for (path, file) in &pkg.files {
            assert!(path.extension().is_some_and(|ext| ext == "ril"));
            let id = FileId::from_path(path);
            result.file_paths.insert(id, path.clone());
            let source = String::from_utf8_lossy(&file.bytes);
            result
                .diagnostics
                .extend(source.match_indices("invalid").map(|(start, word)| {
                    Diagnostic::error(
                        Code::E0120,
                        Span::new(id, start, start + word.len()),
                        "fixture diagnostic",
                    )
                }));
        }
        result
    }
}

#[test]
fn matches_diagnostics_at_remapped_lines() {
    let suite = parse_suite(
        Path::new("suite.ril"),
        "\
-- @suite protocol
-- @default_stage source
-- @prelude
let injected = 1
-- @case with_marker compile-fail E0120 unit=bin
-- @file pkg/main.ril
fn main() -> () { () }
-- @file pkg/side.ril
invalid
  -- ^ E0120
-- @forbid E0104
-- @case pending compile-pass budget=3
",
    )
    .unwrap();
    let [first, pending] = suite.cases.as_slice() else {
        panic!("expected two cases")
    };
    assert_eq!(first.activation(Milestone::M0), Activation::Ready);
    assert_eq!(
        pending.activation(Milestone::M0),
        Activation::KnownPending(Milestone::M2)
    );
    assert_eq!(pending.activation(Milestone::M2), Activation::Ready);
    assert_eq!(
        first.pkg.files[Path::new("pkg/main.ril")].suite_line(1),
        Some(4)
    );
    assert_eq!(
        first.pkg.files[Path::new("pkg/main.ril")].suite_line(2),
        Some(7)
    );
    assert_eq!(
        first.pkg.files[Path::new("pkg/side.ril")].suite_line(1),
        Some(9)
    );
    assert!(run_case(first, &FakeDriver).is_ok());
}

#[test]
fn rejects_unknown_directives_and_paths() {
    for directive in ["-- @unknown E0120", "-- @file pkg/../outside.ril"] {
        let source = format!("-- @suite bad\n-- @case broken compile-pass\n{directive}");
        let err = parse_suite(Path::new("invalid.ril"), &source).unwrap_err();
        assert!(err.to_string().starts_with("invalid.ril:3:"));
    }
}

#[test]
fn diagnostics_match_the_canonical_summary() {
    let spec = include_str!("../../../doc/SPEC.md");
    let (_, summary) = spec
        .split_once("## Diagnostic Error Codes Summary\n")
        .unwrap();
    let entries: Vec<_> = summary
        .lines()
        .filter_map(|line| {
            let (code, name) = line.strip_prefix("| **`")?.split_once("`** | [`")?;
            Some((code, name.split_once('`')?.0))
        })
        .collect();
    assert_eq!(entries.len(), Code::ALL.len());
    for (code, name) in entries {
        assert_eq!(code.parse::<Code>().unwrap().name(), name);
    }
}
