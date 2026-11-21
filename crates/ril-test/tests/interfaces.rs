#![forbid(unsafe_code)]

use std::{
    collections::BTreeSet,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use ril_driver::Driver;
use ril_sema::{access::horn, iface::Interface};
use ril_test::parse_suite;

#[test]
fn interface_roundtrip_is_stable_and_detects_corruption() {
    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let baseline = suite.cases[0].baseline.as_ref().unwrap();
    let interface = Driver.interface(baseline).unwrap();
    let encoded = interface.encode().unwrap();
    let readback = Interface::decode(&encoded).unwrap();
    assert_eq!(encoded, readback.encode().unwrap());
    let text = String::from_utf8(encoded)
        .unwrap()
        .replace("\"format_version\": 1", "\"format_version\": 2");
    assert!(Interface::decode(text.as_bytes()).is_err());
}

#[test]
fn exported_horn_facts_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let mut cases = Vec::new();
    for suite in ril_test::discover(&root).unwrap() {
        for case in suite.cases {
            let inputs: Vec<_> = if let Some(baseline) = &case.baseline {
                vec![("baseline", baseline), ("revision", &case.pkg)]
            } else {
                vec![("source", &case.pkg)]
            };
            for (label, package) in inputs {
                if let Ok(rules) = Driver.horn_rules(package) {
                    cases.push((format!("{}::{} ({label})", suite.name, case.id), rules));
                }
            }
        }
    }
    assert!(cases.len() >= 75);
    let requests = cases.iter().map(|(_, rules)| rules).collect::<Vec<_>>();
    let mut child = Command::new(oracle)
        .arg("batch")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let input = serde_json::to_vec(&requests).unwrap();
    child.stdin.take().unwrap().write_all(&input).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let expected: Vec<BTreeSet<usize>> = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(cases.len(), expected.len());
    for ((case, rules), expected) in cases.into_iter().zip(expected) {
        assert_eq!(horn::solve(&rules), expected, "{case}");
    }
}

#[test]
fn exported_summary_subsumption_agrees_with_lean() {
    use ril_sema::access::{Access, Summary};
    use serde_json::{Value, json};

    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let source = include_str!("../../../tests/08_via_compat/via.ril");
    let suite = parse_suite(Path::new("via.ril"), source).unwrap();
    let mut summaries = vec![
        Summary::default(),
        Summary {
            retained: vec![0],
            effects: vec!["io".into()],
            ..Summary::default()
        },
        Summary {
            roots: vec![1],
            contained: vec![(Access::Ref, 2)],
            constructs: true,
            ..Summary::default()
        },
    ];
    for case in suite.cases {
        if let Ok(interface) = Driver.interface(&case.pkg) {
            summaries.extend(
                interface
                    .functions
                    .into_values()
                    .map(|function| function.summary),
            );
        }
    }
    let wire = |summary: &Summary| -> Value {
        let effects: Vec<_> = summary
            .effects
            .iter()
            .map(|name| {
                name.bytes().fold(0_u64, |prior, b| {
                    prior.wrapping_mul(257).wrapping_add(u64::from(b))
                })
            })
            .collect();
        let contained: Vec<_> = summary
            .contained
            .iter()
            .map(|&(access, param)| {
                let mode = match access {
                    Access::Immutable => 0,
                    Access::Ref => 1,
                    Access::Mut => 2,
                    Access::Shared => 3,
                };
                (mode, param)
            })
            .collect();
        json!({
            "writes": summary.writes,
            "retained": summary.retained,
            "roots": summary.roots,
            "contained": contained,
            "effects": effects,
            "captures": summary.captures,
            "constructs": summary.constructs,
        })
    };
    let cases: Vec<_> = summaries
        .iter()
        .flat_map(|baseline| summaries.iter().map(move |revision| (baseline, revision)))
        .collect();
    let input: Vec<_> = cases
        .iter()
        .map(|(baseline, revision)| json!({"baseline": wire(baseline), "revision": wire(revision)}))
        .collect();
    let expected: Vec<_> = cases
        .iter()
        .map(|(baseline, revision)| baseline.subsumes(revision))
        .collect();

    let mut child = Command::new(oracle)
        .arg("summary")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert_eq!(
        serde_json::from_slice::<Vec<bool>>(&output.stdout).unwrap(),
        expected
    );
}
