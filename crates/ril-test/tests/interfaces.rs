#![forbid(unsafe_code)]

use std::{
    collections::BTreeSet,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use ril_driver::Driver;
use ril_sema::{
    access::{Access, horn},
    iface::{FORMAT_VERSION, Interface},
};
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
    let text = String::from_utf8(encoded).unwrap();
    let other_version = text.replace(
        &format!("\"format_version\": {FORMAT_VERSION}"),
        "\"format_version\": 0",
    );
    assert!(Interface::decode(other_version.as_bytes()).is_err());
    let corrupted = text.replace("c.count", "c.other").replace("read", "other");
    assert_ne!(text, corrupted);
    assert!(Interface::decode(corrupted.as_bytes()).is_err());
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
    use ril_sema::access::{Coordinate, ReturnSource, Summary};
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
            return_sources: vec![ReturnSource {
                formal: 2,
                source_path: vec![Coordinate::Field("count".into())],
                result_path: vec![Coordinate::Index("0".into())],
                access: Access::Ref,
            }],
            constructs: true,
            ..Summary::default()
        },
    ];
    for case in suite.cases {
        for pkg in case.baseline.iter().chain(std::iter::once(&case.pkg)) {
            if let Ok(interface) = Driver.interface(pkg) {
                for function in interface.functions.into_values() {
                    summaries.push(function.summary);
                    for instance in function.domain {
                        if !summaries.contains(&instance.summary) {
                            summaries.push(instance.summary);
                        }
                    }
                }
            }
        }
    }
    let effects: std::collections::BTreeMap<_, _> = summaries
        .iter()
        .flat_map(|summary| &summary.effects)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(index, effect)| (effect, index))
        .collect();
    let wire_coordinate = |coordinate: &Coordinate| match coordinate {
        Coordinate::Field(key) => json!({"kind": "field", "key": key}),
        Coordinate::Index(key) => json!({"kind": "index", "key": key}),
        Coordinate::Dynamic => json!({"kind": "dynamic", "key": ""}),
    };
    let wire = |summary: &Summary| -> Value {
        let effects: Vec<_> = summary
            .effects
            .iter()
            .map(|name| effects.get(name).copied().unwrap())
            .collect();
        let return_sources: Vec<_> = summary
            .return_sources
            .iter()
            .map(|source| {
                json!({
                    "formal": source.formal,
                    "source_path": source.source_path.iter().map(wire_coordinate).collect::<Vec<_>>(),
                    "result_path": source.result_path.iter().map(wire_coordinate).collect::<Vec<_>>(),
                    "access": access_number(source.access),
                })
            })
            .collect();
        json!({
            "writes": summary.writes,
            "retained": summary.retained,
            "return_sources": return_sources,
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

fn access_number(access: Access) -> u8 {
    match access {
        Access::Immutable => 0,
        Access::Ref => 1,
        Access::Mut => 2,
        Access::Shared => 3,
    }
}

#[test]
fn path_attenuation_agrees_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    const MODES: [Access; 4] = [Access::Immutable, Access::Ref, Access::Mut, Access::Shared];
    let mut paths = Vec::new();
    let mut depth = vec![Vec::new()];
    for _ in 0..4 {
        depth = depth
            .into_iter()
            .flat_map(|prefix| {
                MODES.map(|mode| {
                    let mut path = prefix.clone();
                    path.push(mode);
                    path
                })
            })
            .collect();
        paths.extend(depth.iter().cloned());
    }
    let input: Vec<_> = paths
        .iter()
        .map(|path| path.iter().copied().map(access_number).collect::<Vec<_>>())
        .collect();
    let expected: Vec<_> = paths
        .iter()
        .map(|path| {
            let (&root, members) = path.split_first().unwrap();
            access_number(members.iter().copied().fold(root, Access::project))
        })
        .collect();
    let mut child = Command::new(oracle)
        .arg("path-access")
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
        serde_json::from_slice::<Vec<u8>>(&output.stdout).unwrap(),
        expected
    );
}
