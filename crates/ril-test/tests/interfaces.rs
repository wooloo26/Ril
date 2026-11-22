#![forbid(unsafe_code)]

use std::{
    collections::BTreeSet,
    ffi::OsStr,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use ril_driver::Driver;
use ril_sema::{
    access::{Access, horn},
    iface::{FORMAT_VERSION, Interface},
};
use ril_test::{CaseMode, Stage, TestDriver, parse_suite, run_worker};

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
fn forwarded_via_identity_publishes_new_guarantee_only_for_owned_input() {
    use ril_sema::access::Input;

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "replacing_inline_via_body_with_forwarding_is_compatible")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    assert_eq!(decoded.functions.len(), 1);
    let relay = decoded.functions.values().next().unwrap();
    for input in [Input::Plain, Input::Ref, Input::New] {
        assert!(relay.domain.iter().any(|row| row.modes == [input]));
    }
    for row in &relay.domain {
        assert_eq!(row.summary.constructs, row.modes == [Input::New]);
    }
}

#[test]
fn composite_via_rows_publish_the_attenuated_member_source() {
    use ril_sema::access::{Coordinate, Input, ReturnSource};

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "record_member_via_can_be_bound_and_forwarded")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    assert_eq!(export.domain.len(), 4);
    for (mode, access) in [
        (Input::Plain, Access::Immutable),
        (Input::Ref, Access::Ref),
        (Input::Mut, Access::Ref),
        (Input::Shared, Access::Ref),
    ] {
        let row = export
            .domain
            .iter()
            .find(|row| row.modes == [mode])
            .unwrap();
        assert!(!row.summary.constructs);
        assert_eq!(
            row.summary.return_sources,
            [ReturnSource {
                formal: 0,
                source_path: vec![Coordinate::Field("child".into())],
                result_path: Vec::new(),
                access,
            }]
        );
    }
}

#[test]
fn higher_order_via_rows_publish_callback_reception() {
    use ril_sema::access::{Input, Invocation, InvocationMode};

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "forwarding_preserves_higher_order_mode_requirements")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let invocation = |mode| Invocation {
        receiver: 0,
        parameter: 0,
        mode,
        preserves_input: false,
    };
    assert_eq!(
        export.summary.invocations,
        [invocation(InvocationMode::Formal(1))]
    );
    assert_eq!(export.domain.len(), 25);
    for row in &export.domain {
        let [_, input]: [Input; 2] = row.modes.as_slice().try_into().unwrap();
        assert_eq!(
            row.summary.invocations,
            [invocation(InvocationMode::Input(input))]
        );
    }
}

#[test]
fn exported_callback_preservation_is_required_only_for_new_reception() {
    use ril_sema::access::Input;

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "requiring_a_callback_to_preserve_ownership_breaks_compatibility")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let [contract] = export.summary.invocations.as_slice() else {
        panic!("missing callback contract");
    };
    assert!(contract.preserves_input);
    for row in &export.domain {
        let [_, input]: [Input; 2] = row.modes.as_slice().try_into().unwrap();
        let [contract] = row.summary.invocations.as_slice() else {
            panic!("missing specialized callback contract");
        };
        assert_eq!(contract.preserves_input, input == Input::New);
    }
}

#[test]
fn exported_callback_results_retain_their_call_entry_sources() {
    use ril_sema::access::{Input, InvocationMode, ReturnSource};

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "forwarding_preserves_callback_result_sources")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let [result] = export.summary.callback_returns.as_slice() else {
        panic!("missing callback return");
    };
    assert_eq!(result.receiver, 0);
    assert!(result.result_path.is_empty());
    let [argument] = result.arguments.as_slice() else {
        panic!("missing forwarded argument");
    };
    assert_eq!(argument.modes, [InvocationMode::Formal(1)]);
    assert_eq!(
        argument
            .sources
            .iter()
            .map(|source| source.formal)
            .collect::<Vec<_>>(),
        [1]
    );
    let row = export
        .domain
        .iter()
        .find(|row| row.modes == [Input::Plain, Input::Ref])
        .unwrap();
    let [result] = row.summary.callback_returns.as_slice() else {
        panic!("missing specialized return");
    };
    let [argument] = result.arguments.as_slice() else {
        panic!("missing specialized argument");
    };
    assert_eq!(argument.modes, [InvocationMode::Input(Input::Ref)]);
    assert_eq!(
        argument.sources,
        [ReturnSource {
            formal: 1,
            source_path: Vec::new(),
            result_path: Vec::new(),
            access: Access::Ref,
        }]
    );
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
fn exported_summaries_and_via_domains_agree_with_lean() {
    use ril_sema::access::{Coordinate, Instance, InvocationMode, ReturnSource, Summary};
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
    let mut domains = vec![Vec::new()];
    for case in suite.cases {
        for pkg in case.baseline.iter().chain(std::iter::once(&case.pkg)) {
            if let Ok(interface) = Driver.interface(pkg) {
                let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
                for function in decoded.functions.into_values() {
                    summaries.push(function.summary);
                    for instance in &function.domain {
                        if !summaries.contains(&instance.summary) {
                            summaries.push(instance.summary.clone());
                        }
                    }
                    if !domains.contains(&function.domain) {
                        domains.push(function.domain);
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
        let invocations: Vec<_> = summary
            .invocations
            .iter()
            .map(|invoke| {
                let (input, formal) = match invoke.mode {
                    InvocationMode::Input(input) => (Some(input), None),
                    InvocationMode::Formal(formal) => (None, Some(formal)),
                };
                json!({
                    "receiver": invoke.receiver,
                    "parameter": invoke.parameter,
                    "input": input,
                    "formal": formal,
                "preserves_input": invoke.preserves_input,
                })
            })
            .collect();
        json!({
            "writes": summary.writes,
            "retained": summary.retained,
            "return_sources": return_sources,
            "effects": effects,
            "invocations": invocations,
            "callback_returns": summary.callback_returns,
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

    let output = query(&oracle, "summary", &serde_json::to_vec(&input).unwrap()).unwrap();
    assert_eq!(
        serde_json::from_slice::<Vec<bool>>(&output).unwrap(),
        expected
    );

    assert!(domains.len() > 4);
    let domain_wire = |rows: &[Instance]| {
        rows.iter()
            .map(|row| json!({"modes": row.modes, "summary": wire(&row.summary)}))
            .collect::<Vec<_>>()
    };
    let cases: Vec<_> = domains
        .iter()
        .flat_map(|baseline| domains.iter().map(move |revision| (baseline, revision)))
        .collect();
    let input: Vec<_> = cases.iter().map(|(baseline, revision)| {
        json!({"baseline": domain_wire(baseline), "revision": domain_wire(revision)})
    }).collect();
    let actual = query(&oracle, "domain", &serde_json::to_vec(&input).unwrap()).unwrap();
    let expected: Vec<_> = cases
        .iter()
        .map(|(baseline, revision)| Instance::domain_subsumes(baseline, revision))
        .collect();
    assert_eq!(
        serde_json::from_slice::<Vec<bool>>(&actual).unwrap(),
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

#[test]
fn call_entry_examples_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let suite = parse_suite(
        Path::new("access.ril"),
        include_str!("../../../tests/07_access/access.ril"),
    )
    .unwrap();
    let output = query(&oracle, "call-entry", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 4);
    for (name, accepted) in results {
        let case = suite.cases.iter().find(|case| case.id == name).unwrap();
        let diagnostics = Driver.check_stage(&case.pkg, Stage::Access).diagnostics;
        assert_eq!(diagnostics.is_empty(), accepted, "{name}: {diagnostics:?}");
    }
}

#[test]
fn task_join_examples_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let compile = parse_suite(
        Path::new("isolation.ril"),
        include_str!("../../../tests/12_concurrency_isolation/isolation.ril"),
    )
    .unwrap();
    let runtime = parse_suite(
        Path::new("fifo.ril"),
        include_str!("../../../tests/13_concurrency_deterministic/fifo.ril"),
    )
    .unwrap();
    let output = query(&oracle, "task-joins", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 4);
    let temporary = tempfile::tempdir().unwrap();
    for (name, accepted) in results {
        let case = compile
            .cases
            .iter()
            .chain(&runtime.cases)
            .find(|case| case.id == name)
            .unwrap();
        if matches!(case.mode, CaseMode::RunPass) {
            let executable = temporary.path().join(&name);
            Driver.build_aot(&case.pkg, &executable).unwrap();
            let execution = run_worker(&mut Command::new(executable)).unwrap();
            assert_eq!(
                execution.status.success(),
                accepted,
                "{name}: {:?}",
                String::from_utf8_lossy(&execution.stderr)
            );
        } else {
            let diagnostics = Driver.check_stage(&case.pkg, Stage::Access).diagnostics;
            assert_eq!(diagnostics.is_empty(), accepted, "{name}: {diagnostics:?}");
        }
    }
}

#[test]
fn draft_path_updates_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let runtime = parse_suite(
        Path::new("effects.ril"),
        include_str!("../../../tests/11_runtime_effects_panic/effects.ril"),
    )
    .unwrap();
    let output = query(&oracle, "draft", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 2);
    let temporary = tempfile::tempdir().unwrap();
    for (name, valid) in results {
        let case = runtime.cases.iter().find(|case| case.id == name).unwrap();
        let executable = temporary.path().join(&name);
        Driver.build_aot(&case.pkg, &executable).unwrap();
        let execution = run_worker(&mut Command::new(executable)).unwrap();
        assert_eq!(
            execution.status.success(),
            valid,
            "{name}: {:?}",
            String::from_utf8_lossy(&execution.stderr)
        );
    }
}

#[test]
fn visibility_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("visibility", 12)
}

#[test]
fn boundary_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("boundary", 6)
}

#[test]
fn call_authority_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("call-authority", 22)
}

#[test]
fn handoff_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("handoff", 9)
}

#[test]
fn provenance_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("provenance", 11)
}

#[test]
fn scoped_resource_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("scoped", 9)
}

fn check_access_examples(operation: &str, count: usize) -> Result<(), Box<dyn std::error::Error>> {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return Ok(());
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let suites = ril_test::discover(&root)?;
    let output = query(&oracle, operation, b"[]")?;
    let results: Vec<(String, bool)> = serde_json::from_slice(&output)?;
    assert_eq!(results.len(), count);
    for (name, accepted) in results {
        let case = suites
            .iter()
            .flat_map(|suite| &suite.cases)
            .find(|case| case.id == name)
            .ok_or_else(|| format!("no Ril case named {name} for Lean operation {operation}"))?;
        let diagnostics = Driver.check_stage(&case.pkg, Stage::Access).diagnostics;
        assert_eq!(diagnostics.is_empty(), accepted, "{name}: {diagnostics:?}");
        if let CaseMode::CompileFail(code) = case.mode {
            assert!(
                diagnostics.iter().any(|diag| diag.code == Some(code)),
                "{name}: {diagnostics:?}"
            );
        }
    }
    Ok(())
}

fn query(
    oracle: &OsStr,
    operation: &str,
    input: &[u8],
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut child = Command::new(oracle)
        .arg(operation)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .ok_or("missing oracle input pipe")?
        .write_all(input)?;
    let output = child.wait_with_output()?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(format!("Lean oracle failed for {operation}").into())
    }
}
