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
    let paths = [
        (
            "access.ril",
            include_str!("../../../tests/07_access/access.ril"),
        ),
        (
            "via.ril",
            include_str!("../../../tests/08_via_compat/via.ril"),
        ),
        (
            "effects.ril",
            include_str!("../../../tests/09_effects_use_draft/obligations.ril"),
        ),
    ];
    let mut count = 0;
    for (path, source) in paths {
        let suite = parse_suite(Path::new(path), source).unwrap();
        for case in suite.cases {
            if let Ok((_, analysis)) = Driver.analyze(&case.pkg) {
                let mut child = Command::new(&oracle)
                    .stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()
                    .unwrap();
                let input = serde_json::to_vec(&analysis.horn_rules).unwrap();
                child.stdin.take().unwrap().write_all(&input).unwrap();
                let output = child.wait_with_output().unwrap();
                assert!(output.status.success(), "{path} {}", case.id);
                let expected = serde_json::from_slice::<BTreeSet<usize>>(&output.stdout).unwrap();
                assert_eq!(
                    horn::solve(&analysis.horn_rules),
                    expected,
                    "{path} {}",
                    case.id
                );
                count += 1;
            }
        }
    }
    assert!(count >= 10);
}
