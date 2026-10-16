use std::{fs, process::Command};

#[test]
fn static_and_native_interpolation_share_scalar_conversions() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("formatting.ril");
    fs::write(
        &source,
        r#"
var count=0
fn advance_counter()->int &{mut count} { count+=1; count }
pub fn test_formatting() &{mut count} {
    meta let FIXED="{1.25:.1f}"
    meta let SCIENTIFIC="{12.5:.2e}"
    meta let FLOAT32="{1.2f32}"
    meta let NEGATIVE_ZERO="{-0.0}"
    meta let HEX="{-255bigint:07X}"
    meta let TEXT="é🙂x"
    meta let PADDED="{TEXT:🙂^5.2s}"
    meta let INFINITY="{1.0/0.0:08}"
    assert(FIXED=="1.2"&&FIXED=="{1.25:.1f}")
    assert(SCIENTIFIC=="1.25e1"&&SCIENTIFIC=="{12.5:.2e}")
    assert(FLOAT32=="1.2"&&FLOAT32=="{1.2f32}")
    assert(NEGATIVE_ZERO=="-0.0"&&NEGATIVE_ZERO=="{-0.0}")
    assert(HEX=="-0000FF"&&HEX=="{-255bigint:07X}")
    assert(PADDED=="🙂é🙂🙂🙂"&&PADDED=="{TEXT:🙂^5.2s}")
    assert(INFINITY=="     inf"&&INFINITY=="{1.0/0.0:08}")
    assert("{advance_counter():02}{advance_counter():02}"=="0102")
    assert(count==2)
}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(source)
        .args(["--entry", "test_formatting", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}
