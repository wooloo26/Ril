//! Immutable static DAGs are initialized once and retain their graph identities.
use std::{fs, process::Command};

fn executes(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("constants.ril");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn shared_children_remain_shared_and_equal_allocations_stay_distinct() {
    executes(ril_test::case_source(
        "tests/regressions/static.ril::shared-and-distinct",
    ));
}

#[test]
fn later_meta_projections_reference_the_original_child() {
    executes(ril_test::case_source(
        "tests/regressions/static.ril::later-projection",
    ));
}

#[test]
fn map_order_and_variant_payloads_preserve_shared_children() {
    executes(ril_test::case_source(
        "tests/regressions/static.ril::map-and-variant",
    ));
}

#[test]
fn worker_allocation_pressure_keeps_constant_pool_roots() {
    executes(ril_test::case_source(
        "tests/regressions/static.ril::worker-allocation-pressure",
    ));
}

#[test]
fn pool_initialization_survives_collection_between_node_and_cell_publication() {
    // Each empty array needs an array, a cell and its key. These 400 distinct
    // nodes therefore cross Runtime's initial 1024-object collection threshold
    // before user code runs, even without counting the outer array or units.
    let children = vec!["[]"; 400].join(",");
    executes(&format!(
        r#"
meta let ROOT:[][]int = [{children}]
pub fn test_native() &{{ROOT}} {{
    let mut copied = ^mut clone(ROOT)
    copied[0] !> Array::push(7)
    assert(copied[0]==[7] && len(copied[1])==0 && len(copied[399])==0)
    assert(len(ROOT)==400 && len(ROOT[0])==0 && len(ROOT[399])==0)
}}
"#,
    ));
}

#[test]
fn distinct_static_shells_still_share_their_children() {
    executes(
        r#"
meta let A = {let child=[1];[child,child]}
meta let B = Array::reverse(A)
pub fn test_native() &{A,B} {
    let mut copied = ^mut clone((A,B))
    (copied.0)[0] !> Array::push(9)
    assert((copied.0)[1] == [1,9] && (copied.1)[0] == [1,9] && (copied.1)[1] == [1,9])
    copied.0 !> Array::push([2])
    assert(len(copied.0)==3 && len(copied.1)==2)
    assert(A[0]==[1] && B[0]==[1])
}
"#,
    );
}

#[test]
fn empty_optional_and_typed_scalar_nodes_have_their_actual_native_representation() {
    executes(
        r#"
meta let EMPTY:[]int = []
meta let OPTIONS:[]?[]int = [None, Some([7])]
meta let SCALARS = (1, 255u8, -7i64, 18446744073709551616bigint, 1.5f32, b"\x00\xFF", "pool", true)
meta fn pair()->([2]int,[]i64){([1,2],[3i64])}
meta let FIXED=pair()
pub fn test_native() &{EMPTY,OPTIONS,SCALARS,FIXED} {
    let mut copied = ^mut clone((EMPTY,EMPTY))
    copied.0 !> Array::push(1)
    assert(copied.1==[1] && len(EMPTY)==0)
    assert(OPTIONS[0]==None && OPTIONS[1]==Some([7]))
    let ordinary:int=SCALARS.0
    let byte:u8=SCALARS.1
    let wide:i64=SCALARS.2
    assert(ordinary==1 && byte==255u8 && wide == -7i64)
    assert(SCALARS.3==18446744073709551616bigint && SCALARS.4+0.5f32==2.0f32)
    assert(SCALARS.5==b"\x00\xFF" && SCALARS.6=="pool" && SCALARS.7)
    let mut fixed=^mut clone(FIXED)
    fixed.0[0]=8
    assert(fixed.0==[8,2] && fixed.1==[3i64] && FIXED.0==[1,2])
}
"#,
    );
}

#[test]
fn constant_references_are_shared_between_normal_and_metered_entries() {
    executes(
        r#"
meta let ROOT = {let child=[7];(child,child)}
fn read()->int &{ROOT}{ROOT.0[0]+ROOT.1[0]}
fn measured(limit:int)->?int &{ROOT}{with Div::exhausted()->None;Some(Div::budget(limit,read))}
fn read_child()->[]int &{ROOT}{ROOT.0}
fn measured_child()->?[]int &{ROOT}{with Div::exhausted()->None;Some(Div::budget(1,read_child))}
pub fn test_native() &{ROOT}{
    assert(read()==14)
    assert(measured(0)==None && measured(1)==Some(14))
    let selected=match measured_child(){Some(value)->value,None->panic("budget unexpectedly exhausted")}
    let mut copied=^mut clone((read_child(),selected))
    copied.0 !> Array::push(8)
    assert(copied.1==[7,8] && read()==14)
}
"#,
    );
}

#[test]
fn static_local_names_do_not_select_same_named_runtime_functions() {
    executes(
        r#"
meta let ROOT={let child=[7];(child,child)}
fn child()->[]int &{ROOT}{ROOT.0}
pub fn test_native() &{ROOT}{
    let mut copied=^mut clone((ROOT,child()))
    copied.1 !> Array::push(8)
    assert((copied.0).0==[7,8] && (copied.0).1==[7,8])
    assert(ROOT.0==[7] && child()==[7])
}
"#,
    );
}
