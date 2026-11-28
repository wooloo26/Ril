use std::path::PathBuf;

use ril_driver::{
    CompileOptions, Compiler,
    fix::{FixOptions, fix_virtual_package},
    inspect::InspectQuery,
};
use ril_lint::LintConfig;
use ril_source::fix::{FixKind, FixSafety};
use ril_test::{Stage, Unit, VirtualPackage};

fn make_pkg(unit: Unit, source: &str) -> VirtualPackage {
    let mut pkg = VirtualPackage::new(unit);
    pkg.insert(PathBuf::from("pkg/main.ril"), source.as_bytes().to_vec());
    pkg
}

fn pkg_text(pkg: &VirtualPackage) -> Result<String, String> {
    let vfile = pkg
        .files
        .get(&PathBuf::from("pkg/main.ril"))
        .ok_or_else(|| "missing pkg/main.ril".to_owned())?;
    String::from_utf8(vfile.bytes.clone()).map_err(|e| e.to_string())
}

#[test]
fn fix_converges_missing_stdlib_import_and_multihop_io_chain() -> Result<(), String> {
    let src = concat!(
        "fn leaf(msg: str) -> () {\n",
        "    Io::println(msg)\n",
        "}\n\n",
        "fn mid(msg: str) -> () {\n",
        "    leaf(msg)\n",
        "}\n\n",
        "fn main() -> () {\n",
        "    mid(\"hello\")\n",
        "}\n",
    );
    let compiler = Compiler::new(CompileOptions::default());
    let mut pkg = make_pkg(Unit::Bin, src);
    let report = fix_virtual_package(
        &compiler,
        &mut pkg,
        &FixOptions::default(),
        &LintConfig::default(),
    );

    assert!(report.syntax_errors.is_empty(), "{report:#?}");
    assert!(report.converged, "expected convergence: {report:#?}");
    assert!(!report.oscillated, "unexpected oscillation: {report:#?}");
    let updated = pkg_text(&pkg)?;
    assert!(
        report.remaining_errors.is_empty(),
        "expected zero remaining errors, got: {:?}\nupdated:\n{updated}",
        report.remaining_errors,
    );
    assert!(
        report.has_capability_widening(),
        "expected capability delta banner for @io"
    );
    let banner = report
        .format_capability_banner()
        .ok_or_else(|| "expected non-empty capability banner".to_owned())?;
    assert!(banner.contains("+@io"), "banner missing +@io:\n{banner}");

    assert!(
        updated.contains("use ril/io\n"),
        "missing import:\n{updated}"
    );
    assert!(
        updated.contains("fn leaf(msg: str) @io -> ()"),
        "leaf:\n{updated}"
    );
    assert!(
        updated.contains("fn mid(msg: str) @io -> ()"),
        "mid:\n{updated}"
    );
    assert!(updated.contains("fn main() @io -> ()"), "main:\n{updated}");

    // Verify final package passes full Stage::Access cleanly.
    let checked = compiler.check(&pkg, Stage::Access);
    assert!(
        checked.result.diagnostics.is_empty(),
        "checked diagnostics: {:?}",
        checked.result.diagnostics
    );
    Ok(())
}

#[test]
fn fix_repairs_callsite_mode_pipeline_and_mut_signature_multipass() -> Result<(), String> {
    let src = concat!(
        "use ril/array\n\n",
        "fn make_items() -> []int {\n",
        "    [1, 2]\n",
        "}\n\n",
        "fn push_one(mut xs: []int) -> () {\n",
        "    Array::push(xs, 3)\n",
        "}\n\n",
        "fn main() -> () {\n",
        "    let mut xs = make_items()\n",
        "    xs |> push_one\n",
        "    let _ = len(ref xs)\n",
        "}\n",
    );
    let compiler = Compiler::new(CompileOptions::default());
    let mut pkg = make_pkg(Unit::Bin, src);
    let report = fix_virtual_package(
        &compiler,
        &mut pkg,
        &FixOptions::default(),
        &LintConfig::default(),
    );

    assert!(report.syntax_errors.is_empty(), "{report:#?}");
    let updated = pkg_text(&pkg)?;
    assert!(
        report.remaining_errors.is_empty(),
        "remaining errors: {:?}\nupdated:\n{updated}",
        report.remaining_errors,
    );
    assert!(
        updated.contains("-> new []int"),
        "expected -> new on make_items:\n{updated}"
    );
    assert!(
        updated.contains("fn push_one(mut xs: []int) -> ()"),
        "expected push_one signature:\n{updated}"
    );
    assert!(
        updated.contains("Array::push(mut xs, 3)"),
        "expected call-site mut marker:\n{updated}"
    );
    assert!(
        updated.contains("xs |> mut push_one"),
        "expected pipeline mut marker:\n{updated}"
    );
    Ok(())
}

#[test]
fn fix_stops_at_pub_api_boundary_unless_allow_api_change() -> Result<(), String> {
    let src = concat!(
        "use ril/io\n\n",
        "fn inner() -> () {\n",
        "    Io::println(\"hi\")\n",
        "}\n\n",
        "pub fn greet() -> () {\n",
        "    inner()\n",
        "}\n",
    );
    let compiler = Compiler::new(CompileOptions::default());
    let mut pkg = make_pkg(Unit::Lib, src);

    // Default run: fixes private `inner`, refuses `pub fn greet` with Contract skip + causal chain.
    let report = fix_virtual_package(
        &compiler,
        &mut pkg,
        &FixOptions::default(),
        &LintConfig::default(),
    );
    assert!(
        report
            .skipped
            .iter()
            .any(|s| s.safety == FixSafety::Contract && s.title.contains("greet")),
        "expected Contract skip for pub fn greet, got: {:#?}",
        report.skipped
    );
    let mid_text = pkg_text(&pkg)?;
    assert!(
        mid_text.contains("fn inner() @io -> ()"),
        "private inner should be fixed:\n{mid_text}"
    );
    assert!(
        mid_text.contains("pub fn greet() -> ()"),
        "pub fn greet must remain unchanged by default:\n{mid_text}"
    );

    // Explicit opt-in `--allow-api-change`: updates `pub fn greet` and converges cleanly.
    let opts = FixOptions {
        allow_api_change: true,
        ..FixOptions::default()
    };
    let report2 = fix_virtual_package(&compiler, &mut pkg, &opts, &LintConfig::default());
    assert!(
        report2.remaining_errors.is_empty(),
        "remaining errors after --allow-api-change: {:?}",
        report2.remaining_errors
    );
    let final_text = pkg_text(&pkg)?;
    assert!(
        final_text.contains("pub fn greet() @io -> ()"),
        "expected pub fn greet to receive @io:\n{final_text}"
    );
    Ok(())
}

#[test]
fn fix_refuses_syntax_errors_and_user_effects_on_main() -> Result<(), String> {
    let compiler = Compiler::new(CompileOptions::default());

    // 1. Syntax error refusal
    let bad = "fn broken( -> int { 1 }\n";
    let mut bad_pkg = make_pkg(Unit::Lib, bad);
    let bad_report = fix_virtual_package(
        &compiler,
        &mut bad_pkg,
        &FixOptions::default(),
        &LintConfig::default(),
    );
    assert!(
        !bad_report.syntax_errors.is_empty(),
        "expected syntax error refusal"
    );
    assert!(bad_report.modified_files.is_empty());
    assert_eq!(pkg_text(&bad_pkg)?, bad);

    // 2. User effect on `fn main` must never be added
    let user_eff_main = concat!(
        "eff Log {\n",
        "    fn write(msg: str) -> ()\n",
        "}\n\n",
        "fn main() -> () {\n",
        "    Log::write(\"hi\")\n",
        "}\n",
    );
    let mut main_pkg = make_pkg(Unit::Bin, user_eff_main);
    let main_report = fix_virtual_package(
        &compiler,
        &mut main_pkg,
        &FixOptions::default(),
        &LintConfig::default(),
    );
    assert_eq!(
        pkg_text(&main_pkg)?,
        user_eff_main,
        "fn main must not be rewritten with user @Log"
    );
    assert!(
        main_report
            .skipped
            .iter()
            .any(|s| s.reason.contains("fn main")),
        "expected skip explaining fn main restriction: {:#?}",
        main_report.skipped
    );
    Ok(())
}

#[test]
fn fix_dry_run_does_not_mutate_package_and_inspect_fix_hints_works() -> Result<(), String> {
    let src = concat!(
        "use ril/io\n\n",
        "fn say() -> () {\n",
        "    Io::println(\"hello\")\n",
        "}\n\n",
        "fn main() -> () {\n",
        "    say()\n",
        "}\n",
    );
    let compiler = Compiler::new(CompileOptions::default());
    let mut pkg = make_pkg(Unit::Bin, src);

    // Dry-run produces modified_files diff but leaves VirtualPackage untouched.
    let dry_opts = FixOptions {
        dry_run: true,
        ..FixOptions::default()
    };
    let dry_report = fix_virtual_package(&compiler, &mut pkg, &dry_opts, &LintConfig::default());
    assert!(!dry_report.modified_files.is_empty());
    assert_eq!(pkg_text(&pkg)?, src, "dry-run must not mutate package");

    // Inspect `--include fix_hints` validates cleanly and returns structured signature hints.
    let query = InspectQuery {
        includes: vec!["fix_hints".into()],
        ..InspectQuery::default()
    };
    assert!(query.validate().is_ok());
    let reserved = InspectQuery {
        includes: vec!["mir_summary".into()],
        ..InspectQuery::default()
    };
    assert!(reserved.validate().is_err());

    let inspect_report = compiler.inspect_package(&pkg, &query);
    assert!(
        inspect_report.fix_hints.iter().any(|h| {
            h.kind == FixKind::SignatureSync
                && h.capability_delta
                    .as_ref()
                    .is_some_and(|d| d.symbol == "say" && d.added.contains(&"@io".to_owned()))
        }),
        "expected fix_hint for `fn say` +@io, got: {:#?}",
        inspect_report.fix_hints
    );
    Ok(())
}
