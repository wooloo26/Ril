use std::path::PathBuf;

use ril_lint::{LintConfig, LintLevel, lint_source};
use ril_source::span::{FileId, SourceFile};
use ril_syntax::parser::FileKind;

fn run(src: &str, config: &LintConfig) -> Result<ril_lint::LintReport, String> {
    let source = SourceFile::from_bytes(FileId(1), PathBuf::from("pkg/test.ril"), src.as_bytes())
        .map_err(|d| d.message)?;
    Ok(lint_source(&source, FileKind::Module, config))
}

#[test]
fn detects_unused_binding_and_respects_inline_allow_and_expect() -> Result<(), String> {
    let src = concat!(
        "pub fn demo() -> int {\n",
        "    let unused_a = 1\n",
        "    -- ril: allow(unused_binding) -- intentional\n",
        "    let unused_b = 2\n",
        "    -- ril: expect(unused_binding)\n",
        "    let unused_c = 3\n",
        "    42\n",
        "}\n",
    );
    let report = run(src, &LintConfig::default())?;
    let rules: Vec<&str> = report.diagnostics.iter().map(|d| d.rule.as_str()).collect();
    assert_eq!(rules, vec!["unused_binding"]);
    Ok(())
}

#[test]
fn cannot_suppress_compiler_error_code_and_reports_unfulfilled_expect() -> Result<(), String> {
    let src = concat!(
        "-- ril: allow(E0527)\n",
        "pub fn f() -> int {\n",
        "    -- ril: expect(unused_binding)\n",
        "    let x = 1\n",
        "    x\n",
        "}\n",
    );
    let report = run(src, &LintConfig::default())?;
    let rules: Vec<&str> = report.diagnostics.iter().map(|d| d.rule.as_str()).collect();
    assert!(rules.contains(&"cannot_suppress_error"), "got: {rules:?}");
    assert!(rules.contains(&"unfulfilled_expect"), "got: {rules:?}");
    assert!(report.has_denied());
    Ok(())
}

#[test]
fn f64_nan_self_comparison_is_exempt_while_int_flags() -> Result<(), String> {
    let src = concat!(
        "pub fn check(x: f64, n: int) -> (bool, bool) {\n",
        "    (x != x, n == n)\n",
        "}\n",
    );
    let report = run(src, &LintConfig::default())?;
    let self_cmps: Vec<_> = report
        .diagnostics
        .iter()
        .filter(|d| d.rule == "self_comparison")
        .collect();
    assert_eq!(
        self_cmps.len(),
        1,
        "only int self comparison should fire: {self_cmps:?}"
    );
    Ok(())
}

#[test]
fn phantom_generic_on_opaque_type_is_exempt_while_alias_flags() -> Result<(), String> {
    let src = concat!(
        "pub opaque type Conn<State>(.{ fd: int })\n",
        "pub type UnusedAlias<T, U> = T\n",
    );
    let report = run(src, &LintConfig::default())?;
    let unused_gens: Vec<_> = report
        .diagnostics
        .iter()
        .filter(|d| d.rule == "unused_generic_param")
        .collect();
    assert_eq!(
        unused_gens.len(),
        1,
        "only alias generic U should fire: {unused_gens:?}"
    );
    Ok(())
}

#[test]
fn detects_redundant_clone_and_needless_return_and_exempts_with_ctl() -> Result<(), String> {
    let src = concat!(
        "eff Ask {\n",
        "    ctl get() -> int\n",
        "}\n",
        "pub fn f(xs: []int) -> []int {\n",
        "    let copy = clone(xs)\n",
        "    return copy\n",
        "}\n",
        "pub fn g() -> int {\n",
        "    with ctl Ask::get = \\k -> k(1)\n",
        "    return Ask::get()\n",
        "}\n",
    );
    let report = run(src, &LintConfig::default())?;
    let rules: Vec<&str> = report.diagnostics.iter().map(|d| d.rule.as_str()).collect();
    assert!(rules.contains(&"redundant_clone"), "got: {rules:?}");
    let returns: Vec<_> = report
        .diagnostics
        .iter()
        .filter(|d| d.rule == "needless_return")
        .collect();
    assert_eq!(
        returns.len(),
        1,
        "only f's return should fire, not g's with ctl return"
    );
    Ok(())
}

#[test]
fn closure_braces_before_pipeline_are_exempt() -> Result<(), String> {
    let mut cfg = LintConfig::default();
    cfg.rules
        .insert("unnecessary_closure_braces".to_owned(), LintLevel::Warn);
    let src = concat!(
        "pub fn run(xs: []int) -> []int {\n",
        "    let f = \\x: int -> { x + 1 }\n",
        "    let _ = f(1)\n",
        "    xs |> Array::map \\x -> { x * 2 } |> Array::filter \\x -> x > 0\n",
        "}\n",
    );
    let report = run(src, &cfg)?;
    let brace_lints: Vec<_> = report
        .diagnostics
        .iter()
        .filter(|d| d.rule == "unnecessary_closure_braces")
        .collect();
    assert_eq!(
        brace_lints.len(),
        1,
        "only standalone closure should fire, not closure before |>: {brace_lints:?}"
    );
    Ok(())
}
