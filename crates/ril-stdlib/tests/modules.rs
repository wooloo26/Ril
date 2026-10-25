#[test]
fn bundled_modules_parse_as_ordinary_language_declarations() {
    let mut failures = Vec::new();
    for module in ril_stdlib::MODULES {
        let parsed = ril_syntax::parse(module.source);
        if !parsed.is_ok() {
            failures.push(format!("{}: {:?}", module.path, parsed.diagnostics));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
