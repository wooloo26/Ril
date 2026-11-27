#![forbid(unsafe_code)]

use std::io::Cursor;

use serde_json::{Value, json};

fn frame_lsp(msg: &Value) -> Vec<u8> {
    let body = serde_json::to_vec(msg).unwrap_or_default();
    let mut out = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
    out.extend_from_slice(&body);
    out
}

fn parse_lsp_frames(bytes: &[u8]) -> Result<Vec<Value>, String> {
    let mut out = Vec::new();
    let mut rest = bytes;
    while !rest.is_empty() {
        let sep = rest
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .ok_or("missing LSP header separator")?;
        let header = std::str::from_utf8(rest.get(..sep).ok_or("header slice")?)
            .map_err(|e| e.to_string())?;
        let len: usize = header
            .lines()
            .find_map(|l| l.strip_prefix("Content-Length:"))
            .ok_or("missing Content-Length")?
            .trim()
            .parse()
            .map_err(|e: std::num::ParseIntError| e.to_string())?;
        let body_start = sep + 4;
        let body = rest
            .get(body_start..body_start + len)
            .ok_or("truncated LSP body")?;
        let val: Value = serde_json::from_slice(body).map_err(|e| e.to_string())?;
        out.push(val);
        rest = rest.get(body_start + len..).ok_or("advance slice")?;
    }
    Ok(out)
}

#[test]
fn lsp_jsonrpc_diagnostics_hover_definition_and_formatting() -> Result<(), String> {
    let uri = "file:///workspace/pkg/demo.ril";
    let broken = "fn helper(x: int) -> int { x + 1 }\nfn main() -> () { let _: int = \"oops\" }\n";
    let fixed = "fn helper(x: int) -> int {\n    x + 1\n}\n\nfn main() -> () {\n    let y = helper(41)\n    assert(y == 42)\n}\n";

    let mut input = Vec::new();
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {}
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": { "uri": uri, "languageId": "ril", "version": 1, "text": broken }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": uri, "version": 2 },
            "contentChanges": [{ "text": fixed }]
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": uri },
            "position": { "line": 5, "character": 14 }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": uri },
            "position": { "line": 5, "character": 14 }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/formatting",
        "params": {
            "textDocument": { "uri": uri },
            "options": { "tabSize": 4, "insertSpaces": true }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "shutdown",
        "params": null
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "exit"
    })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;
    assert_eq!(frames.len(), 7, "expected 7 LSP messages, got {frames:#?}");

    assert_eq!(
        frames
            .first()
            .and_then(|v| v.pointer("/result/capabilities/hoverProvider")),
        Some(&json!(true))
    );
    let diags_open = frames
        .get(1)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing open diagnostics")?;
    assert!(
        diags_open
            .iter()
            .any(|d| d.get("code") == Some(&json!("E0301"))),
        "expected E0301 in didOpen diagnostics: {diags_open:?}"
    );
    let diags_fixed = frames
        .get(2)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing change diagnostics")?;
    assert!(
        diags_fixed.is_empty(),
        "expected clean diagnostics: {diags_fixed:?}"
    );
    let hover_text = frames
        .get(3)
        .and_then(|v| v.pointer("/result/contents/value"))
        .and_then(Value::as_str)
        .ok_or("missing hover contents")?;
    assert!(
        hover_text.contains("fn helper") && hover_text.contains("int"),
        "unexpected hover: {hover_text}"
    );
    assert_eq!(
        frames
            .get(4)
            .and_then(|v| v.pointer("/result/range/start/line")),
        Some(&json!(0))
    );
    assert!(
        frames
            .get(5)
            .and_then(|v| v.pointer("/result/0/newText"))
            .and_then(Value::as_str)
            .is_some()
    );
    Ok(())
}

#[test]
fn lsp_real_workspace_cross_file_and_stdlib_definition() -> Result<(), String> {
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let main_path = repo_root.join("examples/hello/src/main.ril");
    let main_text = std::fs::read_to_string(&main_path).map_err(|e| e.to_string())?;
    let root_uri = format!("file://{}", repo_root.display());
    let main_uri = format!("file://{}", main_path.display());

    // Find exact 0-based (line, col) of `Math::square` and `Array::at` and `Array::map`.
    let locate = |needle: &str| -> Result<(usize, usize), String> {
        for (line_idx, line) in main_text.lines().enumerate() {
            if let Some(col) = line.find(needle) {
                return Ok((line_idx, col + needle.len().saturating_sub(2)));
            }
        }
        Err(format!(
            "needle {needle:?} not found in examples/hello/src/main.ril"
        ))
    };
    let (sq_line, sq_col) = locate("Math::square")?;
    let (at_line, at_col) = locate("Array::push")?;
    let (map_line, map_col) = locate("Array::map")?;

    let mut input = Vec::new();
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": { "rootUri": root_uri }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": { "uri": main_uri, "languageId": "ril", "version": 1, "text": main_text }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": sq_line, "character": sq_col }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": at_line, "character": at_col }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": main_uri },
            "position": { "line": map_line, "character": map_col }
        }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "shutdown",
        "params": null
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "exit"
    })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;
    assert_eq!(frames.len(), 6, "expected 6 LSP messages, got {frames:#?}");

    // 1. Clean diagnostics on examples/hello/src/main.ril
    let diags = frames
        .get(1)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing diagnostics")?;
    assert!(
        diags.is_empty(),
        "expected clean example diagnostics: {diags:?}"
    );

    // 2. Cross-file Go-To-Definition jumps to examples/hello/src/math.ril
    let math_uri = frames
        .get(2)
        .and_then(|v| v.pointer("/result/uri"))
        .and_then(Value::as_str)
        .ok_or("missing cross-file definition uri")?;
    assert!(
        math_uri.ends_with("examples/hello/src/math.ril"),
        "expected definition in math.ril, got {math_uri}"
    );

    // 3. Stdlib Go-To-Definition jumps directly into std/array.ril!
    let std_uri = frames
        .get(3)
        .and_then(|v| v.pointer("/result/uri"))
        .and_then(Value::as_str)
        .ok_or("missing stdlib definition uri")?;
    assert!(
        std_uri.ends_with("std/array.ril"),
        "expected definition in std/array.ril, got {std_uri}"
    );

    // 4. Hover on Array::map displays its signature from std/array.ril
    let hover = frames
        .get(4)
        .and_then(|v| v.pointer("/result/contents/value"))
        .and_then(Value::as_str)
        .ok_or("missing Array::map hover")?;
    assert!(hover.contains("fn map"), "unexpected hover: {hover}");
    Ok(())
}

#[test]
fn lsp_prelude_definitions_jump_to_std_prelude_ril() -> Result<(), String> {
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let root_uri = format!("file://{}", repo_root.display());
    let doc_uri = format!("file://{}/pkg/prelude_jump.ril", repo_root.display());
    let source = concat!(
        "use ril/panic\n",
        "type Rec(.{ a: int })\n",
        "type S = SharedObject<Rec>\n",
        "fn check<T |> InnerTarget>(t: T, x: Option<int>, y: Result<int, Panic::Error>) -> int {\n",
        "    let _ = t\n",
        "    let fallback = match y {\n",
        "        Ok(n) -> n\n",
        "        Err(_) -> 0\n",
        "    }\n",
        "    match x {\n",
        "        Some(v) -> len([v]) + fallback\n",
        "        None -> fallback\n",
        "    }\n",
        "}\n",
    );

    let locate = |needle: &str| -> Result<(usize, usize), String> {
        for (line_idx, line) in source.lines().enumerate() {
            if let Some(col) = line.find(needle) {
                return Ok((line_idx, col + 1));
            }
        }
        Err(format!("needle {needle:?} not found"))
    };
    let (opt_line, opt_col) = locate("Option")?;
    let (res_line, res_col) = locate("Result")?;
    let (panic_line, panic_col) = locate("Error")?;
    let (len_line, len_col) = locate("len(")?;
    let (so_line, so_col) = locate("SharedObject")?;
    let (inner_line, inner_col) = locate("InnerTarget")?;

    let mut input = Vec::new();
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": { "rootUri": root_uri }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": { "uri": doc_uri, "languageId": "ril", "version": 1, "text": source }
        }
    })));
    for (req_id, (line, col)) in [
        (2, (opt_line, opt_col)),
        (3, (res_line, res_col)),
        (4, (panic_line, panic_col)),
        (5, (len_line, len_col)),
        (6, (so_line, so_col)),
        (7, (inner_line, inner_col)),
    ] {
        input.extend(frame_lsp(&json!({
            "jsonrpc": "2.0",
            "id": req_id,
            "method": "textDocument/definition",
            "params": {
                "textDocument": { "uri": doc_uri },
                "position": { "line": line, "character": col }
            }
        })));
    }
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 8,
        "method": "shutdown",
        "params": null
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "exit"
    })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;
    assert_eq!(frames.len(), 9, "expected 9 LSP messages, got {frames:#?}");

    let diags = frames
        .get(1)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing diagnostics")?;
    assert!(diags.is_empty(), "expected clean diagnostics: {diags:?}");

    for (idx, label, expected_suffix) in [
        (2, "Option", "std/prelude.ril"),
        (3, "Result", "std/prelude.ril"),
        (4, "Panic::Error", "std/panic.ril"),
        (5, "len", "std/prelude.ril"),
        (6, "SharedObject", "std/prelude.ril"),
        (7, "InnerTarget", "std/prelude.ril"),
    ] {
        let uri = frames
            .get(idx)
            .and_then(|v| v.pointer("/result/uri"))
            .and_then(Value::as_str)
            .ok_or_else(|| format!("missing definition uri for {label}: {:?}", frames.get(idx)))?;
        assert!(
            uri.ends_with(expected_suffix),
            "expected {label} definition in {expected_suffix}, got {uri}"
        );
    }
    Ok(())
}

#[test]
fn lsp_stdlib_bodyless_primitives_have_zero_diagnostics() -> Result<(), String> {
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let root_uri = format!("file://{}", repo_root.display());

    let mut input = Vec::new();
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": { "rootUri": root_uri }
    })));
    let std_files = [
        "std/prelude.ril",
        "std/array.ril",
        "std/string.ril",
        "std/io.ril",
        "std/file.ril",
        "std/panic.ril",
    ];
    for rel in std_files {
        let path = repo_root.join(rel);
        let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let uri = format!("file://{}", path.display());
        input.extend(frame_lsp(&json!({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": { "uri": uri, "languageId": "ril", "version": 1, "text": text }
            }
        })));
    }
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "shutdown",
        "params": null
    })));
    input.extend(frame_lsp(&json!({ "jsonrpc": "2.0", "method": "exit" })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;
    assert_eq!(frames.len(), 2 + std_files.len());

    for (idx, rel) in std_files.iter().enumerate() {
        let diags = frames
            .get(1 + idx)
            .and_then(|v| v.pointer("/params/diagnostics"))
            .and_then(Value::as_array)
            .ok_or_else(|| format!("missing diagnostics for {rel}"))?;
        assert!(
            diags.is_empty(),
            "expected zero diagnostics when opening {rel}, got: {diags:#?}"
        );
    }
    Ok(())
}

#[test]
fn lsp_pipeline_auto_suggestion_and_signature_help() -> Result<(), String> {
    let uri = "file:///workspace/pkg/pipe_demo.ril";
    let src = "\
fn double_int(x: int) -> int { x * 2 }

fn demo() -> () {
    let nums = [1, 2, 3]
    let text = \"hello world\"
    let fallible: !<str, str> = Ok(\"hi\")
    let _a = nums |> 
    let _b = text |> 
    let _c = fallible |?> 
    let _d = nums |> mut 
    let _e = nums.
    let _f = nums |> Array::map(
}
";

    let mut input = Vec::new();
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": { "initializationOptions": { "dotToPipe": true, "autoImport": true } }
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": { "uri": uri, "languageId": "ril", "version": 1, "text": src }
        }
    })));
    // id 2: `nums |> ` (line 6, col 21)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/completion",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 6, "character": 21 } }
    })));
    // id 3: `text |> ` (line 7, col 21)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/completion",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 7, "character": 21 } }
    })));
    // id 4: `fallible |?> ` (line 8, col 26)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/completion",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 8, "character": 26 } }
    })));
    // id 5: `nums |> mut ` (line 9, col 25)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "textDocument/completion",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 9, "character": 25 } }
    })));
    // id 6: `nums.` dot-to-pipe (line 10, col 18)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 6,
        "method": "textDocument/completion",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 10, "character": 18 } }
    })));
    // id 7: pipeline-aware signatureHelp on `nums |> Array::map(` (line 11, col 32)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 7,
        "method": "textDocument/signatureHelp",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 11, "character": 32 } }
    })));
    input.extend(frame_lsp(
        &json!({ "jsonrpc": "2.0", "id": 8, "method": "shutdown", "params": null }),
    ));
    input.extend(frame_lsp(&json!({ "jsonrpc": "2.0", "method": "exit" })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;

    let labels = |frame_idx: usize| -> Vec<String> {
        frames
            .get(frame_idx)
            .and_then(|v| v.pointer("/result/items"))
            .and_then(Value::as_array)
            .map(|arr| {
                arr.iter()
                    .filter_map(|it| it.get("label").and_then(Value::as_str).map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default()
    };

    // `nums |> ` suggests Array functions + `len`, NOT String::split or double_int
    let nums_labels = labels(2);
    assert!(
        nums_labels.iter().any(|l| l == "Array::map")
            && nums_labels.iter().any(|l| l == "mut Array::push")
            && nums_labels.iter().any(|l| l == "len"),
        "expected Array::map, mut Array::push, len for []int pipeline, got: {nums_labels:?}"
    );
    assert!(
        !nums_labels
            .iter()
            .any(|l| l == "String::split" || l == "double_int"),
        "should not recommend incompatible String::split/double_int for []int: {nums_labels:?}"
    );

    // `text |> ` suggests String functions + `len`, NOT Array::map
    let text_labels = labels(3);
    assert!(
        text_labels.iter().any(|l| l == "String::split")
            && text_labels.iter().any(|l| l == "String::starts_with")
            && text_labels.iter().any(|l| l == "len"),
        "expected String::split/starts_with/len for str pipeline, got: {text_labels:?}"
    );
    assert!(
        !text_labels.iter().any(|l| l == "Array::map"),
        "should not recommend Array::map for str: {text_labels:?}"
    );

    // `fallible |?> ` unwraps `!<str, str>` -> `str` and suggests `String::split` + auto-import `File::read`
    let prop_items = frames
        .get(4)
        .and_then(|v| v.pointer("/result/items"))
        .and_then(Value::as_array)
        .ok_or("missing |?> completion items")?;
    let prop_labels: Vec<&str> = prop_items
        .iter()
        .filter_map(|it| it.get("label").and_then(Value::as_str))
        .collect();
    assert!(
        prop_labels.contains(&"String::split"),
        "expected unwrapped str suggestions for |?>, got: {prop_labels:?}"
    );
    let file_read = prop_items
        .iter()
        .find(|it| it.get("label").and_then(Value::as_str) == Some("File::read"));
    assert!(
        file_read
            .and_then(|it| it.pointer("/additionalTextEdits/0/newText"))
            .and_then(Value::as_str)
            == Some("use ril/file\n"),
        "expected auto-import edit for File::read, got: {file_read:?}"
    );

    // `nums |> mut ` omits duplicate `mut` prefix on Array::push
    let mut_labels = labels(5);
    assert!(
        mut_labels.iter().any(|l| l == "Array::push")
            && !mut_labels.iter().any(|l| l == "mut Array::push"),
        "expected Array::push without duplicate mut, got: {mut_labels:?}"
    );

    // `nums.` dot-to-pipe offers `|> Array::map` rewriting `.` into ` |> Array::map(...)`
    let dot_items = frames
        .get(6)
        .and_then(|v| v.pointer("/result/items"))
        .and_then(Value::as_array)
        .ok_or("missing dot-to-pipe items")?;
    assert!(
        dot_items.iter().any(|it| {
            it.get("label").and_then(Value::as_str) == Some("|> Array::map")
                && it
                    .pointer("/textEdit/newText")
                    .and_then(Value::as_str)
                    .is_some_and(|t| t.starts_with(" |> Array::map("))
        }),
        "expected dot-to-pipe rewrite for Array::map, got: {dot_items:?}"
    );

    // Pipeline-aware signatureHelp skips param 0 (`xs`) and highlights param 1 (`f`)
    assert_eq!(
        frames
            .get(7)
            .and_then(|v| v.pointer("/result/activeParameter")),
        Some(&json!(1)),
        "expected activeParameter == 1 in piped Array::map(, got: {:?}",
        frames.get(7)
    );
    Ok(())
}

#[test]
fn lsp_semantic_tokens_navigation_symbols_inlay_and_code_actions() -> Result<(), String> {
    let uri = "file:///workspace/pkg/ide_demo.ril";
    let src = "\
-- Adds one to an integer.
fn inc(n: int) -> int {
    n + 1
}

fn main() -> () {
    let base = 41
    let res = inc(base)
    let opt = Some(res)
    assert(opt == Some(42))
}
";

    let mut input = Vec::new();
    input.extend(frame_lsp(
        &json!({ "jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {} }),
    ));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": { "textDocument": { "uri": uri, "languageId": "ril", "version": 1, "text": src } }
    })));
    // id 2: semantic tokens
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/semanticTokens/full",
        "params": { "textDocument": { "uri": uri } }
    })));
    // id 3: hover on `inc` call (line 7, col 15) — should include doc comment!
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 7, "character": 15 } }
    })));
    // id 4: references for `inc`
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/references",
        "params": {
            "textDocument": { "uri": uri },
            "position": { "line": 1, "character": 4 },
            "context": { "includeDeclaration": true }
        }
    })));
    // id 5: rename `inc` -> `increment`
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "textDocument/rename",
        "params": {
            "textDocument": { "uri": uri },
            "position": { "line": 1, "character": 4 },
            "newName": "increment"
        }
    })));
    // id 6: documentSymbol
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 6,
        "method": "textDocument/documentSymbol",
        "params": { "textDocument": { "uri": uri } }
    })));
    // id 7: inlayHint
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 7,
        "method": "textDocument/inlayHint",
        "params": {
            "textDocument": { "uri": uri },
            "range": { "start": { "line": 0, "character": 0 }, "end": { "line": 12, "character": 0 } }
        }
    })));
    // id 8: codeAction quickfix for missing `use ril/file`
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 8,
        "method": "textDocument/codeAction",
        "params": {
            "textDocument": { "uri": uri },
            "range": { "start": { "line": 7, "character": 0 }, "end": { "line": 7, "character": 10 } },
            "context": {
                "diagnostics": [{
                    "range": { "start": { "line": 7, "character": 0 }, "end": { "line": 7, "character": 5 } },
                    "severity": 1,
                    "code": "E0204",
                    "message": "cannot resolve File"
                }]
            }
        }
    })));
    input.extend(frame_lsp(
        &json!({ "jsonrpc": "2.0", "id": 9, "method": "shutdown", "params": null }),
    ));
    input.extend(frame_lsp(&json!({ "jsonrpc": "2.0", "method": "exit" })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;

    // Semantic tokens non-empty & multiple of 5, containing parameter token (type index 4)
    let sem_data = frames
        .get(2)
        .and_then(|v| v.pointer("/result/data"))
        .and_then(Value::as_array)
        .ok_or("missing semanticTokens data")?;
    assert!(!sem_data.is_empty() && sem_data.len() % 5 == 0);
    let has_param_token = sem_data
        .chunks_exact(5)
        .any(|c| c.get(3).and_then(Value::as_u64) == Some(4));
    assert!(
        has_param_token,
        "expected parameter semantic token (type=4)"
    );

    // Hover includes doc comment
    let hover_val = frames
        .get(3)
        .and_then(|v| v.pointer("/result/contents/value"))
        .and_then(Value::as_str)
        .unwrap_or("");
    assert!(
        hover_val.contains("fn inc") && hover_val.contains("Adds one to an integer."),
        "expected doc comment in hover, got: {hover_val}"
    );

    // References finds both declaration and call site (>= 2)
    let refs = frames
        .get(4)
        .and_then(|v| v.get("result"))
        .and_then(Value::as_array)
        .ok_or("missing references")?;
    assert!(
        refs.len() >= 2,
        "expected >= 2 references for inc, got: {refs:?}"
    );

    // Rename produces edits at both declaration and call site
    let rename_edits = frames
        .get(5)
        .and_then(|v| v.pointer("/result/changes"))
        .and_then(|c| c.get(uri))
        .and_then(Value::as_array)
        .ok_or("missing rename edits")?;
    assert_eq!(
        rename_edits.len(),
        2,
        "expected 2 rename edits: {rename_edits:?}"
    );

    // Document symbols contain `inc` and `main`
    let syms = frames
        .get(6)
        .and_then(|v| v.get("result"))
        .and_then(Value::as_array)
        .ok_or("missing document symbols")?;
    let sym_names: Vec<&str> = syms
        .iter()
        .filter_map(|s| s.get("name").and_then(Value::as_str))
        .collect();
    assert!(sym_names.contains(&"inc") && sym_names.contains(&"main"));

    // Inlay hints contain `: int` for `let base = 41`
    let hints = frames
        .get(7)
        .and_then(|v| v.get("result"))
        .and_then(Value::as_array)
        .ok_or("missing inlay hints")?;
    assert!(
        hints
            .iter()
            .any(|h| h.get("label").and_then(Value::as_str) == Some(": int")),
        "expected `: int` inlay hint, got: {hints:?}"
    );

    // Code action quickfix imports `ril/file`
    let actions = frames
        .get(8)
        .and_then(|v| v.get("result"))
        .and_then(Value::as_array)
        .ok_or("missing code actions")?;
    assert!(
        actions.iter().any(|a| {
            a.get("title")
                .and_then(Value::as_str)
                .is_some_and(|t| t.contains("ril/file"))
        }),
        "expected Import ril/file code action, got: {actions:?}"
    );
    Ok(())
}

#[test]
fn lsp_hover_inlay_and_w0601_surface_behavior_and_provenance() -> Result<(), String> {
    let uri = "file:///workspace/provenance.ril";
    let source = concat!(
        "use ril/io\n",
        "fn clamp(x: int, lo: int, hi: int) -> int {\n",
        "    if x < lo { lo } else if x > hi { hi } else { x }\n",
        "}\n",
        "fn flush_batch(mut buf: []int, idx: int) &mut -> int {\n",
        "    defer assert(len(ref buf) == 0, \"unflushed\")\n",
        "    let head = buf[idx]\n",
        "    Array::clear(mut buf)\n",
        "    head\n",
        "}\n",
        "fn main() @io -> () {\n",
        "    let mut out = [1, 2]\n",
        "    let log_push = \\x: int -> {\n",
        "        Io::println(String::inspect(x))\n",
        "        Array::push(mut out, x)\n",
        "    }\n",
        "    log_push(clamp(3, 0, 5))\n",
        "    let _ = flush_batch(mut out, 0)\n",
        "}\n",
    );

    let mut input = Vec::new();
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {}
    })));
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": { "uri": uri, "languageId": "ril", "version": 1, "text": source }
        }
    })));
    // id 2: hover on `clamp` (pure + total)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 1, "character": 4 } }
    })));
    // id 3: hover on `flush_batch` (&mut(buf) + May panic + May abort process)
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": uri }, "position": { "line": 4, "character": 5 } }
    })));
    // id 4: inlayHint over the whole file
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/inlayHint",
        "params": {
            "textDocument": { "uri": uri },
            "range": { "start": { "line": 0, "character": 0 }, "end": { "line": 19, "character": 0 } }
        }
    })));
    input.extend(frame_lsp(
        &json!({ "jsonrpc": "2.0", "id": 5, "method": "shutdown", "params": null }),
    ));
    input.extend(frame_lsp(&json!({ "jsonrpc": "2.0", "method": "exit" })));

    let mut output = Vec::new();
    ril_lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;

    // W0601 warning published for `defer assert(...)` in `flush_batch`
    let diags = frames
        .get(1)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing publishDiagnostics")?;
    assert!(
        diags
            .iter()
            .any(|d| d.get("code").and_then(Value::as_str) == Some("W0601")
                && d.get("severity").and_then(Value::as_u64) == Some(2)),
        "expected W0601 warning diagnostic, got: {diags:?}"
    );

    // Hover on `clamp` shows `pure` and `total`, and no panic noise
    let clamp_hover = frames
        .get(2)
        .and_then(|v| v.pointer("/result/contents/value"))
        .and_then(Value::as_str)
        .unwrap_or("");
    assert!(
        clamp_hover.contains("`pure`")
            && clamp_hover.contains("`total`")
            && !clamp_hover.contains("May panic"),
        "unexpected clamp hover: {clamp_hover}"
    );

    // Hover on `flush_batch` expands `&mut(buf)`, shows May panic and May abort process
    let flush_hover = frames
        .get(3)
        .and_then(|v| v.pointer("/result/contents/value"))
        .and_then(Value::as_str)
        .unwrap_or("");
    assert!(
        flush_hover.contains("&mut(buf)")
            && flush_hover.contains("May panic")
            && flush_hover.contains("May abort process"),
        "unexpected flush_batch hover: {flush_hover}"
    );

    // Inlay hints expand `(buf)` after `&mut` and show `@io &up(mut out)` on closure
    let hints = frames
        .get(4)
        .and_then(|v| v.get("result"))
        .and_then(Value::as_array)
        .ok_or("missing inlay hints")?;
    let labels: Vec<&str> = hints
        .iter()
        .filter_map(|h| h.get("label").and_then(Value::as_str))
        .collect();
    assert!(
        labels.contains(&"(buf)"),
        "expected `(buf)` &mut expansion hint, got: {labels:?}"
    );
    assert!(
        labels
            .iter()
            .any(|l| l.contains("@io") && l.contains("&up(mut out)")),
        "expected closure effect/capture tail hint, got: {labels:?}"
    );
    Ok(())
}
