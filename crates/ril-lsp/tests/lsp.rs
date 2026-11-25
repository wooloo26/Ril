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
    let (at_line, at_col) = locate("Array::at")?;
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
        "fn check(x: Option<int>, y: Result<int, PanicError>) -> int {\n",
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
    let (panic_line, panic_col) = locate("PanicError")?;
    let (len_line, len_col) = locate("len(")?;

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
        "id": 6,
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

    let diags = frames
        .get(1)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing diagnostics")?;
    assert!(diags.is_empty(), "expected clean diagnostics: {diags:?}");

    for (idx, label) in [(2, "Option"), (3, "Result"), (4, "PanicError"), (5, "len")] {
        let uri = frames
            .get(idx)
            .and_then(|v| v.pointer("/result/uri"))
            .and_then(Value::as_str)
            .ok_or_else(|| format!("missing definition uri for {label}: {:?}", frames.get(idx)))?;
        assert!(
            uri.ends_with("std/prelude.ril"),
            "expected {label} definition in std/prelude.ril, got {uri}"
        );
    }
    Ok(())
}
