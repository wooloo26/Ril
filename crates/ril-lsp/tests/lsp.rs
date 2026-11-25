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
