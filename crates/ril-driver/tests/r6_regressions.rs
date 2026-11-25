use std::io::Cursor;

use ril_base::span::{FileId, SourceFile};
use ril_driver::{CompileOptions, Compiler, Driver, lsp};
use ril_frontend::{cst::CstFile, fmt::format_source, parser::FileKind};
use ril_test::{Unit, VirtualPackage};
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
fn cst_is_byte_for_byte_lossless() -> Result<(), String> {
    let sample = "-- header comment\n\
type Box = .{ {- inline -} var value: int }\n\n\
fn add(a: int,   b: int) -> int {\n\
    let msg = \"hello ${a + b}\"\n\
    let _ = msg\n\
    a + b   -- trailing note\n\
}\n";
    let path = std::path::PathBuf::from("pkg/sample.ril");
    let src = SourceFile::from_bytes(FileId::from_path(&path), path, sample.as_bytes())
        .map_err(|d| d.to_string())?;
    let cst = CstFile::lex(&src);
    assert!(cst.diagnostics.is_empty(), "{:?}", cst.diagnostics);
    assert_eq!(cst.reconstruct(&src), sample);
    Ok(())
}

#[test]
fn ril_fmt_preserves_comments_and_is_idempotent() -> Result<(), String> {
    let messy = "-- top comment\n\
type Pair = .{   a:int,b:int   }\n\n\n\n\
fn sum(  p:Pair ) -> int {\n\
  {- keep me -}\n\
let x = p.a+p.b   -- trailing\n\
    x\n\
}\n";
    let path = std::path::PathBuf::from("pkg/messy.ril");
    let src1 = SourceFile::from_bytes(FileId::from_path(&path), path.clone(), messy.as_bytes())
        .map_err(|d| d.to_string())?;
    let pass1 = format_source(&src1, FileKind::Module).map_err(|d| format!("{d:?}"))?;

    assert!(pass1.contains("-- top comment"));
    assert!(pass1.contains("{- keep me -}"));
    assert!(pass1.contains("-- trailing"));
    assert!(pass1.contains("    let x = p.a + p.b -- trailing"));
    assert!(
        !pass1.contains("\n\n\n"),
        "must collapse 3+ blank lines:\n{pass1}"
    );

    // Strict idempotency: formatting formatted output produces byte-identical output.
    let src2 = SourceFile::from_bytes(FileId::from_path(&path), path, pass1.as_bytes())
        .map_err(|d| d.to_string())?;
    let pass2 = format_source(&src2, FileKind::Module).map_err(|d| format!("{d:?}"))?;
    assert_eq!(pass1, pass2, "ril fmt must be idempotent");
    Ok(())
}

#[test]
fn mir_source_locations_clif_srcloc_and_object_unwind_tables() -> Result<(), String> {
    let src = "fn helper(x: int) -> int {\n    x + 1\n}\n\nfn main() -> () {\n    assert(helper(41) == 42)\n}\n";
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert("pkg/main.ril".into(), src.as_bytes().to_vec());

    let mir = Driver.lower(&pkg).map_err(|d| format!("{d:?}"))?;
    assert!(
        mir.source_locations().len() >= 2,
        "expected source_locs for main and helper: {:?}",
        mir.source_locations()
    );
    assert!(
        mir.source_locations()
            .iter()
            .any(|loc| loc.file.ends_with("main.ril") && loc.line == 1)
    );

    let clif = Driver.clif(&pkg).map_err(|d| format!("{d:?}"))?;
    assert!(
        clif.contains("@0001"),
        "expected Cranelift SourceLoc annotations in CLIF:\n{clif}"
    );

    let obj = Compiler::new(CompileOptions::default())
        .compile_object(&pkg)
        .map_err(|d| format!("{d:?}"))?;
    // ELF/Mach-O object emitted with `unwind_info = true` contains `.eh_frame` / unwind metadata.
    assert!(
        obj.windows(b".eh_frame".len()).any(|w| w == b".eh_frame")
            || obj.windows(b"__eh_frame".len()).any(|w| w == b"__eh_frame"),
        "expected unwind metadata section in compiled object"
    );
    Ok(())
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
    // Hover over `helper` call on line 5, column 14 (`    let y = helper(41)`).
    input.extend(frame_lsp(&json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": uri },
            "position": { "line": 5, "character": 14 }
        }
    })));
    // Go-to-definition on `helper` call on line 5, column 14.
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
    lsp::handle_session(Cursor::new(input), &mut output)?;
    let frames = parse_lsp_frames(&output)?;
    assert_eq!(frames.len(), 7, "expected 7 LSP messages, got {frames:#?}");

    // 1. initialize response
    assert_eq!(
        frames
            .first()
            .and_then(|v| v.pointer("/result/capabilities/hoverProvider")),
        Some(&json!(true))
    );
    // 2. didOpen publishes E0301 diagnostic
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
    // 3. didChange clears diagnostics
    let diags_fixed = frames
        .get(2)
        .and_then(|v| v.pointer("/params/diagnostics"))
        .and_then(Value::as_array)
        .ok_or("missing change diagnostics")?;
    assert!(
        diags_fixed.is_empty(),
        "expected clean diagnostics: {diags_fixed:?}"
    );
    // 4. hover returns `fn helper(int) -> int`
    let hover_text = frames
        .get(3)
        .and_then(|v| v.pointer("/result/contents/value"))
        .and_then(Value::as_str)
        .ok_or("missing hover contents")?;
    assert!(
        hover_text.contains("fn helper") && hover_text.contains("int"),
        "unexpected hover: {hover_text}"
    );
    // 5. definition jumps to line 0 (`fn helper`)
    assert_eq!(
        frames
            .get(4)
            .and_then(|v| v.pointer("/result/range/start/line")),
        Some(&json!(0))
    );
    // 6. formatting returns edits
    assert!(
        frames
            .get(5)
            .and_then(|v| v.pointer("/result/0/newText"))
            .and_then(Value::as_str)
            .is_some()
    );
    Ok(())
}
