#![forbid(unsafe_code)]

use ril_driver::{CompileOptions, Compiler, Driver};
use ril_source::span::{FileId, SourceFile};
use ril_syntax::{cst::CstFile, fmt::format_source, parser::FileKind};
use ril_test::{Unit, VirtualPackage};

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
    assert!(
        obj.windows(b".eh_frame".len()).any(|w| w == b".eh_frame")
            || obj.windows(b"__eh_frame".len()).any(|w| w == b"__eh_frame"),
        "expected unwind metadata section in compiled object"
    );
    Ok(())
}
