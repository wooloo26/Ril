Unicode 17.0.0 tables for Ril. The included LICENSE.txt covers Unicode data.

Download UnicodeData.txt, SpecialCasing.txt, DerivedCoreProperties.txt and
PropList.txt from https://www.unicode.org/Public/17.0.0/ucd/ into an offline
directory, along with https://www.unicode.org/license.txt as LICENSE.txt.
The Rust generator verifies the four data-file SHA-256 checksums before writing.

Regenerate with:

```text
cargo run --locked -p xtask --bin unicode-data -- INPUT_DIRECTORY crates/ril-runtime/src/unicode_generated
```

indices.bin contains little-endian u16 page numbers. pages.bin contains interned
256-scalar property pages; lookup takes two bounded array reads. case.rs holds
full, unconditional case mappings; unicode.rs implements Final_Sigma context.
