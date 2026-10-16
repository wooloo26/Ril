//! Regenerate the pinned Unicode 17 tables from an offline UCD directory.
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs, io,
    path::{Path, PathBuf},
};
const INPUTS: [(&str, &str); 4] = [
    (
        "UnicodeData.txt",
        "2e1efc1dcb59c575eedf5ccae60f95229f706ee6d031835247d843c11d96470c",
    ),
    (
        "SpecialCasing.txt",
        "efc25faf19de21b92c1194c111c932e03d2a5eaf18194e33f1156e96de4c9588",
    ),
    (
        "DerivedCoreProperties.txt",
        "24c7fed1195c482faaefd5c1e7eb821c5ee1fb6de07ecdbaa64b56a99da22c08",
    ),
    (
        "PropList.txt",
        "130dcddcaadaf071008bdfce1e7743e04fdfbc910886f017d9f9ac931d8c64dd",
    ),
];
fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}
fn hex(text: &str) -> io::Result<u32> {
    u32::from_str_radix(text.trim(), 16).map_err(|_| invalid(format!("invalid UCD scalar {text}")))
}
fn read(directory: &Path, name: &str, hash: &str) -> io::Result<String> {
    let bytes = fs::read(directory.join(name))?;
    let actual = format!("{:x}", Sha256::digest(&bytes));
    if actual != hash {
        return Err(invalid(format!(
            "{name} does not match pinned Unicode 17.0.0 SHA-256"
        )));
    }
    String::from_utf8(bytes).map_err(|_| invalid("UCD input is not UTF-8"))
}
fn mapping(text: &str) -> io::Result<String> {
    text.split_whitespace()
        .map(|part| {
            char::from_u32(hex(part)?).ok_or_else(|| invalid("UCD case mapping is not scalar"))
        })
        .collect()
}
fn run(input: &Path, output: &Path) -> io::Result<()> {
    let mut properties = vec![0u8; 0x110000];
    let mut lower = BTreeMap::<u32, String>::new();
    let mut upper = BTreeMap::<u32, String>::new();
    for (name, hash) in INPUTS {
        let text = read(input, name, hash)?;
        match name {
            "UnicodeData.txt" => {
                for line in text.lines() {
                    let fields: Vec<_> = line.split(';').collect();
                    if fields.len() != 15 {
                        return Err(invalid("invalid UnicodeData field count"));
                    }
                    let scalar = hex(fields[0])?;
                    if scalar > 0x10ffff {
                        return Err(invalid("UCD scalar exceeds Unicode maximum"));
                    }
                    if fields[2] == "Nd" {
                        properties[scalar as usize] |= 4;
                    }
                    for (field, destination) in [(13, &mut lower), (12, &mut upper)] {
                        if !fields[field].is_empty() {
                            destination.insert(scalar, mapping(fields[field])?);
                        }
                    }
                }
            }
            "SpecialCasing.txt" => {
                for line in text.lines() {
                    let line = line.split('#').next().unwrap().trim();
                    if line.is_empty() {
                        continue;
                    }
                    let fields: Vec<_> = line.split(';').map(str::trim).collect();
                    if fields.len() < 5 {
                        return Err(invalid("invalid SpecialCasing row"));
                    }
                    if fields[4].is_empty() {
                        let scalar = hex(fields[0])?;
                        lower.insert(scalar, mapping(fields[1])?);
                        upper.insert(scalar, mapping(fields[3])?);
                    }
                }
            }
            _ => {
                for line in text.lines() {
                    let line = line.split('#').next().unwrap().trim();
                    if line.is_empty() {
                        continue;
                    }
                    let Some((range, property)) = line.split_once(';') else {
                        return Err(invalid("invalid property row"));
                    };
                    let flag = match property.trim() {
                        "White_Space" => 1,
                        "Alphabetic" => 2,
                        "XID_Start" => 8,
                        "XID_Continue" => 16,
                        "Cased" => 32,
                        "Case_Ignorable" => 64,
                        _ => continue,
                    };
                    let (start, end) = range.trim().split_once("..").map_or_else(
                        || hex(range).map(|value| (value, value)),
                        |(a, b)| Ok((hex(a)?, hex(b)?)),
                    )?;
                    if start > end || end > 0x10ffff {
                        return Err(invalid("invalid Unicode property range"));
                    }
                    for value in &mut properties[start as usize..=end as usize] {
                        *value |= flag;
                    }
                }
            }
        }
    }
    // Page interning keeps lookup constant-time without a 1.1 MB dense table.
    let mut pages = Vec::<Vec<u8>>::new();
    let mut intern = BTreeMap::<Vec<u8>, u16>::new();
    let mut indices = Vec::new();
    for page in properties.as_chunks::<256>().0 {
        let page = page.to_vec();
        let id = if let Some(id) = intern.get(&page) {
            *id
        } else {
            let id = u16::try_from(pages.len()).map_err(|_| invalid("too many Unicode pages"))?;
            pages.push(page.clone());
            intern.insert(page, id);
            id
        };
        indices.extend(id.to_le_bytes());
    }
    let mut generated="// Generated from Unicode 17.0.0. Run cargo run -p xtask --bin unicode-data -- INPUT OUTPUT.\n// Source files are SHA-256 pinned by the generator. See LICENSE.txt.\n".to_owned();
    for (name, table) in [("LOWER", lower), ("UPPER", upper)] {
        generated.push_str(&format!("pub static {name}: &[(u32, &str)] = &[\n"));
        for (scalar, text) in table {
            let escaped = text
                .chars()
                .flat_map(char::escape_unicode)
                .collect::<String>();
            generated.push_str(&format!("    (0x{scalar:x}, \"{escaped}\"),\n"));
        }
        generated.push_str("];\n");
    }
    fs::create_dir_all(output)?;
    fs::write(
        output.join("pages.bin"),
        pages.into_iter().flatten().collect::<Vec<_>>(),
    )?;
    fs::write(output.join("indices.bin"), indices)?;
    fs::write(output.join("case.rs"), generated)?;
    fs::copy(input.join("LICENSE.txt"), output.join("LICENSE.txt"))?;
    Ok(())
}
fn main() -> std::process::ExitCode {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    if arguments.len() != 2 {
        eprintln!("usage: unicode-data INPUT_DIRECTORY OUTPUT_DIRECTORY");
        return std::process::ExitCode::from(1);
    }
    match run(&PathBuf::from(&arguments[0]), &PathBuf::from(&arguments[1])) {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::from(1)
        }
    }
}
