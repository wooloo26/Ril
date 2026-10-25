//! Regenerate the pinned Unicode 17 tables from an offline UCD directory.
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs, io,
    path::{Path, PathBuf},
};
const VERSION: &str = "17.0.0";
const INPUTS: [&str; 4] = [
    "UnicodeData.txt",
    "SpecialCasing.txt",
    "DerivedCoreProperties.txt",
    "PropList.txt",
];

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct InputManifest {
    version: String,
    inputs: BTreeMap<String, String>,
}

fn pinned_inputs() -> io::Result<InputManifest> {
    let manifest: InputManifest =
        serde_json::from_str(include_str!("../../data/unicode-inputs.json")).map_err(|error| {
            invalid(format!("invalid generated Unicode input manifest: {error}"))
        })?;
    if manifest.version != VERSION
        || manifest.inputs.len() != INPUTS.len()
        || INPUTS
            .iter()
            .any(|name| !manifest.inputs.contains_key(*name))
    {
        return Err(invalid(
            "Unicode input manifest version or file set differs",
        ));
    }
    Ok(manifest)
}

/// Explicit maintenance operation. Normal table generation only verifies the
/// committed manifest; it never regenerates its own expected checksums.
fn write_manifest(input: &Path, output: &Path) -> io::Result<()> {
    let mut inputs = BTreeMap::new();
    for name in INPUTS {
        let bytes = fs::read(input.join(name))?;
        let text = std::str::from_utf8(&bytes).map_err(|_| invalid("UCD input is not UTF-8"))?;
        if name != "UnicodeData.txt" {
            let stem = name.trim_end_matches(".txt");
            if !text
                .lines()
                .take(8)
                .any(|line| line.contains(&format!("{stem}-{VERSION}.txt")))
            {
                return Err(invalid(format!(
                    "{name} does not declare Unicode {VERSION}"
                )));
            }
        }
        inputs.insert(name.to_owned(), format!("{:x}", Sha256::digest(&bytes)));
    }
    let mut generated = serde_json::to_vec_pretty(&InputManifest {
        version: VERSION.into(),
        inputs,
    })
    .map_err(io::Error::other)?;
    generated.push(b'\n');
    fs::write(output, generated)
}
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
fn render_tables(
    indices: &[u8],
    pages: &[u8],
    lower: &BTreeMap<u32, String>,
    upper: &BTreeMap<u32, String>,
) -> String {
    use std::fmt::Write;
    let mut generated = "-- Generated from Unicode 17.0.0. Regenerate with xtask unicode-data.\n-- Inputs are SHA-256 pinned. See LICENSE.txt.\n".to_owned();
    for (name, bytes) in [("INDICES", indices), ("PAGES", pages)] {
        write!(generated, "pub meta let {name}: bytes = b\"").unwrap();
        for byte in bytes {
            write!(generated, "\\x{byte:02x}").unwrap();
        }
        generated.push_str("\"\n");
    }
    for (name, table) in [("LOWER", lower), ("UPPER", upper)] {
        writeln!(generated, "pub meta let {name}: [](u32, str) = [").unwrap();
        for (scalar, text) in table {
            let escaped = text
                .chars()
                .flat_map(char::escape_unicode)
                .collect::<String>();
            writeln!(generated, "    (0x{scalar:x}u32, \"{escaped}\"),").unwrap();
        }
        generated.push_str("]\n");
    }
    generated
}

fn run(input: &Path, output: &Path) -> io::Result<()> {
    let manifest = pinned_inputs()?;
    let mut properties = vec![0u8; 0x110000];
    let mut lower = BTreeMap::<u32, String>::new();
    let mut upper = BTreeMap::<u32, String>::new();
    for name in INPUTS {
        let text = read(input, name, &manifest.inputs[name])?;
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
    let pages = pages.into_iter().flatten().collect::<Vec<_>>();
    fs::create_dir_all(output)?;
    fs::write(
        output.join("data.ril"),
        render_tables(&indices, &pages, &lower, &upper),
    )?;
    fs::copy(input.join("LICENSE.txt"), output.join("LICENSE.txt"))?;
    Ok(())
}
fn main() -> std::process::ExitCode {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    let result = match arguments.as_slice() {
        [input, output] => run(&PathBuf::from(input), &PathBuf::from(output)),
        [command, input, output] if command == "manifest" => {
            write_manifest(&PathBuf::from(input), &PathBuf::from(output))
        }
        _ => {
            eprintln!(
                "usage: unicode-data INPUT_DIRECTORY OUTPUT_DIRECTORY\n       unicode-data manifest INPUT_DIRECTORY OUTPUT_MANIFEST"
            );
            return std::process::ExitCode::from(1);
        }
    };
    match result {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inputs(directory: &Path) {
        for name in INPUTS {
            let text = if name == "UnicodeData.txt" {
                "offline Unicode data\n".to_owned()
            } else {
                format!("# {}-{VERSION}.txt\n", name.trim_end_matches(".txt"))
            };
            fs::write(directory.join(name), text).unwrap();
        }
    }

    #[test]
    fn generated_values_detect_changed_inputs_without_rebaselining() {
        let directory = tempfile::tempdir().unwrap();
        inputs(directory.path());
        let output = directory.path().join("inputs.json");
        write_manifest(directory.path(), &output).unwrap();
        let before = fs::read(&output).unwrap();
        let manifest: InputManifest = serde_json::from_slice(&before).unwrap();
        assert_eq!(manifest.version, VERSION);
        assert_eq!(manifest.inputs.len(), INPUTS.len());
        for name in INPUTS {
            read(directory.path(), name, &manifest.inputs[name]).unwrap();
        }
        fs::write(directory.path().join(INPUTS[0]), "changed data").unwrap();
        assert!(read(directory.path(), INPUTS[0], &manifest.inputs[INPUTS[0]]).is_err());
        assert_eq!(fs::read(output).unwrap(), before);
    }

    #[test]
    fn manifest_generation_rejects_another_unicode_version() {
        let directory = tempfile::tempdir().unwrap();
        inputs(directory.path());
        fs::write(
            directory.path().join("PropList.txt"),
            "# PropList-16.0.0.txt\n",
        )
        .unwrap();
        let output = directory.path().join("inputs.json");
        assert!(write_manifest(directory.path(), &output).is_err());
        assert!(!output.exists());
    }
}
