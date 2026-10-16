//! Unicode 17.0.0 properties and locale-independent full case conversion.
//! Data is generated from checksum-pinned UCD inputs, independently of the host.
mod data {
    include!("unicode_generated/case.rs");
}
const INDICES: &[u8] = include_bytes!("unicode_generated/indices.bin");
const PAGES: &[u8] = include_bytes!("unicode_generated/pages.bin");
fn properties(value: u32) -> u8 {
    if char::from_u32(value).is_none() {
        return 0;
    }
    let offset = (value as usize >> 8) * 2;
    let page = u16::from_le_bytes([INDICES[offset], INDICES[offset + 1]]) as usize;
    PAGES[page * 256 + (value as usize & 255)]
}
pub fn is_white_space(value: u32) -> bool {
    properties(value) & 1 != 0
}
pub fn is_alphabetic(value: u32) -> bool {
    properties(value) & 2 != 0
}
pub fn is_decimal_digit(value: u32) -> bool {
    properties(value) & 4 != 0
}
pub fn is_xid_start(value: u32) -> bool {
    properties(value) & 8 != 0
}
pub fn is_xid_continue(value: u32) -> bool {
    properties(value) & 16 != 0
}
fn append_case(output: &mut String, value: char, table: &[(u32, &str)]) {
    if let Ok(index) = table.binary_search_by_key(&(value as u32), |(scalar, _)| *scalar) {
        output.push_str(table[index].1);
    } else {
        output.push(value);
    }
}
pub fn uppercase(text: &str) -> String {
    let mut result = String::with_capacity(text.len());
    for value in text.chars() {
        append_case(&mut result, value, data::UPPER);
    }
    result
}
pub fn lowercase(text: &str) -> String {
    let chars: Vec<_> = text.chars().collect();
    let mut after = vec![false; chars.len()];
    let mut following = false;
    for (index, value) in chars.iter().enumerate().rev() {
        after[index] = following;
        let bits = properties(*value as u32);
        if bits & 32 != 0 {
            following = true;
        } else if bits & 64 == 0 {
            following = false;
        }
    }
    let mut before = false;
    let mut result = String::with_capacity(text.len());
    for (index, value) in chars.into_iter().enumerate() {
        if value == 'Σ' && before && !after[index] {
            result.push('ς');
        } else {
            append_case(&mut result, value, data::LOWER);
        }
        let bits = properties(value as u32);
        if bits & 32 != 0 {
            before = true;
        } else if bits & 64 == 0 {
            before = false;
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn properties_are_pinned_and_non_scalars_are_never_classified() {
        assert!(is_white_space(0x3000));
        assert!(is_alphabetic('A' as u32));
        assert!(is_decimal_digit(0x0660));
        assert!(is_xid_start('A' as u32));
        assert!(is_xid_continue('0' as u32));
        assert!(!is_alphabetic(0xd800));
        assert!(!is_xid_continue(0x110000));
        assert!(is_alphabetic(0x16ea0));
    }
    #[test]
    fn full_mapping_expands_and_final_sigma_observes_ignorable_context() {
        assert_eq!(uppercase("Straße"), "STRASSE");
        assert_eq!(lowercase("İ"), "i\u{307}");
        assert_eq!(lowercase("ΟΣ"), "ος");
        assert_eq!(lowercase("ΟΣΑ"), "οσα");
        assert_eq!(lowercase("ΟΣ\u{301}"), "ος\u{301}");
    }
}
