//! The only raw reads are from the immutable process command line returned by
//! Windows. Case matching uses ordinal OS rules rather than Unicode folding.
#![allow(unsafe_code)]
pub(crate) fn command_line() -> Vec<u16> {
    // SAFETY: GetCommandLineW returns a process-lifetime NUL-terminated buffer;
    // it is read here without modifying it or retaining a borrowed reference.
    unsafe {
        let pointer = windows_sys::Win32::System::Environment::GetCommandLineW();
        let mut length = 0;
        while *pointer.add(length) != 0 {
            length += 1;
        }
        std::slice::from_raw_parts(pointer, length).to_vec()
    }
}
pub(crate) fn compare_environment_names(left: &[u16], right: &[u16]) -> std::cmp::Ordering {
    // OS environment names cannot approach i32::MAX units. This fallback also
    // keeps the total comparison defined for manually constructed internal data.
    let (Ok(left_len), Ok(right_len)) = (i32::try_from(left.len()), i32::try_from(right.len()))
    else {
        return left.cmp(right);
    };
    // SAFETY: the explicit lengths describe the two live input slices exactly.
    match unsafe {
        windows_sys::Win32::Globalization::CompareStringOrdinal(
            left.as_ptr(),
            left_len,
            right.as_ptr(),
            right_len,
            1,
        )
    } {
        1 => std::cmp::Ordering::Less,
        2 => std::cmp::Ordering::Equal,
        3 => std::cmp::Ordering::Greater,
        _ => left.cmp(right),
    }
}
