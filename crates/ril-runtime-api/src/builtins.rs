//! Names implemented by the managed native runtime. This is a code-generation
//! availability contract, separate from the source standard-library type rules.

pub const OPERATIONS: &[&str] = &[
    "\0ril.foreign.invoke",
    "assert",
    "assert_eq",
    "assert_ne",
    "Test::assert_eq",
    "Test::assert_ne",
    "panic",
    "len",
    "clone",
    "clone_immut",
    "print",
    "println",
    "Some",
    "None",
    "Ok",
    "Err",
    "__format",
    "__format_spec",
    "__option_unwrap",
    "__variant_payload",
    "__unwrap_tag",
    "__iter_start",
    "__iter_item",
    "__iter_length",
    "__iter_next",
    "__safe_field",
    "__computed_field",
    "__io_read_validate",
    "__io_write_validate",
    "__io_acc_new",
    "__io_acc_push",
    "__io_acc_finish",
    "__io_bytes_suffix",
    "Io::read_all",
    "Io::write_all",
    "Io::read_buffer",
    "Io::read_position",
    "Io::guard_read",
    "Io::guard_seek",
    "Io::write_buffer",
    "Io::read_buffered",
    "Io::read_buffered_at",
    "Io::write_buffered",
    "Io::flush",
    "inner",
    "Array::push",
    "Array::pop",
    "Array::truncate",
    "Array::insert",
    "Array::remove",
    "Array::reverse",
    "Array::first",
    "Array::concat",
    "Array::contains",
    "Array::clear",
    "Array::get",
    "Array::set",
    "Array::map",
    "Array::filter",
    "Array::fold",
    "Array::find",
    "Array::any",
    "Array::all",
    "Array::for_each",
    "Options::map",
    "Options::and_then",
    "Options::unwrap_or_else",
    "Results::map",
    "Results::map_err",
    "Results::and_then",
    "Results::recover",
    "String::contains",
    "String::starts_with",
    "String::ends_with",
    "String::trim",
    "String::split",
    "String::replace",
    "String::find",
    "String::slice",
    "String::concat",
    "String::join",
    "String::lines",
    "String::scalar_at",
    "String::scalars",
    "String::utf8",
    "String::byte_len",
    "String::byte_offset",
    "String::scalar_offset",
    "StringBuilder::new",
    "StringBuilder::append",
    "StringBuilder::clear",
    "StringBuilder::to_string",
    "StringBuilder::append_scalar",
    "Crypto::sha256",
    "Crypto::sha256_bytes",
    "Unicode::decode_utf8",
    "Unicode::from_scalar",
    "Unicode::lowercase",
    "Unicode::uppercase",
    "Unicode::is_white_space",
    "Unicode::is_alphabetic",
    "Unicode::is_decimal_digit",
    "Unicode::is_xid_start",
    "Unicode::is_xid_continue",
    "Map::from",
    "Map::set",
    "Map::get",
    "Map::contains",
    "Map::remove",
    "Map::keys",
    "Map::values",
    "Map::entries",
    "Set::from",
    "Set::of",
    "Set::contains",
    "Set::insert",
    "Set::remove",
    "Set::values",
    "Set::union",
    "Set::intersect",
    "Set::diff",
    "Bytes::from_array",
    "Bytes::to_array",
    "Bytes::slice",
    "Bytes::concat",
    "Bytes::find",
    "Bytes::at",
    "Hex::encode",
    "Hex::decode",
    "Binary::cursor",
    "Binary::remaining",
    "Time::duration_nanos",
    "Os::platform",
    "Os::from_string",
    "Os::to_string",
    "Os::from_posix_bytes",
    "Os::posix_bytes",
    "Os::from_windows_units",
    "Os::windows_units",
    "Os::compare",
    "Path::from_string",
    "Path::from_native",
    "Path::native",
    "Path::to_string",
    "Path::join",
    "Path::parent",
    "Path::file_name",
    "Path::extension",
    "Path::is_absolute",
    "Path::normalize_lexical",
    "Path::compare",
    "File::open",
    "File::open_path",
    "File::read",
    "File::read_chunk",
    "File::write",
    "File::seek",
    "File::sync",
    "File::close",
    "File::read_bytes",
    "File::read_text",
    "File::write_bytes",
    "File::write_text",
    "File::metadata",
    "File::read_dir",
    "File::create_dir",
    "File::create_dir_all",
    "File::remove_file",
    "File::remove_dir",
    "File::rename",
    "File::canonicalize",
    "File::temp_file",
    "File::with_file",
    "File::SeekFrom::Start",
    "File::SeekFrom::Current",
    "File::SeekFrom::End",
    "Io::stdin_read",
    "Io::stdout_write",
    "Io::stderr_write",
    "Io::write_stdout",
    "Io::write_stderr",
    "Io::error_text",
    "Env::args",
    "Env::get",
    "Env::all",
    "Env::current_dir",
    "Env::temp_dir",
    "Process::command",
    "Process::run",
    "Process::spawn",
    "Process::wait",
    "Process::terminate",
    "Process::success",
    "Time::timestamp",
    "Time::add",
    "Time::elapsed",
    "Time::monotonic",
    "Time::sleep",
    "Clock::now",
    "Random::seeded",
    "Random::next_u64",
    "Random::below",
    "Random::entropy",
    "Order::sorted",
    "Order::binary_search",
    "Order::compare_int",
    "Order::compare_str",
    "Order::compare_bytes",
    "Order::total_f64",
    "Deque::new",
    "Deque::len",
    "Deque::push_front",
    "Deque::push_back",
    "Deque::pop_front",
    "Deque::pop_back",
    "Deque::values",
    "Heap::new",
    "Heap::len",
    "Heap::push",
    "Heap::peek",
    "Heap::pop",
    "Concurrent::scope",
    "Concurrent::fork",
    "Concurrent::join",
    "Channel::bounded",
    "Channel::send",
    "Channel::recv",
    "Channel::detach",
    "Channel::attach",
    "Channel::close",
    "Parallel::map",
    "Parallel::map_bounded",
    "Parallel::find",
    "Parallel::first",
    "Parallel::any",
    "Parallel::fold",
    "Parallel::join",
    "Parallel::join3",
    "Parallel::for_each",
];

pub const CONSTANTS: &[&str] = &[
    "File::OpenMode::Read",
    "File::OpenMode::WriteNew",
    "File::OpenMode::WriteTruncate",
    "File::OpenMode::ReadWrite",
    "File::OpenMode::Append",
    "File::FileKind::Regular",
    "File::FileKind::Directory",
    "File::FileKind::Symlink",
    "File::FileKind::Other",
    "Io::ErrorKind::NotFound",
    "Io::ErrorKind::PermissionDenied",
    "Io::ErrorKind::AlreadyExists",
    "Io::ErrorKind::InvalidInput",
    "Io::ErrorKind::InvalidData",
    "Io::ErrorKind::UnexpectedEnd",
    "Io::ErrorKind::BrokenPipe",
    "Io::ErrorKind::Closed",
    "Io::ErrorKind::Unsupported",
    "Io::ErrorKind::Other",
    "Os::NativeError::InvalidEncoding",
    "Os::NativeError::WrongPlatform",
    "Os::Platform::Windows",
    "Os::Platform::Posix",
    "Num::NumError::InvalidSyntax",
    "Num::NumError::OutOfRange",
    "Num::NumError::InvalidRadix",
    "Binary::ByteOrder::Little",
    "Binary::ByteOrder::Big",
    "Binary::BinaryError::UnexpectedEnd",
    "Binary::BinaryError::Overflow",
    "Binary::BinaryError::NonCanonical",
    "Time::TimeError::OutOfRange",
    "Time::TimeError::DifferentClock",
    "Order::Ordering::Less",
    "Order::Ordering::Equal",
    "Order::Ordering::Greater",
];

pub fn constant(name: &str) -> bool {
    CONSTANTS.contains(&name)
}

const NUMERIC_TYPES: &[&str] = &[
    "int", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64", "bigint", "f32", "f64",
];
const BINARY_TYPES: &[&str] = &[
    "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64", "f32", "f64", "bytes", "uleb128",
];
const MATH_OPERATIONS: &[&str] = &[
    "sqrt",
    "floor",
    "ceil",
    "round",
    "abs",
    "min",
    "max",
    "is_nan",
    "is_finite",
];

/// Only verified generic constructor expressions may produce these aliases.
/// All three source-location components must be exact unsigned 32-bit numbers.
pub fn canonical_builtin(name: &str) -> Option<&str> {
    for (prefix, canonical) in [
        ("Deque::__new_", "Deque::new"),
        ("Heap::__new_", "Heap::new"),
        ("Channel::__bounded_", "Channel::bounded"),
    ] {
        if let Some(location) = name.strip_prefix(prefix) {
            let mut parts = location.split('_');
            for _ in 0..3 {
                let part = parts.next()?;
                if part.is_empty()
                    || !part.bytes().all(|byte| byte.is_ascii_digit())
                    || part.parse::<u32>().is_err()
                {
                    return None;
                }
            }
            return parts.next().is_none().then_some(canonical);
        }
    }
    None
}

/// These operations participate in native control flow. Their implementation
/// must retain the caller's continuation instead of entering the pure callback
/// bridge, including when the builtin is stored in a local callable value.
pub fn requires_native_step(name: &str) -> bool {
    let name = name.strip_prefix("Prelude::").unwrap_or(name);
    let name = canonical_builtin(name).unwrap_or(name);
    matches!(
        name,
        "\0ril.foreign.invoke"
            | "Concurrent::scope"
            | "Concurrent::fork"
            | "Concurrent::join"
            | "Channel::bounded"
            | "Channel::send"
            | "Channel::recv"
            | "Channel::detach"
            | "Channel::attach"
            | "Channel::close"
            | "Parallel::map"
            | "Parallel::map_bounded"
            | "Parallel::find"
            | "Parallel::first"
            | "Parallel::any"
            | "Parallel::fold"
            | "Parallel::join"
            | "Parallel::join3"
            | "Parallel::for_each"
            | "Io::read_buffered"
            | "Io::read_buffered_at"
            | "Io::write_buffered"
            | "Io::flush"
            | "Time::sleep"
            | "Random::entropy"
            | "Io::stdin_read"
            | "Io::stdout_write"
            | "Io::stderr_write"
            | "Io::write_stdout"
            | "Io::write_stderr"
            | "print"
            | "println"
            | "File::open"
            | "File::open_path"
            | "File::read"
            | "File::read_chunk"
            | "File::write"
            | "File::seek"
            | "File::sync"
            | "File::close"
            | "File::read_bytes"
            | "File::read_text"
            | "File::write_bytes"
            | "File::write_text"
            | "File::metadata"
            | "File::read_dir"
            | "File::create_dir"
            | "File::create_dir_all"
            | "File::remove_file"
            | "File::remove_dir"
            | "File::rename"
            | "File::canonicalize"
            | "File::temp_file"
            | "Process::run"
            | "Process::spawn"
            | "Process::wait"
            | "Process::terminate"
    )
}

pub fn supported(name: &str) -> bool {
    let name = name.strip_prefix("Prelude::").unwrap_or(name);
    let name = canonical_builtin(name).unwrap_or(name);
    if matches!(
        name,
        "\0ril.heap.new"
            | "\0ril.heap.begin_push"
            | "\0ril.heap.begin_pop"
            | "\0ril.heap.next"
            | "\0ril.heap.accept"
            | "\0ril.heap.commit"
    ) {
        return true;
    }
    if OPERATIONS.contains(&name) {
        return true;
    }
    if let Some(operation) = name.strip_prefix("Math::") {
        return MATH_OPERATIONS.contains(&operation.strip_suffix("_f32").unwrap_or(operation));
    }
    if let Some(operation) = name.strip_prefix("Num::") {
        if let Some(conversion) = operation.strip_prefix("__convert_")
            && let Some((from, to)) = conversion.split_once("_to_")
        {
            return NUMERIC_TYPES.contains(&from) && NUMERIC_TYPES.contains(&to);
        }
        return ["parse_", "format_", "__convert_"].iter().any(|prefix| {
            operation
                .strip_prefix(prefix)
                .is_some_and(|ty| NUMERIC_TYPES.contains(&ty))
        });
    }
    if let Some(operation) = name.strip_prefix("Binary::") {
        return ["read_", "write_"].iter().any(|prefix| {
            operation
                .strip_prefix(prefix)
                .is_some_and(|ty| BINARY_TYPES.contains(&ty))
        });
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn concurrent_entry_names_are_exact_and_generic_aliases_are_validated() {
        for name in [
            "Concurrent::scope",
            "Concurrent::fork",
            "Concurrent::join",
            "Channel::bounded",
            "Channel::__bounded_0_1_4294967295",
            "Channel::recv",
            "Parallel::map",
            "Parallel::map_bounded",
            "Parallel::find",
            "Parallel::first",
            "Parallel::any",
            "Parallel::fold",
            "Parallel::join",
            "Parallel::join3",
            "Parallel::for_each",
            "Io::read_buffered",
            "Io::read_buffered_at",
            "Io::write_buffered",
            "Io::flush",
        ] {
            assert!(requires_native_step(name));
        }
        for name in [
            "scope",
            "fork",
            "join",
            "String::join",
            "User::Parallel::map",
            "User::Io::read_buffered",
            "Parallel::unknown",
            "User::Concurrent::scope",
            "Channel::__bounded_1_2",
            "Channel::__bounded_1_2_3_4",
            "Channel::__bounded_4294967296_0_1",
            "Channel::__bounded_+1_2_3",
        ] {
            assert!(!requires_native_step(name));
        }
    }
    #[test]
    fn availability_is_finite_and_preserves_namespace_identity() {
        for name in OPERATIONS {
            assert!(supported(name));
        }
        for name in CONSTANTS {
            assert!(constant(name));
            assert!(!supported(name));
        }
        assert!(!constant("User::ByteOrder::Little"));
        for name in [
            "Prelude::Some",
            "Math::sqrt_f32",
            "Num::__convert_bigint",
            "Binary::read_uleb128",
            "Array::map",
            "Array::filter",
            "Array::fold",
            "Array::find",
            "Array::any",
            "Array::all",
            "Array::for_each",
            "Num::__convert_f64_to_int",
            "Deque::__new_0_123_456",
            "Heap::__new_4294967295_0_7",
        ] {
            assert!(supported(name));
        }
        for name in [
            "Foo::Some",
            "Options::unwrap_or",
            "Options::expect",
            "Test::assert_some",
            "Results::expect",
            "Test::assert_ok",
            "Math::unknown",
            "Num::parse_unknown",
            "Binary::read_u128",
            "__private_function",
            "Math::sqrt_f32_f32",
            "Num::__convert_f64_to_unknown",
            "Num::__convert_f64_to_int_to_u8",
            "Deque::__new_1_2",
            "Deque::__new_1_2_3_4",
            "Heap::__new_4294967296_0_1",
            "Heap::__new_+1_2_3",
            "Heap::__new_1__3",
            "User::Deque::__new_1_2_3",
        ] {
            assert!(!supported(name));
        }
    }
}
