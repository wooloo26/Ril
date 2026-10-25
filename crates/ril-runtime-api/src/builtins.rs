//! Names implemented by the managed native runtime. This is a code-generation
//! availability contract, separate from the source standard-library type rules.

pub const OPERATIONS: &[&str] = &[
    "\0ril.control.parallel_run",
    "\0ril.control.branch_rethrow",
    "\0ril.control.branch_rank",
    "\0ril.control.branch_with_index",
    "\0ril.storage.sqrt_f32",
    "\0ril.storage.sqrt_f64",
    "\0ril.storage.instant_parts",
    "\0ril.storage.environment_free",
    "\0ril.storage.set_new",
    "\0ril.identity.fresh",
    "\0ril.identity.reference",
    "\0ril.identity.callable",
    "\0ril.identity.guard_read",
    "\0ril.identity.guard_seek",
    "\0ril.identity.read_guard",
    "\0ril.identity.read_reservation",
    "\0ril.storage.platform_windows",
    "\0ril.storage.native_from_units",
    "\0ril.storage.native_units",
    "\0ril.storage.native_windows",
    "\0ril.storage.path_from_native",
    "\0ril.storage.path_native",
    "\0ril.storage.bytes_from_array",
    "\0ril.storage.bytes_to_array",
    "\0ril.storage.f32_bits",
    "\0ril.storage.f32_from_bits",
    "\0ril.storage.f64_bits",
    "\0ril.storage.f64_from_bits",
    "\0ril.storage.string_scalars",
    "\0ril.storage.string_utf8",
    "\0ril.storage.string_from_scalars",
    "\0ril.foreign.invoke",
    "assert",
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
    "inner",
    "Array::push",
    "Array::pop",
    "Array::truncate",
    "Array::insert",
    "Array::remove",
    "Map::set",
    "Map::remove",
    "Set::contains",
    "Set::insert",
    "Set::remove",
    "File::open_path",
    "File::read_chunk",
    "File::write",
    "File::seek",
    "File::sync",
    "File::close",
    "File::metadata",
    "\0ril.host.file_read_dir",
    "File::create_dir",
    "File::create_dir_all",
    "File::remove_file",
    "File::remove_dir",
    "File::rename",
    "File::canonicalize",
    "File::temp_file",
    "File::SeekFrom::Start",
    "File::SeekFrom::Current",
    "File::SeekFrom::End",
    "Io::stdin_read",
    "Io::stdout_write",
    "Io::stderr_write",
    "Env::args",
    "Env::get",
    "\0ril.host.environment_all",
    "Env::current_dir",
    "Env::temp_dir",
    "Process::run",
    "Process::spawn",
    "Process::wait",
    "Process::terminate",
    "Time::monotonic",
    "Time::sleep",
    "Clock::now",
    "Random::entropy",
    "Concurrent::scope",
    "Concurrent::fork",
    "Concurrent::join",
    "Channel::bounded",
    "Channel::send",
    "Channel::recv",
    "Channel::detach",
    "Channel::attach",
    "Channel::close",
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
    "Num::NumError::InvalidSyntax",
    "Num::NumError::OutOfRange",
    "Num::NumError::InvalidRadix",
    "Time::TimeError::OutOfRange",
    "Time::TimeError::DifferentClock",
];

pub fn constant(name: &str) -> bool {
    CONSTANTS.contains(&name)
}

const NUMERIC_TYPES: &[&str] = &[
    "int", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64", "bigint", "f32", "f64",
];

/// Only verified generic constructor expressions may produce these aliases.
/// All three source-location components must be exact unsigned 32-bit numbers.
pub fn canonical_builtin(name: &str) -> Option<&str> {
    for (prefix, canonical) in [("Channel::__bounded_", "Channel::bounded")] {
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
        "\0ril.control.parallel_run"
            | "\0ril.foreign.invoke"
            | "Concurrent::scope"
            | "Concurrent::fork"
            | "Concurrent::join"
            | "Channel::bounded"
            | "Channel::send"
            | "Channel::recv"
            | "Channel::detach"
            | "Channel::attach"
            | "Channel::close"
            | "Time::sleep"
            | "Random::entropy"
            | "Io::stdin_read"
            | "Io::stdout_write"
            | "Io::stderr_write"
            | "print"
            | "println"
            | "File::open_path"
            | "File::read_chunk"
            | "File::write"
            | "File::seek"
            | "File::sync"
            | "File::close"
            | "File::metadata"
            | "\0ril.host.file_read_dir"
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
    if OPERATIONS.contains(&name) {
        return true;
    }
    if let Some(conversion) = name.strip_prefix("\0ril.numeric.convert_")
        && let Some((from, to)) = conversion.split_once("_to_")
    {
        return NUMERIC_TYPES.contains(&from) && NUMERIC_TYPES.contains(&to);
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
            "\0ril.control.parallel_run",
        ] {
            assert!(requires_native_step(name));
        }
        for name in [
            "scope",
            "fork",
            "join",
            "User::Parallel::map",
            "User::Io::read_buffered",
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
            "\0ril.storage.sqrt_f32",
            "\0ril.numeric.convert_int_to_bigint",
            "\0ril.numeric.convert_f64_to_int",
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
            "Test::assert_eq",
            "Test::assert_ne",
            "assert_eq",
            "assert_ne",
            "Math::unknown",
            "Num::parse_unknown",
            "__private_function",
            "Math::sqrt_f32_f32",
            "\0ril.numeric.convert_f64_to_unknown",
            "\0ril.numeric.convert_f64_to_int_to_u8",
            "User::Deque::__new_1_2_3",
        ] {
            assert!(!supported(name));
        }
    }
    #[test]
    fn parallel_algorithms_have_no_native_library_fallback() {
        for name in [
            "Parallel::map",
            "Parallel::find",
            "Parallel::fold",
            "Parallel::join",
            "Parallel::for_each",
        ] {
            assert!(!supported(name));
            assert!(!requires_native_step(name));
        }
        assert!(supported("\0ril.control.parallel_run"));
        assert!(requires_native_step("\0ril.control.parallel_run"));
    }
}
