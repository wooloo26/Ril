#![forbid(unsafe_code)]
#![deny(clippy::indexing_slicing)]

pub mod diag;
pub mod span;
pub mod symbol;

#[macro_export]
macro_rules! ice {
    ($($arg:tt)*) => {{
        #[allow(clippy::panic, reason = "report a violated compiler invariant")]
        {
            panic!("internal compiler error: {}", format_args!($($arg)*))
        }
    }};
}
