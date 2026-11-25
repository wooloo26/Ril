pub mod cranelift;

pub use cranelift::*;

#[cfg(feature = "native-runtime")]
pub fn runtime_symbol_names() -> Vec<&'static str> {
    ril_rt::symbols()
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}
