//! Cranelift AOT implementation of the native backend contract.
mod emit;
mod managed;
pub use emit::CraneliftBackend;
#[cfg(test)]
mod budget_tests;
#[cfg(test)]
mod host_tests;
