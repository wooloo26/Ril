#[derive(Debug, Clone, thiserror::Error)]
#[error("runtime operation is not implemented: {0}")]
pub struct Unavailable(pub &'static str);
