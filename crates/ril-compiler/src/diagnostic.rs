//! Presentation-independent diagnostics and source-to-use cause chains.
use crate::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CauseId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cause {
    pub id: CauseId,
    pub span: Option<Span>,
    pub description: String,
    pub parents: Vec<CauseId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: String,
    pub severity: Severity,
    pub message: String,
    pub labels: Vec<Label>,
    pub causes: Vec<Cause>,
}
