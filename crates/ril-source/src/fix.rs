use serde::{Deserialize, Serialize};

use crate::span::Span;

/// Risk and applicability tier for a structured [`Fix`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FixSafety {
    /// Tier 1: Applied by default `ril fix`. Mechanical unambiguous fixes, narrowing, safe lints,
    /// and private/`where`-local signature sync (reported in the mandatory capability banner).
    Safe,
    /// Tier 2: Requires `--allow-api-change`. Modifies `pkg` or `pub` function contracts.
    Contract,
    /// Tier 3: Requires `--unsafe`. Heuristic or behavior-affecting edits validated by rollback.
    Unsafe,
    /// Tier 4: Never applied automatically by CLI `ril fix`; exposed in `ril lsp` & `ril inspect`.
    Assist,
}

impl FixSafety {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Safe => "safe",
            Self::Contract => "contract",
            Self::Unsafe => "unsafe",
            Self::Assist => "assist",
        }
    }
}

/// Semantic category of a structured [`Fix`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FixKind {
    CallSiteMode,
    SignatureSync,
    UnusedAuthority,
    LocalSlotPromotion,
    RedundantVia,
    MissingImport,
    SyntaxForm,
    Lint,
    SemanticAssist,
}

impl FixKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CallSiteMode => "call_site_mode",
            Self::SignatureSync => "signature_sync",
            Self::UnusedAuthority => "unused_authority",
            Self::LocalSlotPromotion => "local_slot_promotion",
            Self::RedundantVia => "redundant_via",
            Self::MissingImport => "missing_import",
            Self::SyntaxForm => "syntax_form",
            Self::Lint => "lint",
            Self::SemanticAssist => "semantic_assist",
        }
    }
}

/// Additional diagnostic metadata tags (mirroring LSP `DiagnosticTag`).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticTag {
    Unnecessary,
    Deprecated,
}

impl DiagnosticTag {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unnecessary => "unnecessary",
            Self::Deprecated => "deprecated",
        }
    }
}

/// Byte-exact replacement strictly against the LF-normalized [`crate::span::SourceFile::text`].
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct TextEdit {
    pub span: Span,
    pub replacement: String,
}

impl TextEdit {
    pub fn new(span: Span, replacement: impl Into<String>) -> Self {
        Self {
            span,
            replacement: replacement.into(),
        }
    }
}

/// Explicit capability/effect contract change summary attached to signature-sync fixes.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct CapabilityDelta {
    pub symbol: String,
    pub visibility: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub added: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub removed: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub causal_chain: Vec<String>,
}

/// Structured machine-applicable fix shared across compiler diagnostics, `ril-lint`, `ril fix`,
/// `ril lsp`, and `ril inspect --include fix_hints`.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct Fix {
    pub id: String,
    pub title: String,
    pub safety: FixSafety,
    pub kind: FixKind,
    pub is_preferred: bool,
    #[serde(default)]
    pub is_organize_imports: bool,
    pub edits: Vec<TextEdit>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub delta: Option<CapabilityDelta>,
}

impl Fix {
    /// True iff this fix is safe for silent save-time application (LSP `source.fixAll.ril`):
    /// must be Tier 1 `Safe` AND must not widen any capability contract.
    pub fn is_non_widening_safe(&self) -> bool {
        self.safety == FixSafety::Safe && self.delta.as_ref().is_none_or(|d| d.added.is_empty())
    }
}
