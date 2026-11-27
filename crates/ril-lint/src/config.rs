//! Lint categories, severity levels, `ril.toml` `[lint]` configuration, and CLI overrides.

use std::{collections::BTreeMap, str::FromStr};

use serde::{Deserialize, Serialize};

use crate::registry::{self, LintDescriptor};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LintCategory {
    Correctness,
    Unused,
    Idiom,
    Style,
    Perf,
    Complexity,
}

impl LintCategory {
    pub const ALL: &'static [Self] = &[
        Self::Correctness,
        Self::Unused,
        Self::Idiom,
        Self::Style,
        Self::Perf,
        Self::Complexity,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Correctness => "correctness",
            Self::Unused => "unused",
            Self::Idiom => "idiom",
            Self::Style => "style",
            Self::Perf => "perf",
            Self::Complexity => "complexity",
        }
    }
}

impl FromStr for LintCategory {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "correctness" => Ok(Self::Correctness),
            "unused" => Ok(Self::Unused),
            "idiom" => Ok(Self::Idiom),
            "style" => Ok(Self::Style),
            "perf" => Ok(Self::Perf),
            "complexity" => Ok(Self::Complexity),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LintLevel {
    Allow,
    Warn,
    Deny,
}

impl LintLevel {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Allow => "allow",
            Self::Warn => "warn",
            Self::Deny => "deny",
        }
    }
}

impl FromStr for LintLevel {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "allow" => Ok(Self::Allow),
            "warn" => Ok(Self::Warn),
            "deny" => Ok(Self::Deny),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct LintOptions {
    pub max_args: usize,
    pub max_nesting: usize,
    pub max_lines: usize,
}

impl Default for LintOptions {
    fn default() -> Self {
        Self {
            max_args: 7,
            max_nesting: 5,
            max_lines: 100,
        }
    }
}

/// Ordered CLI override applied on top of `ril.toml` and inline directives.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub enum CliTarget {
    All,
    Warnings,
    Category(LintCategory),
    Rule(String),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct CliOverride {
    pub level: LintLevel,
    pub target: CliTarget,
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct LintConfig {
    #[serde(default)]
    pub categories: BTreeMap<LintCategory, LintLevel>,
    #[serde(default)]
    pub rules: BTreeMap<String, LintLevel>,
    #[serde(default)]
    pub options: LintOptions,
    #[serde(default)]
    pub cli_overrides: Vec<CliOverride>,
}

impl LintConfig {
    /// Parses a single CLI flag target (`all`, `warnings`, `<category>`, or `<rule_id>`).
    pub fn parse_cli_override(level: LintLevel, raw: &str) -> Result<CliOverride, String> {
        let key = raw.trim();
        if registry::is_compiler_error_code(key) {
            return Err(format!(
                "compiler error `{key}` is spec-normative and cannot be configured as a lint"
            ));
        }
        let target = if key == "all" {
            CliTarget::All
        } else if key == "warnings" {
            if level != LintLevel::Deny {
                return Err("`warnings` target is only valid with `--deny warnings`".to_owned());
            }
            CliTarget::Warnings
        } else if let Ok(cat) = LintCategory::from_str(key) {
            CliTarget::Category(cat)
        } else if registry::find_rule(key).is_some() {
            CliTarget::Rule(key.to_owned())
        } else {
            let hint = registry::suggest_rule(key)
                .map(|s| format!(" (did you mean `{s}`?)"))
                .unwrap_or_default();
            return Err(format!("unknown lint rule or category `{key}`{hint}"));
        };
        Ok(CliOverride { level, target })
    }

    /// Inserts a `ril.toml` `[lint]` key-value entry (`category` or `rule_id` = `allow|warn|deny`).
    pub fn insert_manifest_entry(&mut self, key: &str, value: &str) -> Result<(), String> {
        if registry::is_compiler_error_code(key) {
            return Err(format!(
                "compiler error `{key}` cannot be configured under `[lint]`"
            ));
        }
        let level = LintLevel::from_str(value).map_err(|()| {
            format!(
                "invalid lint level `{value}` for `{key}` (expected `allow`, `warn`, or `deny`)"
            )
        })?;
        if let Ok(cat) = LintCategory::from_str(key) {
            self.categories.insert(cat, level);
            Ok(())
        } else if registry::find_rule(key).is_some() {
            self.rules.insert(key.to_owned(), level);
            Ok(())
        } else {
            let hint = registry::suggest_rule(key)
                .map(|s| format!(" (did you mean `{s}`?)"))
                .unwrap_or_default();
            Err(format!("unknown lint rule or category `{key}`{hint}"))
        }
    }

    /// Resolves the effective level of `rule` given an optional inline directive override.
    ///
    /// Precedence (highest → lowest):
    /// 1. CLI `--allow`/`--warn`/`--deny` (left-to-right; `--deny warnings` promotes resolved `Warn`)
    /// 2. Inline `-- ril:` / `--! ril:` directive
    /// 3. Per-rule `ril.toml` `[lint]` entry
    /// 4. Category `ril.toml` `[lint]` entry
    /// 5. Built-in `LintDescriptor::default_level`
    pub fn effective_level(&self, rule: &LintDescriptor, inline_allowed: bool) -> LintLevel {
        let mut level = self
            .rules
            .get(rule.id)
            .copied()
            .or_else(|| self.categories.get(&rule.category).copied())
            .unwrap_or(rule.default_level);

        if inline_allowed {
            level = LintLevel::Allow;
        }

        let mut deny_warnings = false;
        for ov in &self.cli_overrides {
            match &ov.target {
                CliTarget::All => level = ov.level,
                CliTarget::Warnings => deny_warnings = true,
                CliTarget::Category(c) if *c == rule.category => level = ov.level,
                CliTarget::Rule(id) if id == rule.id => level = ov.level,
                _ => {}
            }
        }

        if deny_warnings && level == LintLevel::Warn {
            level = LintLevel::Deny;
        }
        level
    }

    /// Canonical serialized bytes for incremental `LintKey` hashing.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(self).unwrap_or_default()
    }
}
