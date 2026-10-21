//! Source coordinates checked before receiving can replace a descriptor.
//!
//! This relation grants no access, constructor identity, effect-row, default,
//! Result-inspection, freshness or escape authority. Callers must resolve the
//! original Source and validate the physical observation independently. Opaque
//! computations and unrelated rigid identities remain obligations.
use super::effect_identity::ArgumentKey;
use ril_syntax::ast::{Expr, ExprKind, RecordMember};
use std::collections::BTreeMap;

/// Complete expected source frozen at its real elaboration point.
/// None retains an unresolved source obligation; it is not an erased fallback.
#[derive(Debug, Clone)]
pub(crate) struct Target {
    /// The complete interpretation captured before evaluating the incoming
    /// value. Projections retain this same environment identity.
    pub(crate) environment: super::context::FrozenEnvironment,
    pub(crate) span: ril_compiler_core::source::Span,
    pub(crate) schema: Option<super::source_types::SourceSchema>,
    /// Frozen expanded syntax for contextual elaboration (not re-resolved in
    /// a later shadowing scope). Unknown source keeps this absent too.
    pub(crate) syntax: Option<std::sync::Arc<ril_syntax::ast::TypeExpr>>,
    /// A separate empty-literal context whose element graph has been proved
    /// to contain no source-sensitive coordinates. This is not a complete
    /// schema, and cannot authorize a stored array or a nonempty literal.
    pub(crate) empty_array_context: Option<std::sync::Arc<ril_syntax::ast::TypeExpr>>,
    /// Proven absence is distinct from failure to reconstruct a complete key.
    /// This only selects the additional source-coordinate check; ordinary
    /// typing, permissions and shape checks always retain their obligations.
    pub(crate) sensitivity: SchemaSensitivity,
}

impl Target {
    /// Transitional export for remaining key-based consumers. The graph is
    /// the sole stored structural truth; failure retains the source obligation.
    pub(crate) fn key(&self) -> Option<ArgumentKey> {
        self.schema.as_ref()?.key().ok()
    }

    pub(crate) fn receive(
        &self,
        actual: &ArgumentKey,
        fresh: Option<&Construction>,
        work: &mut usize,
    ) -> Option<bool> {
        let mut budget = super::source_types::WorkLimit::new(*work);
        let result = self
            .schema
            .as_ref()?
            .receive_key(actual, fresh, &mut budget);
        *work = budget.remaining();
        result.ok()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SchemaSensitivity {
    NotRequired,
    Required,
    Unknown,
}

#[derive(Debug, Clone)]
pub(crate) enum Construction {
    Opaque,
    Array(Vec<Construction>),
    Map(Vec<(Construction, Construction)>),
    Tuple(Vec<Construction>),
    Record(BTreeMap<String, Construction>),
}

/// Copying changes the outer immutable qualification, while preserving every
/// complete source coordinate. Eligibility and graph/authority transfer are
/// separate obligations, even when this type-view transformation succeeds.
pub(crate) fn copy_view(
    key: ArgumentKey,
    mode: super::copy_contract::CopyMode,
    work: &mut usize,
) -> Option<ArgumentKey> {
    *work = work.checked_sub(1)?;
    let immutable = matches!(&key, ArgumentKey::Name { name, arguments }
        if matches!(name.as_str(), "Immut" | "Prelude::Immut") && arguments.len() == 1);
    match (mode, immutable) {
        (super::copy_contract::CopyMode::Mutable, true) => {
            let ArgumentKey::Name { mut arguments, .. } = key else {
                return None;
            };
            arguments.pop()
        }
        (super::copy_contract::CopyMode::Immutable, false) => Some(ArgumentKey::Name {
            name: "Immut".into(),
            arguments: vec![key],
        }),
        _ => Some(key),
    }
}

fn charge(work: &mut usize, depth: usize) -> Option<()> {
    if depth > 64 {
        return None;
    }
    *work = work.checked_sub(1)?;
    Some(())
}

fn text_equal(left: &str, right: &str, work: &mut usize) -> Option<bool> {
    *work = work.checked_sub(left.len().max(right.len()).div_ceil(32))?;
    Some(left == right)
}

pub(crate) fn construction(expression: &Expr, work: &mut usize) -> Option<Construction> {
    fn walk(expression: &Expr, work: &mut usize, depth: usize) -> Option<Construction> {
        charge(work, depth)?;
        Some(match &expression.kind {
            ExprKind::Array(items) => Construction::Array(
                items
                    .iter()
                    .map(|item| walk(item, work, depth + 1))
                    .collect::<Option<_>>()?,
            ),
            ExprKind::Map(entries) => Construction::Map(
                entries
                    .iter()
                    .map(|(key, value)| {
                        Some((walk(key, work, depth + 1)?, walk(value, work, depth + 1)?))
                    })
                    .collect::<Option<_>>()?,
            ),
            ExprKind::Tuple(items) => Construction::Tuple(
                items
                    .iter()
                    .map(|item| walk(item, work, depth + 1))
                    .collect::<Option<_>>()?,
            ),
            // A named/typed constructor has already chosen its own declared
            // field types. Outer receiving cannot reopen that construction.
            ExprKind::Record {
                ty: None, members, ..
            } => {
                let mut fields = BTreeMap::new();
                for member in members {
                    charge(work, depth + 1)?;
                    let RecordMember::Field(field) = member else {
                        return Some(Construction::Opaque);
                    };
                    *work = work.checked_sub(field.name.len().div_ceil(32))?;
                    if fields
                        .insert(field.name.clone(), walk(&field.value, work, depth + 1)?)
                        .is_some()
                    {
                        return None;
                    }
                }
                Construction::Record(fields)
            }
            _ => Construction::Opaque,
        })
    }
    walk(expression, work, 0)
}

/// A genuinely empty construction has no existing element coordinates to
/// reopen. Only its actual syntax and a complete receiving schema admit this
/// rule; no current heap size or stored value supplies construction evidence.
pub(crate) fn empty_context(
    expected: &ArgumentKey,
    fresh: &Construction,
    work: &mut usize,
) -> Option<bool> {
    charge(work, 0)?;
    match (expected, fresh) {
        (ArgumentKey::Array { length, .. }, Construction::Array(items)) if items.is_empty() => {
            complete(expected, work)?;
            Some(
                length
                    .as_ref()
                    .is_none_or(|length| length == "const(int:0)"),
            )
        }
        (ArgumentKey::Map { .. }, Construction::Map(entries)) if entries.is_empty() => {
            complete(expected, work)?;
            Some(true)
        }
        _ => None,
    }
}

fn fixed(length: &str, work: &mut usize) -> Option<u64> {
    *work = work.checked_sub(length.len().div_ceil(32))?;
    length
        .strip_prefix("const(int:")?
        .strip_suffix(')')?
        .parse()
        .ok()
}

pub(crate) fn sensitive(key: &ArgumentKey, work: &mut usize) -> Option<bool> {
    fn walk(key: &ArgumentKey, work: &mut usize, depth: usize) -> Option<bool> {
        charge(work, depth)?;
        Some(match key {
            ArgumentKey::Closed(_) => return None,
            ArgumentKey::Binder { .. } => false,
            ArgumentKey::Array { element, .. } => {
                walk(element, work, depth + 1)?;
                // A dynamic outer target still has invariant element types.
                // Its nested dimensions cannot be erased by this fast path.
                true
            }
            ArgumentKey::Callable { .. } | ArgumentKey::GenericBuiltin(_) => true,
            ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                let mut any = false;
                for key in arguments {
                    any |= walk(key, work, depth + 1)?;
                }
                any
            }
            ArgumentKey::Map { key, value } => {
                let key = walk(key, work, depth + 1)?;
                let value = walk(value, work, depth + 1)?;
                key || value
            }
            ArgumentKey::Record { fields, row } => {
                let mut any = false;
                for (_, _, key) in fields {
                    any |= walk(key, work, depth + 1)?;
                }
                if let Some(row) = row {
                    any |= walk(row, work, depth + 1)?;
                }
                any
            }
        })
    }
    walk(key, work, 0)
}

pub(crate) fn complete(key: &ArgumentKey, work: &mut usize) -> Option<()> {
    fn walk(key: &ArgumentKey, work: &mut usize, depth: usize) -> Option<()> {
        charge(work, depth)?;
        match key {
            ArgumentKey::GenericBuiltin(_) => {}
            ArgumentKey::Closed(_) => return None,
            ArgumentKey::Binder { identity, .. } => {
                text_equal(identity, identity, work)?;
            }
            ArgumentKey::Array { length, element } => {
                if let Some(length) = length {
                    fixed(length, work)?;
                }
                walk(element, work, depth + 1)?;
            }
            ArgumentKey::Name { name, arguments } => {
                text_equal(name, name, work)?;
                for key in arguments {
                    walk(key, work, depth + 1)?;
                }
            }
            ArgumentKey::Tuple(items) => {
                for key in items {
                    walk(key, work, depth + 1)?;
                }
            }
            ArgumentKey::Map { key, value } => {
                walk(key, work, depth + 1)?;
                walk(value, work, depth + 1)?;
            }
            ArgumentKey::Record { fields, row } => {
                for (label, _, key) in fields {
                    text_equal(label, label, work)?;
                    walk(key, work, depth + 1)?;
                }
                if let Some(row) = row {
                    walk(row, work, depth + 1)?;
                }
            }
            ArgumentKey::Callable {
                parameters, result, ..
            } => {
                for (_, key) in parameters {
                    walk(key, work, depth + 1)?;
                }
                walk(result, work, depth + 1)?;
            }
        }
        Some(())
    }
    walk(key, work, 0)
}

/// Some(true) proves only these source coordinates; None proves nothing.
pub(crate) fn compatible(
    expected: &ArgumentKey,
    actual: &ArgumentKey,
    fresh: Option<&Construction>,
    work: &mut usize,
) -> Option<bool> {
    super::source_types::reception::receive_keys(expected, actual, fresh, work)
}
