//! Source coordinates checked before receiving can replace a descriptor.
//!
//! This relation grants no access, constructor identity, effect-row, default,
//! Result-inspection, freshness or escape authority. Callers must resolve the
//! original Source and validate the physical observation independently. Opaque
//! computations and unrelated rigid identities remain obligations.
use super::effect_identity::ArgumentKey;
use ril_syntax::ast::{Expr, ExprKind, RecordMember};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub(crate) struct TargetSource {
    pub(crate) header: std::sync::Arc<ril_syntax::ast::TypeExpr>,
    pub(crate) path: Vec<super::source_types::SourcePath>,
    pub(crate) environment: super::context::FrozenEnvironment,
}

impl TargetSource {
    pub(crate) fn projected(
        &self,
        step: super::source_types::SourcePath,
        work: &mut super::source_types::WorkLimit,
    ) -> Result<Self, super::source_types::SourceTypesError> {
        use super::source_types::{SourcePath, SourceTypesError};
        if self.path.len() >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        work.charge(1 + self.path.len())?;
        for step in self.path.iter().chain(std::iter::once(&step)) {
            match step {
                SourcePath::Field(name) => work.text(name)?,
                SourcePath::RecordRemainder(names) => {
                    work.charge(names.len())?;
                    for name in names {
                        work.text(name)?;
                    }
                }
                _ => {}
            }
        }
        let mut path = self.path.clone();
        path.push(step);
        Ok(Self {
            header: self.header.clone(),
            path,
            environment: self.environment.clone(),
        })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct StaticProjectionTarget {
    pub(crate) key: String,
    pub(crate) base: super::source_types::SourceSchema,
}

/// Complete expected source frozen at its real elaboration point.
/// None retains an unresolved source obligation; it is not an erased fallback.
#[derive(Debug, Clone)]
pub(crate) struct Target {
    pub(crate) source: Option<TargetSource>,
    pub(crate) static_projection: Option<StaticProjectionTarget>,
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
    pub(crate) fn receive_schema(
        &self,
        actual: &super::source_types::SourceSchema,
        fresh: Option<&Construction>,
        work: &mut super::source_types::WorkLimit,
    ) -> Result<bool, super::source_types::SourceTypesError> {
        self.schema
            .as_ref()
            .ok_or(super::source_types::SourceTypesError::Unresolved)?
            .receive_schema(actual, fresh, work)
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
    Nullary {
        declaration: ril_compiler_core::builtin_calls::NullaryConstructor,
        source: ril_compiler_core::ids::ExprId,
    },
    Array(Vec<Construction>),
    Map(Vec<(Construction, Construction)>),
    Tuple(Vec<Construction>),
    Record(BTreeMap<String, Construction>),
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
        // This records a syntactic claim only. Reception also requires the
        // independently resolved constructor template at this same HIR read.
        let declaration = match &expression.kind {
            ExprKind::Name(name) => {
                *work = work.checked_sub(name.len().div_ceil(32))?;
                ril_compiler_core::builtin_calls::NullaryConstructor::lookup(name)
            }
            ExprKind::Path(path) => {
                *work = work.checked_sub(path.len())?;
                for part in path {
                    *work = work.checked_sub(part.len().div_ceil(32))?;
                }
                ril_compiler_core::builtin_calls::NullaryConstructor::lookup(&path.join("::"))
            }
            _ => None,
        };
        if let Some((declaration, source)) = declaration.zip(expression.hir_id) {
            return Some(Construction::Nullary {
                declaration,
                source,
            });
        }
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

fn fixed(length: &str, work: &mut usize) -> Option<u64> {
    *work = work.checked_sub(length.len().div_ceil(32))?;
    length
        .strip_prefix("const(int:")?
        .strip_suffix(')')?
        .parse()
        .ok()
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
