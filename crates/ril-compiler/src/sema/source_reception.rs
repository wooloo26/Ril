//! Source coordinates checked before receiving can replace a descriptor.
//!
//! This relation grants no access, constructor identity, effect-row, default,
//! Result-inspection, freshness or escape authority. Callers must resolve the
//! original Source and validate the physical observation independently. Opaque
//! computations and unrelated rigid identities remain obligations.
use super::effect_identity::ArgumentKey;
use ril_syntax::ast::{Expr, ExprKind, ParameterMode, RecordMember};
use std::collections::BTreeMap;

/// Complete expected source frozen at its real elaboration point.
/// None retains an unresolved source obligation; it is not an erased fallback.
#[derive(Debug, Clone)]
pub(crate) struct Target {
    pub(crate) span: ril_compiler_core::source::Span,
    pub(crate) key: Option<ArgumentKey>,
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
        Some(match &expression.kind {
            ExprKind::Array(items) => Construction::Array(
                items
                    .iter()
                    .map(|item| walk(item, work, depth + 1))
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
            ArgumentKey::Callable { .. } => true,
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

#[derive(Clone, Copy)]
enum Position {
    Receiving,
    Invariant,
}

type RecordView<'a> = (
    BTreeMap<&'a str, (bool, &'a ArgumentKey)>,
    Option<&'a ArgumentKey>,
);

/// A selected closed remainder is part of this record. Open remainders retain
/// their exact identity and structure; this view proves no new lacks equation.
fn record_view<'a>(
    fields: &'a [(String, bool, ArgumentKey)],
    row: Option<&'a ArgumentKey>,
    work: &mut usize,
    depth: usize,
) -> Option<RecordView<'a>> {
    let mut cursor = row;
    let mut level = depth;
    let closed = loop {
        match cursor {
            None => break true,
            Some(ArgumentKey::Record { row, .. }) => {
                charge(work, level)?;
                level += 1;
                cursor = row.as_deref();
            }
            Some(_) => break false,
        }
    };
    let mut entries = BTreeMap::new();
    let mut insert = |fields: &'a [(String, bool, ArgumentKey)]| -> Option<()> {
        for (name, mutable, key) in fields {
            charge(work, depth)?;
            *work = work.checked_sub(name.len().div_ceil(32))?;
            if entries.insert(name.as_str(), (*mutable, key)).is_some() {
                return None;
            }
        }
        Some(())
    };
    insert(fields)?;
    if !closed {
        return Some((entries, row));
    }
    cursor = row;
    while let Some(ArgumentKey::Record { fields, row }) = cursor {
        insert(fields)?;
        cursor = row.as_deref();
    }
    Some((entries, None))
}

/// Some(true) proves only these source coordinates; None proves nothing.
pub(crate) fn compatible(
    expected: &ArgumentKey,
    actual: &ArgumentKey,
    fresh: Option<&Construction>,
    work: &mut usize,
) -> Option<bool> {
    // Admit both complete trees under the same work/depth boundary before an
    // empty literal can take its contextual element type.
    complete(expected, work)?;
    complete(actual, work)?;
    compare(expected, actual, fresh, Position::Receiving, work, 0)
}

fn compare(
    expected: &ArgumentKey,
    actual: &ArgumentKey,
    fresh: Option<&Construction>,
    position: Position,
    work: &mut usize,
    depth: usize,
) -> Option<bool> {
    fn contents(key: &ArgumentKey) -> Option<&ArgumentKey> {
        match key {
            ArgumentKey::Name { name, arguments } if name == "Immut" && arguments.len() == 1 => {
                Some(&arguments[0])
            }
            _ => None,
        }
    }
    charge(work, depth)?;
    if matches!(position, Position::Receiving) {
        if let Some(expected) = contents(expected) {
            // The ordinary immutability/initial-publication checks still own
            // this qualification. Source receiving compares the same written
            // inner dimensions, never converts a stored array's element type.
            return compare(
                expected,
                contents(actual).unwrap_or(actual),
                fresh,
                position,
                work,
                depth + 1,
            );
        }
        if let Some(actual) = contents(actual) {
            return compare(expected, actual, fresh, position, work, depth + 1);
        }
    }
    let answer = match (expected, actual) {
        (ArgumentKey::Closed(_), _) | (_, ArgumentKey::Closed(_)) => return None,
        (
            ArgumentKey::Binder {
                identity: left,
                sort: ls,
            },
            ArgumentKey::Binder {
                identity: right,
                sort: rs,
            },
        ) => {
            if ls != rs || !text_equal(left, right, work)? {
                return None;
            }
            true
        }
        (ArgumentKey::Binder { .. }, _) | (_, ArgumentKey::Binder { .. }) => return None,
        (
            ArgumentKey::Array {
                length: left,
                element: le,
            },
            ArgumentKey::Array {
                length: right,
                element: re,
            },
        ) => {
            let items = match fresh {
                Some(Construction::Array(items)) => Some(items),
                _ => None,
            };
            let lengths = match (left, right) {
                (Some(left), Some(right)) => fixed(left, work)? == fixed(right, work)?,
                (Some(left), None) => {
                    if let Some(items) = items {
                        fixed(left, work)? == u64::try_from(items.len()).ok()?
                    } else {
                        false
                    }
                }
                (None, Some(right)) => {
                    fixed(right, work)?;
                    matches!(position, Position::Receiving)
                }
                (None, None) => true,
            };
            if !lengths {
                return Some(false);
            }
            if let Some(items) = items {
                // A real empty construction receives the written element type.
                // There is no stored element/cardinality theorem to invent.
                if items.is_empty() {
                    complete(le, work)?;
                    true
                } else {
                    for item in items {
                        if !compare(le, re, Some(item), Position::Receiving, work, depth + 1)? {
                            return Some(false);
                        }
                    }
                    true
                }
            } else {
                compare(le, re, None, Position::Invariant, work, depth + 1)?
            }
        }
        (
            ArgumentKey::Callable {
                parameters: lp,
                result: lr,
                annotations: la,
            },
            ArgumentKey::Callable {
                parameters: rp,
                result: rr,
                annotations: ra,
            },
        ) => {
            // Invariance is a declared-type requirement even for an empty
            // enclosing container: no concrete callback object can pay it.
            if matches!(position, Position::Invariant) {
                if la.len() != ra.len() {
                    return None;
                }
                for (left, right) in la.iter().zip(ra) {
                    if !text_equal(left, right, work)? {
                        // Raw annotation text is not a normalized row set.
                        // Alias expansion and member order need their real
                        // captured Source identities, not string inequality.
                        return None;
                    }
                }
            }
            if lp.len() != rp.len() {
                return Some(false);
            }
            for ((lm, left), (rm, right)) in lp.iter().zip(rp) {
                if lm != rm {
                    return Some(false);
                }
                let fits = if *lm == ParameterMode::Read && matches!(position, Position::Receiving)
                {
                    compare(right, left, None, Position::Receiving, work, depth + 1)?
                } else {
                    compare(left, right, None, Position::Invariant, work, depth + 1)?
                };
                if !fits {
                    return Some(false);
                }
            }
            compare(lr, rr, None, position, work, depth + 1)?
        }
        (
            ArgumentKey::Name {
                name: left,
                arguments: la,
            },
            ArgumentKey::Name {
                name: right,
                arguments: ra,
            },
        ) => {
            if !text_equal(left, right, work)? || la.len() != ra.len() {
                return Some(false);
            }
            for (left, right) in la.iter().zip(ra) {
                if !compare(left, right, None, Position::Invariant, work, depth + 1)? {
                    return Some(false);
                }
            }
            true
        }
        (ArgumentKey::Tuple(left), ArgumentKey::Tuple(right)) => {
            if left.len() != right.len() {
                return Some(false);
            }
            let members = match fresh {
                Some(Construction::Tuple(items)) if items.len() == left.len() => Some(items),
                Some(Construction::Tuple(_)) => return None,
                _ => None,
            };
            for (index, (left, right)) in left.iter().zip(right).enumerate() {
                let child = members.map(|items| &items[index]);
                let position = if child.is_some() {
                    Position::Receiving
                } else {
                    Position::Invariant
                };
                if !compare(left, right, child, position, work, depth + 1)? {
                    return Some(false);
                }
            }
            true
        }
        (ArgumentKey::Map { key: lk, value: lv }, ArgumentKey::Map { key: rk, value: rv }) => {
            compare(lk, rk, None, Position::Invariant, work, depth + 1)?
                && compare(lv, rv, None, Position::Invariant, work, depth + 1)?
        }
        (
            ArgumentKey::Record {
                fields: left,
                row: lr,
            },
            ArgumentKey::Record {
                fields: right,
                row: rr,
            },
        ) => {
            let (left, lr) = record_view(left, lr.as_deref(), work, depth + 1)?;
            let (right, rr) = record_view(right, rr.as_deref(), work, depth + 1)?;
            if left.len() != right.len() {
                return if lr.is_some() || rr.is_some() {
                    None
                } else {
                    Some(false)
                };
            }
            let members = match fresh {
                Some(Construction::Record(fields)) => Some(fields),
                _ => None,
            };
            for ((ln, (lm, left)), (rn, (rm, right))) in left.iter().zip(&right) {
                if lm != rm || !text_equal(ln, rn, work)? {
                    return Some(false);
                }
                let child = members.and_then(|members| members.get(*ln));
                let child_position = if child.is_some() {
                    Position::Receiving
                } else if *lm {
                    Position::Invariant
                } else {
                    position
                };
                if !compare(left, right, child, child_position, work, depth + 1)? {
                    return Some(false);
                }
            }
            match (lr, rr) {
                (None, None) => true,
                (Some(left), Some(right)) => {
                    compare(left, right, None, Position::Invariant, work, depth + 1)?
                }
                _ => return None,
            }
        }
        _ => false,
    };
    Some(answer)
}
