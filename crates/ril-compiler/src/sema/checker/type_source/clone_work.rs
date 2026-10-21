//! Preflight the data actually copied by TypingEnvironment::clone. Immutable
//! witness handles cost one entry and do not recursively copy their syntax.
use crate::sema::{
    context::TypingEnvironment,
    effect_identity::ArgumentKey,
    model::{
        Env, StaticCoordinate, Ty, TypeArgument,
        rows::{OpenTail, RowIdentity, RowTail},
    },
};

fn charge(work: &mut usize, count: usize) -> Option<()> {
    *work = work.checked_sub(count)?;
    Some(())
}
fn text(work: &mut usize, value: &str) -> Option<()> {
    charge(work, 1 + value.len().div_ceil(32))
}
fn row(work: &mut usize, tail: &OpenTail) -> Option<()> {
    match &tail.identity {
        RowIdentity::Binder(name) => text(work, name)?,
        RowIdentity::Fresh { owner, .. } => text(work, owner)?,
    }
    for name in &tail.lacks {
        text(work, name)?;
    }
    Some(())
}
fn ty(work: &mut usize, value: &Ty, depth: usize) -> Option<()> {
    charge(work, 1)?;
    if depth > 128 {
        return None;
    }
    match value {
        Ty::Int(name)
        | Ty::Float(name)
        | Ty::Named(name)
        | Ty::Generic(name)
        | Ty::StaticKey(name) => text(work, name)?,
        Ty::Applied {
            constructor,
            arguments,
        } => {
            text(work, constructor)?;
            for argument in arguments {
                charge(work, 1)?;
                match argument {
                    TypeArgument::Type(value) => ty(work, value, depth + 1)?,
                    TypeArgument::CanonicalType { ty: value, key } => {
                        text(work, key)?;
                        ty(work, value, depth + 1)?;
                    }
                    TypeArgument::Static(key) | TypeArgument::Symbolic(key) => text(work, key)?,
                }
            }
        }
        Ty::Projection { base, key } => {
            text(work, key)?;
            ty(work, base, depth + 1)?;
        }
        Ty::Immutable(value)
        | Ty::Optional(value)
        | Ty::Array(value)
        | Ty::Set(value)
        | Ty::Range(value) => ty(work, value, depth + 1)?,
        Ty::Result(left, right) | Ty::Map(left, right) => {
            ty(work, left, depth + 1)?;
            ty(work, right, depth + 1)?;
        }
        Ty::Tuple(values) => {
            for value in values {
                ty(work, value, depth + 1)?;
            }
        }
        Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
            for (name, (_, value)) in fields {
                text(work, name)?;
                ty(work, value, depth + 1)?;
            }
            if let Ty::OpenRecord { row: tail, .. } = value {
                row(work, tail)?;
            }
        }
        Ty::Callable(parameters, result) => {
            for parameter in parameters {
                ty(work, parameter, depth + 1)?;
            }
            ty(work, result, depth + 1)?;
        }
        Ty::NumericHole(_)
        | Ty::Unknown
        | Ty::Never
        | Ty::Unit
        | Ty::Bool
        | Ty::Str
        | Ty::Bytes => {}
    }
    Some(())
}
fn key(work: &mut usize, value: &ArgumentKey, depth: usize) -> Option<()> {
    charge(work, 1)?;
    if depth > 128 {
        return None;
    }
    match value {
        ArgumentKey::GenericBuiltin(_) => {}
        ArgumentKey::Closed(value)
        | ArgumentKey::Binder {
            identity: value, ..
        } => text(work, value)?,
        ArgumentKey::Name { name, arguments } => {
            text(work, name)?;
            for value in arguments {
                key(work, value, depth + 1)?;
            }
        }
        ArgumentKey::Tuple(values) => {
            for value in values {
                key(work, value, depth + 1)?;
            }
        }
        ArgumentKey::Array { length, element } => {
            if let Some(length) = length {
                text(work, length)?;
            }
            key(work, element, depth + 1)?;
        }
        ArgumentKey::Map {
            key: left,
            value: right,
        } => {
            key(work, left, depth + 1)?;
            key(work, right, depth + 1)?;
        }
        ArgumentKey::Record { fields, row } => {
            for (name, _, value) in fields {
                text(work, name)?;
                key(work, value, depth + 1)?;
            }
            if let Some(row) = row {
                key(work, row, depth + 1)?;
            }
        }
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => {
            for (_, value) in parameters {
                key(work, value, depth + 1)?;
            }
            key(work, result, depth + 1)?;
            for annotation in annotations {
                text(work, annotation)?;
            }
        }
    }
    Some(())
}

pub(super) fn environment(value: &TypingEnvironment, work: &mut usize) -> Option<()> {
    charge(work, 1)?;
    for (name, identity) in &value.generic_context {
        text(work, name)?;
        text(work, identity)?;
    }
    for (name, value) in &value.generic_substitutions {
        text(work, name)?;
        ty(work, value, 0)?;
    }
    for name in value.generic_sources.keys() {
        text(work, name)?;
    }
    for (name, value) in &value.static_key_arguments {
        text(work, name)?;
        if let StaticCoordinate::Label(value) = value {
            text(work, value)?;
        }
    }
    for name in value.bound_row_context.keys() {
        text(work, name)?;
    }
    for selection in value.bound_row_selections.values() {
        charge(work, 1)?;
        for (name, (_, value)) in &selection.remainder.fields {
            text(work, name)?;
            ty(work, value, 0)?;
        }
        if let RowTail::Open(tail) = &selection.remainder.tail {
            row(work, tail)?;
        }
        for field in &selection.fields {
            text(work, &field.label)?;
            ty(work, &field.ty, 0)?;
            key(work, &field.key, 0)?;
            crate::static_eval::charge_type_syntax_clone(&field.syntax, work)?;
        }
    }
    bindings(&value.contract_bindings, work)?;
    Some(())
}

pub(super) fn bindings(value: &Env, work: &mut usize) -> Option<()> {
    charge(work, 1)?;
    for name in value.keys() {
        text(work, name)?;
    }
    Some(())
}
