//! Transitional ingress for existing immutable ArgumentKey facts. This adapter
//! retains complete coordinates; it does not resolve an alias by name or
//! infer dimensions from a collection's runtime contents.
use super::*;
use crate::sema::effect_identity::ArgumentKey;

pub(crate) fn scalar(name: &str) -> Option<SourceScalar> {
    use SourceScalar::*;
    Some(match name.strip_prefix("Prelude::").unwrap_or(name) {
        "bool" => Bool,
        "str" => Str,
        "bytes" => Bytes,
        "never" => Never,
        "int" => Int,
        "i8" => I8,
        "i16" => I16,
        "i32" => I32,
        "i64" => I64,
        "i128" => I128,
        "isize" => Isize,
        "u8" => U8,
        "u16" => U16,
        "u32" => U32,
        "u64" => U64,
        "u128" => U128,
        "usize" => Usize,
        "bigint" => BigInt,
        "f32" => F32,
        "f64" => F64,
        other => Intrinsic(ril_compiler_core::builtin_types::AtomicBuiltinType::from_name(other)?),
    })
}

pub(super) fn container(name: &str) -> Option<SourceContainer> {
    use SourceContainer::*;
    Some(match name.strip_prefix("Prelude::").unwrap_or(name) {
        "Immut" => Immutable,
        "Option" => Option,
        "Result" => Result,
        "Set" => Set,
        "Range" => Range,
        "Heap::Heap" => Heap,
        "Deque::Deque" => Deque,
        _ => return None,
    })
}

pub(super) fn import_node(
    key: &ArgumentKey,
    builder: &mut SourceBuilder,
    work: &mut WorkLimit,
    depth: usize,
) -> Result<SourceTypeId, SourceTypesError> {
    work.charge(1)?;
    if depth >= 64 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    let mut child = |key| import_node(key, builder, work, depth + 1);
    let shape = match key {
        ArgumentKey::GenericBuiltin(id) => SourceNode::GenericBuiltin(*id),
        ArgumentKey::Closed(key) => {
            work.text(key)?;
            SourceNode::OpaqueComputation(key.clone())
        }
        ArgumentKey::Binder { identity, .. } => {
            work.text(identity)?;
            SourceNode::Binder(identity.clone())
        }
        ArgumentKey::Name { name, arguments } => {
            if let Some(schema) = super::standard_data::schema(name) {
                if !arguments.is_empty() {
                    return Err(SourceTypesError::InvalidContainer);
                }
                return schema.insert(builder, work);
            }
            let arguments = arguments
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?;
            work.text(name)?;
            if arguments.is_empty()
                && let Some(kind) = scalar(name)
            {
                SourceNode::Scalar(kind)
            } else if let Some(kind) = container(name) {
                SourceNode::Container { kind, arguments }
            } else {
                SourceNode::OpaqueName {
                    declaration: super::graph::IntrinsicNominal::lookup(name)
                        .map(super::graph::NominalDeclaration::Intrinsic),
                    name: name.clone(),
                    arguments,
                }
            }
        }
        ArgumentKey::Array { length, element } => {
            let element = child(element)?;
            let length = match length {
                None => SourceLength::Dynamic,
                Some(text) => {
                    work.text(text)?;
                    SourceLength::Fixed(
                        text.strip_prefix("const(int:")
                            .and_then(|text| text.strip_suffix(')'))
                            .and_then(|text| text.parse::<u64>().ok())
                            .ok_or(SourceTypesError::Unresolved)?,
                    )
                }
            };
            SourceNode::Array { length, element }
        }
        ArgumentKey::Map { key, value } => SourceNode::Map {
            key: child(key)?,
            value: child(value)?,
        },
        ArgumentKey::Tuple(items) if items.is_empty() => SourceNode::Scalar(SourceScalar::Unit),
        ArgumentKey::Tuple(items) => {
            SourceNode::Tuple(items.iter().map(&mut child).collect::<Result<_, _>>()?)
        }
        ArgumentKey::Record { fields, row } => {
            let fields = fields
                .iter()
                .map(|(label, mutable, key)| {
                    let value = import_node(key, builder, work, depth + 1)?;
                    work.text(label)?;
                    Ok(SourceField {
                        label: label.clone(),
                        mutable: *mutable,
                        value,
                    })
                })
                .collect::<Result<_, SourceTypesError>>()?;
            let row = row
                .as_deref()
                .map(|key| import_node(key, builder, work, depth + 1))
                .transpose()?;
            SourceNode::Record { fields, row }
        }
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => {
            let parameters = parameters
                .iter()
                .map(|(mode, key)| child(key).map(|key| (*mode, key)))
                .collect::<Result<_, _>>()?;
            let result = child(result)?;
            for annotation in annotations {
                work.text(annotation)?;
            }
            SourceNode::Callable {
                parameters,
                result,
                annotations: annotations.clone(),
                row_identity: None,
            }
        }
    };
    builder.insert(shape, work)
}

impl SourceBuilder {
    pub(crate) fn import_key(
        &mut self,
        key: &ArgumentKey,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let checkpoint = self.begin_transaction(work)?;
        match import_node(key, self, work, 0) {
            Ok(root) => {
                self.commit_transaction(checkpoint)?;
                Ok(root)
            }
            Err(error) => {
                self.rollback_transaction(checkpoint)?;
                Err(error)
            }
        }
    }
}

pub(crate) fn resolved_names(
    witness: &crate::sema::model::SourceTypeWitness,
    declarations: &std::collections::BTreeMap<String, ril_syntax::ast::TypeDeclaration>,
) -> bool {
    use ril_syntax::ast::TypeKind;
    let mut pending = vec![&witness.syntax];
    let mut visits = 0;
    while let Some(syntax) = pending.pop() {
        visits += 1;
        if visits > 4096 {
            return false;
        }
        match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                let full = path.join("::");
                let name = full.strip_prefix("Prelude::").unwrap_or(&full);
                let known = matches!(
                    name,
                    "bool"
                        | "str"
                        | "bytes"
                        | "never"
                        | "f32"
                        | "f64"
                        | "int"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                        | "bigint"
                        | "Immut"
                        | "Option"
                        | "Result"
                        | "Set"
                        | "Range"
                        | "Heap::Heap"
                        | "Deque::Deque"
                ) || (arguments.is_empty()
                    && crate::sema::checker::is_known_builtin_source_type(&full))
                    || declarations.get(&full).is_some_and(|declaration| {
                        declaration.nominal
                            || declaration.opaque
                            || !declaration.variants.is_empty()
                    });
                if !known {
                    return false;
                }
                pending.extend(arguments);
            }
            TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
                pending.push(inner)
            }
            TypeKind::Map { key, value } => pending.extend([&**key, &**value]),
            TypeKind::Tuple(items) => pending.extend(items),
            TypeKind::Record { fields, .. } => pending.extend(fields.iter().map(|field| &field.ty)),
            TypeKind::Callable {
                parameters, result, ..
            } => {
                pending.extend(
                    parameters
                        .iter()
                        .filter_map(|parameter| parameter.ty.as_ref()),
                );
                pending.extend(result.iter().map(|result| &**result));
            }
            TypeKind::Computation(_) => {}
            _ => return false,
        }
    }
    true
}
