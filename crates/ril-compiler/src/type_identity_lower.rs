//! Preserve normalized source identity at the IR boundary. This conversion
//! never derives value permissions, storage cardinality, or allocation facts.
use crate::sema::effect_identity::ArgumentKey;
use ril_compiler_core::phase::{NotImplemented, Stage};
use ril_ir::specialization as irs;
use ril_syntax::ast::ParameterMode;

pub(crate) fn closed_key(value: &ArgumentKey) -> Result<irs::ArgumentKey, NotImplemented> {
    use irs::ArgumentKey as K;
    Ok(match value {
        ArgumentKey::GenericBuiltin(id) => K::GenericBuiltin(*id),
        ArgumentKey::Closed(value) => K::Closed(value.clone()),
        ArgumentKey::Binder { .. } => {
            return Err(NotImplemented::new(
                Stage::Lowering,
                "native specialization has an unclosed static binder",
            ));
        }
        ArgumentKey::Name { name, arguments } => K::Name {
            name: name.clone(),
            arguments: arguments.iter().map(closed_key).collect::<Result<_, _>>()?,
        },
        ArgumentKey::Array { length, element } => K::Array {
            length: length.clone(),
            element: Box::new(closed_key(element)?),
        },
        ArgumentKey::Map { key, value } => K::Map {
            key: Box::new(closed_key(key)?),
            value: Box::new(closed_key(value)?),
        },
        ArgumentKey::Tuple(items) => {
            K::Tuple(items.iter().map(closed_key).collect::<Result<_, _>>()?)
        }
        ArgumentKey::Record { fields, row } => K::Record {
            fields: fields
                .iter()
                .map(|(name, mutable, value)| Ok((name.clone(), *mutable, closed_key(value)?)))
                .collect::<Result<_, NotImplemented>>()?,
            row: row
                .as_ref()
                .map(|row| closed_key(row).map(Box::new))
                .transpose()?,
        },
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => K::Callable {
            parameters: parameters
                .iter()
                .map(|(mode, value)| {
                    Ok((
                        match mode {
                            ParameterMode::Read => irs::ParameterMode::Read,
                            ParameterMode::Mut => irs::ParameterMode::Mut,
                            ParameterMode::SharedMut => irs::ParameterMode::SharedMut,
                        },
                        closed_key(value)?,
                    ))
                })
                .collect::<Result<_, NotImplemented>>()?,
            result: Box::new(closed_key(result)?),
            annotations: annotations.clone(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::effect_identity::StaticBinderSort;

    #[test]
    fn empty_outer_arrays_keep_their_inner_dimension() {
        let value = ArgumentKey::Array {
            length: Some("0".into()),
            element: Box::new(ArgumentKey::Array {
                length: Some("2".into()),
                element: Box::new(ArgumentKey::Name {
                    name: "int".into(),
                    arguments: vec![],
                }),
            }),
        };
        let irs::ArgumentKey::Array { length, element } = closed_key(&value).unwrap() else {
            panic!("array identity erased")
        };
        assert_eq!(length.as_deref(), Some("0"));
        assert!(
            matches!(*element, irs::ArgumentKey::Array { length: Some(ref length), .. } if length == "2")
        );
    }

    #[test]
    fn callable_modes_and_qualified_bounds_survive_conversion() {
        let value = ArgumentKey::Callable {
            parameters: vec![(
                ParameterMode::SharedMut,
                ArgumentKey::Name {
                    name: "Cell".into(),
                    arguments: vec![],
                },
            )],
            result: Box::new(ArgumentKey::Tuple(vec![])),
            annotations: vec!["@{Read<int>}".into(), "&^mut".into()],
        };
        let irs::ArgumentKey::Callable {
            parameters,
            annotations,
            ..
        } = closed_key(&value).unwrap()
        else {
            panic!("callable identity erased")
        };
        assert_eq!(parameters[0].0, irs::ParameterMode::SharedMut);
        assert_eq!(annotations, ["@{Read<int>}", "&^mut"]);
    }

    #[test]
    fn an_unclosed_descendant_does_not_become_a_closed_leaf() {
        let value = ArgumentKey::Array {
            length: Some("0".into()),
            element: Box::new(ArgumentKey::Binder {
                identity: "definition:7:T".into(),
                sort: StaticBinderSort::Type,
            }),
        };
        assert!(closed_key(&value).is_err());
    }
}
