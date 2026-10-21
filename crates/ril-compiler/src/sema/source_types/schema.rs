//! An immutable complete receiving schema. Syntax is an origin, never the
//! authoritative structural representation after the graph has been frozen.
use super::*;
use ril_compiler_core::ids::TypeExprId;

#[derive(Debug, Clone)]
pub(crate) struct SourceSchema {
    types: SourceTypes,
    root: SourceTypeId,
    original: Option<TypeExprId>,
}

impl SourceSchema {
    pub(crate) fn copy_from(
        graph: &impl SourceTypeQueries,
        root: SourceTypeId,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        let copy = graph.substitute(root, &std::collections::BTreeMap::new(), work)?;
        Ok(Self {
            types: copy.types,
            root: copy.root,
            original,
        })
    }

    pub(crate) fn equivalent_key(
        &self,
        key: &crate::sema::effect_identity::ArgumentKey,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let mut builder = SourceBuilder::new()?;
        let root = builder.import_key(key, work)?;
        super::reception::equivalent(&self.types, self.root, &builder, root, work)
    }
    pub(crate) fn import(
        key: &crate::sema::effect_identity::ArgumentKey,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        let mut builder = SourceBuilder::new()?;
        let root = builder.import_key(key, work)?;
        let types = builder.freeze(work)?;
        Ok(Self {
            types,
            root,
            original,
        })
    }

    pub(crate) fn key(
        &self,
    ) -> Result<crate::sema::effect_identity::ArgumentKey, SourceTypesError> {
        self.types.legacy_key(self.root, &mut WorkLimit::new(4096))
    }

    pub(crate) fn project(&self, path: &[SourcePath]) -> Result<Self, SourceTypesError> {
        let root = self
            .types
            .project(self.root, path, &mut WorkLimit::new(4096))?;
        Ok(Self {
            types: self.types.clone(),
            root,
            original: self.original,
        })
    }

    pub(crate) fn original(&self) -> Option<TypeExprId> {
        self.original
    }

    /// A row selection removes declared members from the complete actual
    /// record. Retain every other member and its original rigid tail; an
    /// unavailable field or cyclic/unknown row cannot become an empty row.
    pub(crate) fn record_remainder(
        &self,
        excluded: &std::collections::BTreeSet<String>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        use std::collections::{BTreeMap, BTreeSet};
        let mut cursor = Some(self.root);
        let mut seen = BTreeSet::new();
        let mut fields = BTreeMap::new();
        let tail = loop {
            work.charge(1)?;
            let Some(id) = cursor else { break None };
            let id = self.types.unalias(id, work)?;
            if !seen.insert(id) {
                return Err(SourceTypesError::RowCycle);
            }
            match self.types.get(id)? {
                SourceNode::Record { fields: next, row } => {
                    for field in next {
                        work.charge(1)?;
                        work.text(&field.label)?;
                        if fields
                            .insert(field.label.clone(), (field.mutable, field.value))
                            .is_some()
                        {
                            return Err(SourceTypesError::DuplicateField);
                        }
                    }
                    cursor = *row;
                }
                SourceNode::Binder(_) if seen.len() > 1 => break Some(id),
                _ => return Err(SourceTypesError::Unresolved),
            }
        };
        for label in excluded {
            work.text(label)?;
            if fields.remove(label).is_none() {
                return Err(SourceTypesError::MissingProjection);
            }
        }
        let mut builder = SourceBuilder::new()?;
        let mapping = self.types.copy_into(
            fields.values().map(|(_, id)| *id).chain(tail),
            &mut builder,
            work,
        )?;
        let root = if let Some(tail) = tail.filter(|_| fields.is_empty()) {
            mapping[&tail]
        } else {
            work.charge(fields.len())?;
            builder.insert(
                SourceNode::Record {
                    fields: fields
                        .into_iter()
                        .map(|(label, (mutable, value))| SourceField {
                            label,
                            mutable,
                            value: mapping[&value],
                        })
                        .collect(),
                    row: tail.map(|id| mapping[&id]),
                },
                work,
            )?
        };
        Ok(Self {
            types: builder.freeze(work)?,
            root,
            original: self.original,
        })
    }

    pub(crate) fn project_field(&self, name: &str) -> Result<Self, SourceTypesError> {
        let mut work = WorkLimit::new(4096);
        work.text(name)?;
        let root = self
            .types
            .project(self.root, &[SourcePath::Field(name.into())], &mut work)?;
        Ok(Self {
            types: self.types.clone(),
            root,
            original: self.original,
        })
    }

    pub(crate) fn receive_key(
        &self,
        actual: &crate::sema::effect_identity::ArgumentKey,
        fresh: Option<&crate::sema::source_reception::Construction>,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let mut builder = SourceBuilder::new()?;
        let actual = builder.import_key(actual, work)?;
        super::reception::receive_from(&self.types, self.root, &builder, actual, fresh, work)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{effect_identity::ArgumentKey, source_reception::Construction};

    fn array(length: Option<u64>, element: ArgumentKey) -> ArgumentKey {
        ArgumentKey::Array {
            length: length.map(|n| format!("const(int:{n})")),
            element: Box::new(element),
        }
    }

    fn int() -> ArgumentKey {
        ArgumentKey::Name {
            name: "int".into(),
            arguments: vec![],
        }
    }

    #[test]
    fn projected_schema_keeps_its_original_annotation_and_hidden_empty_dimensions() {
        let original = TypeExprId(17);
        let key = ArgumentKey::Record {
            fields: vec![("rows".into(), true, array(Some(0), array(Some(2), int())))],
            row: None,
        };
        let schema = SourceSchema::import(&key, Some(original), &mut WorkLimit::new(4096)).unwrap();
        let rows = schema.project_field("rows").unwrap();
        assert_eq!(rows.original(), Some(original));
        assert_eq!(
            rows.project(&[SourcePath::Element]).unwrap().key().unwrap(),
            array(Some(2), int())
        );
        assert_eq!(
            rows.receive_key(
                &array(Some(0), array(Some(3), int())),
                None,
                &mut WorkLimit::new(4096)
            ),
            Ok(false)
        );
        assert_eq!(schema.key().unwrap(), key);
    }

    #[test]
    fn row_remainders_keep_dimensions_callable_contracts_and_rigid_tails() {
        use crate::sema::effect_identity::StaticBinderSort;
        use std::collections::BTreeSet;
        let tail = ArgumentKey::Binder {
            identity: "caller:S".into(),
            sort: StaticBinderSort::Type,
        };
        let action = ArgumentKey::Callable {
            parameters: vec![(ril_syntax::ast::ParameterMode::Read, int())],
            result: Box::new(int()),
            annotations: vec!["Source(value)".into()],
        };
        let retained = vec![
            ("action".into(), false, action),
            ("empty".into(), true, array(Some(0), array(Some(3), int()))),
        ];
        let mut fields = retained.clone();
        fields.push(("items".into(), true, array(Some(2), int())));
        let source = SourceSchema::import(
            &ArgumentKey::Record {
                fields,
                row: Some(Box::new(tail.clone())),
            },
            Some(TypeExprId(19)),
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        let remainder = source
            .record_remainder(&BTreeSet::from(["items".into()]), &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(remainder.original(), source.original());
        assert_eq!(
            remainder.key().unwrap(),
            ArgumentKey::Record {
                fields: retained,
                row: Some(Box::new(tail.clone()))
            }
        );
        let all = BTreeSet::from(["action".into(), "empty".into(), "items".into()]);
        assert_eq!(
            source
                .record_remainder(&all, &mut WorkLimit::new(4096))
                .unwrap()
                .key()
                .unwrap(),
            tail
        );
        assert!(matches!(
            source.record_remainder(
                &BTreeSet::from(["unknown".into()]),
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::MissingProjection)
        ));
        assert!(matches!(
            source.record_remainder(&all, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn row_remainders_copy_recursive_members_but_reject_circular_rows() {
        use std::collections::BTreeSet;
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let root = builder.reserve(&mut work).unwrap();
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![
                        SourceField {
                            label: "value".into(),
                            mutable: true,
                            value: scalar,
                        },
                        SourceField {
                            label: "next".into(),
                            mutable: false,
                            value: root,
                        },
                    ],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let source = SourceSchema {
            types: builder.freeze(&mut work).unwrap(),
            root,
            original: None,
        };
        let remainder = source
            .record_remainder(&BTreeSet::from(["value".into()]), &mut work)
            .unwrap();
        assert_eq!(
            remainder
                .project(&[
                    SourcePath::Field("next".into()),
                    SourcePath::Field("value".into())
                ])
                .unwrap()
                .key()
                .unwrap(),
            int()
        );
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![],
                    row: Some(root),
                },
                &mut work,
            )
            .unwrap();
        let cyclic = SourceSchema {
            types: builder.freeze(&mut work).unwrap(),
            root,
            original: None,
        };
        assert!(matches!(
            cyclic.record_remainder(&BTreeSet::new(), &mut work),
            Err(SourceTypesError::RowCycle)
        ));
    }

    #[test]
    fn graph_reception_keeps_literal_context_distinct_from_stored_or_copied_values() {
        let target =
            SourceSchema::import(&array(Some(2), int()), None, &mut WorkLimit::new(4096)).unwrap();
        let actual = array(None, int());
        assert_eq!(
            target.receive_key(&actual, None, &mut WorkLimit::new(4096)),
            Ok(false)
        );
        let fresh = Construction::Array(vec![Construction::Opaque, Construction::Opaque]);
        assert_eq!(
            target.receive_key(&actual, Some(&fresh), &mut WorkLimit::new(4096)),
            Ok(true)
        );
        let mut exhausted = WorkLimit::new(0);
        assert_eq!(
            target.receive_key(&actual, None, &mut exhausted),
            Err(SourceTypesError::BudgetExceeded)
        );
    }
}
