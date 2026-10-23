//! An immutable complete receiving schema. Syntax is an origin, never the
//! authoritative structural representation after the graph has been frozen.
use super::*;
use ril_compiler_core::ids::TypeExprId;
#[path = "schema_const_nominal.rs"]
mod const_nominal;
#[path = "schema_operations.rs"]
mod operations;

#[derive(Debug, Clone)]
pub(crate) struct SourceSchema {
    types: SourceTypes,
    root: SourceTypeId,
    original: Option<TypeExprId>,
}

impl SourceSchema {
    pub(crate) fn scalar(
        scalar: SourceScalar,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let mut builder = SourceBuilder::new()?;
        let root = builder.insert(SourceNode::Scalar(scalar), work)?;
        Ok(Self {
            types: builder.freeze(work)?,
            root,
            original,
        })
    }

    pub(crate) fn syntax_projection(
        &self,
        span: ril_compiler_core::source::Span,
        work: &mut WorkLimit,
        binder: &mut impl FnMut(
            &str,
            bool,
            &mut WorkLimit,
        ) -> Result<ril_syntax::ast::TypeExpr, SourceTypesError>,
    ) -> Result<ril_syntax::ast::TypeExpr, SourceTypesError> {
        super::syntax_projection::project(&self.types, self.root, span, work, binder)
    }

    /// Only a binder at the current receiver needs its genuine constraint.
    /// Binders in unrelated members or the selected result remain valid Source.
    pub(crate) fn root_is_binder(&self, work: &mut WorkLimit) -> Result<bool, SourceTypesError> {
        let mut root = self.root;
        let mut seen = std::collections::BTreeSet::new();
        loop {
            work.charge(1)?;
            root = self.types.unalias(root, work)?;
            if !seen.insert(root) {
                return Err(SourceTypesError::AliasCycle);
            }
            let node = self.types.get(root)?;
            node.charge(work)?;
            match node {
                SourceNode::Container {
                    kind: SourceContainer::Immutable,
                    arguments,
                } => {
                    root = *arguments
                        .first()
                        .ok_or(SourceTypesError::InvalidContainer)?;
                }
                SourceNode::Binder(_) => return Ok(true),
                _ => return Ok(false),
            }
        }
    }

    /// None delegates exactly a projection through a genuine binder receiver.
    /// Missing members, invalid graphs and exhausted work remain errors.
    pub(crate) fn project_steps_if_structural(
        &self,
        path: &[SourcePath],
        work: &mut WorkLimit,
    ) -> Result<Option<Self>, SourceTypesError> {
        work.charge(1)?;
        self.types.get(self.root)?;
        let mut selected = self.clone();
        for step in path {
            if selected.root_is_binder(work)? {
                return Ok(None);
            }
            selected = selected.project_steps(std::slice::from_ref(step), work)?;
        }
        Ok(Some(selected))
    }

    pub(crate) fn is_builtin_instance(
        &self,
        declaration: ril_compiler_core::builtin_calls::GenericBuiltin,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let root = self.types.unalias(self.root, work)?;
        let node = self.types.get(root)?;
        node.charge(work)?;
        if let SourceNode::GenericBuiltin(actual) = node {
            return Ok(*actual == declaration);
        }
        let Some(instance) = super::polymorphic::instantiate(&self.types, declaration, root, work)?
        else {
            return Ok(false);
        };
        let SourceNode::Callable { annotations, .. } = node else {
            return Ok(false);
        };
        Ok(instance.fits_bounds(annotations))
    }

    /// Select the primitive's complete type correlations without discharging
    /// its latent bounds. Direct callers still check the resulting obligations.
    pub(crate) fn instantiate_builtin(
        &self,
        declaration: ril_compiler_core::builtin_calls::GenericBuiltin,
        work: &mut WorkLimit,
    ) -> Result<Option<super::polymorphic::Instance>, SourceTypesError> {
        super::reception::receive(&self.types, self.root, self.root, None, work)?;
        super::polymorphic::instantiate(&self.types, declaration, self.root, work)
    }

    /// A quantified declaration selects primitive argument labels before an
    /// instance has been chosen. A compatible monomorphic callable is not that
    /// declaration and cannot recover its polymorphic interface.
    pub(crate) fn is_generic_builtin(
        &self,
        declaration: ril_compiler_core::builtin_calls::GenericBuiltin,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let root = self.types.unalias(self.root, work)?;
        let node = self.types.get(root)?;
        node.charge(work)?;
        Ok(matches!(node, SourceNode::GenericBuiltin(actual) if *actual == declaration))
    }

    pub(crate) fn graph(&self) -> (&SourceTypes, SourceTypeId) {
        (&self.types, self.root)
    }

    /// This is the retained node identity, without unaliasing or a new graph.
    pub(crate) fn root_id(&self) -> SourceTypeId {
        self.root
    }

    /// A shared arena may also contain unrelated declarations. A view can
    /// select only a node reachable from this actual source root.
    pub(crate) fn view_at(
        &self,
        root: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        self.types.get(root)?;
        if !self.types.reachable([self.root], work)?.contains(&root) {
            return Err(SourceTypesError::MissingProjection);
        }
        Self::frozen_view(&self.types, root, self.original, work)
    }

    /// An immutable snapshot can lend its existing arena without rebuilding
    /// that arena or changing the selected node's identity.
    pub(crate) fn frozen_view(
        types: &SourceTypes,
        root: SourceTypeId,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        types.get(root)?;
        Ok(Self {
            types: types.clone(),
            root,
            original,
        })
    }

    /// Copy a complete graph into the existing live arena. A failed bounded
    /// copy leaves that arena intact, without unfinished reserved nodes.
    pub(crate) fn copy_into(
        &self,
        builder: &mut SourceBuilder,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        builder.import_frozen(&self.types, self.root, work)
    }

    pub(crate) fn equivalent(
        &self,
        other: &Self,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        super::reception::equivalent(&self.types, self.root, &other.types, other.root, work)
    }

    /// Relational type equality under two already authenticated captures.
    /// This neither registers those environments nor proves a callable row.
    pub(crate) fn equivalent_in(
        &self,
        other: &Self,
        self_environment: &crate::sema::context::FrozenEnvironment,
        other_environment: &crate::sema::context::FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        super::reception::equivalent_with_environments(
            &self.types,
            self.root,
            &other.types,
            other.root,
            (self_environment, other_environment),
            work,
        )
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
        self.key_with_work(&mut WorkLimit::new(4096))
    }

    pub(crate) fn key_with_work(
        &self,
        work: &mut WorkLimit,
    ) -> Result<crate::sema::effect_identity::ArgumentKey, SourceTypesError> {
        self.types.legacy_key(self.root, work)
    }

    pub(crate) fn project(&self, path: &[SourcePath]) -> Result<Self, SourceTypesError> {
        self.project_steps(path, &mut WorkLimit::new(4096))
    }

    /// Project one immutable view at a time. Remainder steps can create a new
    /// graph, while ordinary steps retain the selected graph's arena identity.
    pub(crate) fn project_steps(
        &self,
        path: &[ril_compiler_core::projection::TypeProjection],
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let mut selected = self.clone();
        for step in path {
            work.charge(1)?;
            if let SourcePath::ArrayRemainder { prefix, suffix } = step {
                selected = selected.array_remainder(*prefix, *suffix, work)?;
            } else if let SourcePath::RecordRemainder(excluded) = step {
                selected = selected.record_remainder(excluded, work)?;
            } else {
                selected.root =
                    selected
                        .types
                        .project(selected.root, std::slice::from_ref(step), work)?;
            }
        }
        Ok(selected)
    }

    /// The remaining shape comes only from the declared array coordinate.
    /// A dynamic input never becomes fixed merely because storage has a length.
    pub(crate) fn array_remainder(
        &self,
        prefix: u32,
        suffix: u32,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let (length, element) = self
            .array_parts(work)?
            .ok_or(SourceTypesError::MissingProjection)?;
        let removed = u64::from(prefix) + u64::from(suffix);
        let length = match length {
            SourceLength::Fixed(length) => SourceLength::Fixed(
                length
                    .checked_sub(removed)
                    .ok_or(SourceTypesError::MissingProjection)?,
            ),
            SourceLength::Dynamic => SourceLength::Dynamic,
        };
        let remainder = Self::array(length, &element, self.original, work)?;
        let root = self.types.unalias(self.root, work)?;
        if matches!(
            self.types.get(root)?,
            SourceNode::Container {
                kind: SourceContainer::Immutable,
                ..
            }
        ) {
            Self::container(
                SourceContainer::Immutable,
                &[remainder],
                self.original,
                work,
            )
        } else {
            Ok(remainder)
        }
    }

    pub(crate) fn original(&self) -> Option<TypeExprId> {
        self.original
    }

    /// The complete closed field domain of this view. A rigid, unresolved or
    /// cyclic row cannot be lowered as an empty remainder.
    pub(crate) fn closed_record_labels(
        &self,
        work: &mut WorkLimit,
    ) -> Result<std::collections::BTreeSet<String>, SourceTypesError> {
        use std::collections::BTreeSet;
        let mut cursor = Some(self.root);
        let mut seen = BTreeSet::new();
        let mut labels = BTreeSet::new();
        while let Some(id) = cursor {
            work.charge(1)?;
            let id = self.types.unalias(id, work)?;
            if !seen.insert(id) {
                return Err(SourceTypesError::RowCycle);
            }
            let SourceNode::Record { fields, row } = self.types.get(id)? else {
                return Err(SourceTypesError::Unresolved);
            };
            work.charge(fields.len())?;
            for field in fields {
                work.text(&field.label)?;
                if !labels.insert(field.label.clone()) {
                    return Err(SourceTypesError::DuplicateField);
                }
            }
            cursor = *row;
        }
        Ok(labels)
    }

    /// A row selection removes declared members from the complete actual
    /// record. Retain every other member and its original rigid tail; an
    /// unavailable field or cyclic/unknown row cannot become an empty row.
    pub(crate) fn record_remainder(
        &self,
        excluded: &std::collections::BTreeSet<String>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        use std::collections::BTreeMap;
        let (parts, tail) = self
            .record_parts(work)?
            .ok_or(SourceTypesError::Unresolved)?;
        work.charge(parts.len())?;
        let mut fields: BTreeMap<_, _> = parts
            .into_iter()
            .map(|(label, mutable, value)| (label, (mutable, value.root_id())))
            .collect();
        for label in excluded {
            work.text(label)?;
            if fields.remove(label).is_none() {
                return Err(SourceTypesError::MissingProjection);
            }
        }
        let tail = match tail {
            Some(tail) if fields.is_empty() => return Ok(tail),
            tail => tail.map(|tail| tail.root_id()),
        };
        let mut builder = SourceBuilder::new()?;
        let mapping = self.types.copy_into(
            fields.values().map(|(_, id)| *id).chain(tail),
            &mut builder,
            work,
        )?;
        work.charge(fields.len())?;
        let root = builder.insert(
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
        )?;
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{effect_identity::ArgumentKey, source_reception::Construction};

    #[test]
    fn array_remainders_preserve_declared_coordinates_and_do_not_strengthen_dynamic_views() {
        let mut work = WorkLimit::new(16384);
        let leaf = SourceSchema::scalar(SourceScalar::I32, None, &mut work).unwrap();
        let element = SourceSchema::array(SourceLength::Fixed(2), &leaf, None, &mut work).unwrap();
        let fixed = SourceSchema::array(SourceLength::Fixed(5), &element, None, &mut work).unwrap();
        let remainder = fixed.array_remainder(2, 1, &mut work).unwrap();
        let (extent, retained) = remainder.array_parts(&mut work).unwrap().unwrap();
        assert_eq!(extent, SourceLength::Fixed(2));
        assert!(retained.equivalent(&element, &mut work).unwrap());
        assert_eq!(
            fixed
                .array_remainder(5, 0, &mut work)
                .unwrap()
                .array_parts(&mut work)
                .unwrap()
                .unwrap()
                .0,
            SourceLength::Fixed(0)
        );
        assert!(fixed.array_remainder(4, 2, &mut work).is_err());
        let dynamic =
            SourceSchema::array(SourceLength::Dynamic, &element, None, &mut work).unwrap();
        assert_eq!(
            dynamic
                .array_remainder(2, 1, &mut work)
                .unwrap()
                .array_parts(&mut work)
                .unwrap()
                .unwrap()
                .0,
            SourceLength::Dynamic
        );
        let immutable = SourceSchema::container(
            SourceContainer::Immutable,
            std::slice::from_ref(&fixed),
            None,
            &mut work,
        )
        .unwrap();
        let expected =
            SourceSchema::container(SourceContainer::Immutable, &[remainder], None, &mut work)
                .unwrap();
        assert!(
            immutable
                .array_remainder(2, 1, &mut work)
                .unwrap()
                .equivalent(&expected, &mut work)
                .unwrap()
        );
        assert!(matches!(
            fixed.array_remainder(0, 0, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn tuple_suffixes_select_the_original_member_and_reject_large_or_empty_offsets() {
        let mut work = WorkLimit::new(8192);
        let first = SourceSchema::scalar(SourceScalar::I32, None, &mut work).unwrap();
        let last = SourceSchema::array(SourceLength::Fixed(3), &first, None, &mut work).unwrap();
        let tuple = SourceSchema::tuple(&[first.clone(), last.clone()], None, &mut work).unwrap();
        assert!(
            tuple
                .project_steps(&[SourcePath::TupleFromEnd(0)], &mut work)
                .unwrap()
                .equivalent(&last, &mut work)
                .unwrap()
        );
        assert!(
            tuple
                .project_steps(&[SourcePath::TupleFromEnd(1)], &mut work)
                .unwrap()
                .equivalent(&first, &mut work)
                .unwrap()
        );
        assert!(
            tuple
                .project_steps(&[SourcePath::TupleFromEnd(u32::MAX)], &mut work)
                .is_err()
        );
        let empty = SourceSchema::tuple(&[], None, &mut work).unwrap();
        assert!(
            empty
                .project_steps(&[SourcePath::TupleFromEnd(0)], &mut work)
                .is_err()
        );
    }

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
    fn structural_projection_retains_quantified_results_and_unrelated_binders() {
        use crate::sema::effect_identity::StaticBinderSort;
        let binder = ArgumentKey::Binder {
            identity: "declaration:U".into(),
            sort: StaticBinderSort::Type,
        };
        let key = ArgumentKey::Tuple(vec![ArgumentKey::Record {
            fields: vec![
                ("items".into(), false, array(Some(2), binder.clone())),
                ("other".into(), false, binder.clone()),
            ],
            row: None,
        }]);
        let schema = SourceSchema::import(&key, None, &mut WorkLimit::new(4096)).unwrap();
        assert!(
            schema
                .project_steps_if_structural(&[], &mut WorkLimit::new(4096))
                .unwrap()
                .unwrap()
                .equivalent_key(&key, &mut WorkLimit::new(4096))
                .unwrap()
        );
        let path = [
            SourcePath::Tuple(0),
            SourcePath::Field("items".into()),
            SourcePath::Element,
        ];
        let selected = schema
            .project_steps_if_structural(&path, &mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        assert_eq!(selected.key().unwrap(), binder);
        assert!(selected.root_is_binder(&mut WorkLimit::new(4096)).unwrap());
        assert!(
            selected
                .project_steps_if_structural(
                    &[SourcePath::Field("requires_constraint".into())],
                    &mut WorkLimit::new(4096),
                )
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            schema.project_steps_if_structural(
                &[SourcePath::Tuple(0), SourcePath::Field("absent".into())],
                &mut WorkLimit::new(4096),
            ),
            Err(SourceTypesError::MissingProjection)
        ));
        assert!(matches!(
            schema.project_steps_if_structural(&path, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let immutable = SourceSchema::import(
            &ArgumentKey::Name {
                name: "Immut".into(),
                arguments: vec![binder],
            },
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert!(immutable.root_is_binder(&mut WorkLimit::new(4096)).unwrap());
        assert!(
            immutable
                .project_steps_if_structural(&[], &mut WorkLimit::new(4096))
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn typed_projection_steps_compose_remainders_without_losing_hidden_dimensions() {
        use std::collections::BTreeSet;
        let original = Some(TypeExprId(31));
        let nested = array(Some(0), array(Some(2), int()));
        let key = ArgumentKey::Tuple(vec![
            int(),
            ArgumentKey::Record {
                fields: vec![
                    ("drop".into(), false, int()),
                    ("rows".into(), true, nested.clone()),
                ],
                row: None,
            },
        ]);
        let source = SourceSchema::import(&key, original, &mut WorkLimit::new(4096)).unwrap();
        let selected = source
            .project_steps(
                &[
                    SourcePath::Tuple(1),
                    SourcePath::RecordRemainder(BTreeSet::from(["drop".into()])),
                    SourcePath::Field("rows".into()),
                ],
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        assert_eq!(selected.original(), original);
        assert_eq!(
            selected.equivalent_key(&nested, &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_eq!(
            selected.equivalent_key(
                &array(Some(0), array(Some(3), int())),
                &mut WorkLimit::new(4096)
            ),
            Ok(false)
        );
        assert_eq!(source.key().unwrap(), key);
        assert!(matches!(
            source.project_steps(&[SourcePath::Tuple(1)], &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            source.project_steps(
                &[
                    SourcePath::Tuple(1),
                    SourcePath::RecordRemainder(BTreeSet::from(["absent".into()])),
                ],
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::MissingProjection)
        ));
    }

    #[test]
    fn bounded_graph_copy_rolls_back_every_partial_reservation() {
        let source = SourceSchema::import(
            &array(Some(0), array(Some(2), int())),
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        let mut failures = 0;
        for budget in 0..32 {
            let mut builder = SourceBuilder::new().unwrap();
            let preserved = builder
                .insert(
                    SourceNode::Scalar(SourceScalar::Bool),
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
            let checkpoint = builder.checkpoint();
            if let Err(reason) = source.copy_into(&mut builder, &mut WorkLimit::new(budget)) {
                assert_eq!(reason, SourceTypesError::BudgetExceeded);
                assert_eq!(builder.checkpoint(), checkpoint);
                failures += 1;
            }
            let types = builder.freeze(&mut WorkLimit::new(4096)).unwrap();
            assert!(matches!(
                types.get(preserved),
                Ok(SourceNode::Scalar(SourceScalar::Bool))
            ));
        }
        assert!(failures > 1);
    }

    #[test]
    fn graph_equivalence_preserves_recursive_edges_without_a_legacy_export() {
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let root = builder.reserve(&mut work).unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![SourceField {
                        label: "next".into(),
                        mutable: false,
                        value: root,
                    }],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let source = SourceSchema {
            types: builder.freeze(&mut work).unwrap(),
            root,
            original: Some(TypeExprId(32)),
        };
        assert!(matches!(
            source.key(),
            Err(SourceTypesError::RecursiveLegacyKey)
        ));
        let mut destination = SourceBuilder::new().unwrap();
        let copied = source.copy_into(&mut destination, &mut work).unwrap();
        let copy = SourceSchema::frozen_view(
            &destination.freeze(&mut work).unwrap(),
            copied,
            source.original(),
            &mut work,
        )
        .unwrap();
        assert_ne!(source.root_id(), copy.root_id());
        assert_eq!(source.equivalent(&copy, &mut work), Ok(true));
        assert!(matches!(
            source.equivalent(&copy, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
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
            rows.receive_schema(
                &SourceSchema::import(
                    &array(Some(0), array(Some(3), int())),
                    None,
                    &mut WorkLimit::new(4096)
                )
                .unwrap(),
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
        let actual =
            SourceSchema::import(&array(None, int()), None, &mut WorkLimit::new(4096)).unwrap();
        assert_eq!(
            target.receive_schema(&actual, None, &mut WorkLimit::new(4096)),
            Ok(false)
        );
        let fresh = Construction::Array(vec![Construction::Opaque, Construction::Opaque]);
        assert_eq!(
            target.receive_schema(&actual, Some(&fresh), &mut WorkLimit::new(4096)),
            Ok(true)
        );
        let mut exhausted = WorkLimit::new(0);
        assert_eq!(
            target.receive_schema(&actual, None, &mut exhausted),
            Err(SourceTypesError::BudgetExceeded)
        );
    }
}
