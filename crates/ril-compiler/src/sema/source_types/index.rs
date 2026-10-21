//! Snapshot-owned storage view index. An ID is a cache of coordinates whose
//! original binding/declaration/occurrence must still be independently checked.
use super::*;
use crate::sema::context::{FrozenEnvId, FrozenEnvironment};
use crate::sema::{effect_identity::ArgumentKey, facts::Slot};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone)]
pub struct SourceTypeIndex(Arc<IndexData>);

#[derive(Debug)]
struct IndexData {
    types: Result<SourceTypes, SourceTypesError>,
    bindings: BTreeMap<usize, BindingView>,
}

#[derive(Debug)]
struct BindingView {
    ty: Result<Option<SourceTypeId>, SourceTypesError>,
    environment: FrozenEnvironment,
}

/// Complete coordinates and their declaration interpretation are one view.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceView {
    pub ty: SourceTypeId,
    pub environment: FrozenEnvId,
}

impl Default for SourceTypeIndex {
    fn default() -> Self {
        Self(Arc::new(IndexData {
            types: Ok(SourceTypes::default()),
            bindings: BTreeMap::new(),
        }))
    }
}

impl SourceTypeIndex {
    pub(super) fn retained_types(&self) -> Result<&SourceTypes, SourceTypesError> {
        self.0.types.as_ref().map_err(Clone::clone)
    }
    pub(super) fn retained_bindings(
        &self,
    ) -> impl ExactSizeIterator<
        Item = (
            usize,
            &Result<Option<SourceTypeId>, SourceTypesError>,
            &FrozenEnvironment,
        ),
    > {
        self.0
            .bindings
            .iter()
            .map(|(&binding, view)| (binding, &view.ty, &view.environment))
    }

    /// Admission failure and a poisoned declaration environment are not an
    /// unknown schema, even when no later source query happens to use them.
    pub(crate) fn validate(&self, work: &mut WorkLimit) -> Result<(), SourceTypesError> {
        work.charge(1)?;
        let types = self.retained_types()?;
        work.charge(self.0.bindings.len())?;
        for view in self.0.bindings.values() {
            let root = view.ty.as_ref().copied().map_err(Clone::clone)?;
            if view.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            if let Some(root) = root {
                work.charge(1)?;
                types.get(root)?;
            }
        }
        Ok(())
    }

    /// The capture exists even when the original type remains unresolved.
    /// An environment identity alone never supplies a missing type schema.
    pub fn binding_environment(&self, binding: usize) -> Option<FrozenEnvId> {
        let view = self.0.bindings.get(&binding)?;
        (!view.environment.is_poisoned()).then_some(view.environment.id())
    }
    /// Coordinate cache only: None is not proof of an absent schema. Admission
    /// and graph-retention consumers use the checked Result-returning APIs.
    pub fn binding_type(&self, binding: usize) -> Option<SourceTypeId> {
        match &self.0.bindings.get(&binding)?.ty {
            Ok(root) => *root,
            Err(_) => None,
        }
    }
    pub fn binding_view(&self, binding: usize) -> Option<SourceView> {
        let view = self.0.bindings.get(&binding)?;
        (!view.environment.is_poisoned()).then_some(SourceView {
            ty: self.binding_type(binding)?,
            environment: view.environment.id(),
        })
    }
    pub fn contains_binding(&self, binding: usize) -> bool {
        self.0.bindings.contains_key(&binding)
    }
    pub(crate) fn binding_schema(
        &self,
        binding: usize,
        original: Option<ril_compiler_core::ids::TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        self.binding_schema_if_known(binding, original, work)?
            .ok_or(SourceTypesError::Unresolved)
    }
    /// Unknown is a recorded declaration state, not an absent or corrupt
    /// lookup. Callers must preserve errors rather than infer unknown from one.
    pub(crate) fn binding_schema_if_known(
        &self,
        binding: usize,
        original: Option<ril_compiler_core::ids::TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError> {
        work.charge(1)?;
        let view = self
            .0
            .bindings
            .get(&binding)
            .ok_or(SourceTypesError::MissingNode)?;
        if view.environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let types = self.0.types.as_ref().map_err(Clone::clone)?;
        let Some(root) = view.ty.as_ref().copied().map_err(Clone::clone)? else {
            return Ok(None);
        };
        Ok(Some((
            SourceSchema::frozen_view(types, root, original, work)?,
            view.environment.clone(),
        )))
    }
    pub fn key(&self, id: SourceTypeId) -> Result<ArgumentKey, SourceTypesError> {
        self.0
            .types
            .as_ref()
            .map_err(Clone::clone)?
            .legacy_key(id, &mut WorkLimit::new(4096))
    }
    pub fn sensitivity(&self, id: SourceTypeId) -> SourceSensitivity {
        match &self.0.types {
            Ok(types) => types.sensitivity(id, &mut WorkLimit::new(4096)),
            Err(reason) => SourceSensitivity::Unknown {
                reason: reason.clone(),
            },
        }
    }
    pub fn project(
        &self,
        id: SourceTypeId,
        path: &[SourcePath],
    ) -> Result<SourceTypeId, SourceTypesError> {
        self.0
            .types
            .as_ref()
            .map_err(Clone::clone)?
            .project(id, path, &mut WorkLimit::new(4096))
    }
    pub(crate) fn projected_binding_key(
        &self,
        binding: usize,
        path: &[Slot],
        hir: Option<&crate::hir::nodes::HirProgram>,
    ) -> Result<ArgumentKey, SourceTypesError> {
        let id = self
            .0
            .bindings
            .get(&binding)
            .ok_or(SourceTypesError::MissingNode)?
            .ty
            .as_ref()
            .copied()
            .map_err(Clone::clone)?
            .ok_or(SourceTypesError::Unresolved)?;
        let types = self.0.types.as_ref().map_err(Clone::clone)?;
        projected_key(types, id, path, hir, &mut WorkLimit::new(12288))
    }
    pub(crate) fn validate_binding_schema(
        &self,
        binding: usize,
        original: Option<&SourceSchema>,
        environment: FrozenEnvId,
    ) -> bool {
        let Some(view) = self.0.bindings.get(&binding) else {
            return false;
        };
        if view.environment.id() != environment || view.environment.is_poisoned() {
            return false;
        }
        match (&view.ty, original) {
            (Ok(None), None) => self.0.types.is_ok(),
            (Ok(Some(id)), Some(original)) => {
                let check = || -> Result<bool, SourceTypesError> {
                    let types = self.0.types.as_ref().map_err(Clone::clone)?;
                    let mut work = WorkLimit::new(16384);
                    let recorded = SourceSchema::frozen_view(types, *id, None, &mut work)?;
                    recorded.equivalent(original, &mut work)
                };
                check() == Ok(true)
            }
            _ => false,
        }
    }
}

#[derive(Default)]
pub(crate) struct LiveSourceTypes {
    builder: Option<SourceBuilder>,
    bindings: BTreeMap<usize, BindingView>,
}

impl LiveSourceTypes {
    pub(crate) fn binding_schema(
        &self,
        binding: usize,
        original: Option<ril_compiler_core::ids::TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        self.binding_schema_if_known(binding, original, work)?
            .ok_or(SourceTypesError::Unresolved)
    }
    pub(crate) fn binding_schema_if_known(
        &self,
        binding: usize,
        original: Option<ril_compiler_core::ids::TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError> {
        work.charge(1)?;
        let view = self
            .bindings
            .get(&binding)
            .ok_or(SourceTypesError::MissingNode)?;
        if view.environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let Some(root) = view.ty.as_ref().copied().map_err(Clone::clone)? else {
            return Ok(None);
        };
        let builder = self.builder.as_ref().ok_or(SourceTypesError::MissingNode)?;
        Ok(Some((
            SourceSchema::copy_from(builder, root, original, work)?,
            view.environment.clone(),
        )))
    }
    pub(crate) fn record(
        &mut self,
        binding: usize,
        key: Option<&ArgumentKey>,
        environment: FrozenEnvironment,
    ) -> Result<(), SourceTypesError> {
        if self.bindings.contains_key(&binding) {
            return Err(SourceTypesError::AlreadyDefined);
        }
        let result = (|| {
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            let Some(key) = key else { return Ok(None) };
            if self.builder.is_none() {
                self.builder = Some(SourceBuilder::new()?);
            }
            self.builder
                .as_mut()
                .ok_or(SourceTypesError::MissingNode)?
                .import_key(key, &mut WorkLimit::new(4096))
                .map(Some)
        })();
        self.bindings.insert(
            binding,
            BindingView {
                ty: result.clone(),
                environment,
            },
        );
        result.map(|_| ())
    }
    pub(crate) fn record_schema(
        &mut self,
        binding: usize,
        schema: Option<&SourceSchema>,
        environment: FrozenEnvironment,
    ) -> Result<(), SourceTypesError> {
        if self.bindings.contains_key(&binding) {
            return Err(SourceTypesError::AlreadyDefined);
        }
        let mut work = WorkLimit::new(16384);
        work.charge(1)?;
        let result = (|| {
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            let Some(schema) = schema else {
                return Ok(None);
            };
            if self.builder.is_none() {
                self.builder = Some(SourceBuilder::new()?);
            }
            schema
                .copy_into(
                    self.builder.as_mut().ok_or(SourceTypesError::MissingNode)?,
                    &mut work,
                )
                .map(Some)
        })();
        self.bindings.insert(
            binding,
            BindingView {
                ty: result.clone(),
                environment,
            },
        );
        result.map(|_| ())
    }
    pub(crate) fn projected_binding_key(
        &self,
        binding: usize,
        path: &[Slot],
        hir: Option<&crate::hir::nodes::HirProgram>,
    ) -> Result<ArgumentKey, SourceTypesError> {
        let id = self
            .bindings
            .get(&binding)
            .ok_or(SourceTypesError::MissingNode)?
            .ty
            .as_ref()
            .copied()
            .map_err(Clone::clone)?
            .ok_or(SourceTypesError::Unresolved)?;
        let builder = self.builder.as_ref().ok_or(SourceTypesError::MissingNode)?;
        projected_key(builder, id, path, hir, &mut WorkLimit::new(8192))
    }
    pub(crate) fn freeze(self) -> SourceTypeIndex {
        let types = match self.builder {
            Some(builder) => builder.freeze(&mut WorkLimit::new(65536)),
            None => Ok(SourceTypes::default()),
        };
        SourceTypeIndex(Arc::new(IndexData {
            types,
            bindings: self.bindings,
        }))
    }
}

fn projected_key(
    types: &(impl SourceTypeQueries + LegacySourceExport),
    root: SourceTypeId,
    path: &[Slot],
    hir: Option<&crate::hir::nodes::HirProgram>,
    work: &mut WorkLimit,
) -> Result<ArgumentKey, SourceTypesError> {
    let steps = steps_in(path, work)?;
    match (types.project(root, &steps, work), hir) {
        (Ok(selected), _) => types.legacy_key(selected, work),
        (Err(SourceTypesError::MissingProjection | SourceTypesError::Unresolved), Some(hir)) => {
            // Resolve the indexed declaration, never a later mutable value.
            // The same budget pays for the unresolved walk and its expansion.
            let key = types.legacy_key(root, work)?;
            super::declarations::project_steps(&key, &steps, hir, work)
        }
        (Err(error), _) => Err(error),
    }
}

pub(crate) fn steps_in(
    path: &[Slot],
    work: &mut WorkLimit,
) -> Result<Vec<SourcePath>, SourceTypesError> {
    path.iter()
        .map(|slot| {
            work.charge(1)?;
            Ok(match slot {
                Slot::Field(label) => {
                    work.text(label)?;
                    SourcePath::Field(label.clone())
                }
                Slot::Tuple(index) => SourcePath::Tuple(*index),
                Slot::Index(_) | Slot::AnyIndex => SourcePath::Element,
                _ => return Err(SourceTypesError::MissingProjection),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_legacy_admissions_cannot_be_reclassified_as_unknown_views() {
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        let invalid = ArgumentKey::Array {
            length: Some("not a resolved extent".into()),
            element: Box::new(ArgumentKey::Tuple(vec![])),
        };
        assert_eq!(
            live.record(1, Some(&invalid), environment.clone()),
            Err(SourceTypesError::Unresolved)
        );
        live.record_schema(2, None, environment.clone()).unwrap();
        assert!(matches!(
            live.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        let frozen = live.freeze();
        assert!(matches!(
            frozen.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(!frozen.validate_binding_schema(1, None, environment.id()));
        assert!(frozen.validate_binding_schema(2, None, environment.id()));
        assert_eq!(
            frozen.validate(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
        assert!(matches!(
            frozen.retained(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn failed_schema_copies_keep_the_old_arena_and_the_exact_admission_failure() {
        let mut work = WorkLimit::new(100_000);
        let mut builder = SourceBuilder::new().unwrap();
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let root = builder
            .insert(
                SourceNode::Record {
                    fields: (0..5000)
                        .map(|index| SourceField {
                            label: format!("field_{index:04}"),
                            mutable: false,
                            value: scalar,
                        })
                        .collect(),
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let large = SourceSchema::frozen_view(&types, root, None, &mut work).unwrap();
        let small = SourceSchema::frozen_view(&types, scalar, None, &mut work).unwrap();
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        live.record_schema(0, Some(&small), environment.clone())
            .unwrap();
        assert_eq!(
            live.record_schema(1, Some(&large), environment),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert!(matches!(
            live.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let frozen = live.freeze();
        assert!(
            matches!(frozen.key(frozen.binding_type(0).unwrap()), Ok(ArgumentKey::Name {name, arguments}) if name=="int" && arguments.is_empty())
        );
        assert_eq!(
            frozen.validate(&mut WorkLimit::new(1_000_000)),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert!(matches!(
            frozen.retained(&mut WorkLimit::new(1_000_000)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn recorded_unknown_views_are_distinct_from_failed_lookups() {
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        live.record_schema(1, None, environment.clone()).unwrap();
        assert!(matches!(
            live.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Ok(None)
        ));
        assert!(matches!(
            live.binding_schema_if_known(2, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        assert!(matches!(
            live.binding_schema_if_known(1, None, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            live.record_schema(2, None, FrozenEnvironment::poisoned()),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(matches!(
            live.binding_schema_if_known(2, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        let frozen = live.freeze();
        assert!(matches!(
            frozen.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Ok(None)
        ));
        assert!(matches!(
            frozen.binding_schema_if_known(2, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(matches!(
            frozen.binding_schema_if_known(3, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        assert!(matches!(
            frozen.binding_schema_if_known(1, None, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let failed_arena = SourceTypeIndex(Arc::new(IndexData {
            types: Err(SourceTypesError::BudgetExceeded),
            bindings: BTreeMap::from([(
                1,
                BindingView {
                    ty: Ok(None),
                    environment,
                },
            )]),
        }));
        assert!(matches!(
            failed_arena.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn binding_graphs_keep_frozen_interpretations_and_unknowns_separate() {
        let original = Some(ril_compiler_core::ids::TypeExprId(7));
        let key = |length| ArgumentKey::Array {
            length: Some("const(int:0)".into()),
            element: Box::new(ArgumentKey::Array {
                length: Some(format!("const(int:{length})")),
                element: Box::new(ArgumentKey::Name {
                    name: "int".into(),
                    arguments: vec![],
                }),
            }),
        };
        let source = SourceSchema::import(&key(2), original, &mut WorkLimit::new(4096)).unwrap();
        let other = SourceSchema::import(&key(3), original, &mut WorkLimit::new(4096)).unwrap();
        let environment = FrozenEnvironment::default();
        let poisoned = FrozenEnvironment::poisoned();
        let mut live = LiveSourceTypes::default();
        live.record_schema(1, Some(&source), environment.clone())
            .unwrap();
        live.record_schema(2, None, environment.clone()).unwrap();
        assert_eq!(
            live.record_schema(1, Some(&other), environment.clone()),
            Err(SourceTypesError::AlreadyDefined)
        );
        assert_eq!(
            live.record_schema(3, Some(&source), poisoned.clone()),
            Err(SourceTypesError::Unresolved)
        );
        let index = live.freeze();
        let (copy, captured) = index
            .binding_schema(1, original, &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(copy.original(), original);
        assert_eq!(captured.id(), environment.id());
        assert_eq!(
            copy.equivalent(&source, &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_ne!(index.binding_type(1), Some(source.graph().1));
        assert!(index.validate_binding_schema(1, Some(&source), environment.id()));
        assert!(!index.validate_binding_schema(1, Some(&other), environment.id()));
        assert!(!index.validate_binding_schema(1, None, environment.id()));
        assert!(!index.validate_binding_schema(
            1,
            Some(&source),
            FrozenEnvironment::default().id()
        ));
        assert!(index.validate_binding_schema(2, None, environment.id()));
        assert!(!index.validate_binding_schema(2, Some(&source), environment.id()));
        assert!(!index.validate_binding_schema(3, None, poisoned.id()));
        assert!(matches!(
            index.binding_schema(2, original, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(matches!(
            index.binding_schema(1, original, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn binding_views_are_pinned_and_cannot_borrow_another_snapshot() {
        let key = ArgumentKey::Array {
            length: Some("const(int:0)".into()),
            element: Box::new(ArgumentKey::Array {
                length: Some("const(int:2)".into()),
                element: Box::new(ArgumentKey::Name {
                    name: "int".into(),
                    arguments: vec![],
                }),
            }),
        };
        let mut first = LiveSourceTypes::default();
        let environment = FrozenEnvironment::default();
        first.record(2, Some(&key), environment.clone()).unwrap();
        let first = first.freeze();
        let mut second = LiveSourceTypes::default();
        let other_environment = FrozenEnvironment::default();
        second
            .record(2, Some(&key), other_environment.clone())
            .unwrap();
        let second = second.freeze();
        let schema = SourceSchema::import(&key, None, &mut WorkLimit::new(4096)).unwrap();
        assert!(first.validate_binding_schema(2, Some(&schema), environment.id()));
        assert!(!first.validate_binding_schema(2, Some(&schema), other_environment.id()));
        assert_eq!(first.binding_view(2).unwrap().environment, environment.id());
        assert!(matches!(
            second.key(first.binding_type(2).unwrap()),
            Err(SourceTypesError::ForeignIdentity)
        ));
        let child = first
            .projected_binding_key(2, &[Slot::AnyIndex], None)
            .unwrap();
        assert!(
            matches!(child, ArgumentKey::Array { length: Some(length), .. } if length == "const(int:2)")
        );
        assert!(!SourceTypeIndex::default().validate_binding_schema(
            2,
            Some(&schema),
            environment.id()
        ));
    }
}
