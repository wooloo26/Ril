//! Snapshot-owned storage view index. An ID is a cache of coordinates whose
//! original binding/declaration/occurrence must still be independently checked.
use super::*;
use crate::sema::context::{FrozenEnvId, FrozenEnvironment};
use crate::sema::{effect_identity::ArgumentKey, facts::Slot};
use ril_compiler_core::ids::TypeExprId;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone)]
pub struct SourceTypeIndex(Arc<IndexData>);

#[derive(Debug)]
struct IndexData {
    types: Result<SourceTypes, SourceTypesError>,
    bindings: BTreeMap<usize, BindingView>,
    environments: BTreeMap<FrozenEnvId, FrozenEnvironment>,
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
            environments: BTreeMap::new(),
        }))
    }
}

impl SourceTypeIndex {
    pub(crate) fn environment(
        &self,
        id: FrozenEnvId,
        work: &mut WorkLimit,
    ) -> Result<FrozenEnvironment, SourceTypesError> {
        work.charge(2 + self.0.environments.len().checked_ilog2().unwrap_or(0) as usize)?;
        let environment = self
            .0
            .environments
            .get(&id)
            .ok_or(SourceTypesError::MissingNode)?;
        if environment.is_poisoned() || environment.id() != id {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(environment.clone())
    }

    pub(crate) fn view_schema(
        &self,
        view: SourceView,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        work.charge(1)?;
        let types = self.retained_types()?;
        let environment = self.environment(view.environment, work)?;
        Ok((
            SourceSchema::frozen_view(types, view.ty, original, work)?,
            environment,
        ))
    }

    pub(super) fn retained_types(&self) -> Result<&SourceTypes, SourceTypesError> {
        self.0.types.as_ref().map_err(Clone::clone)
    }
    /// Admission failure and a poisoned declaration environment are not an
    /// unknown schema, even when no later source query happens to use them.
    pub(crate) fn validate(&self, work: &mut WorkLimit) -> Result<(), SourceTypesError> {
        work.charge(1)?;
        let types = self.retained_types()?;
        work.charge(self.0.environments.len())?;
        for (identity, environment) in &self.0.environments {
            if environment.is_poisoned() || environment.id() != *identity {
                return Err(SourceTypesError::Unresolved);
            }
        }
        work.charge(self.0.bindings.len())?;
        for view in self.0.bindings.values() {
            let root = view.ty.as_ref().copied().map_err(Clone::clone)?;
            if view.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            if !self.0.environments.contains_key(&view.environment.id()) {
                return Err(SourceTypesError::MissingNode);
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
    environments: BTreeMap<FrozenEnvId, FrozenEnvironment>,
}

impl LiveSourceTypes {
    fn admit_environment(
        &self,
        environment: &FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<FrozenEnvId, SourceTypesError> {
        // Lookup, possible insertion and shared-handle storage are all paid
        // before a schema import can publish nodes into this same domain.
        work.charge(3 + 2 * (self.environments.len().checked_ilog2().unwrap_or(0) as usize + 1))?;
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let id = environment.id();
        if self
            .environments
            .get(&id)
            .is_some_and(|previous| previous.is_poisoned() || previous.id() != id)
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(id)
    }

    pub(crate) fn intern_environment(
        &mut self,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<FrozenEnvId, SourceTypesError> {
        let id = self.admit_environment(&environment, work)?;
        self.environments.entry(id).or_insert(environment);
        Ok(id)
    }

    pub(crate) fn environment(
        &self,
        id: FrozenEnvId,
        work: &mut WorkLimit,
    ) -> Result<FrozenEnvironment, SourceTypesError> {
        work.charge(2 + self.environments.len().checked_ilog2().unwrap_or(0) as usize)?;
        let environment = self
            .environments
            .get(&id)
            .ok_or(SourceTypesError::MissingNode)?;
        if environment.is_poisoned() || environment.id() != id {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(environment.clone())
    }

    pub(crate) fn view_schema(
        &self,
        view: SourceView,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        work.charge(1)?;
        let environment = self.environment(view.environment, work)?;
        let builder = self.builder.as_ref().ok_or(SourceTypesError::MissingNode)?;
        let types = builder.snapshot(work)?;
        Ok((
            SourceSchema::frozen_view(&types, view.ty, original, work)?,
            environment,
        ))
    }

    /// Every receiving boundary may retain a complete view in this same arena.
    /// An unsuccessful copy publishes neither a type root nor an environment.
    pub(crate) fn intern_schema(
        &mut self,
        schema: &SourceSchema,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<SourceView, SourceTypesError> {
        work.charge(2)?;
        let id = self.admit_environment(&environment, work)?;
        if self.builder.is_none() {
            self.builder = Some(SourceBuilder::new()?);
        }
        let ty = schema.copy_into(
            self.builder.as_mut().ok_or(SourceTypesError::MissingNode)?,
            work,
        )?;
        self.environments.entry(id).or_insert(environment);
        Ok(SourceView {
            ty,
            environment: id,
        })
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
        let types = builder.snapshot(work)?;
        Ok(Some((
            SourceSchema::frozen_view(&types, root, original, work)?,
            view.environment.clone(),
        )))
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
        work.charge(3 + 2 * (self.bindings.len().checked_ilog2().unwrap_or(0) as usize + 1))?;
        let admitted = self.admit_environment(&environment, &mut work);
        let result = (|| {
            admitted.as_ref().map_err(Clone::clone)?;
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
        if admitted.is_ok() {
            self.environments
                .entry(environment.id())
                .or_insert_with(|| environment.clone());
        }
        self.bindings.insert(
            binding,
            BindingView {
                ty: result.clone(),
                environment,
            },
        );
        result.map(|_| ())
    }
    pub(crate) fn freeze(self) -> SourceTypeIndex {
        let types = match self.builder {
            Some(builder) => builder.freeze(&mut WorkLimit::new(65536)),
            None => Ok(SourceTypes::default()),
        };
        SourceTypeIndex(Arc::new(IndexData {
            types,
            bindings: self.bindings,
            environments: self.environments,
        }))
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

    fn recursive_schema() -> SourceSchema {
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let inner = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(3),
                    element: scalar,
                },
                &mut work,
            )
            .unwrap();
        let outer = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: inner,
                },
                &mut work,
            )
            .unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![
                        SourceField {
                            label: "again".into(),
                            mutable: false,
                            value: root,
                        },
                        SourceField {
                            label: "empty".into(),
                            mutable: false,
                            value: outer,
                        },
                    ],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        SourceSchema::frozen_view(&types, root, None, &mut work).unwrap()
    }

    #[test]
    fn live_views_keep_original_roots_and_reintern_without_read_copy_growth() {
        let source = recursive_schema();
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        let view = live
            .intern_schema(&source, environment.clone(), &mut WorkLimit::new(4096))
            .unwrap();
        live.record_schema(1, Some(&source), environment.clone())
            .unwrap();
        let before = live.builder.as_ref().unwrap().checkpoint();
        let original = Some(TypeExprId(91));
        let (borrowed, captured) = live
            .view_schema(view, original, &mut WorkLimit::new(16))
            .unwrap();
        assert_eq!(borrowed.root_id(), view.ty);
        assert_eq!(borrowed.original(), original);
        assert_eq!(captured.id(), environment.id());
        for _ in 0..128 {
            let (read, _) = live
                .view_schema(view, original, &mut WorkLimit::new(16))
                .unwrap();
            let (binding, _) = live
                .binding_schema_if_known(1, original, &mut WorkLimit::new(16))
                .unwrap()
                .unwrap();
            assert_eq!(read.root_id(), view.ty);
            assert_eq!(binding.root_id(), view.ty);
            assert_eq!(binding.original(), original);
            assert_eq!(
                live.intern_schema(&read, environment.clone(), &mut WorkLimit::new(16))
                    .unwrap(),
                view
            );
        }
        assert_eq!(live.builder.as_ref().unwrap().checkpoint(), before);
        let extra =
            SourceSchema::scalar(SourceScalar::Str, None, &mut WorkLimit::new(4096)).unwrap();
        live.intern_schema(&extra, environment, &mut WorkLimit::new(4096))
            .unwrap();
        assert!(
            borrowed
                .equivalent(&source, &mut WorkLimit::new(4096))
                .unwrap()
        );
        let frozen = live.freeze();
        let (read, _) = frozen
            .view_schema(view, original, &mut WorkLimit::new(16))
            .unwrap();
        assert_eq!(read.root_id(), borrowed.root_id());
        assert_eq!(read.original(), original);
    }

    #[test]
    fn environment_only_registration_is_checked_shared_and_does_not_invent_a_type() {
        let mut live = LiveSourceTypes::default();
        let environment = FrozenEnvironment::default();
        assert_eq!(
            live.intern_environment(environment.clone(), &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert!(live.environments.is_empty());
        let mut work = WorkLimit::new(4096);
        let id = live
            .intern_environment(environment.clone(), &mut work)
            .unwrap();
        let used = 4096 - work.remaining();
        let mut exact = WorkLimit::new(used);
        let mut another = LiveSourceTypes::default();
        assert_eq!(
            another.intern_environment(environment.clone(), &mut exact),
            Ok(id)
        );
        assert_eq!(exact.remaining(), 0);
        assert_eq!(
            LiveSourceTypes::default()
                .intern_environment(environment.clone(), &mut WorkLimit::new(used - 1)),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert!(
            live.builder.is_none(),
            "an unknown Source stores its environment without fabricating a node"
        );
        assert_eq!(
            live.environment(id, &mut WorkLimit::new(16)).unwrap().id(),
            id
        );
        assert_eq!(
            live.environment(id, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
        let foreign = FrozenEnvironment::default().id();
        assert_eq!(
            live.environment(foreign, &mut WorkLimit::new(16)),
            Err(SourceTypesError::MissingNode)
        );
        let count = live.environments.len();
        assert_eq!(
            live.intern_environment(FrozenEnvironment::poisoned(), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
        assert_eq!(live.environments.len(), count);
        let frozen = live.freeze();
        assert_eq!(
            frozen
                .environment(id, &mut WorkLimit::new(16))
                .unwrap()
                .id(),
            id
        );
        assert_eq!(
            frozen.environment(foreign, &mut WorkLimit::new(16)),
            Err(SourceTypesError::MissingNode)
        );
        assert_eq!(
            frozen.environment(id, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
    }

    #[test]
    fn nonbinding_views_borrow_the_same_frozen_arena_and_retain_their_complete_core_roots() {
        let source = recursive_schema();
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        let view = live
            .intern_schema(&source, environment.clone(), &mut WorkLimit::new(4096))
            .unwrap();
        let index = live.freeze();
        assert_eq!(view.environment, environment.id());
        assert!(!index.contains_binding(0));
        let (schema, frozen) = index
            .view_schema(view, None, &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(frozen.id(), environment.id());
        assert_eq!(schema.key(), Err(SourceTypesError::RecursiveLegacyKey));
        assert!(
            schema
                .equivalent(&source, &mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(
            index
                .view_schema(view, None, &mut WorkLimit::new(0))
                .is_err()
        );
    }

    #[test]
    fn shared_imports_keep_frozen_environments_distinct() {
        let source = recursive_schema();
        let first_environment = FrozenEnvironment::default();
        let second_environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        let first = live
            .intern_schema(
                &source,
                first_environment.clone(),
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        let checkpoint = live.builder.as_ref().unwrap().checkpoint();
        let second = live
            .intern_schema(&source, second_environment.clone(), &mut WorkLimit::new(16))
            .unwrap();
        assert_eq!(live.builder.as_ref().unwrap().checkpoint(), checkpoint);
        assert_eq!(first.ty, second.ty);
        assert_ne!(first.environment, second.environment);
        let frozen = live.freeze();
        for (view, environment) in [(first, first_environment), (second, second_environment)] {
            let (schema, actual) = frozen
                .view_schema(view, None, &mut WorkLimit::new(16))
                .unwrap();
            assert_eq!(schema.root_id(), view.ty);
            assert_eq!(actual.id(), environment.id());
        }
    }

    #[test]
    fn intern_failure_keeps_old_roots_and_cannot_publish_an_environment_or_foreign_view() {
        let source = recursive_schema();
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        let view = live
            .intern_schema(&source, environment.clone(), &mut WorkLimit::new(4096))
            .unwrap();
        let checkpoint = live.builder.as_ref().unwrap().checkpoint();
        let unpublished = FrozenEnvironment::default();
        let uncopied = recursive_schema();
        assert_eq!(
            live.intern_schema(&uncopied, unpublished.clone(), &mut WorkLimit::new(20)),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert_eq!(live.builder.as_ref().unwrap().checkpoint(), checkpoint);
        assert!(!live.environments.contains_key(&unpublished.id()));
        assert_eq!(
            live.intern_schema(
                &source,
                FrozenEnvironment::poisoned(),
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::Unresolved)
        );
        let first = live.freeze();
        let mut another = LiveSourceTypes::default();
        let foreign = another
            .intern_schema(&source, environment, &mut WorkLimit::new(4096))
            .unwrap();
        assert!(matches!(
            first.view_schema(foreign, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::ForeignIdentity)
        ));
        let missing = SourceView {
            environment: unpublished.id(),
            ..view
        };
        assert!(matches!(
            first.view_schema(missing, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        first
            .view_schema(view, None, &mut WorkLimit::new(4096))
            .unwrap();
    }

    #[test]
    fn failed_header_ingress_cannot_create_an_unknown_binding_view() {
        let environment = FrozenEnvironment::default();
        let mut live = LiveSourceTypes::default();
        let invalid = ArgumentKey::Array {
            length: Some("not a resolved extent".into()),
            element: Box::new(ArgumentKey::Tuple(vec![])),
        };
        assert_eq!(
            SourceSchema::import(&invalid, None, &mut WorkLimit::new(4096)).unwrap_err(),
            SourceTypesError::Unresolved
        );
        live.record_schema(2, None, environment.clone()).unwrap();
        assert!(matches!(
            live.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        let frozen = live.freeze();
        assert!(matches!(
            frozen.binding_schema_if_known(1, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        ));
        assert!(!frozen.validate_binding_schema(1, None, environment.id()));
        assert!(frozen.validate_binding_schema(2, None, environment.id()));
        frozen.validate(&mut WorkLimit::new(4096)).unwrap();
    }

    #[test]
    fn failed_schema_copies_keep_the_old_arena_and_the_exact_admission_failure() {
        // Construct the deliberately oversized input, including bounded label
        // sorting. record_schema below still uses its unchanged ingress limit.
        let mut work = WorkLimit::new(1_000_000);
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
            environments: BTreeMap::from([(environment.id(), environment.clone())]),
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
        let schema = SourceSchema::import(&key, None, &mut WorkLimit::new(4096)).unwrap();
        first
            .record_schema(2, Some(&schema), environment.clone())
            .unwrap();
        let first = first.freeze();
        let mut second = LiveSourceTypes::default();
        let other_environment = FrozenEnvironment::default();
        second
            .record_schema(2, Some(&schema), other_environment.clone())
            .unwrap();
        let second = second.freeze();
        assert!(first.validate_binding_schema(2, Some(&schema), environment.id()));
        assert!(!first.validate_binding_schema(2, Some(&schema), other_environment.id()));
        assert_eq!(first.binding_view(2).unwrap().environment, environment.id());
        assert!(matches!(
            second.project(first.binding_type(2).unwrap(), &[]),
            Err(SourceTypesError::ForeignIdentity)
        ));
        let (source, _) = first
            .view_schema(
                first.binding_view(2).unwrap(),
                None,
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        let child = source
            .project_steps(&[SourcePath::Element], &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(
            child
                .array_parts(&mut WorkLimit::new(4096))
                .unwrap()
                .unwrap()
                .0,
            SourceLength::Fixed(2)
        );
        assert!(!SourceTypeIndex::default().validate_binding_schema(
            2,
            Some(&schema),
            environment.id()
        ));
    }
}
