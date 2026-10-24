//! Read-only receiving bindings and type-arena snapshots. The owning analyzer
//! checks their references when it completes the type store.
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
    #[cfg(test)]
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

    #[cfg(test)]
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
}
