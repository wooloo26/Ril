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
    ty: Option<SourceTypeId>,
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
    pub fn binding_type(&self, binding: usize) -> Option<SourceTypeId> {
        self.0.bindings.get(&binding)?.ty
    }
    pub fn binding_view(&self, binding: usize) -> Option<SourceView> {
        let view = self.0.bindings.get(&binding)?;
        (!view.environment.is_poisoned()).then_some(SourceView {
            ty: view.ty?,
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
    pub(crate) fn projected_binding_key(
        &self,
        binding: usize,
        path: &[Slot],
        hir: Option<&crate::hir::nodes::HirProgram>,
    ) -> Result<ArgumentKey, SourceTypesError> {
        let id = self
            .binding_type(binding)
            .ok_or(SourceTypesError::Unresolved)?;
        let types = self.0.types.as_ref().map_err(Clone::clone)?;
        projected_key(types, id, path, hir, &mut WorkLimit::new(12288))
    }
    pub(crate) fn validate_binding(
        &self,
        binding: usize,
        original: Option<&ArgumentKey>,
        environment: FrozenEnvId,
    ) -> bool {
        if self.0.bindings.get(&binding).is_none_or(|view| {
            view.environment.id() != environment || view.environment.is_poisoned()
        }) {
            return false;
        }
        match (self.binding_type(binding), original) {
            (None, None) => true,
            (Some(id), Some(original)) => {
                let check = || -> Result<bool, SourceTypesError> {
                    let types = self.0.types.as_ref().map_err(Clone::clone)?;
                    let mut work = WorkLimit::new(4096);
                    let mut original_types = SourceBuilder::new()?;
                    let original = original_types.import_key(original, &mut work)?;
                    super::reception::equivalent(types, id, &original_types, original, &mut work)
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
                ty: result.as_ref().copied().unwrap_or(None),
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
            .and_then(|view| view.ty)
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

pub(super) fn steps_in(
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
        assert!(first.validate_binding(2, Some(&key), environment.id()));
        assert!(!first.validate_binding(2, Some(&key), other_environment.id()));
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
        assert!(!SourceTypeIndex::default().validate_binding(2, Some(&key), environment.id()));
    }
}
