//! Snapshot-owned storage view index. An ID is a cache of coordinates whose
//! original binding/declaration/occurrence must still be independently checked.
use super::*;
use crate::sema::{effect_identity::ArgumentKey, facts::Slot};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone)]
pub struct SourceTypeIndex(Arc<IndexData>);

#[derive(Debug)]
struct IndexData {
    types: Result<SourceTypes, SourceTypesError>,
    bindings: BTreeMap<usize, Option<SourceTypeId>>,
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
        self.0.bindings.get(&binding).copied().flatten()
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
    ) -> Result<ArgumentKey, SourceTypesError> {
        let id = self
            .binding_type(binding)
            .ok_or(SourceTypesError::Unresolved)?;
        let steps = steps(path)?;
        self.key(self.project(id, &steps)?)
    }
    pub(crate) fn validate_binding(&self, binding: usize, original: Option<&ArgumentKey>) -> bool {
        if !self.contains_binding(binding) {
            return false;
        }
        match (self.binding_type(binding), original) {
            (None, None) => true,
            (Some(id), Some(original)) => self.key(id).is_ok_and(|stored| stored == *original),
            _ => false,
        }
    }
}

#[derive(Default)]
pub(crate) struct LiveSourceTypes {
    builder: Option<SourceBuilder>,
    bindings: BTreeMap<usize, Option<SourceTypeId>>,
}

impl LiveSourceTypes {
    pub(crate) fn record(
        &mut self,
        binding: usize,
        key: Option<&ArgumentKey>,
    ) -> Result<(), SourceTypesError> {
        if self.bindings.contains_key(&binding) {
            return Err(SourceTypesError::AlreadyDefined);
        }
        let result = (|| {
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
        self.bindings
            .insert(binding, result.as_ref().copied().unwrap_or(None));
        result.map(|_| ())
    }
    pub(crate) fn projected_binding_key(
        &self,
        binding: usize,
        path: &[Slot],
    ) -> Result<ArgumentKey, SourceTypesError> {
        let id = self
            .bindings
            .get(&binding)
            .copied()
            .flatten()
            .ok_or(SourceTypesError::Unresolved)?;
        let builder = self.builder.as_ref().ok_or(SourceTypesError::MissingNode)?;
        let mut work = WorkLimit::new(4096);
        let selected = builder.project(id, &steps(path)?, &mut work)?;
        builder.legacy_key(selected, &mut work)
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

fn steps(path: &[Slot]) -> Result<Vec<SourcePath>, SourceTypesError> {
    let mut work = WorkLimit::new(4096);
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
        first.record(2, Some(&key)).unwrap();
        let first = first.freeze();
        let mut second = LiveSourceTypes::default();
        second.record(2, Some(&key)).unwrap();
        let second = second.freeze();
        assert!(first.validate_binding(2, Some(&key)));
        assert!(matches!(
            second.key(first.binding_type(2).unwrap()),
            Err(SourceTypesError::ForeignIdentity)
        ));
        let child = first.projected_binding_key(2, &[Slot::AnyIndex]).unwrap();
        assert!(
            matches!(child, ArgumentKey::Array { length: Some(length), .. } if length == "const(int:2)")
        );
        assert!(!SourceTypeIndex::default().validate_binding(2, Some(&key)));
    }
}
