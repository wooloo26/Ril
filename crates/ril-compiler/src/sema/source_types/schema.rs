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
