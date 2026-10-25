//! The single ingress for already certified Const arguments of a nominal.
//! Neither a spelling nor an arbitrary legacy Closed key establishes Const.
use super::*;
use crate::sema::effect_identity::ArgumentKey;

impl SourceSchema {
    /// The caller must independently authenticate the original nominal, its
    /// all-Const parameter sorts and ordinary static normalization of every
    /// argument. Values remain uninterpreted canonical identities here.
    pub(crate) fn certified_const_nominal(
        name: &str,
        arguments: &[ArgumentKey],
        declaration: Option<ril_compiler_core::ids::StmtId>,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1 + arguments.len())?;
        work.text(name)?;
        if name.is_empty() {
            return Err(SourceTypesError::Unresolved);
        }
        let mut builder = SourceBuilder::new()?;
        let mut coordinates = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let ArgumentKey::Closed(value) = argument else {
                return Err(SourceTypesError::Unresolved);
            };
            work.text(value)?;
            coordinates.push(builder.insert(SourceNode::StaticValue(value.clone()), work)?);
        }
        let root = builder.insert(
            SourceNode::OpaqueName {
                declaration: declaration.map(super::graph::NominalDeclaration::Hir),
                name: name.to_owned(),
                arguments: coordinates,
            },
            work,
        )?;
        let types = builder.freeze(work)?;
        super::super::reception::complete(&types, root, work)?;
        Ok(Self {
            types,
            root,
            original,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::context::FrozenEnvironment;
    use ril_compiler_core::source::{FileId, Span};

    fn nominal(value: &str, work: &mut WorkLimit) -> Result<SourceSchema, SourceTypesError> {
        SourceSchema::certified_const_nominal(
            "Token",
            &[ArgumentKey::Closed(value.into())],
            Some(ril_compiler_core::ids::StmtId(9)),
            Some(TypeExprId(7)),
            work,
        )
    }

    #[test]
    fn certified_nominal_coordinates_receive_and_compare_by_exact_value() {
        let mut work = WorkLimit::new(4096);
        let first = nominal("const(int:1)", &mut work).unwrap();
        let same = nominal("const(int:1)", &mut work).unwrap();
        let other = nominal("const(int:2)", &mut work).unwrap();
        assert!(first.equivalent(&same, &mut work).unwrap());
        assert!(first.receive_schema(&same, None, &mut work).unwrap());
        assert!(!first.equivalent(&other, &mut work).unwrap());
        assert!(!first.receive_schema(&other, None, &mut work).unwrap());
        assert_eq!(first.original(), Some(TypeExprId(7)));
        assert_eq!(
            first.key().unwrap(),
            ArgumentKey::Name {
                name: "Token".into(),
                arguments: vec![ArgumentKey::Closed("const(int:1)".into())],
            }
        );
        let mut destination = SourceBuilder::new().unwrap();
        let root = first.copy_into(&mut destination, &mut work).unwrap();
        let copied = SourceSchema::frozen_view(
            &destination.freeze(&mut work).unwrap(),
            root,
            first.original,
            &mut work,
        )
        .unwrap();
        assert_ne!(first.root_id(), copied.root_id());
        assert!(first.equivalent(&copied, &mut work).unwrap());
    }

    #[test]
    fn ordinary_closed_ingress_does_not_certify_a_const_coordinate() {
        let mut work = WorkLimit::new(4096);
        let first = nominal("const(int:1)", &mut work).unwrap();
        let opaque = SourceSchema::import(&first.key().unwrap(), None, &mut work).unwrap();
        assert!(matches!(
            first.equivalent(&opaque, &mut work),
            Err(SourceTypesError::Unresolved)
        ));
        let arbitrary =
            SourceSchema::import(&ArgumentKey::Closed("const(int:1)".into()), None, &mut work)
                .unwrap();
        assert!(matches!(
            arbitrary.receive_schema(&arbitrary, None, &mut work),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(matches!(
            SourceSchema::certified_const_nominal(
                "Token",
                &[ArgumentKey::Tuple(vec![])],
                None,
                None,
                &mut work
            ),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn const_coordinates_cannot_be_used_as_types_or_synthetic_runtime_values() {
        let mut work = WorkLimit::new(4096);
        let first = nominal("const(int:1)", &mut work).unwrap();
        let SourceNode::OpaqueName { arguments, .. } = first.types.get(first.root).unwrap() else {
            panic!("expected the declared nominal instance")
        };
        let coordinate =
            SourceSchema::frozen_view(&first.types, arguments[0], None, &mut work).unwrap();
        assert!(matches!(
            coordinate.equivalent(&coordinate, &mut work),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(matches!(
            coordinate.sensitivity(&mut work),
            SourceSensitivity::Unknown {
                reason: SourceTypesError::Unresolved
            }
        ));
        assert!(matches!(
            super::super::super::builtins::erased_type(
                &coordinate.types,
                coordinate.root,
                &mut work
            ),
            Err(SourceTypesError::Unresolved)
        ));
        assert!(matches!(
            first.syntax_projection(
                Span {
                    file: FileId(0),
                    start: 0,
                    end: 0,
                },
                &mut work,
                &mut |_, _, _| panic!("a Const coordinate is not a Type binder"),
            ),
            Err(SourceTypesError::Unresolved)
        ));
        let invalid_array =
            SourceSchema::array(SourceLength::Dynamic, &coordinate, None, &mut work).unwrap();
        assert!(matches!(
            invalid_array.equivalent(&invalid_array, &mut work),
            Err(SourceTypesError::Unresolved)
        ));
        // Visit the valid nominal argument before the very same node in a
        // Type position. Reachability caching must retain the edge's role.
        let shared =
            SourceSchema::tuple(&[coordinate.clone(), first.clone()], None, &mut work).unwrap();
        assert!(matches!(
            shared.equivalent(&shared, &mut work),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn canonical_const_coordinates_survive_retention_and_respect_work_limits() {
        assert!(matches!(
            nominal("const(int:1)", &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            nominal(&"value".repeat(64), &mut WorkLimit::new(3)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut work = WorkLimit::new(4096);
        let first = nominal("const(int:1)", &mut work).unwrap();
        assert!(matches!(
            first.equivalent(&first, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut live = LiveSourceTypes::default();
        live.record_schema(0, Some(&first), FrozenEnvironment::default())
            .unwrap();
    }
}
