//! Source receiving for actual fresh syntax. Unknown stored values remain
//! unresolved; a complete receiver cannot supply their missing coordinates.
use super::{
    context::FrozenEnvironment,
    source_reception::Construction,
    source_types::{SourceLength, SourcePath, SourceSchema, SourceTypesError as Error, WorkLimit},
};
use std::collections::BTreeMap;

#[derive(Debug)]
pub(crate) enum Literal<T> {
    Opaque,
    Array(Vec<T>),
    Tuple(Vec<T>),
    Map(Vec<(T, T)>),
    Record(BTreeMap<String, T>),
}

impl<T> Literal<T> {
    pub(crate) fn try_map<U, E>(
        self,
        mut map: impl FnMut(T) -> Result<U, E>,
    ) -> Result<Literal<U>, E> {
        Ok(match self {
            Self::Opaque => Literal::Opaque,
            Self::Array(items) => {
                Literal::Array(items.into_iter().map(map).collect::<Result<_, _>>()?)
            }
            Self::Tuple(items) => {
                Literal::Tuple(items.into_iter().map(map).collect::<Result<_, _>>()?)
            }
            Self::Map(items) => Literal::Map(
                items
                    .into_iter()
                    .map(|(key, value)| Ok((map(key)?, map(value)?)))
                    .collect::<Result<_, E>>()?,
            ),
            Self::Record(items) => Literal::Record(
                items
                    .into_iter()
                    .map(|(key, value)| Ok((key, map(value)?)))
                    .collect::<Result<_, E>>()?,
            ),
        })
    }
}

impl Literal<Construction> {
    fn construction(self) -> Construction {
        match self {
            Self::Opaque => Construction::Opaque,
            Self::Array(items) => Construction::Array(items),
            Self::Tuple(items) => Construction::Tuple(items),
            Self::Map(items) => Construction::Map(items),
            Self::Record(items) => Construction::Record(items),
        }
    }
}

pub(crate) fn hir_literal_plan(
    source: ril_compiler_core::ids::ExprId,
    hir: &crate::hir::nodes::HirProgram,
    work: &mut WorkLimit,
) -> Result<Literal<ril_compiler_core::ids::ExprId>, Error> {
    use crate::hir::nodes::{ExprKind as HirExpr, RecordMember as HirMember};
    work.charge(1)?;
    Ok(
        match &hir.expression(source).ok_or(Error::MissingNode)?.kind {
            HirExpr::Array(items) | HirExpr::Tuple(items) => {
                work.charge(items.len())?;
                if matches!(hir.expression(source).unwrap().kind, HirExpr::Array(_)) {
                    Literal::Array(items.clone())
                } else {
                    Literal::Tuple(items.clone())
                }
            }
            HirExpr::Map(items) => {
                work.charge(items.len().saturating_mul(2))?;
                Literal::Map(items.clone())
            }
            HirExpr::Record {
                ty: None, members, ..
            } => {
                work.charge(members.len())?;
                let mut fields = BTreeMap::new();
                for member in members {
                    let HirMember::Field { name, value, .. } = member else {
                        return Ok(Literal::Opaque);
                    };
                    work.text(name)?;
                    if fields.insert(name.clone(), *value).is_some() {
                        return Err(Error::DuplicateField);
                    }
                }
                Literal::Record(fields)
            }
            _ => Literal::Opaque,
        },
    )
}

pub(crate) fn hir_construction(
    source: ril_compiler_core::ids::ExprId,
    hir: &crate::hir::nodes::HirProgram,
    work: &mut WorkLimit,
    depth: usize,
) -> Result<Construction, Error> {
    use crate::hir::nodes::ExprKind as HirExpr;
    use ril_compiler_core::builtin_calls::NullaryConstructor;
    work.charge(1)?;
    if depth >= 64 {
        return Err(Error::BudgetExceeded);
    }
    let declaration = match &hir.expression(source).ok_or(Error::MissingNode)?.kind {
        HirExpr::Name(name) => {
            work.text(name)?;
            NullaryConstructor::lookup(name)
        }
        HirExpr::Path(path) => {
            work.charge(path.len())?;
            for part in path {
                work.text(part)?;
            }
            NullaryConstructor::lookup(&path.join("::"))
        }
        _ => None,
    };
    if let Some(declaration) = declaration {
        return Ok(Construction::Nullary {
            declaration,
            source,
        });
    }
    hir_literal_plan(source, hir, work)?
        .try_map(|child| hir_construction(child, hir, work, depth + 1))
        .map(Literal::construction)
}

pub(crate) struct Input {
    pub(crate) source: Option<(SourceSchema, FrozenEnvironment)>,
    pub(crate) fresh: Construction,
    pub(crate) literal: Literal<Input>,
}

pub(crate) fn receives(
    expected: &SourceSchema,
    environment: &FrozenEnvironment,
    input: &Input,
    work: &mut WorkLimit,
) -> Result<bool, Error> {
    if !expected.equivalent(expected, work)? {
        return Err(Error::InvalidEvidence(
            "contextual receiving has an inconsistent declaration graph".into(),
        ));
    }
    receive_at(expected, environment, input, work, 0)
}

fn receive_at(
    expected: &SourceSchema,
    environment: &FrozenEnvironment,
    input: &Input,
    work: &mut WorkLimit,
    depth: usize,
) -> Result<bool, Error> {
    work.charge(1)?;
    if depth >= 64 {
        return Err(Error::BudgetExceeded);
    }
    if environment.is_poisoned() {
        return Err(Error::Unresolved);
    }
    if let Some((actual, actual_environment)) = &input.source {
        if actual_environment.is_poisoned() {
            return Err(Error::Unresolved);
        }
        return expected.receive_schema_in(
            actual,
            environment,
            actual_environment,
            Some(&input.fresh),
            work,
        );
    }
    // No inferred runtime shape participates in this decision. Only the
    // original literal structure can establish contextual construction.
    match (&input.literal, &input.fresh) {
        (Literal::Array(items), Construction::Array(syntax)) if items.len() == syntax.len() => {
            let Some((length, element)) = expected.array_parts(work)? else {
                return Ok(false);
            };
            let count = u64::try_from(items.len()).map_err(|_| Error::IdentityExhausted)?;
            if !matches!(length, SourceLength::Dynamic) && length != SourceLength::Fixed(count) {
                return Ok(false);
            }
            for item in items {
                if !receive_at(&element, environment, item, work, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Literal::Tuple(items), Construction::Tuple(syntax)) if items.len() == syntax.len() => {
            let Some(elements) = expected.tuple_parts(work)? else {
                return Ok(false);
            };
            if elements.len() != items.len() {
                return Ok(false);
            }
            for (element, item) in elements.iter().zip(items) {
                if !receive_at(element, environment, item, work, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Literal::Map(items), Construction::Map(syntax)) if items.len() == syntax.len() => {
            let key = match expected.project_steps(&[SourcePath::MapKey], work) {
                Ok(key) => key,
                Err(Error::MissingProjection) => return Ok(false),
                Err(error) => return Err(error),
            };
            let value = expected.project_steps(&[SourcePath::MapValue], work)?;
            for (a, b) in items {
                if !receive_at(&key, environment, a, work, depth + 1)?
                    || !receive_at(&value, environment, b, work, depth + 1)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Literal::Record(items), Construction::Record(syntax))
            if items.keys().eq(syntax.keys()) =>
        {
            let Some((fields, row)) = expected.record_parts(work)? else {
                return Ok(false);
            };
            if row.is_some() {
                return Err(Error::Unresolved);
            }
            if fields.len() != items.len() {
                return Ok(false);
            }
            for (label, _, field) in fields {
                let Some(item) = items.get(&label) else {
                    return Ok(false);
                };
                if !receive_at(&field, environment, item, work, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Literal::Opaque, _) => Err(Error::Unresolved),
        _ => Err(Error::InvalidEvidence(
            "fresh construction differs from its actual child plan".into(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::{SourceBuilder, SourceNode, SourceScalar};

    fn empty() -> Input {
        Input {
            source: None,
            fresh: Construction::Array(vec![]),
            literal: Literal::Array(vec![]),
        }
    }

    #[test]
    fn open_callable_receiving_does_not_require_equal_rows_or_waive_scoped_types() {
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let unit = builder
            .insert(SourceNode::Scalar(SourceScalar::Unit), &mut work)
            .unwrap();
        let open = builder
            .insert(
                SourceNode::Callable {
                    parameters: vec![],
                    result: unit,
                    annotations: vec![],
                    row_identity: None,
                },
                &mut work,
            )
            .unwrap();
        let closed = builder
            .insert(
                SourceNode::Callable {
                    parameters: vec![],
                    result: unit,
                    annotations: vec!["&mut".into()],
                    row_identity: None,
                },
                &mut work,
            )
            .unwrap();
        let binder = builder
            .insert(SourceNode::Binder("decl:T".into()), &mut work)
            .unwrap();
        let graph = builder.freeze(&mut work).unwrap();
        let expected = SourceSchema::frozen_view(&graph, open, None, &mut work).unwrap();
        let actual = SourceSchema::frozen_view(&graph, closed, None, &mut work).unwrap();
        let left = FrozenEnvironment::default();
        let right = FrozenEnvironment::default();
        let input = Input {
            source: Some((actual.clone(), right.clone())),
            fresh: Construction::Opaque,
            literal: Literal::Opaque,
        };
        assert!(receives(&expected, &left, &input, &mut work).unwrap());
        assert!(
            !expected
                .equivalent_in(&actual, &left, &right, &mut work)
                .unwrap()
        );
        let scoped = SourceSchema::frozen_view(&graph, binder, None, &mut work).unwrap();
        let input = Input {
            source: Some((scoped.clone(), right)),
            fresh: Construction::Opaque,
            literal: Literal::Opaque,
        };
        assert!(receives(&scoped, &left, &input, &mut work).is_err());
    }

    #[test]
    fn nested_literal_constraints_preserve_stored_members_and_missing_inputs() {
        let environment = FrozenEnvironment::default();
        let mut work = WorkLimit::new(16384);
        let int = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        let inner = SourceSchema::array(SourceLength::Fixed(3), &int, None, &mut work).unwrap();
        let row = SourceSchema::array(SourceLength::Fixed(0), &inner, None, &mut work).unwrap();
        let matrix = SourceSchema::array(SourceLength::Fixed(2), &row, None, &mut work).unwrap();
        let mut input = Input {
            source: None,
            fresh: Construction::Array(vec![
                Construction::Array(vec![]),
                Construction::Array(vec![]),
            ]),
            literal: Literal::Array(vec![empty(), empty()]),
        };
        assert!(receives(&matrix, &environment, &input, &mut work).unwrap());
        let other = SourceSchema::array(SourceLength::Fixed(4), &int, None, &mut work).unwrap();
        let wrong = SourceSchema::array(SourceLength::Fixed(0), &other, None, &mut work).unwrap();
        let Literal::Array(items) = &mut input.literal else {
            panic!()
        };
        items[0] = Input {
            source: Some((wrong, environment.clone())),
            fresh: Construction::Opaque,
            literal: Literal::Opaque,
        };
        assert!(!receives(&matrix, &environment, &input, &mut work).unwrap());
        let missing = Input {
            source: None,
            fresh: Construction::Opaque,
            literal: Literal::Opaque,
        };
        assert!(receives(&matrix, &environment, &missing, &mut work).is_err());
        assert!(receives(&matrix, &environment, &input, &mut WorkLimit::new(0)).is_err());
        let mut builder = SourceBuilder::new().unwrap();
        let hole = builder
            .insert(
                SourceNode::Unresolved {
                    description: "missing element".into(),
                    arguments: vec![],
                },
                &mut work,
            )
            .unwrap();
        let root = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: hole,
                },
                &mut work,
            )
            .unwrap();
        let graph = builder.freeze(&mut work).unwrap();
        let poison = SourceSchema::frozen_view(&graph, root, None, &mut work).unwrap();
        assert!(
            receives(&poison, &environment, &empty(), &mut work).is_err(),
            "an empty construction cannot hide an incomplete receiver"
        );
    }
}
