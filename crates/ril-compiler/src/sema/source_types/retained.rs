//! Export one finite immutable arena without reconstructing legacy trees.
//! Every edge is checked in its original snapshot before its ordinal is copied.
use super::*;
use ril_ir::provenance as p;
use ril_syntax::ast::ParameterMode;

pub(crate) struct RetainedSourceTypes {
    pub(crate) graph: p::SourceTypeGraph,
    /// Binding ordinals remain sorted as in the immutable declaration index.
    bindings: Vec<(usize, Option<p::SourceTypeId>)>,
}

impl RetainedSourceTypes {
    pub(crate) fn binding_root(
        &self,
        binding: usize,
        work: &mut WorkLimit,
    ) -> Result<Option<p::SourceTypeId>, SourceTypesError> {
        work.charge(1 + self.bindings.len().checked_ilog2().unwrap_or(0) as usize)?;
        self.bindings
            .binary_search_by_key(&binding, |(binding, _)| *binding)
            .map(|index| self.bindings[index].1)
            .map_err(|_| SourceTypesError::MissingNode)
    }
}

fn retained_id(
    types: &SourceTypes,
    id: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<p::SourceTypeId, SourceTypesError> {
    work.charge(1)?;
    types.get(id)?;
    Ok(p::SourceTypeId(id.index))
}

fn nominal(declaration: super::standard_data::Nominal) -> p::SourceNominal {
    use super::standard_data::Nominal as N;
    match declaration {
        N::ProcessInput => p::SourceNominal::ProcessInput,
        N::ProcessOutputMode => p::SourceNominal::ProcessOutputMode,
        N::ProcessExitStatus => p::SourceNominal::ProcessExitStatus,
        N::ProcessError => p::SourceNominal::ProcessError,
        N::IoErrorKind => p::SourceNominal::IoErrorKind,
    }
}

fn node(
    types: &SourceTypes,
    source: &SourceNode,
    work: &mut WorkLimit,
) -> Result<p::SourceTypeNode, SourceTypesError> {
    // This pays for vectors, text and fields before their allocation or clone.
    source.charge(work)?;
    let mut edge = |id| retained_id(types, id, work);
    Ok(match source {
        SourceNode::GenericBuiltin(id) => p::SourceTypeNode::GenericBuiltin(*id),
        SourceNode::Scalar(kind) => p::SourceTypeNode::Scalar(*kind),
        SourceNode::Nominal(id) => p::SourceTypeNode::Nominal(nominal(*id)),
        SourceNode::Binder(identity) => p::SourceTypeNode::Binder(identity.clone()),
        SourceNode::Array { length, element } => p::SourceTypeNode::Array {
            length: *length,
            element: edge(*element)?,
        },
        SourceNode::Map { key, value } => p::SourceTypeNode::Map {
            key: edge(*key)?,
            value: edge(*value)?,
        },
        SourceNode::Tuple(items) => {
            p::SourceTypeNode::Tuple(items.iter().map(|id| edge(*id)).collect::<Result<_, _>>()?)
        }
        SourceNode::Record { fields, row } => p::SourceTypeNode::Record {
            fields: fields
                .iter()
                .map(|field| {
                    Ok(p::SourceTypeField {
                        label: field.label.clone(),
                        mutable: field.mutable,
                        value: edge(field.value)?,
                    })
                })
                .collect::<Result<_, SourceTypesError>>()?,
            row: row.map(&mut edge).transpose()?,
        },
        SourceNode::Callable {
            parameters,
            result,
            annotations,
        } => p::SourceTypeNode::Callable {
            parameters: parameters
                .iter()
                .map(|(mode, id)| {
                    Ok((
                        match mode {
                            ParameterMode::Read => p::Access::Read,
                            ParameterMode::Mut => p::Access::Write,
                            ParameterMode::SharedMut => p::Access::Retain,
                        },
                        edge(*id)?,
                    ))
                })
                .collect::<Result<_, SourceTypesError>>()?,
            result: edge(*result)?,
            annotations: annotations.clone(),
        },
        SourceNode::Container { kind, arguments } => p::SourceTypeNode::Container {
            kind: *kind,
            arguments: arguments
                .iter()
                .map(|id| edge(*id))
                .collect::<Result<_, _>>()?,
        },
        SourceNode::Alias {
            declaration,
            target,
        } => p::SourceTypeNode::Alias {
            declaration: declaration.clone(),
            target: edge(*target)?,
        },
        SourceNode::OpaqueName { name, arguments } => p::SourceTypeNode::OpaqueName {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|id| edge(*id))
                .collect::<Result<_, _>>()?,
        },
        SourceNode::OpaqueComputation(key) => p::SourceTypeNode::OpaqueComputation(key.clone()),
        SourceNode::Unresolved {
            description,
            arguments,
        } => p::SourceTypeNode::Unresolved {
            description: description.clone(),
            arguments: arguments
                .iter()
                .map(|id| edge(*id))
                .collect::<Result<_, _>>()?,
        },
    })
}

impl SourceTypeIndex {
    pub(crate) fn retained(
        &self,
        work: &mut WorkLimit,
    ) -> Result<RetainedSourceTypes, SourceTypesError> {
        let types = self.retained_types()?;
        let bindings = self.retained_bindings();
        work.charge(bindings.len())?;
        let mut roots = Vec::with_capacity(bindings.len());
        for (binding, root, environment) in bindings {
            work.charge(1)?;
            let root = root.as_ref().copied().map_err(Clone::clone)?;
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            roots.push((
                binding,
                root.map(|id| retained_id(types, id, work)).transpose()?,
            ));
        }
        let nodes = types.indexed_nodes();
        work.charge(nodes.len())?;
        let mut retained = Vec::with_capacity(nodes.len());
        for (_, source) in nodes {
            retained.push(node(types, source, work)?);
        }
        Ok(RetainedSourceTypes {
            graph: p::SourceTypeGraph { nodes: retained },
            bindings: roots,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::context::FrozenEnvironment;

    fn index(builder: SourceBuilder, root: SourceTypeId) -> SourceTypeIndex {
        let mut work = WorkLimit::new(16384);
        let types = builder.freeze(&mut work).unwrap();
        let schema = SourceSchema::frozen_view(&types, root, None, &mut work).unwrap();
        let mut live = LiveSourceTypes::default();
        let environment = FrozenEnvironment::default();
        live.record_schema(7, Some(&schema), environment.clone())
            .unwrap();
        live.record_schema(9, None, environment).unwrap();
        live.freeze()
    }

    fn recursive() -> SourceTypeIndex {
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(16384);
        let root = builder.reserve(&mut work).unwrap();
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let inner = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
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
        let record = builder
            .insert(
                SourceNode::Record {
                    fields: vec![
                        SourceField {
                            label: "data".into(),
                            mutable: false,
                            value: outer,
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
        builder
            .define(
                root,
                SourceNode::Alias {
                    declaration: "declaration:Node".into(),
                    target: record,
                },
                &mut work,
            )
            .unwrap();
        index(builder, root)
    }

    #[test]
    fn core_retains_recursive_backedges_and_hidden_dimensions_without_legacy_keys() {
        let index = recursive();
        assert!(matches!(
            index.key(index.binding_type(7).unwrap()),
            Err(SourceTypesError::RecursiveLegacyKey)
        ));
        let mut work = WorkLimit::new(16384);
        let retained = index.retained(&mut work).unwrap();
        let root = retained.binding_root(7, &mut work).unwrap().unwrap();
        let p::SourceTypeNode::Alias {
            declaration,
            target,
        } = retained.graph.get(root).unwrap()
        else {
            panic!()
        };
        assert_eq!(declaration, "declaration:Node");
        let p::SourceTypeNode::Record { fields, row: None } = retained.graph.get(*target).unwrap()
        else {
            panic!()
        };
        assert_eq!(
            fields
                .iter()
                .find(|field| field.label == "next")
                .unwrap()
                .value,
            root
        );
        let data = fields
            .iter()
            .find(|field| field.label == "data")
            .unwrap()
            .value;
        let p::SourceTypeNode::Array {
            length: SourceLength::Fixed(0),
            element,
        } = retained.graph.get(data).unwrap()
        else {
            panic!()
        };
        assert!(matches!(
            retained.graph.get(*element),
            Some(p::SourceTypeNode::Array {
                length: SourceLength::Fixed(2),
                ..
            })
        ));
        assert_eq!(retained.graph.nodes.len(), 5);
    }

    #[test]
    fn opaque_and_unresolved_nodes_keep_their_identity_instead_of_becoming_missing_roots() {
        use ril_compiler_core::{builtin_calls::GenericBuiltin, builtin_types::AtomicBuiltinType};
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(16384);
        let binder = builder
            .insert(SourceNode::Binder("type:7:T".into()), &mut work)
            .unwrap();
        let generic = builder
            .insert(
                SourceNode::GenericBuiltin(GenericBuiltin::ArrayPush),
                &mut work,
            )
            .unwrap();
        let atomic = builder
            .insert(
                SourceNode::Scalar(SourceScalar::Intrinsic(AtomicBuiltinType::ReadPosition)),
                &mut work,
            )
            .unwrap();
        let nominal = builder
            .insert(
                SourceNode::Nominal(super::super::standard_data::Nominal::ProcessInput),
                &mut work,
            )
            .unwrap();
        let opaque = builder
            .insert(
                SourceNode::OpaqueName {
                    name: "Opaque".into(),
                    arguments: vec![binder],
                },
                &mut work,
            )
            .unwrap();
        let computation = builder
            .insert(
                SourceNode::OpaqueComputation("closed:type-computation".into()),
                &mut work,
            )
            .unwrap();
        let unresolved = builder
            .insert(
                SourceNode::Unresolved {
                    description: "missing declaration".into(),
                    arguments: vec![opaque],
                },
                &mut work,
            )
            .unwrap();
        let array = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Dynamic,
                    element: binder,
                },
                &mut work,
            )
            .unwrap();
        let map = builder
            .insert(
                SourceNode::Map {
                    key: atomic,
                    value: array,
                },
                &mut work,
            )
            .unwrap();
        let record = builder
            .insert(
                SourceNode::Record {
                    fields: vec![SourceField {
                        label: "value".into(),
                        mutable: true,
                        value: map,
                    }],
                    row: Some(binder),
                },
                &mut work,
            )
            .unwrap();
        let callable = builder
            .insert(
                SourceNode::Callable {
                    parameters: vec![
                        (ParameterMode::Read, binder),
                        (ParameterMode::Mut, map),
                        (ParameterMode::SharedMut, array),
                    ],
                    result: record,
                    annotations: vec!["@Read<type:7:T>".into(), "&capture".into()],
                },
                &mut work,
            )
            .unwrap();
        let result = builder
            .insert(
                SourceNode::Container {
                    kind: SourceContainer::Result,
                    arguments: vec![callable, nominal],
                },
                &mut work,
            )
            .unwrap();
        let root = builder
            .insert(
                SourceNode::Tuple(vec![generic, result, computation, unresolved]),
                &mut work,
            )
            .unwrap();
        let index = index(builder, root);
        let retained = index.retained(&mut work).unwrap();
        assert!(retained.binding_root(7, &mut work).unwrap().is_some());
        assert_eq!(retained.binding_root(9, &mut work), Ok(None));
        assert_eq!(
            retained.binding_root(999, &mut work),
            Err(SourceTypesError::MissingNode)
        );
        assert_eq!(
            retained.binding_root(7, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
        let nodes = &retained.graph.nodes;
        assert!(nodes.iter().any(|node| matches!(
            node,
            p::SourceTypeNode::GenericBuiltin(GenericBuiltin::ArrayPush)
        )));
        assert!(nodes.iter().any(|node| matches!(
            node,
            p::SourceTypeNode::Nominal(p::SourceNominal::ProcessInput)
        )));
        assert!(nodes.iter().any(
            |node| matches!(node, p::SourceTypeNode::Binder(identity) if identity == "type:7:T")
        ));
        assert!(nodes.iter().any(
            |node| matches!(node, p::SourceTypeNode::OpaqueName {name, ..} if name == "Opaque")
        ));
        assert!(nodes.iter().any(|node| matches!(node, p::SourceTypeNode::OpaqueComputation(text) if text == "closed:type-computation")));
        assert!(nodes.iter().any(|node| matches!(node, p::SourceTypeNode::Unresolved {description, ..} if description == "missing declaration")));
        assert!(nodes.iter().any(|node| matches!(node, p::SourceTypeNode::Callable {parameters, annotations, ..}
            if parameters.iter().map(|(mode,_)| *mode).collect::<Vec<_>>() == [p::Access::Read,p::Access::Write,p::Access::Retain]
                && annotations == &["@Read<type:7:T>", "&capture"])));
        assert!(nodes.iter().any(|node| matches!(node, p::SourceTypeNode::Record {fields, row:Some(_)} if fields[0].mutable)));
    }

    #[test]
    fn retention_budget_or_poison_never_turns_a_known_root_into_unknown() {
        let index = recursive();
        let mut work = WorkLimit::new(16384);
        let expected = index.retained(&mut work).unwrap();
        let used = 16384 - work.remaining();
        for budget in 0..used {
            assert!(
                matches!(
                    index.retained(&mut WorkLimit::new(budget)),
                    Err(SourceTypesError::BudgetExceeded)
                ),
                "budget {budget}"
            );
        }
        assert_eq!(
            index.retained(&mut WorkLimit::new(used)).unwrap().graph,
            expected.graph
        );
        let mut poisoned = LiveSourceTypes::default();
        assert_eq!(
            poisoned.record_schema(1, None, FrozenEnvironment::poisoned()),
            Err(SourceTypesError::Unresolved)
        );
        assert!(matches!(
            poisoned.freeze().retained(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
        let mut other = SourceBuilder::new().unwrap();
        let foreign = other
            .insert(
                SourceNode::Scalar(SourceScalar::Bool),
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        assert_eq!(
            retained_id(
                index.retained_types().unwrap(),
                foreign,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::ForeignIdentity)
        );
    }
}
