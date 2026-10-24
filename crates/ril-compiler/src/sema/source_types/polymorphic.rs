//! Polymorphic primitive Source declarations. Variables are scoped by the
//! declaration identity and their ordinal. Selecting a variable retains a full
//! Source graph node; neither erased Ty nor a receiver's contents participate.
use super::*;
use ril_compiler_core::builtin_calls::GenericBuiltin;
use ril_syntax::ast::ParameterMode;
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
enum Pattern {
    Variable(u8),
    Array(&'static Pattern),
    Map(&'static Pattern, &'static Pattern),
    Integer,
}

#[derive(Clone, Copy)]
enum Mode {
    Exact(ParameterMode),
    Stored,
}

struct Declaration {
    parameters: &'static [(&'static str, Mode, Pattern)],
    written_formals: &'static [u32],
}

const T: Pattern = Pattern::Variable(0);
const V: Pattern = Pattern::Variable(1);
use Mode::{Exact, Stored};
use ParameterMode::{Mut, Read, SharedMut};
use Pattern::{Array, Integer, Map};

fn declaration(id: GenericBuiltin) -> Declaration {
    Declaration {
        written_formals: &[0],
        parameters: match id {
            GenericBuiltin::ArrayPush => &[("items", Exact(Mut), Array(&T)), ("value", Stored, T)],
            GenericBuiltin::ArrayInsert => &[
                ("items", Exact(Mut), Array(&T)),
                ("index", Exact(Read), Integer),
                ("value", Stored, T),
            ],
            GenericBuiltin::ArrayTruncate => &[
                ("items", Exact(Mut), Array(&T)),
                ("length", Exact(Read), Integer),
            ],
            GenericBuiltin::MapSet => &[
                ("items", Exact(Mut), Map(&T, &V)),
                ("key", Exact(Read), T),
                ("value", Stored, V),
            ],
        },
    }
}

pub(crate) fn parameter_labels(id: GenericBuiltin) -> Vec<Option<&'static str>> {
    declaration(id)
        .parameters
        .iter()
        .map(|(name, _, _)| Some(*name))
        .collect()
}

fn variable_path(pattern: Pattern, variable: u8, path: &mut Vec<SourcePath>) -> bool {
    match pattern {
        Pattern::Variable(actual) => actual == variable,
        Array(element) => {
            path.push(SourcePath::Element);
            if variable_path(*element, variable, path) {
                return true;
            }
            path.pop();
            false
        }
        Map(key, value) => {
            for (child, step) in [(*key, SourcePath::MapKey), (*value, SourcePath::MapValue)] {
                path.push(step);
                if variable_path(child, variable, path) {
                    return true;
                }
                path.pop();
            }
            false
        }
        Integer => false,
    }
}

/// Numeric context is a scalar projection of the original receiver Source.
/// Fixed index/length parameters need no receiver. No collection contents or
/// current lexical binding are used to reconstruct a prior operand.
pub(crate) fn numeric_parameters_schema(
    id: GenericBuiltin,
    receiver: Option<&SourceSchema>,
    work: &mut WorkLimit,
) -> Result<Vec<Option<SourceScalar>>, SourceTypesError> {
    let declaration = declaration(id);
    work.charge(declaration.parameters.len())?;
    declaration
        .parameters
        .iter()
        .map(|(_, _, pattern)| {
            work.charge(1)?;
            if matches!(pattern, Integer) {
                return Ok(Some(SourceScalar::Int));
            }
            let (Pattern::Variable(variable), Some(source)) = (pattern, receiver) else {
                return Ok(None);
            };
            let (types, root) = source.graph();
            let mut path = Vec::new();
            if !variable_path(declaration.parameters[0].2, *variable, &mut path) {
                return Ok(None);
            }
            let target = types.project(root, &path, work)?;
            let target = types.unalias(target, work)?;
            let node = types.get(target)?;
            node.charge(work)?;
            Ok(match node {
                SourceNode::Scalar(kind)
                    if !matches!(
                        kind,
                        SourceScalar::Unit
                            | SourceScalar::Bool
                            | SourceScalar::Str
                            | SourceScalar::Bytes
                            | SourceScalar::Never
                            | SourceScalar::Intrinsic(_)
                    ) =>
                {
                    Some(*kind)
                }
                _ => None,
            })
        })
        .collect()
}

/// The latent requirement of the selected declaration alternative. These are
/// primitive contract requirements, not invented runtime accesses or loans.
pub(crate) struct Instance {
    pub(crate) parameter_write: bool,
    pub(crate) retention: bool,
}

pub(crate) fn written_formals(id: GenericBuiltin) -> &'static [u32] {
    declaration(id).written_formals
}

impl Instance {}

fn select(
    graph: &impl SourceTypeQueries,
    pattern: Pattern,
    actual: SourceTypeId,
    selected: &mut BTreeMap<u8, SourceTypeId>,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    work.charge(1)?;
    let actual = graph.unalias(actual, work)?;
    Ok(match pattern {
        Pattern::Variable(variable) => match selected.get(&variable) {
            Some(original) => reception::equivalent_in(graph, *original, actual, work)?,
            None => {
                selected.insert(variable, actual);
                true
            }
        },
        Array(element) => match graph.get(actual)? {
            SourceNode::Array {
                length: SourceLength::Dynamic,
                element: actual,
            } => select(graph, *element, *actual, selected, work)?,
            _ => false,
        },
        Map(key, value) => match graph.get(actual)? {
            SourceNode::Map {
                key: actual_key,
                value: actual_value,
            } => {
                select(graph, *key, *actual_key, selected, work)?
                    && select(graph, *value, *actual_value, selected, work)?
            }
            _ => false,
        },
        Integer => matches!(graph.get(actual)?, SourceNode::Scalar(SourceScalar::Int)),
    })
}

pub(crate) fn instantiate(
    graph: &impl SourceTypeQueries,
    id: GenericBuiltin,
    target: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<Option<Instance>, SourceTypesError> {
    work.charge(1)?;
    let target = graph.unalias(target, work)?;
    let SourceNode::Callable {
        parameters, result, ..
    } = graph.get(target)?
    else {
        return Ok(None);
    };
    let declaration = declaration(id);
    if parameters.len() != declaration.parameters.len()
        || !matches!(
            graph.get(graph.unalias(*result, work)?)?,
            SourceNode::Scalar(SourceScalar::Unit)
        )
    {
        return Ok(None);
    }
    let mut selected = BTreeMap::new();
    let mut retention = false;
    for ((mode, actual), (_, required, pattern)) in parameters.iter().zip(declaration.parameters) {
        work.charge(1)?;
        let mode_valid = match required {
            Exact(required) => mode == required,
            Stored => {
                retention |= *mode == SharedMut;
                matches!(mode, Read | SharedMut)
            }
        };
        if !mode_valid || !select(graph, *pattern, *actual, &mut selected, work)? {
            return Ok(None);
        }
    }
    Ok(Some(Instance {
        parameter_write: !declaration.written_formals.is_empty(),
        retention,
    }))
}
