//! Structural standard interfaces instantiated with their actual argument
//! nodes. These operations never reify a type tree or inspect runtime values.
use super::{
    SourceBuilder, SourceContainer, SourceField, SourceNode, SourceScalar, SourceTypeId,
    SourceTypesError, WorkLimit, standard_data,
};
use ril_syntax::ast::ParameterMode;

pub(super) fn instantiate(
    name: &str,
    arguments: &[SourceTypeId],
    builder: &mut SourceBuilder,
    work: &mut WorkLimit,
) -> Result<Option<SourceTypeId>, SourceTypesError> {
    work.charge(1 + arguments.len())?;
    work.text(name)?;
    let fields = match (name, arguments) {
        ("Io::ReadOps" | "Io::WriteOps", [receiver]) => {
            let read = name == "Io::ReadOps";
            let input = builder.insert(
                SourceNode::Scalar(if read {
                    SourceScalar::Int
                } else {
                    SourceScalar::Bytes
                }),
                work,
            )?;
            let result = if read {
                let chunk = standard_data::READ_CHUNK.insert(builder, work)?;
                let error = standard_data::IO_ERROR.insert(builder, work)?;
                work.charge(2)?;
                builder.insert(
                    SourceNode::Container {
                        kind: SourceContainer::Result,
                        arguments: vec![chunk, error],
                    },
                    work,
                )?
            } else {
                standard_data::WRITE_PROGRESS.insert(builder, work)?
            };
            work.charge(3)?;
            work.text("&mut")?;
            let callable = builder.insert(
                SourceNode::Callable {
                    parameters: vec![
                        (ParameterMode::Mut, *receiver),
                        (ParameterMode::Read, input),
                    ],
                    result,
                    annotations: vec!["&mut".into()],
                    row_identity: None,
                },
                work,
            )?;
            let label = if read { "read" } else { "write" };
            work.text(label)?;
            vec![SourceField {
                label: label.into(),
                mutable: false,
                value: callable,
            }]
        }
        ("Iter::Source", [state, item]) => {
            work.charge(3)?;
            work.text("Iter::Step")?;
            let result = builder.insert(
                SourceNode::OpaqueName {
                    declaration: Some(super::graph::NominalDeclaration::Intrinsic(
                        super::graph::IntrinsicNominal::Step,
                    )),
                    name: "Iter::Step".into(),
                    arguments: vec![*state, *item],
                },
                work,
            )?;
            let callable = builder.insert(
                SourceNode::Callable {
                    parameters: vec![(ParameterMode::Read, *state)],
                    result,
                    annotations: Vec::new(),
                    row_identity: None,
                },
                work,
            )?;
            work.text("step")?;
            vec![SourceField {
                label: "step".into(),
                mutable: false,
                value: callable,
            }]
        }
        ("Iter::Cursor", [state]) => {
            work.charge(2)?;
            work.text("state")?;
            work.text("ended")?;
            let ended = builder.insert(SourceNode::Scalar(SourceScalar::Bool), work)?;
            vec![
                SourceField {
                    label: "state".into(),
                    mutable: true,
                    value: *state,
                },
                SourceField {
                    label: "ended".into(),
                    mutable: true,
                    value: ended,
                },
            ]
        }
        ("Io::ReadOps" | "Io::WriteOps" | "Iter::Source" | "Iter::Cursor", _) => {
            return Err(SourceTypesError::Unresolved);
        }
        _ => return Ok(None),
    };
    builder
        .insert(SourceNode::Record { fields, row: None }, work)
        .map(Some)
}
