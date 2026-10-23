use super::*;
use crate::sema::application_effect as a;

pub(super) fn callable_entry(
    entry: &a::CallableEntry,
    span: Span,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> Result<p::CallableEntry, NotImplemented> {
    contracts.source_query(|_, work| {
        work.charge(1 + entry.arguments.len())?;
        if entry
            .callee
            .as_ref()
            .is_some_and(|callee| callee.current_epoch() != entry.allocation_epoch)
            || entry
                .arguments
                .iter()
                .any(|argument| argument.packet.current_epoch() != entry.allocation_epoch)
        {
            return Err(crate::sema::source_types::SourceTypesError::Unresolved);
        }
        Ok(())
    })?;
    admit_entry_origin(&entry.origin, types, contracts)?;
    Ok(p::CallableEntry {
        parent: entry.parent,
        caller_context: resumption_context(entry.caller_context),
        allocation_epoch: entry.allocation_epoch as u64,
        callee: entry
            .callee
            .as_ref()
            .map(|callee| contracts.packet(types, callee, span))
            .transpose()?,
        origin: entry_origin(&entry.origin, types, contracts),
        arguments: std::sync::Arc::new(
            entry
                .arguments
                .iter()
                .map(|argument| {
                    if argument.heap.is_some() {
                        contracts
                            .source_query(|_, work| argument.snapshot_view(work).map(|_| ()))?;
                    }
                    Ok(p::EntryArgument {
                        mode: parameter_mode(argument.mode),
                        packet: contracts.packet(types, &argument.packet, argument.span)?,
                        span: argument.span,
                        heap: argument
                            .heap
                            .as_ref()
                            .map(|heap| contracts.packet_heap(types, heap, argument.span))
                            .transpose()?,
                    })
                })
                .collect::<Result<_, NotImplemented>>()?,
        ),
    })
}

fn admit_entry_origin(
    origin: &a::EntryOrigin,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> Result<(), NotImplemented> {
    use ril_compiler_core::projection::TypeProjection;
    contracts.source_query(|_, work| {
        work.charge(1)?;
        match origin {
            a::EntryOrigin::Generated { inputs, .. } => work.charge(inputs.len())?,
            a::EntryOrigin::SignatureProbe(source) => {
                work.charge(source.path.len() + source.formals.len())?;
                for step in source.path.iter() {
                    match step {
                        TypeProjection::Field(name) => work.text(name)?,
                        TypeProjection::RecordRemainder(names) => {
                            work.charge(names.len())?;
                            for name in names {
                                work.text(name)?;
                            }
                        }
                        _ => {}
                    }
                }
            }
            a::EntryOrigin::Application(_)
            | a::EntryOrigin::DeclarationProbe
            | a::EntryOrigin::Unresolved => {}
        }
        Ok(())
    })?;
    if let a::EntryOrigin::SignatureProbe(source) = origin {
        contracts.retained_packet_environment(types, &source.environment)?;
    }
    Ok(())
}

pub(super) fn entry_origin(
    origin: &a::EntryOrigin,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::EntryOrigin {
    match origin {
        a::EntryOrigin::Application(id) => p::EntryOrigin::Application(p::CopyCallEventId(id.0)),
        a::EntryOrigin::DeclarationProbe => p::EntryOrigin::DeclarationProbe,
        a::EntryOrigin::SignatureProbe(source) => {
            p::EntryOrigin::SignatureProbe(p::SignatureProbeSource {
                source: source.source,
                path: source.path.as_ref().clone(),
                environment: contracts.environment(types, &source.environment),
                formals: source
                    .formals
                    .iter()
                    .map(|formal| p::SignatureFormal {
                        slot: formal.slot,
                        binding: formal.binding as u32,
                    })
                    .collect(),
            })
        }
        a::EntryOrigin::Unresolved => p::EntryOrigin::Unresolved,
        a::EntryOrigin::Generated {
            anchor,
            callee,
            inputs,
        } => p::EntryOrigin::Generated {
            anchor: *anchor,
            callee: *callee,
            inputs: inputs
                .iter()
                .map(|input| match input {
                    a::InputOrigin::Scope(boundary) => p::InputOrigin::Scope(*boundary),
                    a::InputOrigin::Observed(id) => p::InputOrigin::Observed(*id),
                    a::InputOrigin::Widened(id) => p::InputOrigin::Widened(*id),
                    a::InputOrigin::Scalar(a::ScalarInput::PositiveInt) => {
                        p::InputOrigin::Scalar(p::ScalarInput::PositiveInt)
                    }
                    a::InputOrigin::Scalar(a::ScalarInput::ByteSuffix(id)) => {
                        p::InputOrigin::Scalar(p::ScalarInput::ByteSuffix(*id))
                    }
                    a::InputOrigin::Scalar(a::ScalarInput::BufferedBytes(id)) => {
                        p::InputOrigin::Scalar(p::ScalarInput::BufferedBytes(*id))
                    }
                    a::InputOrigin::Copied {
                        observation,
                        boundary,
                    } => p::InputOrigin::Copied {
                        observation: *observation,
                        boundary: p::CopyBoundaryId(boundary.0),
                    },
                })
                .collect(),
        },
    }
}
