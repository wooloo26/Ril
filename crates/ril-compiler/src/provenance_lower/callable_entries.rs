use super::*;
use crate::sema::application_effect as a;

pub(super) fn callable_entry(
    entry: &a::CallableEntry,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::CallableEntry {
    p::CallableEntry {
        parent: entry.parent,
        caller_context: resumption_context(entry.caller_context),
        allocation_epoch: entry.allocation_epoch as u64,
        origin: entry_origin(&entry.origin),
        arguments: entry
            .arguments
            .iter()
            .map(|(mode, argument, span)| {
                (
                    parameter_mode(*mode),
                    value(types, contracts, argument, *span),
                )
            })
            .collect(),
    }
}

pub(super) fn entry_origin(origin: &a::EntryOrigin) -> p::EntryOrigin {
    match origin {
        a::EntryOrigin::Application(id) => p::EntryOrigin::Application(p::CopyCallEventId(id.0)),
        a::EntryOrigin::DeclarationProbe => p::EntryOrigin::DeclarationProbe,
        a::EntryOrigin::SignatureProbe => p::EntryOrigin::SignatureProbe,
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
