use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use super::{Access, Coordinate, Input, Invocation, InvocationMode};

/// A root or member mode parameter in a callable's signature.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct ModeAxis {
    pub parameter: usize,
    pub path: Vec<Coordinate>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum ModeStep<A> {
    Axis(A),
    Fixed(Access),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum ModeExpression<A> {
    Input(Input),
    Axis(A),
    Projection(Vec<ModeStep<A>>),
    Unknown,
}

impl<A> ModeExpression<A> {
    pub(super) fn axes(&self) -> impl Iterator<Item = &A> {
        let (root, steps) = match self {
            Self::Axis(axis) => (Some(axis), &[][..]),
            Self::Projection(steps) => (None, steps.as_slice()),
            Self::Input(_) | Self::Unknown => (None, &[][..]),
        };
        root.into_iter()
            .chain(steps.iter().filter_map(|step| match step {
                ModeStep::Axis(axis) => Some(axis),
                ModeStep::Fixed(_) => None,
            }))
    }

    pub(super) fn select(&self, input: &impl Fn(&A) -> Option<Input>) -> Option<Input> {
        match self {
            Self::Input(mode) => Some(*mode),
            Self::Axis(axis) => input(axis),
            Self::Projection(steps) => {
                let access = steps.iter().try_fold(Access::Mut, |base, step| {
                    let member = match step {
                        ModeStep::Fixed(access) => *access,
                        ModeStep::Axis(axis) => input(axis)?.access(),
                    };
                    Some(base.project(member))
                })?;
                Input::from_mode(access.as_mode())
            }
            Self::Unknown => None,
        }
    }

    pub(super) fn substitute<B: Ord>(
        &self,
        axis: &impl Fn(&A) -> ModeExpression<B>,
    ) -> ModeExpression<B> {
        match self {
            Self::Input(mode) => ModeExpression::Input(*mode),
            Self::Axis(source) => axis(source),
            Self::Projection(steps) => {
                let mut projection = Vec::new();
                for step in steps {
                    match step {
                        ModeStep::Fixed(access) => projection.push(ModeStep::Fixed(*access)),
                        ModeStep::Axis(source) => match axis(source) {
                            ModeExpression::Input(mode) => {
                                projection.push(ModeStep::Fixed(mode.access()));
                            }
                            ModeExpression::Axis(axis) => projection.push(ModeStep::Axis(axis)),
                            ModeExpression::Projection(steps) => projection.extend(steps),
                            ModeExpression::Unknown => return ModeExpression::Unknown,
                        },
                    }
                }
                ModeExpression::projection(projection)
            }
            Self::Unknown => ModeExpression::Unknown,
        }
    }
}

impl<A: Ord> ModeExpression<A> {
    pub(super) fn projection(mut steps: Vec<ModeStep<A>>) -> Self {
        if steps.contains(&ModeStep::Fixed(Access::Immutable)) {
            return Self::Input(Input::Plain);
        }
        let Some(last) = steps.pop() else {
            return Self::Input(Input::Mut);
        };
        // Only the final member determines the writable mode. Earlier members
        // can cap it at ref or immutable. Canonicalizing those caps keeps
        // substitution finite even when a recursive call repeats a projection.
        steps.retain(|step| {
            *step != last && !matches!(step, ModeStep::Fixed(Access::Mut | Access::Shared))
        });
        steps.sort_unstable();
        steps.dedup();
        steps.push(last);
        let result = Self::Projection(steps);
        result.select(&|_| None).map_or(result, Self::Input)
    }
}

/// Mode offers made together in one invocation of a callback formal.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct CallbackModeCall {
    pub receiver: ModeAxis,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recursive_path: Option<Vec<Coordinate>>,
    pub arguments: Vec<(ModeAxis, ModeExpression<ModeAxis>)>,
}

impl CallbackModeCall {
    pub(super) fn specialize(&mut self, input: &impl Fn(&ModeAxis) -> Option<Input>) {
        for (_, mode) in &mut self.arguments {
            *mode = mode.substitute(&|axis| {
                input(axis)
                    .map_or_else(|| ModeExpression::Axis(axis.clone()), ModeExpression::Input)
            });
        }
    }

    pub(super) fn permits(&self, revision: &Self) -> bool {
        self.receiver == revision.receiver
            && self.recursive_path == revision.recursive_path
            && self.arguments.len() == revision.arguments.len()
            && self.arguments.iter().zip(&revision.arguments).all(
                |((axis, mode), (revised_axis, revised_mode))| {
                    axis == revised_axis
                        && (*mode == ModeExpression::Unknown || mode == revised_mode)
                },
            )
    }
}

/// Older interfaces store the marginal root offers. The possible calls are
/// their Cartesian product because the interface gives no correlation.
pub(super) fn legacy_mode_calls(invocations: &[Invocation]) -> Vec<CallbackModeCall> {
    let mut receivers = BTreeMap::<_, BTreeMap<_, Vec<_>>>::new();
    for invocation in invocations {
        receivers
            .entry(invocation.receiver)
            .or_default()
            .entry(invocation.parameter)
            .or_default()
            .push(invocation.mode);
    }
    let mut calls = Vec::new();
    for (receiver, arguments) in receivers {
        let mut combinations = vec![Vec::new()];
        for (parameter, modes) in arguments {
            combinations = combinations
                .into_iter()
                .flat_map(|prefix| {
                    modes.iter().map(move |mode| {
                        let mut arguments = prefix.clone();
                        let axis = ModeAxis {
                            parameter,
                            path: Vec::new(),
                        };
                        let mode = match mode {
                            InvocationMode::Input(input) => ModeExpression::Input(*input),
                            InvocationMode::Formal(parameter) => ModeExpression::Axis(ModeAxis {
                                parameter: *parameter,
                                path: Vec::new(),
                            }),
                        };
                        arguments.push((axis, mode));
                        arguments
                    })
                })
                .collect();
        }
        calls.extend(combinations.into_iter().map(|arguments| CallbackModeCall {
            receiver: ModeAxis {
                parameter: receiver,
                path: Vec::new(),
            },
            recursive_path: None,
            arguments,
        }));
    }
    calls.sort_unstable();
    calls.dedup();
    calls
}
