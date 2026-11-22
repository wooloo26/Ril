use std::collections::{BTreeMap, BTreeSet, VecDeque};

use ril_base::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_frontend::syntax::Mode;

use super::{Analyzer, Context, Datum, Fact, Input, Obligation, Rule};
use crate::{
    access::{Invocation as PublishedInvocation, InvocationMode},
    ty::{Callable, Ty},
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Offer {
    Input(Input),
    Formal(Span),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Invocation {
    receiver: Span,
    position: usize,
    offer: Offer,
}

struct Argument {
    offers: BTreeSet<Offer>,
    targets: BTreeSet<Span>,
    dependencies: BTreeSet<Span>,
    existing: BTreeSet<Span>,
    span: Span,
}

struct Call {
    owner: Span,
    arguments: BTreeMap<Span, Argument>,
}

#[derive(Default)]
pub(super) struct Calls {
    calls: BTreeMap<Span, Vec<Call>>,
    invocations: BTreeSet<(Span, Invocation, Span)>,
}

impl Offer {
    fn of(mode: Mode, value: &Datum) -> BTreeSet<Self> {
        if mode == Mode::Via {
            return value
                .roots
                .iter()
                .filter(|root| root.inherits_mode)
                .map(|root| Self::Formal(root.region.source))
                .collect();
        }
        BTreeSet::from([Self::Input(match mode {
            Mode::Ref => Input::Ref,
            Mode::Mut => Input::Mut,
            Mode::Shared => Input::Shared,
            Mode::New => Input::New,
            _ => Input::Plain,
        })])
    }
}

impl Analyzer<'_> {
    pub(super) fn record_indirect_modes(
        &mut self,
        ctx: &Context,
        target: &Datum,
        signature: &Callable,
        values: &[(usize, Mode, Datum)],
        spans: &[Span],
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        for root in &target.roots {
            let receiver = root.region.source;
            if !root.region.selection.is_empty() || self.closure_modes.contains_key(&receiver) {
                continue;
            }
            for ((position, mode, value), &span) in values.iter().zip(spans) {
                if !signature
                    .parameters
                    .get(*position)
                    .is_some_and(|param| param.callable_mode() == Mode::Via)
                {
                    continue;
                }
                for offer in Offer::of(*mode, value) {
                    self.higher_order.invocations.insert((
                        ctx.owner,
                        Invocation {
                            receiver,
                            position: *position,
                            offer,
                        },
                        span,
                    ));
                }
            }
        }
    }

    pub(super) fn record_callable_arguments(
        &mut self,
        ctx: &Context,
        (callee, formals): (Span, &[Option<Span>]),
        signature: &Callable,
        values: &[(usize, Mode, Datum)],
        spans: &[Span],
    ) {
        if !ctx.reachable || ctx.shadow || !signature.parameters.iter().any(|param| {
            matches!(&param.ty, Ty::Callable(call) if call.parameters.iter().any(|input| input.callable_mode() == Mode::Via))
        }) {
            return;
        }
        let arguments = values
            .iter()
            .zip(spans)
            .filter_map(|((index, mode, value), &span)| {
                let formal = formals.get(*index).copied().flatten()?;
                let targets = if matches!(self.ty(span), Ty::Callable(_)) {
                    value
                        .roots
                        .iter()
                        .filter(|root| root.region.selection.is_empty())
                        .map(|root| root.region.source)
                        .collect()
                } else {
                    BTreeSet::new()
                };
                let argument = Argument {
                    offers: Offer::of(*mode, value),
                    targets,
                    dependencies: value.root_dependencies().collect(),
                    existing: value
                        .roots
                        .iter()
                        .filter(|root| !root.new)
                        .map(|root| root.region.source)
                        .collect(),
                    span,
                };
                Some((formal, argument))
            })
            .collect();
        self.higher_order
            .calls
            .entry(callee)
            .or_default()
            .push(Call {
                owner: ctx.owner,
                arguments,
            });
    }

    pub(super) fn link_higher_order_calls(&mut self) {
        let Calls { calls, invocations } = std::mem::take(&mut self.higher_order);
        let providers: BTreeMap<_, _> = self
            .functions
            .iter()
            .map(|f| (f.owner, f.formals.clone()))
            .chain(
                self.closure_modes
                    .iter()
                    .map(|(&owner, closure)| (owner, closure.formals.clone())),
            )
            .collect();
        let formal_owners: BTreeMap<_, _> = providers
            .iter()
            .flat_map(|(&owner, formals)| {
                formals.iter().flatten().map(move |&formal| (formal, owner))
            })
            .collect();
        let mut pending: VecDeque<_> = invocations.into_iter().collect();
        let mut visited = BTreeSet::new();
        while let Some((owner, invocation, span)) = pending.pop_front() {
            if !visited.insert((owner, invocation, span)) {
                continue;
            }
            if let Some(formals) = providers.get(&owner)
                && let Some(receiver) = formals
                    .iter()
                    .position(|formal| *formal == Some(invocation.receiver))
            {
                let mode = match invocation.offer {
                    Offer::Input(input) => Some(InvocationMode::Input(input)),
                    Offer::Formal(source) => formals
                        .iter()
                        .position(|formal| *formal == Some(source))
                        .map(InvocationMode::Formal),
                };
                if let Some(mode) = mode {
                    self.invocation_summaries.entry(owner).or_default().insert(
                        PublishedInvocation {
                            receiver,
                            parameter: invocation.position,
                            mode,
                        },
                    );
                }
            }
            let formal_of = |target| {
                providers
                    .get(&target)
                    .and_then(|params| params.get(invocation.position))
                    .copied()
                    .flatten()
            };
            if let Some(formal) = formal_of(invocation.receiver) {
                self.check_callback_offer(
                    owner,
                    (invocation.receiver, formal),
                    invocation.offer,
                    span,
                    None,
                );
            }
            // Substitute arguments on one edge at a time so a callback at one
            // call site cannot constrain a different instantiation.
            for call in calls.get(&owner).into_iter().flatten() {
                let Some(callback) = call.arguments.get(&invocation.receiver) else {
                    continue;
                };
                let argument = match invocation.offer {
                    Offer::Formal(formal) => call.arguments.get(&formal),
                    Offer::Input(_) => None,
                };
                let offers = argument.map_or_else(
                    || BTreeSet::from([invocation.offer]),
                    |arg| arg.offers.clone(),
                );
                for &target in &callback.targets {
                    for &offer in &offers {
                        if let Some(formal) = formal_of(target) {
                            self.check_callback_offer(
                                call.owner,
                                (target, formal),
                                offer,
                                callback.span,
                                argument,
                            );
                        } else if formal_owners.get(&target) == Some(&call.owner) {
                            pending.push_back((
                                call.owner,
                                Invocation {
                                    receiver: target,
                                    offer,
                                    ..invocation
                                },
                                callback.span,
                            ));
                        }
                    }
                }
            }
        }
    }

    fn check_callback_offer(
        &mut self,
        owner: Span,
        (callee, formal): (Span, Span),
        offer: Offer,
        span: Span,
        argument: Option<&Argument>,
    ) {
        let write = Fact {
            owner: callee,
            obligation: Obligation::Write(formal),
        };
        for (condition, accepts, code, message) in [
            (
                Obligation::Handoff(formal),
                &[Input::New][..],
                Code::E0548,
                "callback requires a new argument",
            ),
            (
                Obligation::Share(formal),
                &[Input::Shared],
                Code::E0520,
                "callback requires a shared writable argument",
            ),
            (
                Obligation::Write(formal),
                &[Input::Mut, Input::Shared, Input::New],
                Code::E0520,
                "callback requires a writable argument",
            ),
        ] {
            let premise = Fact {
                owner: callee,
                obligation: condition.clone(),
            };
            match offer {
                Offer::Input(input) if !accepts.contains(&input) => self
                    .deferred_errors
                    .push((vec![premise], Diagnostic::error(code, span, message))),
                Offer::Formal(source) => {
                    let obligation = match condition {
                        Obligation::Handoff(_) => Obligation::Handoff(source),
                        Obligation::Share(_) => Obligation::Share(source),
                        _ => Obligation::Write(source),
                    };
                    self.rules.push(Rule {
                        premises: vec![premise],
                        conclusion: Fact { owner, obligation },
                    });
                }
                Offer::Input(_) => {}
            }
        }
        if let Some(argument) = argument
            && !matches!(offer, Offer::Input(Input::Plain | Input::Ref))
        {
            for obligation in argument
                .dependencies
                .iter()
                .copied()
                .map(Obligation::Write)
                .chain(
                    argument
                        .existing
                        .iter()
                        .copied()
                        .map(Obligation::WriteExisting),
                )
            {
                self.rules.push(Rule {
                    premises: vec![write.clone()],
                    conclusion: Fact { owner, obligation },
                });
            }
        }
    }
}
